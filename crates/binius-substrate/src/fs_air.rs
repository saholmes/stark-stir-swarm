// fs_air — Tier-B M4: in-circuit Fiat-Shamir transcript (multi-block SHA-256) over B256.
//
// The recursive master must recompute the FS challenges in-circuit. binius's
// `HasherChallenger<Sha256>` is a SHA-256 duplex: absorb transcript bytes (incremental
// Digest::update), squeeze a challenge by finalize() then feed the digest back. The
// load-bearing new primitive over M1 (single-block compression) is FULL MULTI-BLOCK
// SHA-256 — FIPS 180-4 padding + chaining M1's compression from the standard IV. This
// module builds that (M4a) and gates it against `sha2::Sha256`. The duplex state
// management (M4b) is the protocol layer atop it.

use anyhow::Result;

use binius_core::fiat_shamir::HasherChallenger;
use binius_field::Field;
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{Col, ConstraintSystem, Statement, WitnessIndex, B1};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::sha256_air::{build_k_cols, build_sha256_core, populate_sha256_core, Sha256Core, K256};

/// SHA-256 initial hash values (FIPS 180-4 §5.3.3).
pub const SHA256_IV: [u32; 8] = [
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

fn u32_bits(v: u32) -> Vec<bool> {
	(0..32).map(|k| (v >> k) & 1 == 1).collect()
}
fn wc(seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, col: Col<B1, 32>, row: usize, v: u32) -> Result<()> {
	crate::nonnative::write_col::<32>(seg, col, row, &u32_bits(v))
}

/// FIPS 180-4 padding: append 0x80, zero-pad to 56 mod 64, then the 64-bit big-endian
/// bit length. Returns the padded message (a multiple of 64 bytes).
pub fn sha256_pad(msg: &[u8]) -> Vec<u8> {
	let bitlen = (msg.len() as u64) * 8;
	let mut m = msg.to_vec();
	m.push(0x80);
	while m.len() % 64 != 56 {
		m.push(0);
	}
	m.extend_from_slice(&bitlen.to_be_bytes());
	m
}

/// The 16 big-endian u32 block words of a 64-byte block.
fn block_words(block: &[u8]) -> [u32; 16] {
	std::array::from_fn(|i| u32::from_be_bytes([block[4 * i], block[4 * i + 1], block[4 * i + 2], block[4 * i + 3]]))
}

/// Native full SHA-256 (FIPS 180-4): chain the compression over the padded blocks from
/// the standard IV. Returns the 8-word state (digest = the words in big-endian bytes).
pub fn sha256_hash_ref(msg: &[u8]) -> [u32; 8] {
	let padded = sha256_pad(msg);
	let mut state = SHA256_IV;
	for block in padded.chunks(64) {
		state = crate::sha256_air::compress256_ref(&state, &block_words(block));
	}
	state
}

/// Prove + verify a full multi-block SHA-256 of `msg` IN-CIRCUIT over B256 — the FIPS IV
/// chained through one M1 compression core per padded block. Returns `(proof_bytes,
/// digest)`. Gated against `sha2::Sha256`.
pub fn prove_verify_sha256_hash(msg: &[u8]) -> Result<(usize, [u8; 32])> {
	let padded = sha256_pad(msg);
	let n_blocks = padded.len() / 64;
	assert!(n_blocks >= 1);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut table = cs.add_table("multi-block SHA-256 (FIPS 180-4)");
	let k_cols = build_k_cols(&mut table);
	// Standard SHA-256 IV as constant input-state columns for block 0.
	let ivc: [Col<B1, 32>; 8] = std::array::from_fn(|i| {
		let bits = u32_bits(SHA256_IV[i]);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		table.add_constant(format!("iv{i}"), arr)
	});

	// Chain: block k's input state = block k-1's output (block 0 = IV); w_in = block words.
	let mut cores: Vec<Sha256Core> = Vec::with_capacity(n_blocks);
	let mut win_all: Vec<[Col<B1, 32>; 16]> = Vec::with_capacity(n_blocks);
	let mut h_in = ivc;
	for k in 0..n_blocks {
		let w_in: [Col<B1, 32>; 16] =
			std::array::from_fn(|i| table.add_committed::<B1, 32>(format!("w{k}_{i}")));
		let core = build_sha256_core(&mut table.with_namespace(format!("blk{k}")), h_in, w_in, &k_cols);
		h_in = core.h_out;
		win_all.push(w_in);
		cores.push(core);
	}
	let out_state = cores[n_blocks - 1].h_out;
	let table_id = table.id();

	let statement = Statement { boundaries: vec![], table_sizes: vec![1] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let digest;
	{
		let tw = witness.init_table(table_id, 1)?;
		let mut seg = tw.full_segment();
		for i in 0..8 {
			wc(&mut seg, ivc[i], 0, SHA256_IV[i])?;
		}
		for (t, col) in k_cols.iter().enumerate() {
			wc(&mut seg, *col, 0, K256[t])?;
		}
		let mut state = SHA256_IV;
		for k in 0..n_blocks {
			let blk = block_words(&padded[k * 64..k * 64 + 64]);
			for i in 0..16 {
				wc(&mut seg, win_all[k][i], 0, blk[i])?;
			}
			populate_sha256_core(&cores[k], &mut seg, 0, &state, &blk)?;
			state = crate::sha256_air::compress256_ref(&state, &blk);
		}
		// read the digest from the final output state columns.
		let mut d = [0u8; 32];
		for i in 0..8 {
			let bits = crate::nonnative::read_col::<32>(&seg, out_state[i], 0)?;
			let w = (0..32).fold(0u32, |a, k| a | ((bits[k] as u32) << k));
			d[4 * i..4 * i + 4].copy_from_slice(&w.to_be_bytes());
		}
		digest = d;
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let sz = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	// silence unused Field import when assertions compile out
	let _ = <OurB256 as Field>::ZERO;
	Ok((sz, digest))
}

#[cfg(test)]
mod tests {
	use super::*;
	use sha2::Digest;

	/// The native multi-block hash matches `sha2::Sha256`.
	#[test]
	fn sha256_hash_ref_matches_sha2() {
		for len in [0usize, 1, 55, 56, 64, 100, 200] {
			let msg: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(31)).collect();
			let want = Sha256::digest(&msg);
			let got = sha256_hash_ref(&msg);
			let mut gb = [0u8; 32];
			for i in 0..8 {
				gb[4 * i..4 * i + 4].copy_from_slice(&got[i].to_be_bytes());
			}
			assert_eq!(&gb[..], want.as_slice(), "sha256_hash_ref != sha2 at len {len}");
		}
	}

	/// GATE M4a — a full multi-block SHA-256 proves+verifies IN-CIRCUIT over B256 and
	/// its digest == `sha2::Sha256` (2-block message).
	#[test]
	fn sha256_multiblock_proves_over_b256() {
		let msg: Vec<u8> = (0..100u32).map(|i| (i as u8) ^ 0xa5).collect(); // 100 bytes -> 2 blocks
		let want = Sha256::digest(&msg);
		let (size, got) = prove_verify_sha256_hash(&msg).expect("multi-block SHA-256 must PROVE+VERIFY");
		assert_eq!(&got[..], want.as_slice(), "in-circuit multi-block digest != sha2");
		println!(
			"GATE M4a sha256-multiblock: full FIPS-180-4 SHA-256 ({} blocks) PROVES+VERIFIES over \
			 B256 @L1(128); digest == sha2::Sha256; proof = {size} bytes",
			sha256_pad(&msg).len() / 64
		);
	}
}
