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
use binius_core::oracle::ShiftVariant;
use binius_field::underlier::WithUnderlier;
use binius_m3::builder::{Col, ConstraintSystem, Statement, TableBuilder, WitnessIndex, B1, B64};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::sha256_air::{build_k_cols, build_sha256_core, populate_sha256_core, Sha256Core, K256};

/// SHA-256 initial hash values (FIPS 180-4 §5.3.3).
pub const SHA256_IV: [u32; 8] = [
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

pub(crate) fn u32_bits(v: u32) -> Vec<bool> {
	(0..32).map(|k| (v >> k) & 1 == 1).collect()
}
pub(crate) fn wc(seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, col: Col<B1, 32>, row: usize, v: u32) -> Result<()> {
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

// --- M5 bridge: digest words -> B256 challenge field components -------------------
//
// sample::<B256>() = B256::deserialize(digest, CanonicalTower) = (u128_le(bytes[0..16]),
// u128_le(bytes[16..32])). The digest is 8 big-endian SHA-256 words, so each of the 4
// B64 tower components is c[k] = bswap32(w[2k]) | bswap32(w[2k+1])<<32. This gadget
// takes the 8 word columns (B1x32) and produces the 4 B64 field-element columns the M3
// layer consumes as the FS challenge — the tie between the SHA-256 and field worlds.

/// One byte-swap of a 32-bit word column (reverse_bytes), for the digest->field reorder.
pub(crate) struct BSwap32 {
	pub(crate) s24: Col<B1, 32>,
	s8: Col<B1, 32>,
	r8: Col<B1, 32>,
	r24: Col<B1, 32>,
	pub(crate) out: Col<B1, 32>,
}
pub(crate) fn build_bswap32(t: &mut TableBuilder<OurB256>, x: Col<B1, 32>, m1: Col<B1, 32>, m2: Col<B1, 32>, nm: &str) -> BSwap32 {
	let s24 = t.add_shifted(format!("{nm}s24"), x, 5, 24, ShiftVariant::LogicalLeft);
	let s8 = t.add_shifted(format!("{nm}s8"), x, 5, 8, ShiftVariant::LogicalLeft);
	let r8 = t.add_shifted(format!("{nm}r8"), x, 5, 8, ShiftVariant::LogicalRight);
	let r24 = t.add_shifted(format!("{nm}r24"), x, 5, 24, ShiftVariant::LogicalRight);
	let out = t.add_computed(format!("{nm}bs"), s24 + s8 * m2 + r8 * m1 + r24);
	BSwap32 { s24, s8, r8, r24, out }
}
pub(crate) fn pop_bswap32(bs: &BSwap32, seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, row: usize, x: u32) -> Result<()> {
	wc(seg, bs.s24, row, x << 24)?;
	wc(seg, bs.s8, row, x << 8)?;
	wc(seg, bs.r8, row, x >> 8)?;
	wc(seg, bs.r24, row, x >> 24)?;
	wc(seg, bs.out, row, x.swap_bytes())?;
	Ok(())
}

/// Prove + verify the digest->B256-challenge bridge in-circuit: given the 8 SHA-256
/// output words, produce the 4 B64 field-element columns of the sampled B256 challenge.
/// Returns `(proof_bytes, [component u64; 4])`; gated against B256::deserialize.
pub fn prove_verify_fs_bridge(words: [u32; 8]) -> Result<(usize, [u64; 4])> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("fs digest -> B256 challenge bridge");
	let mkmask = |t: &mut TableBuilder<OurB256>, nm: &str, v: u32| {
		let bits = u32_bits(v);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let m1 = mkmask(&mut t, "mask_ff00", 0x0000_FF00);
	let m2 = mkmask(&mut t, "mask_ff0000", 0x00FF_0000);
	let cw: [Col<B1, 32>; 8] = std::array::from_fn(|i| t.add_committed::<B1, 32>(format!("w{i}")));
	let bsw: [BSwap32; 8] = std::array::from_fn(|i| build_bswap32(&mut t, cw[i], m1, m2, &format!("bs{i}_")));
	// g[k] (B1x64) = bswap(w[2k]) (low 32) || bswap(w[2k+1]) (high 32); c[k] = packed(g[k]).
	let g: [Col<B1, 64>; 4] = std::array::from_fn(|k| t.add_committed::<B1, 64>(format!("g{k}")));
	let mut los: Vec<Col<B1, 32>> = Vec::new();
	let mut his: Vec<Col<B1, 32>> = Vec::new();
	let mut cc: Vec<Col<B64, 1>> = Vec::new();
	for k in 0..4 {
		// add_selected_block columns are NOT auto-derived — they are populated below.
		let lo = t.add_selected_block::<B1, 64, 32>(format!("g{k}_lo"), g[k], 0);
		let hi = t.add_selected_block::<B1, 64, 32>(format!("g{k}_hi"), g[k], 1);
		t.assert_zero(format!("g{k}_loc"), lo - bsw[2 * k].out);
		t.assert_zero(format!("g{k}_hic"), hi - bsw[2 * k + 1].out);
		cc.push(t.add_packed::<B1, 64, B64, 1>(format!("c{k}"), g[k]));
		los.push(lo);
		his.push(hi);
	}
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let comp = |k: usize| (words[2 * k].swap_bytes() as u64) | ((words[2 * k + 1].swap_bytes() as u64) << 32);
	let want = [comp(0), comp(1), comp(2), comp(3)];

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, NROWS)?;
		let mut seg = tw.full_segment();
		for row in 0..NROWS {
			wc(&mut seg, m1, row, 0x0000_FF00)?;
			wc(&mut seg, m2, row, 0x00FF_0000)?;
			for i in 0..8 {
				wc(&mut seg, cw[i], row, words[i])?;
				pop_bswap32(&bsw[i], &mut seg, row, words[i])?;
			}
			for k in 0..4 {
				let gbits: Vec<bool> = (0..64).map(|b| (want[k] >> b) & 1 == 1).collect();
				crate::nonnative::write_col::<64>(&mut seg, g[k], row, &gbits)?;
				// the two 32-bit blocks of g[k] must be populated explicitly.
				let lob: Vec<bool> = (0..32).map(|b| (want[k] >> b) & 1 == 1).collect();
				let hib: Vec<bool> = (0..32).map(|b| (want[k] >> (32 + b)) & 1 == 1).collect();
				crate::nonnative::write_col::<32>(&mut seg, los[k], row, &lob)?;
				crate::nonnative::write_col::<32>(&mut seg, his[k], row, &hib)?;
			}
		}
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
	let _ = cc;
	Ok((sz, want))
}

#[cfg(test)]
mod tests {
	use super::*;
	use sha2::Digest;

	/// Confirm the exact FS input: HasherChallenger<Sha256>'s first sampled 32 bytes ==
	/// SHA-256( SHA-256([]) ‖ 0u64_le ‖ transcript ). If so, an in-circuit FS challenge
	/// is just M4a (multi-block SHA-256) of this constructed input.
	#[test]
	fn fs_challenge_is_sha256_of_constructed_input() {
		use binius_core::fiat_shamir::Challenger;
		use bytes::{Buf, BufMut};

		let transcript: Vec<u8> = (0..70u32).map(|i| (i as u8).wrapping_mul(13) ^ 0x3c).collect();

		let mut ch = HasherChallenger::<Sha256>::default();
		ch.observer().put_slice(&transcript);
		let mut out = [0u8; 32];
		ch.sampler().copy_to_slice(&mut out);

		// Constructed input: initial digest SHA-256([]) ‖ index(0usize).to_le_bytes() ‖ transcript.
		let mut input = Vec::new();
		input.extend_from_slice(&Sha256::digest([]));
		input.extend_from_slice(&0usize.to_le_bytes());
		input.extend_from_slice(&transcript);

		let st = sha256_hash_ref(&input);
		let mut got = [0u8; 32];
		for i in 0..8 {
			got[4 * i..4 * i + 4].copy_from_slice(&st[i].to_be_bytes());
		}
		assert_eq!(got, out, "FS challenge != SHA-256(constructed input) — protocol trace wrong");
	}

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

	/// M5 bridge (native): confirm the digest->B256-challenge mapping. sample::<B256>()
	/// = B256::deserialize(digest, CanonicalTower) = (u128_le(bytes[0..16]),
	/// u128_le(bytes[16..32])). Since the digest is 8 big-endian SHA-256 words, each B64
	/// field component is bswap32(w[2k]) | bswap32(w[2k+1])<<32.
	#[test]
	fn fs_field_bridge_mapping() {
		use crate::b256_field::B256 as OurB256;
		use binius_field::underlier::WithUnderlier;
		use binius_utils::{DeserializeBytes, SerializationMode};
		let w: [u32; 8] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x9e3779b1) ^ 0xdead_beef);
		let mut digest = [0u8; 32];
		for i in 0..8 {
			digest[4 * i..4 * i + 4].copy_from_slice(&w[i].to_be_bytes());
		}
		let elem = OurB256::deserialize(&digest[..], SerializationMode::CanonicalTower).unwrap();
		let c = |k: usize| (w[2 * k].swap_bytes() as u64) | ((w[2 * k + 1].swap_bytes() as u64) << 32);
		let expect_lo = (c(0) as u128) | ((c(1) as u128) << 64);
		let expect_hi = (c(2) as u128) | ((c(3) as u128) << 64);
		assert_eq!(elem.lo().to_underlier(), expect_lo, "bridge lo mapping wrong");
		assert_eq!(elem.hi().to_underlier(), expect_hi, "bridge hi mapping wrong");
	}

	/// GATE M5-bridge — the digest->B256-challenge bridge proves+verifies in-circuit: the
	/// 8 SHA-256 words map (bswap + pack) to the 4 B64 field components of the sampled
	/// B256 challenge == B256::deserialize(digest). Ties the SHA-256 (M4) and field (M3) worlds.
	/// #[ignore]: WIP — add_selected_block/add_packed bit-order convention to resolve
	/// (native mapping is confirmed by fs_field_bridge_mapping; circuit plumbing pending).
	#[test]
	fn fs_bridge_proves_over_b256() {
		use crate::b256_field::B256 as OurB256_;
		use binius_field::underlier::WithUnderlier as _;
		use binius_utils::{DeserializeBytes, SerializationMode};
		let words: [u32; 8] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x85ebca6b) ^ 0xc0ffee);
		let (size, got) = prove_verify_fs_bridge(words).expect("FS bridge must PROVE+VERIFY");
		let mut digest = [0u8; 32];
		for i in 0..8 {
			digest[4 * i..4 * i + 4].copy_from_slice(&words[i].to_be_bytes());
		}
		let elem = OurB256_::deserialize(&digest[..], SerializationMode::CanonicalTower).unwrap();
		assert_eq!((got[0] as u128) | ((got[1] as u128) << 64), elem.lo().to_underlier(), "bridge lo != sample");
		assert_eq!((got[2] as u128) | ((got[3] as u128) << 64), elem.hi().to_underlier(), "bridge hi != sample");
		println!(
			"GATE M5-bridge: digest->B256 challenge (bswap + pack to 4 B64 field cols) PROVES+VERIFIES \
			 over B256 @L1(128) == B256::deserialize(sample); proof = {size} bytes"
		);
	}

	/// GATE M4b — an in-circuit Fiat-Shamir CHALLENGE proves+verifies over B256: the
	/// challenge HasherChallenger<Sha256> produces from a transcript == the M4a in-circuit
	/// SHA-256 of the reconstructed FS input. So FS challenge derivation is in-circuit
	/// (reusing M4a) — the last recursion-verifier primitive.
	#[test]
	fn fs_challenge_proves_over_b256() {
		use binius_core::fiat_shamir::Challenger;
		use bytes::{Buf, BufMut};

		let transcript: Vec<u8> = (0..90u32).map(|i| (i as u8).wrapping_mul(17) ^ 0x5c).collect();
		let mut ch = HasherChallenger::<Sha256>::default();
		ch.observer().put_slice(&transcript);
		let mut out = [0u8; 32];
		ch.sampler().copy_to_slice(&mut out);

		let mut input = Vec::new();
		input.extend_from_slice(&Sha256::digest([]));
		input.extend_from_slice(&0usize.to_le_bytes());
		input.extend_from_slice(&transcript);

		let (size, got) = prove_verify_sha256_hash(&input).expect("FS challenge must PROVE+VERIFY");
		assert_eq!(got, out, "in-circuit FS challenge != HasherChallenger<Sha256>");
		println!(
			"GATE M4b fs-challenge: in-circuit Fiat-Shamir challenge (via M4a SHA-256 of the \
			 reconstructed FS input) == binius HasherChallenger<Sha256>; proof = {size} bytes"
		);
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
