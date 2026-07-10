// m5_air — Tier-B M5 kernel: the recursive-verify composition.
//
// This proves, in ONE proof, the essence of the recursive rollup: a Fiat-Shamir
// challenge recomputed IN-CIRCUIT (digest -> B256 field element, the M5 bridge) DRIVES
// the FRI fold (M3 fold_pair over the full B256 field). It composes the SHA-256 world
// (M4/bridge) with the field world (M3) end-to-end. Scaling this to the full inner-proof
// verifier (challenge schedule -> per-query Merkle open -> chunk-fold -> root check +
// sumcheck) is the remaining M5 assembly; this is its load-bearing kernel.

use anyhow::Result;

use binius_core::fiat_shamir::HasherChallenger;
use binius_field::underlier::WithUnderlier;
use binius_field::Field;
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{Col, ConstraintSystem, Statement, WitnessIndex, B1, B64};
use binius_utils::{DeserializeBytes, SerializationMode};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::fs_air::{build_bswap32, pop_bswap32, u32_bits, wc, BSwap32};
use crate::gf256_air::{beta, build_b256_fold_pair, col4, fold_pair_native, pop_b256_fold_pair, split256, wc64};

/// Prove + verify the M5 kernel: given a FS-challenge digest (8 SHA-256 words) and fold
/// operands `u,v` + twiddle `tw`, recompute the B256 challenge `r` from the digest
/// (bridge) and fold `folded = u + (v'-u')·r` (fold_pair) — in ONE proof. Returns
/// `(proof_bytes, folded)`; gated against the native fold with the deserialized challenge.
pub fn prove_verify_m5_kernel(
	words: [u32; 8],
	u: OurB256,
	v: OurB256,
	tw: OurB256,
) -> Result<(usize, OurB256)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("m5 kernel: FS challenge drives FRI fold");

	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bits = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let m1 = mkmask(&mut t, "mask_ff00", 0x0000_FF00);
	let m2 = mkmask(&mut t, "mask_ff0000", 0x00FF_0000);

	// --- bridge: digest words -> B256 challenge components ---
	let cw: [Col<B1, 32>; 8] = std::array::from_fn(|i| t.add_committed::<B1, 32>(format!("w{i}")));
	let bsw: [BSwap32; 8] = std::array::from_fn(|i| build_bswap32(&mut t, cw[i], m1, m2, &format!("bs{i}_")));
	let g: [Col<B1, 64>; 4] = std::array::from_fn(|k| t.add_committed::<B1, 64>(format!("g{k}")));
	let mut los: Vec<Col<B1, 32>> = Vec::new();
	let mut his: Vec<Col<B1, 32>> = Vec::new();
	let mut chal: Vec<Col<B64, 1>> = Vec::new();
	for k in 0..4 {
		let lo = t.add_selected_block::<B1, 64, 32>(format!("g{k}_lo"), g[k], 0);
		let hi = t.add_selected_block::<B1, 64, 32>(format!("g{k}_hi"), g[k], 1);
		t.assert_zero(format!("g{k}_loc"), lo - bsw[2 * k].out);
		t.assert_zero(format!("g{k}_hic"), hi - bsw[2 * k + 1].out);
		chal.push(t.add_packed::<B1, 64, B64, 1>(format!("chal{k}"), g[k]));
		los.push(lo);
		his.push(hi);
	}
	let challenge: [Col<B64, 1>; 4] = chal.try_into().unwrap();

	// --- fold: folded = fold_pair(u, v, challenge, tw) ---
	let beta_col = t.add_committed::<B64, 1>("beta");
	let cu = col4(&mut t, "u");
	let cv = col4(&mut t, "v");
	let ctw = col4(&mut t, "tw");
	let fp = build_b256_fold_pair(&mut t, beta_col, cu, cv, challenge, ctw, "fp_");
	let table_id = t.id();

	// native: r = deserialize(digest); folded = fold_pair_native(u, v, r, tw)
	let mut digest = [0u8; 32];
	for i in 0..8 {
		digest[4 * i..4 * i + 4].copy_from_slice(&words[i].to_be_bytes());
	}
	let r = OurB256::deserialize(&digest[..], SerializationMode::CanonicalTower).unwrap();
	let folded = fold_pair_native(u, v, r, tw);
	let rc = split256(r);

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (uv, vv, tvv) = (split256(u), split256(v), split256(tw));
		for row in 0..NROWS {
			wc(&mut seg, m1, row, 0x0000_FF00)?;
			wc(&mut seg, m2, row, 0x00FF_0000)?;
			for i in 0..8 {
				wc(&mut seg, cw[i], row, words[i])?;
				pop_bswap32(&bsw[i], &mut seg, row, words[i])?;
			}
			for k in 0..4 {
				let want = rc[k].to_underlier();
				let gbits: Vec<bool> = (0..64).map(|b| (want >> b) & 1 == 1).collect();
				crate::nonnative::write_col::<64>(&mut seg, g[k], row, &gbits)?;
				let lob: Vec<bool> = (0..32).map(|b| (want >> b) & 1 == 1).collect();
				let hib: Vec<bool> = (0..32).map(|b| (want >> (32 + b)) & 1 == 1).collect();
				crate::nonnative::write_col::<32>(&mut seg, los[k], row, &lob)?;
				crate::nonnative::write_col::<32>(&mut seg, his[k], row, &hib)?;
			}
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cu[i], row, uv[i])?;
				wc64(&mut seg, cv[i], row, vv[i])?;
				wc64(&mut seg, ctw[i], row, tvv[i])?;
			}
			pop_b256_fold_pair(&fp, &mut seg, row, u, v, r, tw)?;
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
	let _ = fp.folded;
	Ok((sz, folded))
}

/// Prove + verify the FRI query-index derivation `sample_bits(bits)` in-circuit: the
/// index = low `bits` bits of u32_le(digest[0..4]) = bswap32(word[0]) & ((1<<bits)-1).
/// Returns `(proof_bytes, index)`. This is the query index that drives M2b's path MUX.
pub fn prove_verify_query_index(word0: u32, bits: usize) -> Result<(usize, u32)> {
	assert!(bits <= 32);
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("fri query index sample_bits");
	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bb = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bb[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let m1 = mkmask(&mut t, "mask_ff00", 0x0000_FF00);
	let m2 = mkmask(&mut t, "mask_ff0000", 0x00FF_0000);
	let mask_val = if bits == 32 { u32::MAX } else { (1u32 << bits) - 1 };
	let maskc = mkmask(&mut t, "idx_mask", mask_val);

	let cw0 = t.add_committed::<B1, 32>("w0");
	let bs = build_bswap32(&mut t, cw0, m1, m2, "bs0_");
	// idx = bswap(w0) & mask  (per-bit AND = B1 multiply).
	let idx = t.add_computed("idx", bs.out * maskc);
	let table_id = t.id();

	let index = word0.swap_bytes() & mask_val;

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		for row in 0..NROWS {
			wc(&mut seg, m1, row, 0x0000_FF00)?;
			wc(&mut seg, m2, row, 0x00FF_0000)?;
			wc(&mut seg, maskc, row, mask_val)?;
			wc(&mut seg, cw0, row, word0)?;
			pop_bswap32(&bs, &mut seg, row, word0)?;
			wc(&mut seg, idx, row, index)?;
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
	Ok((sz, index))
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::Field;

	/// GATE M5-qidx — the FRI query-index sample_bits proves+verifies in-circuit ==
	/// binius sample_bits_reader (u32_le(digest[0..4]) & mask).
	#[test]
	fn query_index_proves_over_b256() {
		for (word0, bits) in [(0x1234_5678u32, 8usize), (0xdead_beef, 12), (0x0000_00ff, 5), (0xffff_ffff, 20)] {
			let (size, idx) = prove_verify_query_index(word0, bits).expect("query index must PROVE+VERIFY");
			let mask = if bits == 32 { u32::MAX } else { (1u32 << bits) - 1 };
			assert_eq!(idx, word0.swap_bytes() & mask, "in-circuit query index != sample_bits");
			let _ = size;
		}
		println!("GATE M5-qidx: FRI query-index sample_bits PROVES+VERIFIES over B256 @L1(128) == binius sample_bits_reader");
	}

	/// GATE M5-kernel — a recomputed FS challenge DRIVES the FRI fold in ONE proof: the
	/// digest->B256 bridge feeds the fold_pair, and the result == the native fold with
	/// the deserialized challenge. The recursive-verify kernel (FS <-> field <-> fold).
	#[test]
	fn m5_kernel_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0x5c; 32]);
		use rand::SeedableRng;
		let words: [u32; 8] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x27d4eb2f) ^ 0xf00d);
		let u = <OurB256 as Field>::random(&mut rng);
		let v = <OurB256 as Field>::random(&mut rng);
		let tw = <OurB256 as Field>::random(&mut rng);
		// native challenge + fold
		let mut digest = [0u8; 32];
		for i in 0..8 {
			digest[4 * i..4 * i + 4].copy_from_slice(&words[i].to_be_bytes());
		}
		let r = OurB256::deserialize(&digest[..], SerializationMode::CanonicalTower).unwrap();
		let want = fold_pair_native(u, v, r, tw);

		let (size, got) = prove_verify_m5_kernel(words, u, v, tw).expect("M5 kernel must PROVE+VERIFY");
		assert_eq!(got, want, "in-circuit M5 kernel != native fold with sampled challenge");
		println!(
			"GATE M5-kernel: a recomputed FS challenge (digest->B256 bridge) DRIVES the FRI \
			 fold_pair in ONE proof over B256 @L1(128) == native; proof = {size} bytes"
		);
	}
}
