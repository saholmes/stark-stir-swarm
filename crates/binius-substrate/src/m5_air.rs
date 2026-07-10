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
use crate::gf256_air::{
	beta, build_b256_fold_pair, build_b256_mul, col4, fold_pair_native, pop_b256_fold_pair, pop_b256_mul, split256, wc64,
};
use crate::merkle_air::{merkle_root_from_path, MerklePath};
use crate::sha256_air::{build_k_cols, build_sha256_core, populate_sha256_core, K256};
use crate::fs_air::{sha256_hash_ref, sha256_pad, SHA256_IV};

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

/// Prove + verify the CODEWORD-LEAF -> B256-field bridge in-circuit: a FRI codeword value
/// as it appears in a query opening — its 32 canonical-serialization bytes read big-endian
/// into 8 SHA-256 message words (the M2 Merkle-leaf representation) — bridges (bswap + pack)
/// to the 4 B64 field components the fold consumes. Returns `(proof_bytes, [component u64;
/// 4])`, gated == `split256(value)`. read_scalar_slice deserializes with the SAME
/// SerializationMode::CanonicalTower as the challenge sampler, so this is the M5 challenge
/// bridge re-applied to a codeword value — no new primitive for the per-query value path.
pub fn prove_verify_codeword_bridge(value: OurB256) -> Result<(usize, [u64; 4])> {
	// canonical serialization: lo(16 LE) ‖ hi(16 LE); read BE into 8 SHA-256 message words.
	let mut bytes = [0u8; 32];
	bytes[0..16].copy_from_slice(&value.lo().to_underlier().to_le_bytes());
	bytes[16..32].copy_from_slice(&value.hi().to_underlier().to_le_bytes());
	let words: [u32; 8] = std::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()));

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("codeword leaf -> B256 field bridge");
	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bits = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let m1 = mkmask(&mut t, "mask_ff00", 0x0000_FF00);
	let m2 = mkmask(&mut t, "mask_ff0000", 0x00FF_0000);
	let cw: [Col<B1, 32>; 8] = std::array::from_fn(|i| t.add_committed::<B1, 32>(format!("w{i}")));
	let bsw: [BSwap32; 8] = std::array::from_fn(|i| build_bswap32(&mut t, cw[i], m1, m2, &format!("bs{i}_")));
	let g: [Col<B1, 64>; 4] = std::array::from_fn(|k| t.add_committed::<B1, 64>(format!("g{k}")));
	let mut los: Vec<Col<B1, 32>> = Vec::new();
	let mut his: Vec<Col<B1, 32>> = Vec::new();
	let mut cc: Vec<Col<B64, 1>> = Vec::new();
	for k in 0..4 {
		let lo = t.add_selected_block::<B1, 64, 32>(format!("g{k}_lo"), g[k], 0);
		let hi = t.add_selected_block::<B1, 64, 32>(format!("g{k}_hi"), g[k], 1);
		t.assert_zero(format!("g{k}_loc"), lo - bsw[2 * k].out);
		t.assert_zero(format!("g{k}_hic"), hi - bsw[2 * k + 1].out);
		cc.push(t.add_packed::<B1, 64, B64, 1>(format!("c{k}"), g[k]));
		los.push(lo);
		his.push(hi);
	}
	let table_id = t.id();

	// native gate: the bridged components == the B256 tower components of `value`.
	let want: [u64; 4] = std::array::from_fn(|k| split256(value)[k].to_underlier());
	let comp = |k: usize| (words[2 * k].swap_bytes() as u64) | ((words[2 * k + 1].swap_bytes() as u64) << 32);
	for k in 0..4 {
		assert_eq!(comp(k), want[k], "codeword-leaf bridge native mapping != split256(value)");
	}

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
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

/// Prove + verify the FRI per-query FOLD-CONSISTENCY chain IN-CIRCUIT over B256 (2 rounds,
/// arity 1). Realizes the `verify_query_internal` invariant: round r folds an opened coset,
/// and round r+1 asserts the previous fold result appears in its coset at the index-selected
/// position (`next_value == values[index % coset]`) before folding again. Here: round 0
/// folds `a=[a0,a1]` -> `f1`; round 1's coset `b` has `b[sel] = f1` (the cross-round bind,
/// asserted in-circuit) and folds -> `f2` (the terminal value). Returns `(proof_bytes, f2)`,
/// gated == the native chained fold. Composes M3c fold_pair x2 + the consistency assert —
/// the FRI query loop's core binding.
pub fn prove_verify_fold_consistency(
	a: [OurB256; 2],
	b_other: OurB256,
	r0: OurB256,
	r1: OurB256,
	tw0: OurB256,
	tw1: OurB256,
	sel: usize,
) -> Result<(usize, OurB256)> {
	assert!(sel < 2);
	// native: round 0 fold, then build round-1 coset with b[sel] = f1, then fold.
	let f1 = fold_pair_native(a[0], a[1], r0, tw0);
	let mut b = [OurB256::default(); 2];
	b[sel] = f1;
	b[1 - sel] = b_other;
	let f2 = fold_pair_native(b[0], b[1], r1, tw1);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("FRI query fold-consistency chain (2 rounds)");
	let beta_col = t.add_committed::<B64, 1>("beta");
	let ca0 = col4(&mut t, "a0");
	let ca1 = col4(&mut t, "a1");
	let cr0 = col4(&mut t, "r0");
	let ctw0 = col4(&mut t, "tw0");
	let fp0 = build_b256_fold_pair(&mut t, beta_col, ca0, ca1, cr0, ctw0, "rnd0_");

	let cb0 = col4(&mut t, "b0");
	let cb1 = col4(&mut t, "b1");
	let cr1 = col4(&mut t, "r1");
	let ctw1 = col4(&mut t, "tw1");
	// cross-round consistency: round-0's folded value == round-1 coset at position `sel`.
	let b_sel = if sel == 0 { cb0 } else { cb1 };
	for k in 0..4 {
		t.assert_zero(format!("consistency{k}"), fp0.folded[k] - b_sel[k]);
	}
	let fp1 = build_b256_fold_pair(&mut t, beta_col, cb0, cb1, cr1, ctw1, "rnd1_");
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (a0v, a1v) = (split256(a[0]), split256(a[1]));
		let (r0v, t0v) = (split256(r0), split256(tw0));
		let (b0v, b1v) = (split256(b[0]), split256(b[1]));
		let (r1v, t1v) = (split256(r1), split256(tw1));
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, ca0[i], row, a0v[i])?;
				wc64(&mut seg, ca1[i], row, a1v[i])?;
				wc64(&mut seg, cr0[i], row, r0v[i])?;
				wc64(&mut seg, ctw0[i], row, t0v[i])?;
				wc64(&mut seg, cb0[i], row, b0v[i])?;
				wc64(&mut seg, cb1[i], row, b1v[i])?;
				wc64(&mut seg, cr1[i], row, r1v[i])?;
				wc64(&mut seg, ctw1[i], row, t1v[i])?;
			}
			pop_b256_fold_pair(&fp0, &mut seg, row, a[0], a[1], r0, tw0)?;
			pop_b256_fold_pair(&fp1, &mut seg, row, b[0], b[1], r1, tw1)?;
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
	Ok((sz, f2))
}

// --- reusable codeword-leaf bridge: 8 SHA words -> 4 B64 field cols (bswap + pack) -----
// Takes the 8 leaf word columns as INPUT (not committed here), so the caller can share the
// SAME columns with an M2 Merkle path — binding the folded value to the authenticated leaf.
struct LeafBridge {
	bsw: [BSwap32; 8],
	g: [Col<B1, 64>; 4],
	los: [Col<B1, 32>; 4],
	his: [Col<B1, 32>; 4],
	cc: [Col<B64, 1>; 4], // the 4 B64 field components (add_packed, auto-derived)
}
fn build_leaf_bridge(
	t: &mut binius_m3::builder::TableBuilder<OurB256>,
	words: [Col<B1, 32>; 8],
	m1: Col<B1, 32>,
	m2: Col<B1, 32>,
	pfx: &str,
) -> LeafBridge {
	let bsw: [BSwap32; 8] = std::array::from_fn(|i| build_bswap32(t, words[i], m1, m2, &format!("{pfx}bs{i}_")));
	let g: [Col<B1, 64>; 4] = std::array::from_fn(|k| t.add_committed::<B1, 64>(format!("{pfx}g{k}")));
	let mut los = Vec::new();
	let mut his = Vec::new();
	let mut cc = Vec::new();
	for k in 0..4 {
		let lo = t.add_selected_block::<B1, 64, 32>(format!("{pfx}g{k}_lo"), g[k], 0);
		let hi = t.add_selected_block::<B1, 64, 32>(format!("{pfx}g{k}_hi"), g[k], 1);
		t.assert_zero(format!("{pfx}g{k}_loc"), lo - bsw[2 * k].out);
		t.assert_zero(format!("{pfx}g{k}_hic"), hi - bsw[2 * k + 1].out);
		cc.push(t.add_packed::<B1, 64, B64, 1>(format!("{pfx}c{k}"), g[k]));
		los.push(lo);
		his.push(hi);
	}
	LeafBridge {
		bsw,
		g,
		los: los.try_into().unwrap(),
		his: his.try_into().unwrap(),
		cc: cc.try_into().unwrap(),
	}
}
/// The 8 big-endian SHA-256 message words of a codeword value's 32 canonical bytes — the
/// M2 Merkle-leaf representation and the bridge's word-column inputs.
fn leaf_words(value: OurB256) -> [u32; 8] {
	let mut bytes = [0u8; 32];
	bytes[0..16].copy_from_slice(&value.lo().to_underlier().to_le_bytes());
	bytes[16..32].copy_from_slice(&value.hi().to_underlier().to_le_bytes());
	std::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()))
}

/// Populate the bridge's derived columns (bswap + g + los/his) from the leaf `value`. The
/// 8 word columns themselves are populated by the caller (they may be shared M2 leaf cols).
fn pop_leaf_bridge(lb: &LeafBridge, seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, row: usize, value: OurB256) -> Result<()> {
	let mut bytes = [0u8; 32];
	bytes[0..16].copy_from_slice(&value.lo().to_underlier().to_le_bytes());
	bytes[16..32].copy_from_slice(&value.hi().to_underlier().to_le_bytes());
	let words: [u32; 8] = std::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()));
	let want: [u64; 4] = std::array::from_fn(|k| split256(value)[k].to_underlier());
	for i in 0..8 {
		pop_bswap32(&lb.bsw[i], seg, row, words[i])?;
	}
	for k in 0..4 {
		let gbits: Vec<bool> = (0..64).map(|b| (want[k] >> b) & 1 == 1).collect();
		crate::nonnative::write_col::<64>(seg, lb.g[k], row, &gbits)?;
		let lob: Vec<bool> = (0..32).map(|b| (want[k] >> b) & 1 == 1).collect();
		let hib: Vec<bool> = (0..32).map(|b| (want[k] >> (32 + b)) & 1 == 1).collect();
		crate::nonnative::write_col::<32>(seg, lb.los[k], row, &lob)?;
		crate::nonnative::write_col::<32>(seg, lb.his[k], row, &hib)?;
	}
	Ok(())
}

/// Prove + verify that two FRI codeword LEAVES (32 canonical bytes each) bridge to field
/// and FOLD in ONE proof over B256: the bridge's 4 B64 output columns ARE the fold_pair
/// operands (no intermediate commit), so the folded value provably derives from the leaf
/// bytes. Returns `(proof_bytes, folded)`, gated == the native fold of the deserialized
/// leaves. Composes M5-cwbridge x2 + M3c fold_pair — the value half of the query path.
pub fn prove_verify_bridge_fold(uval: OurB256, vval: OurB256, r: OurB256, tw: OurB256) -> Result<(usize, OurB256)> {
	let folded = fold_pair_native(uval, vval, r, tw);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("codeword bridge -> fold");
	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bits = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let m1 = mkmask(&mut t, "mask_ff00", 0x0000_FF00);
	let m2 = mkmask(&mut t, "mask_ff0000", 0x00FF_0000);
	let cw_u: [Col<B1, 32>; 8] = std::array::from_fn(|i| t.add_committed::<B1, 32>(format!("u_w{i}")));
	let cw_v: [Col<B1, 32>; 8] = std::array::from_fn(|i| t.add_committed::<B1, 32>(format!("v_w{i}")));
	let lb_u = build_leaf_bridge(&mut t, cw_u, m1, m2, "u_");
	let lb_v = build_leaf_bridge(&mut t, cw_v, m1, m2, "v_");
	// the bridged field cols ARE the fold operands (the binding).
	let beta_col = t.add_committed::<B64, 1>("beta");
	let cr = col4(&mut t, "r");
	let ctw = col4(&mut t, "tw");
	let fp = build_b256_fold_pair(&mut t, beta_col, lb_u.cc, lb_v.cc, cr, ctw, "fp_");
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (rv, tvv) = (split256(r), split256(tw));
		for row in 0..NROWS {
			wc(&mut seg, m1, row, 0x0000_FF00)?;
			wc(&mut seg, m2, row, 0x00FF_0000)?;
			for (cw, val) in [(cw_u, uval), (cw_v, vval)] {
				for (i, w) in leaf_words(val).into_iter().enumerate() {
					wc(&mut seg, cw[i], row, w)?;
				}
			}
			pop_leaf_bridge(&lb_u, &mut seg, row, uval)?;
			pop_leaf_bridge(&lb_v, &mut seg, row, vval)?;
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cr[i], row, rv[i])?;
				wc64(&mut seg, ctw[i], row, tvv[i])?;
			}
			pop_b256_fold_pair(&fp, &mut seg, row, uval, vval, r, tw)?;
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
	Ok((sz, folded))
}

/// Prove + verify the FULL per-query binding IN-CIRCUIT over B256: a codeword leaf is
/// Merkle-AUTHENTICATED (M2 path leaf -> root) AND the SAME leaf columns bridge to field
/// and FOLD — all in ONE table/proof. So the folded value is provably the value committed
/// at the authenticated leaf. Returns `(proof_bytes, root, folded)`; gated == native root
/// and native fold. Composes M2b(open) + M5-cwbridge + M3c(fold) on shared leaf columns —
/// the per-query verifier's authentication+value binding.
pub fn prove_verify_query_open_fold(
	value: OurB256,
	index: usize,
	siblings: &[[u8; 32]],
	v_other: OurB256,
	r: OurB256,
	tw: OurB256,
) -> Result<(usize, [u8; 32], OurB256)> {
	let depth = siblings.len();
	// native: leaf bytes = canonical serialization of `value` (so digest_to_words == leaf_words).
	let mut leaf = [0u8; 32];
	leaf[0..16].copy_from_slice(&value.lo().to_underlier().to_le_bytes());
	leaf[16..32].copy_from_slice(&value.hi().to_underlier().to_le_bytes());
	let root_native = merkle_root_from_path(&leaf, index, siblings);
	let folded = fold_pair_native(value, v_other, r, tw);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut table = cs.add_table("query: merkle-open leaf -> bridge -> fold");
	let path = MerklePath::build_in(&mut table, depth);
	// bridge masks (distinct names from the path's own masks) + bridge over the SHARED leaf.
	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bits = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let bm1 = mkmask(&mut table, "brmask_ff00", 0x0000_FF00);
	let bm2 = mkmask(&mut table, "brmask_ff0000", 0x00FF_0000);
	let lb = build_leaf_bridge(&mut table, path.leaf, bm1, bm2, "lf_");
	// fold the authenticated leaf (lb.cc) with a second opened value.
	let beta_col = table.add_committed::<B64, 1>("beta");
	let cv = col4(&mut table, "v");
	let cr = col4(&mut table, "r");
	let ctw = col4(&mut table, "tw");
	let fp = build_b256_fold_pair(&mut table, beta_col, lb.cc, cv, cr, ctw, "fp_");
	let table_id = table.id();

	const NROWS: usize = 64; // fold's B64 packing needs a batch; replicate the query across rows.
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let mut root = [0u8; 32];
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (vv, rv, tvv) = (split256(v_other), split256(r), split256(tw));
		for row in 0..NROWS {
			path.populate(&mut seg, row, &leaf, index, siblings)?;
			wc(&mut seg, bm1, row, 0x0000_FF00)?;
			wc(&mut seg, bm2, row, 0x00FF_0000)?;
			pop_leaf_bridge(&lb, &mut seg, row, value)?;
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cv[i], row, vv[i])?;
				wc64(&mut seg, cr[i], row, rv[i])?;
				wc64(&mut seg, ctw[i], row, tvv[i])?;
			}
			pop_b256_fold_pair(&fp, &mut seg, row, value, v_other, r, tw)?;
		}
		root = path.read_root(&seg, 0)?;
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
	assert_eq!(root, root_native, "in-circuit merkle root != native");
	Ok((sz, root, folded))
}

/// Prove + verify a TWO-ROUND single FRI query IN-CIRCUIT over B256 — the query-phase
/// spine. Each round: a codeword leaf is Merkle-AUTHENTICATED to that round's root, bridged
/// to field, and folded with its coset partner. The cross-round bind (M5-foldchain) asserts
/// round 0's folded output IS round 1's authenticated leaf value (`next_value ==
/// values[index%coset]`). Returns `(proof_bytes, [root0, root1], terminal)`; gated == native
/// roots + native chained fold. Composes M5-queryopen x2 + the consistency assert.
#[allow(clippy::too_many_arguments)]
pub fn prove_verify_query_2rounds(
	v0: OurB256,
	partner0: OurB256,
	r0: OurB256,
	tw0: OurB256,
	idx0: usize,
	sib0: &[[u8; 32]],
	partner1: OurB256,
	r1: OurB256,
	tw1: OurB256,
	idx1: usize,
	sib1: &[[u8; 32]],
) -> Result<(usize, [[u8; 32]; 2], OurB256)> {
	let ser = |x: OurB256| {
		let mut b = [0u8; 32];
		b[0..16].copy_from_slice(&x.lo().to_underlier().to_le_bytes());
		b[16..32].copy_from_slice(&x.hi().to_underlier().to_le_bytes());
		b
	};
	// round 0 folds v0 with partner0 -> value1; round 1's authenticated leaf IS value1.
	let value1 = fold_pair_native(v0, partner0, r0, tw0);
	let leaf0 = ser(v0);
	let leaf1 = ser(value1);
	let root0_native = merkle_root_from_path(&leaf0, idx0, sib0);
	let root1_native = merkle_root_from_path(&leaf1, idx1, sib1);
	let terminal = fold_pair_native(value1, partner1, r1, tw1);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut table = cs.add_table("query: 2-round authenticated fold chain");
	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bits = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let bm1 = mkmask(&mut table, "brmask_ff00", 0x0000_FF00);
	let bm2 = mkmask(&mut table, "brmask_ff0000", 0x00FF_0000);
	let beta_col = table.add_committed::<B64, 1>("beta");

	// round 0: authenticate leaf0 (namespaced path) -> bridge -> fold with partner0.
	let path0 = MerklePath::build_in(&mut table.with_namespace("r0"), sib0.len());
	let lb0 = build_leaf_bridge(&mut table, path0.leaf, bm1, bm2, "lf0_");
	let cv0 = col4(&mut table, "v0");
	let cr0 = col4(&mut table, "cr0");
	let ct0 = col4(&mut table, "ct0");
	let fp0 = build_b256_fold_pair(&mut table, beta_col, lb0.cc, cv0, cr0, ct0, "fp0_");

	// round 1: authenticate leaf1 -> bridge; consistency: fp0.folded == leaf1 value; fold.
	let path1 = MerklePath::build_in(&mut table.with_namespace("r1"), sib1.len());
	let lb1 = build_leaf_bridge(&mut table, path1.leaf, bm1, bm2, "lf1_");
	for k in 0..4 {
		table.assert_zero(format!("xround{k}"), fp0.folded[k] - lb1.cc[k]);
	}
	let cv1 = col4(&mut table, "v1");
	let cr1 = col4(&mut table, "cr1");
	let ct1 = col4(&mut table, "ct1");
	let fp1 = build_b256_fold_pair(&mut table, beta_col, lb1.cc, cv1, cr1, ct1, "fp1_");
	let table_id = table.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let (mut root0, mut root1) = ([0u8; 32], [0u8; 32]);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (p0, rr0, t0) = (split256(partner0), split256(r0), split256(tw0));
		let (p1, rr1, t1) = (split256(partner1), split256(r1), split256(tw1));
		for row in 0..NROWS {
			wc(&mut seg, bm1, row, 0x0000_FF00)?;
			wc(&mut seg, bm2, row, 0x00FF_0000)?;
			wc64(&mut seg, beta_col, row, beta())?;
			path0.populate(&mut seg, row, &leaf0, idx0, sib0)?;
			pop_leaf_bridge(&lb0, &mut seg, row, v0)?;
			path1.populate(&mut seg, row, &leaf1, idx1, sib1)?;
			pop_leaf_bridge(&lb1, &mut seg, row, value1)?;
			for i in 0..4 {
				wc64(&mut seg, cv0[i], row, p0[i])?;
				wc64(&mut seg, cr0[i], row, rr0[i])?;
				wc64(&mut seg, ct0[i], row, t0[i])?;
				wc64(&mut seg, cv1[i], row, p1[i])?;
				wc64(&mut seg, cr1[i], row, rr1[i])?;
				wc64(&mut seg, ct1[i], row, t1[i])?;
			}
			pop_b256_fold_pair(&fp0, &mut seg, row, v0, partner0, r0, tw0)?;
			pop_b256_fold_pair(&fp1, &mut seg, row, value1, partner1, r1, tw1)?;
		}
		root0 = path0.read_root(&seg, 0)?;
		root1 = path1.read_root(&seg, 0)?;
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
	assert_eq!(root0, root0_native, "in-circuit root0 != native");
	assert_eq!(root1, root1_native, "in-circuit root1 != native");
	Ok((sz, [root0, root1], terminal))
}

/// Prove + verify that a fold challenge DERIVED from the transcript by an in-circuit
/// SHA-256 drives the FRI fold — the honest-challenge tie. Unlike M5-kernel (which takes
/// the digest as a committed input), here the digest is COMPUTED in-circuit: the FS input
/// `SHA-256([]) ‖ 0u64 ‖ transcript` is hashed (M4a core), its output bridges to the B256
/// challenge, and that challenge folds `u,v`. So the challenge is provably `SHA-256` of the
/// transcript — non-malleable. `transcript` must be <= 15 bytes (single SHA block). Returns
/// `(proof_bytes, folded)`, gated == native fold with the real FS challenge.
pub fn prove_verify_scheduled_fold(transcript: &[u8], u: OurB256, v: OurB256, tw: OurB256) -> Result<(usize, OurB256)> {
	use sha2::Digest;
	// native FS challenge from the transcript, and the fold it should produce.
	let mut fs_input = Vec::new();
	fs_input.extend_from_slice(&Sha256::digest([]));
	fs_input.extend_from_slice(&0u64.to_le_bytes());
	fs_input.extend_from_slice(transcript);
	let padded = sha256_pad(&fs_input);
	assert!(padded.len() == 64, "transcript must be <= 15 bytes for a single SHA block");
	let block: [u32; 16] = std::array::from_fn(|i| {
		u32::from_be_bytes([padded[4 * i], padded[4 * i + 1], padded[4 * i + 2], padded[4 * i + 3]])
	});
	let st = sha256_hash_ref(&fs_input); // 8 digest words
	let mut digest = [0u8; 32];
	for i in 0..8 {
		digest[4 * i..4 * i + 4].copy_from_slice(&st[i].to_be_bytes());
	}
	let r = OurB256::deserialize(&digest[..], SerializationMode::CanonicalTower).unwrap();
	let folded = fold_pair_native(u, v, r, tw);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("scheduled challenge drives fold");
	let mkmask = |t: &mut binius_m3::builder::TableBuilder<OurB256>, nm: &str, val: u32| {
		let bits = u32_bits(val);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(nm.to_string(), arr)
	};
	let m1 = mkmask(&mut t, "mask_ff00", 0x0000_FF00);
	let m2 = mkmask(&mut t, "mask_ff0000", 0x00FF_0000);
	// in-circuit SHA-256 of the FS input -> digest columns.
	let k_cols = build_k_cols(&mut t);
	let ivc: [Col<B1, 32>; 8] = std::array::from_fn(|i| {
		let bits = u32_bits(SHA256_IV[i]);
		let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
		t.add_constant(format!("iv{i}"), arr)
	});
	let w_in: [Col<B1, 32>; 16] = std::array::from_fn(|i| t.add_committed::<B1, 32>(format!("w{i}")));
	let core = build_sha256_core(&mut t.with_namespace("h"), ivc, w_in, &k_cols);
	let dcols = core.h_out; // the digest words that seed the challenge
	// bridge: digest words -> B256 challenge (bswap + pack), reusing the leaf bridge.
	let lb = build_leaf_bridge(&mut t, dcols, m1, m2, "ch_");
	// fold u,v with the derived challenge.
	let beta_col = t.add_committed::<B64, 1>("beta");
	let cu = col4(&mut t, "u");
	let cv = col4(&mut t, "v");
	let ctw = col4(&mut t, "tw");
	let fp = build_b256_fold_pair(&mut t, beta_col, cu, cv, lb.cc, ctw, "fp_");
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (uv, vv, tvv) = (split256(u), split256(v), split256(tw));
		// the challenge value r (as split256) is what pop_leaf_bridge must encode.
		for row in 0..NROWS {
			wc(&mut seg, m1, row, 0x0000_FF00)?;
			wc(&mut seg, m2, row, 0x00FF_0000)?;
			for (t2, col) in k_cols.iter().enumerate() {
				wc(&mut seg, *col, row, K256[t2])?;
			}
			for i in 0..8 {
				wc(&mut seg, ivc[i], row, SHA256_IV[i])?;
				wc(&mut seg, w_in[i], row, block[i])?;
			}
			for i in 8..16 {
				wc(&mut seg, w_in[i], row, block[i])?;
			}
			populate_sha256_core(&core, &mut seg, row, &SHA256_IV, &block)?;
			pop_leaf_bridge(&lb, &mut seg, row, r)?; // bridge over the (computed) digest words -> r
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
	Ok((sz, folded))
}

/// Prove + verify ONE sumcheck round IN-CIRCUIT over B256 — the STARK verifier's other
/// half (field arithmetic, not FRI). A round univariate `g` of degree <= 2 is given by
/// coefficients `[c0,c1,c2]` (g(X)=c0+c1·X+c2·X²). The verifier checks the round claim
/// `g(0)+g(1) == claim` (over GF(2^k), g(0)+g(1)=c1+c2) and reduces to the next claim
/// `g(x)` at the sampled challenge `x` via Horner (two B256 muls). Returns
/// `(proof_bytes, next_claim)`; gated == native `g(x)`, with the round check enforced
/// in-circuit. Composes gf256_air B256 multiply — reusable per sumcheck round.
pub fn prove_verify_sumcheck_round(c0: OurB256, c1: OurB256, c2: OurB256, x: OurB256) -> Result<(usize, OurB256)> {
	let claim = c1 + c2; // = g(0)+g(1) in characteristic 2
	let next = c0 + c1 * x + c2 * x * x; // g(x)

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("sumcheck round: claim check + g(x) reduce");
	let beta_col = t.add_committed::<B64, 1>("beta");
	let cc0 = col4(&mut t, "c0");
	let cc1 = col4(&mut t, "c1");
	let cc2 = col4(&mut t, "c2");
	let cx = col4(&mut t, "x");
	let cclaim = col4(&mut t, "claim");
	// round check: claim == c1 + c2 (componentwise B64 add).
	for k in 0..4 {
		t.assert_zero(format!("roundchk{k}"), cclaim[k] - (cc1[k] + cc2[k]));
	}
	// g(x) = c0 + x·(c1 + x·c2)  [Horner].
	let m1 = build_b256_mul(&mut t, beta_col, cx, cc2, "m1_"); // x·c2
	let s1 = col4(&mut t, "s1");
	for k in 0..4 {
		t.assert_zero(format!("s1c{k}"), s1[k] - (cc1[k] + m1.c[k])); // c1 + x·c2
	}
	let m2 = build_b256_mul(&mut t, beta_col, cx, s1, "m2_"); // x·(c1 + x·c2)
	let gx = col4(&mut t, "gx");
	for k in 0..4 {
		t.assert_zero(format!("gxc{k}"), gx[k] - (cc0[k] + m2.c[k])); // c0 + …
	}
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (v0, v1, v2, vx, vcl) = (split256(c0), split256(c1), split256(c2), split256(x), split256(claim));
		let xc2 = x * c2;
		let s1v = c1 + xc2;
		let vs1 = split256(s1v);
		let vgx = split256(next);
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cc0[i], row, v0[i])?;
				wc64(&mut seg, cc1[i], row, v1[i])?;
				wc64(&mut seg, cc2[i], row, v2[i])?;
				wc64(&mut seg, cx[i], row, vx[i])?;
				wc64(&mut seg, cclaim[i], row, vcl[i])?;
				wc64(&mut seg, s1[i], row, vs1[i])?;
				wc64(&mut seg, gx[i], row, vgx[i])?;
			}
			pop_b256_mul(&m1, &mut seg, row, vx, v2)?;
			pop_b256_mul(&m2, &mut seg, row, vx, vs1)?;
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
	Ok((sz, next))
}

/// Prove + verify a TWO-ROUND sumcheck CHAIN IN-CIRCUIT over B256 — the sumcheck-phase
/// spine. Round 0 checks `g0(0)+g0(1)==claim0` and reduces to `g0(x0)`; round 1's claim IS
/// that reduced value (the cross-round bind: `claim1 == g0(x0)`), which its own round check
/// `g1(0)+g1(1)==claim1` enforces, before reducing to `g1(x1)` (the final claim). `c2_1` is
/// derived so the chain is consistent. Returns `(proof_bytes, final_claim)`; gated == native.
/// Composes M5-sumcheck x2 + the cross-round claim bind.
#[allow(clippy::too_many_arguments)]
pub fn prove_verify_sumcheck_2rounds(
	c0_0: OurB256,
	c1_0: OurB256,
	c2_0: OurB256,
	x0: OurB256,
	c0_1: OurB256,
	c1_1: OurB256,
	x1: OurB256,
) -> Result<(usize, OurB256)> {
	// round 0
	let claim0 = c1_0 + c2_0;
	let g0x = c0_0 + c1_0 * x0 + c2_0 * x0 * x0;
	// round 1: claim1 = g0x (carried); pick c2_1 so c1_1 + c2_1 == claim1.
	let c2_1 = g0x + c1_1; // char 2: c1_1 + c2_1 = g0x
	let g1x = c0_1 + c1_1 * x1 + c2_1 * x1 * x1;

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("sumcheck 2-round chain");
	let beta_col = t.add_committed::<B64, 1>("beta");

	// round 0 columns + check + reduce.
	let a0 = col4(&mut t, "a0_c0");
	let a1 = col4(&mut t, "a0_c1");
	let a2 = col4(&mut t, "a0_c2");
	let ax = col4(&mut t, "a0_x");
	let acl = col4(&mut t, "a0_claim");
	for k in 0..4 {
		t.assert_zero(format!("r0chk{k}"), acl[k] - (a1[k] + a2[k]));
	}
	let am1 = build_b256_mul(&mut t, beta_col, ax, a2, "a0m1_");
	let as1 = col4(&mut t, "a0_s1");
	for k in 0..4 {
		t.assert_zero(format!("a0s1c{k}"), as1[k] - (a1[k] + am1.c[k]));
	}
	let am2 = build_b256_mul(&mut t, beta_col, ax, as1, "a0m2_");
	let agx = col4(&mut t, "a0_gx");
	for k in 0..4 {
		t.assert_zero(format!("a0gxc{k}"), agx[k] - (a0[k] + am2.c[k]));
	}

	// round 1 columns; round check uses agx as the claim (the cross-round bind).
	let b0 = col4(&mut t, "b1_c0");
	let b1 = col4(&mut t, "b1_c1");
	let b2 = col4(&mut t, "b1_c2");
	let bx = col4(&mut t, "b1_x");
	for k in 0..4 {
		t.assert_zero(format!("r1chk{k}"), agx[k] - (b1[k] + b2[k])); // claim1 == g0(x0) == c1_1+c2_1
	}
	let bm1 = build_b256_mul(&mut t, beta_col, bx, b2, "b1m1_");
	let bs1 = col4(&mut t, "b1_s1");
	for k in 0..4 {
		t.assert_zero(format!("b1s1c{k}"), bs1[k] - (b1[k] + bm1.c[k]));
	}
	let bm2 = build_b256_mul(&mut t, beta_col, bx, bs1, "b1m2_");
	let bgx = col4(&mut t, "b1_gx");
	for k in 0..4 {
		t.assert_zero(format!("b1gxc{k}"), bgx[k] - (b0[k] + bm2.c[k]));
	}
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let s = split256;
		let (as1v, ag) = (s(c1_0 + x0 * c2_0), s(g0x));
		let (bs1v, bg) = (s(c1_1 + x1 * c2_1), s(g1x));
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for (col, val) in [
				(a0, c0_0), (a1, c1_0), (a2, c2_0), (ax, x0), (acl, claim0), (as1, c1_0 + x0 * c2_0), (agx, g0x),
				(b0, c0_1), (b1, c1_1), (b2, c2_1), (bx, x1), (bs1, c1_1 + x1 * c2_1), (bgx, g1x),
			] {
				let sv = s(val);
				for i in 0..4 {
					wc64(&mut seg, col[i], row, sv[i])?;
				}
			}
			pop_b256_mul(&am1, &mut seg, row, s(x0), s(c2_0))?;
			pop_b256_mul(&am2, &mut seg, row, s(x0), as1v)?;
			pop_b256_mul(&bm1, &mut seg, row, s(x1), s(c2_1))?;
			pop_b256_mul(&bm2, &mut seg, row, s(x1), bs1v)?;
		}
		let _ = (ag, bg);
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
	Ok((sz, g1x))
}

/// Structural scope of a real inner proof's verification — reconstructs `fri_params` the
/// way `constraint_system::verify` does, so we know the exact in-circuit verifier workload
/// (FRI fold rounds/arities, query domain bits, terminate-codeword size, #oracles) BEFORE
/// wiring the full recursive verifier. Grounds the benchmark's single-proof-verify cost.
#[derive(Debug, Clone)]
pub struct RecursionScope {
	pub proof_bytes: usize,
	pub fold_arities: Vec<usize>,
	pub n_fri_rounds: usize,
	pub index_bits: usize,
	pub n_final_challenges: usize,
	pub terminate_codeword_len: usize,
	pub n_oracles: usize,
	pub total_vars: usize,
	pub n_test_queries: usize,
}

/// Build a minimal real inner proof (one B256 fold_pair) at the given `log_inv_rate`
/// (blowup = 2^log_inv_rate) and report its verification scope.
pub fn introspect_recursion_scope(log_inv_rate: usize) -> Result<RecursionScope> {
	use binius_core::merkle_tree::BinaryMerkleTreeScheme;
	use binius_core::piop;
	use binius_field::BinaryField32b;

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("inner: one B256 fold_pair");
	let beta_col = t.add_committed::<B64, 1>("beta");
	let cu = col4(&mut t, "u");
	let cv = col4(&mut t, "v");
	let cr = col4(&mut t, "r");
	let ctw = col4(&mut t, "tw");
	let fp = build_b256_fold_pair(&mut t, beta_col, cu, cv, cr, ctw, "fp_");
	let table_id = t.id();

	use binius_field::Field;
	let mut rng = rand::rngs::StdRng::from_seed([0x1c; 32]);
	use rand::SeedableRng;
	let (u, v, r, tw) = (
		<OurB256 as Field>::random(&mut rng),
		<OurB256 as Field>::random(&mut rng),
		<OurB256 as Field>::random(&mut rng),
		<OurB256 as Field>::random(&mut rng),
	);
	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		let (uv, vv, rv, tvv) = (split256(u), split256(v), split256(r), split256(tw));
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cu[i], row, uv[i])?;
				wc64(&mut seg, cv[i], row, vv[i])?;
				wc64(&mut seg, cr[i], row, rv[i])?;
				wc64(&mut seg, ctw[i], row, tvv[i])?;
			}
			pop_b256_fold_pair(&fp, &mut seg, row, u, v, r, tw)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, log_inv_rate, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let proof_bytes = proof.get_proof_size();

	// reconstruct fri_params exactly as constraint_system::verify does.
	let merkle_scheme = BinaryMerkleTreeScheme::<OurB256, Sha256, _>::new(Sha256Compression::default());
	let (commit_meta, _oracle_to_commit) = piop::make_oracle_commit_meta(&ccs.oracles)?;
	let fri_params = piop::make_commit_params_with_optimal_arity::<OurB256, BinaryField32b, _>(
		&commit_meta,
		&merkle_scheme,
		128,
		log_inv_rate,
	)?;
	let fold_arities = fri_params.fold_arities().to_vec();
	Ok(RecursionScope {
		proof_bytes,
		n_fri_rounds: fold_arities.len(),
		fold_arities,
		index_bits: fri_params.index_bits(),
		n_final_challenges: fri_params.n_final_challenges(),
		terminate_codeword_len: 1 << fri_params.n_final_challenges(),
		n_oracles: fri_params.n_oracles(),
		total_vars: commit_meta.total_vars(),
		n_test_queries: fri_params.n_test_queries(),
	})
}

/// Measure how a fold_pair table's PROVE and VERIFY scale with ROW count. The recursion
/// verifier batches its ~thousands of identical ops (each fold_pair / SHA compression is the
/// same circuit on different inputs) as ROWS of one op-table, not as width. If verify is
/// ~row-flat, the Tier-B edge-verify constant stays small even as prove grows — the O(1)
/// verify we want. Returns `(rows, prove_ms, verify_ms, proof_bytes)` per row count.
pub fn measure_fold_verify_scaling(rows_list: &[usize]) -> Result<Vec<(usize, u128, u128, usize)>> {
	use binius_field::Field;
	use std::time::Instant;
	let mut out = Vec::new();
	for &nrows in rows_list {
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let mut t = cs.add_table("fold_pair batch");
		let beta_col = t.add_committed::<B64, 1>("beta");
		let cu = col4(&mut t, "u");
		let cv = col4(&mut t, "v");
		let cr = col4(&mut t, "r");
		let ctw = col4(&mut t, "tw");
		let fp = build_b256_fold_pair(&mut t, beta_col, cu, cv, cr, ctw, "fp_");
		let table_id = t.id();
		let mut rng = rand::rngs::StdRng::from_seed([0x33; 32]);
		use rand::SeedableRng;
		let statement = Statement { boundaries: vec![], table_sizes: vec![nrows] };
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		{
			let tw_ = witness.init_table(table_id, nrows)?;
			let mut seg = tw_.full_segment();
			for row in 0..nrows {
				let (u, v, r, tw) = (
					<OurB256 as Field>::random(&mut rng),
					<OurB256 as Field>::random(&mut rng),
					<OurB256 as Field>::random(&mut rng),
					<OurB256 as Field>::random(&mut rng),
				);
				wc64(&mut seg, beta_col, row, beta())?;
				let (uv, vv, rv, tvv) = (split256(u), split256(v), split256(r), split256(tw));
				for i in 0..4 {
					wc64(&mut seg, cu[i], row, uv[i])?;
					wc64(&mut seg, cv[i], row, vv[i])?;
					wc64(&mut seg, cr[i], row, rv[i])?;
					wc64(&mut seg, ctw[i], row, tvv[i])?;
				}
				pop_b256_fold_pair(&fp, &mut seg, row, u, v, r, tw)?;
			}
		}
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<
			U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
		>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<
			U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
		>(&ccs, 1, 128, &statement.boundaries, proof)?;
		let verify_ms = t1.elapsed().as_millis();
		out.push((nrows, prove_ms, verify_ms, sz));
	}
	Ok(out)
}

/// Isolation probe: a batch of N independent SHA-256 compressions in one table (the LDT
/// Merkle-path / FS-replay op-table). Returns (verify_ms, proof_bytes). Used to confirm the
/// multi-row SHA core before assembling it with fold + sumcheck.
pub fn measure_sha_batch_verify(n_rows: usize) -> Result<(u128, usize)> {
	use std::time::Instant;
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut ts = cs.add_table("sha256 compressions");
	// Multi-row constants must be COMMITTED (populated every row), NOT add_constant transparent
	// oracles — the SHA core's adders read these values, and a transparent single-value poly
	// disagrees with a filled multi-row column under the ring-switch evaluation.
	let k_cols: Vec<Col<B1, 32>> = (0..64).map(|t| ts.add_committed::<B1, 32>(format!("K{t}"))).collect();
	let ivc: [Col<B1, 32>; 8] = std::array::from_fn(|i| ts.add_committed::<B1, 32>(format!("iv{i}")));
	let w_in: [Col<B1, 32>; 16] = std::array::from_fn(|i| ts.add_committed::<B1, 32>(format!("w{i}")));
	let core = build_sha256_core(&mut ts.with_namespace("c"), ivc, w_in, &k_cols);
	let _ = core.h_out;
	let sha_id = ts.id();
	let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let mut rng = rand::rngs::StdRng::from_seed([0x4a; 32]);
	use rand::{RngCore, SeedableRng};
	{
		let tw = witness.init_table(sha_id, n_rows)?;
		let mut seg = tw.full_segment();
		for row in 0..n_rows {
			for i in 0..8 {
				wc(&mut seg, ivc[i], row, SHA256_IV[i])?;
			}
			for (t, col) in k_cols.iter().enumerate() {
				wc(&mut seg, *col, row, K256[t])?;
			}
			let blk: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
			for i in 0..16 {
				wc(&mut seg, w_in[i], row, blk[i])?;
			}
			populate_sha256_core(&core, &mut seg, row, &SHA256_IV, &blk)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let sz = proof.get_proof_size();
	let t1 = Instant::now();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((t1.elapsed().as_millis(), sz))
}

/// Measure the ASSEMBLED recursion verify as ONE number, with the three-term decomposition.
/// Builds the three real op-tables the row-batched recursion verifier reduces to — SHA-256
/// compressions (LDT Merkle paths + FS replay), fold_pairs (LDT coset folds), sumcheck
/// rounds — in ONE constraint system at the given row counts, and times the single verify.
/// Because verify is row-flat, moderate row counts read off the recursion-scale constant.
/// Returns `(n_sha, n_fold, n_sum, prove_ms, verify_ms, proof_bytes)` per scale.
pub fn measure_assembled_recursion_verify(scales: &[(usize, usize, usize)]) -> Result<Vec<(usize, usize, usize, u128, u128, usize)>> {
	use binius_field::Field;
	use std::time::Instant;
	let mut out = Vec::new();
	for &(n_sha, n_fold, n_sum) in scales {
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();

		// --- table 0: SHA-256 compressions (one per row); COMMITTED constants (multi-row) ---
		let mut ts = cs.add_table("sha256 compressions");
		let k_cols: Vec<Col<B1, 32>> = (0..64).map(|t| ts.add_committed::<B1, 32>(format!("K{t}"))).collect();
		let ivc: [Col<B1, 32>; 8] = std::array::from_fn(|i| ts.add_committed::<B1, 32>(format!("iv{i}")));
		let w_in: [Col<B1, 32>; 16] = std::array::from_fn(|i| ts.add_committed::<B1, 32>(format!("w{i}")));
		let core = build_sha256_core(&mut ts.with_namespace("c"), ivc, w_in, &k_cols);
		let _ = core.h_out;
		let sha_id = ts.id();

		// --- table 1: fold_pairs ---
		let mut tf = cs.add_table("fold_pairs");
		let beta_col = tf.add_committed::<B64, 1>("beta");
		let fu = col4(&mut tf, "u");
		let fv = col4(&mut tf, "v");
		let frr = col4(&mut tf, "r");
		let ftw = col4(&mut tf, "tw");
		let fp = build_b256_fold_pair(&mut tf, beta_col, fu, fv, frr, ftw, "fp_");
		let fold_id = tf.id();

		// --- table 2: sumcheck rounds ---
		let mut tc = cs.add_table("sumcheck rounds");
		let sbeta = tc.add_committed::<B64, 1>("sbeta");
		let sc0 = col4(&mut tc, "sc0");
		let sc1 = col4(&mut tc, "sc1");
		let sc2 = col4(&mut tc, "sc2");
		let sx = col4(&mut tc, "sx");
		let sclaim = col4(&mut tc, "sclaim");
		for k in 0..4 {
			tc.assert_zero(format!("srchk{k}"), sclaim[k] - (sc1[k] + sc2[k]));
		}
		let sm1 = build_b256_mul(&mut tc, sbeta, sx, sc2, "sm1_");
		let ss1 = col4(&mut tc, "ss1");
		for k in 0..4 {
			tc.assert_zero(format!("ss1c{k}"), ss1[k] - (sc1[k] + sm1.c[k]));
		}
		let sm2 = build_b256_mul(&mut tc, sbeta, sx, ss1, "sm2_");
		let sgx = col4(&mut tc, "sgx");
		for k in 0..4 {
			tc.assert_zero(format!("sgxc{k}"), sgx[k] - (sc0[k] + sm2.c[k]));
		}
		let sum_id = tc.id();

		let statement = Statement { boundaries: vec![], table_sizes: vec![n_sha, n_fold, n_sum] };
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		let mut rng = rand::rngs::StdRng::from_seed([0x4a; 32]);
		use rand::{RngCore, SeedableRng};
		// SHA rows
		{
			let tw = witness.init_table(sha_id, n_sha)?;
			let mut seg = tw.full_segment();
			for row in 0..n_sha {
				for i in 0..8 {
					wc(&mut seg, ivc[i], row, SHA256_IV[i])?;
				}
				for (t, col) in k_cols.iter().enumerate() {
					wc(&mut seg, *col, row, K256[t])?;
				}
				let blk: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
				for i in 0..16 {
					wc(&mut seg, w_in[i], row, blk[i])?;
				}
				populate_sha256_core(&core, &mut seg, row, &SHA256_IV, &blk)?;
			}
		}
		// fold rows
		{
			let tw = witness.init_table(fold_id, n_fold)?;
			let mut seg = tw.full_segment();
			for row in 0..n_fold {
				let (u, v, r, tw2) = (
					<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng),
					<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng),
				);
				wc64(&mut seg, beta_col, row, beta())?;
				let (uv, vv, rv, tvv) = (split256(u), split256(v), split256(r), split256(tw2));
				for i in 0..4 {
					wc64(&mut seg, fu[i], row, uv[i])?;
					wc64(&mut seg, fv[i], row, vv[i])?;
					wc64(&mut seg, frr[i], row, rv[i])?;
					wc64(&mut seg, ftw[i], row, tvv[i])?;
				}
				pop_b256_fold_pair(&fp, &mut seg, row, u, v, r, tw2)?;
			}
		}
		// sumcheck rows
		{
			let tw = witness.init_table(sum_id, n_sum)?;
			let mut seg = tw.full_segment();
			for row in 0..n_sum {
				let (c0, c1, c2, x) = (
					<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng),
					<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng),
				);
				let claim = c1 + c2;
				let s1v = c1 + x * c2;
				wc64(&mut seg, sbeta, row, beta())?;
				for (col, val) in [(sc0, c0), (sc1, c1), (sc2, c2), (sx, x), (sclaim, claim), (ss1, s1v), (sgx, c0 + x * s1v)] {
					let sv = split256(val);
					for i in 0..4 {
						wc64(&mut seg, col[i], row, sv[i])?;
					}
				}
				pop_b256_mul(&sm1, &mut seg, row, split256(x), split256(c2))?;
				pop_b256_mul(&sm2, &mut seg, row, split256(x), split256(s1v))?;
			}
		}

		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<
			U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
		>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<
			U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
		>(&ccs, 1, 128, &statement.boundaries, proof)?;
		out.push((n_sha, n_fold, n_sum, prove_ms, t1.elapsed().as_millis(), sz));
	}
	Ok(out)
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

	/// Introspect a real inner proof's verification scope — the concrete FRI/sumcheck
	/// structure the recursive verifier must reproduce. Reported (not asserted) to scope
	/// the assembly + ground the benchmark's single-verify cost.
	#[test]
	fn recursion_scope_introspection() {
		let s = introspect_recursion_scope(1).expect("introspection must succeed");
		println!(
			"RECURSION-SCOPE (inner = 1 B256 fold_pair, L1, blowup=2): proof={} B  total_vars={}  \
			 FRI: {} rounds arities={:?} index_bits={} terminate_len={} n_oracles={} n_queries={}",
			s.proof_bytes, s.total_vars, s.n_fri_rounds, s.fold_arities, s.index_bits,
			s.terminate_codeword_len, s.n_oracles, s.n_test_queries
		);
		assert!(s.proof_bytes > 0);
	}

	/// Probe: multi-row SHA-256 compression batch verifies (isolates the SHA op-table).
	#[test]
	fn sha_batch_probe() {
		for n in [64usize, 256, 1024] {
			let (v, sz) = super::measure_sha_batch_verify(n).expect("sha batch must verify");
			println!("# SHA batch {n} rows: verify {v} ms, proof {} KB", sz / 1024);
		}
	}

	/// The ASSEMBLED recursion verify as ONE measured number (L1) — the three real op-tables
	/// (SHA-256 compressions + fold_pairs + sumcheck) in one CS. ★DOMINATED BY THE SHA TABLE:
	/// SHA-256 is the adder-heavy in-circuit gadget (~26s+ verify even at 64 rows), so the
	/// assembled verify is TENS OF SECONDS, NOT the ~60ms the fold-only table suggested. This
	/// is the number the reviewer asked for; it motivates leveling the recursion hash to
	/// Keccak/SHA3 (the cheap in-circuit arithmetization AND the correct binding hash).
	#[test]
	#[ignore] // heavy (~minutes): SHA op-table dominates prove+verify
	fn assembled_recursion_verify() {
		let scales = [(64usize, 256usize, 64usize), (256, 512, 64)];
		let res = measure_assembled_recursion_verify(&scales).expect("assembled measure must succeed");
		println!("| n_sha | n_fold | n_sum | prove ms | verify ms | proof KB |");
		println!("|---:|---:|---:|---:|---:|---:|");
		for (a, b, c, p, v, sz) in &res {
			println!("| {} | {} | {} | {} | {} | {} |", a, b, c, p, v, sz / 1024);
		}
		let (_, _, _, _, v_scale, _) = *res.last().unwrap();
		println!(
			"# ASSEMBLED L1 recursion verify = {} ms — DOMINATED by the SHA-256 op-table (adder-heavy). \
			 The fold-only ~60ms was unrepresentative. Leveling recursion hash -> Keccak/SHA3 collapses \
			 this term (cheap in-circuit) AND fixes binding soundness. Steady-state amortization survives.",
			v_scale
		);
	}

	/// Verify-vs-rows scaling for a batched fold_pair table — answers whether the recursion
	/// verify constant stays small as the op count (rows) grows to the ~6.8k-op recursion
	/// scale. If verify is ~flat while prove grows, the Tier-B O(1)-in-N edge verify is fast.
	#[test]
	fn fold_verify_row_scaling() {
		let rows = [64usize, 256, 1024, 4096, 16384];
		let res = measure_fold_verify_scaling(&rows).expect("scaling measurement must succeed");
		println!("| rows | prove ms | verify ms | proof B |");
		println!("|---:|---:|---:|---:|");
		for (n, p, v, sz) in &res {
			println!("| {} | {} | {} | {} |", n, p, v, sz);
		}
		let v0 = res.first().map(|r| r.2).unwrap_or(0);
		let vn = res.last().map(|r| r.2).unwrap_or(0);
		println!(
			"# verify {} ms @ {} rows -> {} ms @ {} rows ({:.1}x for {}x rows). Recursion verify \
			 is row-batched: prove scales with ops, verify stays ~flat -> small O(1) edge verify.",
			v0, rows[0], vn, rows[rows.len() - 1],
			if v0 > 0 { vn as f64 / v0 as f64 } else { 0.0 }, rows[rows.len() - 1] / rows[0]
		);
	}

	/// Blowup sweep — n_queries (and thus the in-circuit verifier workload) vs blowup. The
	/// recursion circuit is dominated by n_queries x per-query [Merkle opens + chunk-folds];
	/// higher blowup cuts n_queries. Reports the per-op verifier work each blowup implies.
	#[test]
	fn recursion_scope_blowup_sweep() {
		println!(
			"| blowup | proof B | n_queries | FRI rounds (arities) | per-query SHA-compress | \
			 per-query fold_pairs | total SHA-compress | total fold_pairs |"
		);
		println!("|---:|---:|---:|:--|---:|---:|---:|---:|");
		for lir in 1..=5usize {
			let s = match introspect_recursion_scope(lir) {
				Ok(s) => s,
				Err(e) => {
					println!("| {} | (prove failed: {e}) |", 1usize << lir);
					continue;
				}
			};
			// per query: for each FRI round r, open a coset of size 2^arity via a Merkle path
			// of depth = index_bits - (sum of prior arities); a depth-d path = d SHA-256
			// compressions; an arity-a coset fold = (2^a - 1) fold_pairs (chunk-fold).
			let mut depth = s.index_bits;
            let mut sha_per_q = 0usize;
			let mut folds_per_q = 0usize;
			for &a in &s.fold_arities {
				sha_per_q += depth; // one authentication path this round
				folds_per_q += (1usize << a) - 1; // chunk-fold of the 2^a coset
				depth = depth.saturating_sub(a);
			}
			let tot_sha = sha_per_q * s.n_test_queries;
			let tot_folds = folds_per_q * s.n_test_queries;
			println!(
				"| {} | {} | {} | {} {:?} | {} | {} | {} | {} |",
				1usize << lir, s.proof_bytes, s.n_test_queries, s.n_fri_rounds, s.fold_arities,
				sha_per_q, folds_per_q, tot_sha, tot_folds
			);
		}
		println!(
			"# Recursion circuit is dominated by n_queries x per-query work. Higher blowup cuts \
			 n_queries (fewer in-circuit Merkle opens + folds) at the cost of a larger inner proof."
		);
	}

	/// GATE M5-sumchain — a TWO-ROUND sumcheck chain PROVES+VERIFIES in-circuit over B256:
	/// round 1's claim is bound to round 0's reduced value g0(x0) (enforced by round 1's own
	/// g1(0)+g1(1)==claim1 check), and the final claim g1(x1) == native. The sumcheck-phase
	/// spine — symmetric to the FRI query-phase spine.
	#[test]
	fn sumcheck_2rounds_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0x77; 32]);
		use rand::SeedableRng;
		let c0_0 = <OurB256 as Field>::random(&mut rng);
		let c1_0 = <OurB256 as Field>::random(&mut rng);
		let c2_0 = <OurB256 as Field>::random(&mut rng);
		let x0 = <OurB256 as Field>::random(&mut rng);
		let c0_1 = <OurB256 as Field>::random(&mut rng);
		let c1_1 = <OurB256 as Field>::random(&mut rng);
		let x1 = <OurB256 as Field>::random(&mut rng);
		let g0x = c0_0 + c1_0 * x0 + c2_0 * x0 * x0;
		let c2_1 = g0x + c1_1;
		let want = c0_1 + c1_1 * x1 + c2_1 * x1 * x1;
		let (size, got) =
			prove_verify_sumcheck_2rounds(c0_0, c1_0, c2_0, x0, c0_1, c1_1, x1).expect("sumcheck chain must PROVE+VERIFY");
		assert_eq!(got, want, "in-circuit sumcheck chain final claim != native");
		println!(
			"GATE M5-sumchain: 2-round sumcheck chain (claim1 bound to g0(x0)) PROVES+VERIFIES over \
			 B256 @L1(128) == native; proof = {size} bytes"
		);
	}

	/// GATE M5-sumcheck — ONE sumcheck round PROVES+VERIFIES in-circuit over B256: the
	/// round check `g(0)+g(1)==claim` is enforced and the next claim `g(x)` is computed by
	/// Horner (two B256 muls) == native. The STARK verifier's field-arithmetic half, per
	/// round — reused across the sumcheck phase.
	#[test]
	fn sumcheck_round_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0x11; 32]);
		use rand::SeedableRng;
		for _ in 0..2 {
			let c0 = <OurB256 as Field>::random(&mut rng);
			let c1 = <OurB256 as Field>::random(&mut rng);
			let c2 = <OurB256 as Field>::random(&mut rng);
			let x = <OurB256 as Field>::random(&mut rng);
			let want = c0 + c1 * x + c2 * x * x;
			let (size, got) = prove_verify_sumcheck_round(c0, c1, c2, x).expect("sumcheck round must PROVE+VERIFY");
			assert_eq!(got, want, "in-circuit g(x) != native");
			let _ = size;
		}
		println!(
			"GATE M5-sumcheck: one sumcheck round (check g(0)+g(1)==claim; reduce to g(x) via \
			 Horner) PROVES+VERIFIES over B256 @L1(128) == native"
		);
	}

	/// GATE M5-schedfold — a fold challenge DERIVED from the transcript by an in-circuit
	/// SHA-256 drives the FRI fold: the FS input is hashed (M4a), its digest bridges to the
	/// B256 challenge, and that challenge folds u,v == native fold with the real FS
	/// challenge. Closes the honest-challenge gap — the fold challenge is provably SHA-256
	/// of the transcript, not a free input.
	#[test]
	fn scheduled_fold_proves_over_b256() {
		use binius_utils::{DeserializeBytes, SerializationMode};
		use sha2::Digest;
		let mut rng = rand::rngs::StdRng::from_seed([0x5e; 32]);
		use rand::SeedableRng;
		let transcript: [u8; 12] = std::array::from_fn(|i| (i as u8).wrapping_mul(19) ^ 0x2c);
		let u = <OurB256 as Field>::random(&mut rng);
		let v = <OurB256 as Field>::random(&mut rng);
		let tw = <OurB256 as Field>::random(&mut rng);
		// independent native expectation
		let mut fs_input = Vec::new();
		fs_input.extend_from_slice(&Sha256::digest([]));
		fs_input.extend_from_slice(&0u64.to_le_bytes());
		fs_input.extend_from_slice(&transcript);
		let st = crate::fs_air::sha256_hash_ref(&fs_input);
		let mut digest = [0u8; 32];
		for i in 0..8 {
			digest[4 * i..4 * i + 4].copy_from_slice(&st[i].to_be_bytes());
		}
		let r = OurB256::deserialize(&digest[..], SerializationMode::CanonicalTower).unwrap();
		let want = fold_pair_native(u, v, r, tw);

		let (size, got) = prove_verify_scheduled_fold(&transcript, u, v, tw).expect("scheduled fold must PROVE+VERIFY");
		assert_eq!(got, want, "in-circuit scheduled fold != native fold with FS challenge");
		println!(
			"GATE M5-schedfold: fold challenge DERIVED in-circuit (SHA-256 of transcript -> bridge) \
			 drives the fold over B256 @L1(128) == native; proof = {size} bytes"
		);
	}

	/// GATE M5-query2 — a TWO-ROUND single FRI query PROVES+VERIFIES in ONE proof over
	/// B256: each round authenticates its leaf (path->root), bridges, and folds; the
	/// cross-round assert binds round 0's fold output to round 1's authenticated leaf value.
	/// The query-phase spine (authenticate -> fold -> consistency -> authenticate -> fold).
	#[test]
	fn query_2rounds_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0x21; 32]);
		use rand::SeedableRng;
		let v0 = <OurB256 as Field>::random(&mut rng);
		let partner0 = <OurB256 as Field>::random(&mut rng);
		let (r0, tw0) = (<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng));
		let partner1 = <OurB256 as Field>::random(&mut rng);
		let (r1, tw1) = (<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng));
		let sib0: [[u8; 32]; 2] = [std::array::from_fn(|i| (i as u8) ^ 0x33), std::array::from_fn(|i| (i as u8).wrapping_mul(5) ^ 0x71)];
		let sib1: [[u8; 32]; 2] = [std::array::from_fn(|i| (i as u8).wrapping_mul(3) ^ 0x18), std::array::from_fn(|i| (i as u8) ^ 0xc4)];
		let value1 = fold_pair_native(v0, partner0, r0, tw0);
		let want_terminal = fold_pair_native(value1, partner1, r1, tw1);

		let (size, roots, terminal) =
			prove_verify_query_2rounds(v0, partner0, r0, tw0, 2, &sib0, partner1, r1, tw1, 1, &sib1)
				.expect("2-round query must PROVE+VERIFY");
		let ser = |x: OurB256| {
			let mut b = [0u8; 32];
			b[0..16].copy_from_slice(&x.lo().to_underlier().to_le_bytes());
			b[16..32].copy_from_slice(&x.hi().to_underlier().to_le_bytes());
			b
		};
		assert_eq!(roots[0], crate::merkle_air::merkle_root_from_path(&ser(v0), 2, &sib0), "root0 != native");
		assert_eq!(roots[1], crate::merkle_air::merkle_root_from_path(&ser(value1), 1, &sib1), "root1 != native");
		assert_eq!(terminal, want_terminal, "terminal fold != native");
		println!(
			"GATE M5-query2: 2-round single FRI query (authenticate->fold->consistency->\
			 authenticate->fold) PROVES+VERIFIES over B256 @L1(128) == native; proof = {size} bytes"
		);
	}

	/// GATE M5-queryopen — the FULL per-query binding in ONE proof: a codeword leaf is
	/// Merkle-AUTHENTICATED (path -> root) and the SAME leaf columns bridge to field and
	/// FOLD, so the folded value is provably the value committed at the authenticated leaf.
	/// Composes M2b(open) + cwbridge + fold on shared columns == native root + native fold.
	#[test]
	fn query_open_fold_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0x90; 32]);
		use rand::SeedableRng;
		let value = <OurB256 as Field>::random(&mut rng);
		let v_other = <OurB256 as Field>::random(&mut rng);
		let r = <OurB256 as Field>::random(&mut rng);
		let tw = <OurB256 as Field>::random(&mut rng);
		let siblings: [[u8; 32]; 2] =
			[std::array::from_fn(|i| (i as u8).wrapping_mul(13) ^ 0x22), std::array::from_fn(|i| (i as u8).wrapping_mul(7) ^ 0x9e)];
		let index = 2usize;
		let want_fold = fold_pair_native(value, v_other, r, tw);
		let mut leaf = [0u8; 32];
		use binius_field::underlier::WithUnderlier as _;
		leaf[0..16].copy_from_slice(&value.lo().to_underlier().to_le_bytes());
		leaf[16..32].copy_from_slice(&value.hi().to_underlier().to_le_bytes());
		let want_root = crate::merkle_air::merkle_root_from_path(&leaf, index, &siblings);

		let (size, root, folded) =
			prove_verify_query_open_fold(value, index, &siblings, v_other, r, tw).expect("query open+fold must PROVE+VERIFY");
		assert_eq!(root, want_root, "in-circuit root != native");
		assert_eq!(folded, want_fold, "in-circuit folded != native");
		println!(
			"GATE M5-queryopen: Merkle-authenticated leaf (path->root) AND its fold share the SAME \
			 columns in ONE proof over B256 @L1(128) == native root + fold; proof = {size} bytes"
		);
	}

	/// GATE M5-bridgefold — two FRI codeword leaves bridge to field AND fold in ONE proof:
	/// the bridge's B64 output columns ARE the fold_pair operands (no intermediate commit),
	/// so the folded value provably derives from the 32 canonical leaf bytes == native fold
	/// of the deserialized leaves. The value half of the per-query path, bound end-to-end.
	#[test]
	fn bridge_fold_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0xbf; 32]);
		use rand::SeedableRng;
		let uval = <OurB256 as Field>::random(&mut rng);
		let vval = <OurB256 as Field>::random(&mut rng);
		let r = <OurB256 as Field>::random(&mut rng);
		let tw = <OurB256 as Field>::random(&mut rng);
		let want = fold_pair_native(uval, vval, r, tw);
		let (size, got) = prove_verify_bridge_fold(uval, vval, r, tw).expect("bridge->fold must PROVE+VERIFY");
		assert_eq!(got, want, "in-circuit bridge->fold != native fold of deserialized leaves");
		println!(
			"GATE M5-bridgefold: codeword leaves bridge (bytes->field) AND fold in ONE proof over \
			 B256 @L1(128) — bridged cols ARE the fold operands == native; proof = {size} bytes"
		);
	}

	/// GATE M5-foldchain — the FRI per-query fold-consistency chain PROVES+VERIFIES in
	/// ONE proof over B256: round 0 folds a coset -> f1; round 1 asserts f1 is its coset's
	/// value at the index-selected position (the `next_value == values[index%coset]` bind
	/// from verify_query_internal) then folds -> f2 == native. A tampered f1 breaks the
	/// consistency assert. The FRI query loop's core cross-round binding, in-circuit.
	#[test]
	fn fold_consistency_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0xf0; 32]);
		use rand::SeedableRng;
		for sel in [0usize, 1] {
			let a = [<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng)];
			let b_other = <OurB256 as Field>::random(&mut rng);
			let (r0, r1) = (<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng));
			let (tw0, tw1) = (<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng));
			// native expected terminal
			let f1 = fold_pair_native(a[0], a[1], r0, tw0);
			let mut b = [OurB256::default(); 2];
			b[sel] = f1;
			b[1 - sel] = b_other;
			let want = fold_pair_native(b[0], b[1], r1, tw1);
			let (size, got) =
				prove_verify_fold_consistency(a, b_other, r0, r1, tw0, tw1, sel).expect("fold chain must PROVE+VERIFY");
			assert_eq!(got, want, "in-circuit fold-consistency terminal != native (sel={sel})");
			let _ = size;
		}
		println!(
			"GATE M5-foldchain: FRI per-query fold-consistency chain (fold -> assert \
			 next_value==values[index%coset] -> fold) PROVES+VERIFIES over B256 @L1(128) == native"
		);
	}

	/// GATE M5-cwbridge — a FRI codeword leaf value bridges to the fold's field cols
	/// in-circuit: the 32 canonical-serialization bytes (as M2 hashes them, big-endian SHA
	/// words) map (bswap + pack) to the 4 B64 components == split256(value). Since
	/// read_scalar_slice uses the SAME CanonicalTower mode as challenge sampling, the per-
	/// query VALUE path reuses the M5 bridge — no new primitive.
	#[test]
	fn codeword_bridge_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0xc0; 32]);
		use rand::SeedableRng;
		for _ in 0..3 {
			let value = <OurB256 as Field>::random(&mut rng);
			let (size, got) = prove_verify_codeword_bridge(value).expect("codeword bridge must PROVE+VERIFY");
			let want: [u64; 4] = std::array::from_fn(|k| split256(value)[k].to_underlier());
			assert_eq!(got, want, "in-circuit codeword bridge != split256(value)");
			let _ = size;
		}
		println!(
			"GATE M5-cwbridge: FRI codeword leaf (canonical bytes, big-endian SHA words) bridges \
			 to 4 B64 fold cols == split256(value) over B256 @L1(128) — per-query value path"
		);
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
