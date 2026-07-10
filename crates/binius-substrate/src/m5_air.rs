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
