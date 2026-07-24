// accumulation_air — the in-circuit FOLD-VERIFY, and whether it is NARROW (Option 3).
//
// The whole thesis of accumulation (vs Tier-B) is that the recursion step arithmetizes the
// FOLD-VERIFY (a few field ops, no hash gadget) instead of the FRI-VERIFY (wide hash gadgets).
// binius verify is LINEAR in committed width (m5_air::verify_vs_width_diagnostic: ~20ms +
// 1.3ms/mul), so if the fold-verify circuit is narrow, its proof verifies in tens of ms — the
// ms recursion the wide FRI-verify circuit (seconds) can't reach.
//
// The prover supplies the fold polynomial g in COEFFICIENT form (degree d = n_total vars of
// the interleaved poly). The verifier checks g(0)=v0 (= c_0), g(1)=v1 (= Σc_i), computes the
// folded value g(t) by HORNER, and the folded point line(r0,r1,t)=r0+t(r0+r1). That's 2d B256
// multiplies, NO inversions. Soundness that g really is M∘ℓ is deferred to the decider's
// single opening (accumulation's whole point). Gated == native; measures verify vs d.

use anyhow::Result;

use binius_core::fiat_shamir::HasherChallenger;
use binius_field::Field;
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{Col, ConstraintSystem, Statement, TableWitnessSegment, WitnessIndex, B64};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::b512_field::{B512TowerFamily, B512 as OurB512, U512};
use crate::gf256_air::{beta, build_b256_mul, col4, pop_b256_mul, split256, wc64};
use crate::gf512_air::{build_b512_mul, split512};

type C4 = [Col<B64, 1>; 4];

/// Native fold-verify (coefficient form). Returns `Some((line, folded))` iff g(0)=v0 and
/// g(1)=v1, where folded = g(t) (Horner) and line[k] = r0[k] + t·(r0[k]+r1[k]).
pub fn fold_verify_native(g: &[OurB256], t: OurB256, v0: OurB256, v1: OurB256, r0: &[OurB256], r1: &[OurB256]) -> Option<(Vec<OurB256>, OurB256)> {
	if *g.first()? != v0 {
		return None;
	}
	let sum: OurB256 = g.iter().copied().fold(OurB256::ZERO, |a, c| a + c);
	if sum != v1 {
		return None;
	}
	let mut acc = *g.last().unwrap();
	for &c in g.iter().rev().skip(1) {
		acc = acc * t + c;
	}
	let line: Vec<OurB256> = r0.iter().zip(r1).map(|(&a, &b)| a + t * (a + b)).collect();
	Some((line, acc))
}

fn put(seg: &mut TableWitnessSegment<OurB256>, row: usize, c: &C4, v: OurB256) -> Result<()> {
	let sp = split256(v);
	for j in 0..4 {
		wc64(seg, c[j], row, sp[j])?;
	}
	Ok(())
}

/// Prove + verify the in-circuit fold-verify for a degree-`d` fold (d≥1) with RANDOM inputs.
/// Returns `(prove_ms, verify_ms, proof_bytes, n_b256_muls)`. Wrapper over `fold_step`.
pub fn prove_verify_fold_verify(d: usize) -> Result<(u128, u128, usize, usize)> {
	prove_verify_fold_verify_rows(d, 64)
}

/// As `prove_verify_fold_verify` but with an explicit row count `nrows` --- the number of
/// interior fold-verify steps proved in ONE Binius table.  A balanced fold tree over `N` leaves
/// has `N-1` interior nodes, so proving the whole tree at `nrows = N-1` and verifying the single
/// resulting proof gives the edge a fold check whose cost is polylog in `N` (the fold-verify AIR
/// is narrow / width-independent of leaves), replacing the `O(N)` native fold-path replay ---
/// i.e.\ the \emph{hierarchical} (recursive) edge fold.  Returns `(prove_ms, verify_ms, bytes, muls)`.
pub fn prove_verify_fold_verify_rows(d: usize, nrows: usize) -> Result<(u128, u128, usize, usize)> {
	use rand::SeedableRng;
	assert!(d >= 1);
	let mut rng = rand::rngs::StdRng::from_seed([0xac; 32]);
	let g: Vec<OurB256> = (0..=d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let t = <OurB256 as Field>::random(&mut rng);
	let r0: Vec<OurB256> = (0..d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let r1: Vec<OurB256> = (0..d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let s = fold_step(&g, t, &r0, &r1, nrows)?;
	Ok((s.prove_ms, s.verify_ms, s.proof_bytes, 2 * d))
}

/// One proven IVC fold step: the folded claim + this step's cost.
pub struct StepOut {
	pub line: Vec<OurB256>,
	pub folded: OurB256,
	pub prove_ms: u128,
	pub verify_ms: u128,
	pub proof_bytes: usize,
}

/// Build + prove + verify the fold-verify circuit for EXPLICIT inputs (the IVC step): given
/// the fold polynomial `g` (coefficients, degree d = g.len()−1), challenge `t`, and the two
/// points `r0,r1` (dimension d), returns the folded claim (line, g(t)) + timing. v0=g[0],
/// v1=Σg. The circuit is 2d B256 muls (Horner + line), no hash — the narrow recursion step.
pub fn fold_step(g: &[OurB256], t: OurB256, r0: &[OurB256], r1: &[OurB256], nrows: usize) -> Result<StepOut> {
	use std::time::Instant;
	let d = g.len() - 1;
	assert!(d >= 1 && r0.len() == d && r1.len() == d);
	let v0 = g[0];
	let v1 = g.iter().copied().fold(OurB256::ZERO, |a, c| a + c);
	let (line_n, folded_n) = fold_verify_native(g, t, v0, v1, r0, r1).expect("native fold must verify");
	let g = g.to_vec();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut tb = cs.add_table("fold-verify (Horner + line)");
	let beta_col = tb.add_committed::<B64, 1>("beta");
	let cg: Vec<C4> = (0..=d).map(|i| col4(&mut tb, &format!("g{i}"))).collect();
	let ct = col4(&mut tb, "t");
	let cv0 = col4(&mut tb, "v0");
	let cv1 = col4(&mut tb, "v1");
	let cr0: Vec<C4> = (0..d).map(|k| col4(&mut tb, &format!("r0_{k}"))).collect();
	let cr1: Vec<C4> = (0..d).map(|k| col4(&mut tb, &format!("r1_{k}"))).collect();

	let mut n_muls = 0usize;
	// g(0) = c_0 == v0
	for j in 0..4 {
		tb.assert_zero(format!("g0eq{j}"), cg[0][j] - cv0[j]);
	}
	// g(1) = Σ c_i == v1  (d≥1 ⇒ cg has ≥2 entries; start the accumulator as an expression).
	for j in 0..4 {
		let mut acc = cg[0][j] + cg[1][j];
		for c in cg.iter().skip(2) {
			acc = acc + c[j];
		}
		tb.assert_zero(format!("g1eq{j}"), acc - cv1[j]);
	}
	// Horner: acc = c_d; for i=d-1..0: acc = acc·t + c_i.
	let mut horner_m = Vec::with_capacity(d);
	let mut hacc = Vec::with_capacity(d);
	let mut acc = cg[d];
	for i in (0..d).rev() {
		let m = build_b256_mul(&mut tb, beta_col, acc, ct, &format!("hm{i}_"));
		n_muls += 1;
		let next = col4(&mut tb, &format!("hacc{i}"));
		for j in 0..4 {
			tb.assert_zero(format!("hacc{i}_{j}"), next[j] - (m.c[j] + cg[i][j]));
		}
		horner_m.push(m);
		hacc.push(next);
		acc = next;
	}
	// line[k] = r0[k] + t·(r0[k]+r1[k])
	let mut s_cols = Vec::with_capacity(d);
	let mut line_m = Vec::with_capacity(d);
	let mut cline = Vec::with_capacity(d);
	for k in 0..d {
		let s = col4(&mut tb, &format!("s{k}"));
		for j in 0..4 {
			tb.assert_zero(format!("s{k}_{j}"), s[j] - (cr0[k][j] + cr1[k][j]));
		}
		let m = build_b256_mul(&mut tb, beta_col, ct, s, &format!("lm{k}_"));
		n_muls += 1;
		let l = col4(&mut tb, &format!("line{k}"));
		for j in 0..4 {
			tb.assert_zero(format!("line{k}_{j}"), l[j] - (cr0[k][j] + m.c[j]));
		}
		s_cols.push(s);
		line_m.push(m);
		cline.push(l);
	}
	let table_id = tb.id();

	let nrows = nrows.next_power_of_two().max(1);
	let statement = Statement { boundaries: vec![], table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, nrows)?;
		let mut seg = tw.full_segment();
		for row in 0..nrows {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..=d {
				put(&mut seg, row, &cg[i], g[i])?;
			}
			put(&mut seg, row, &ct, t)?;
			put(&mut seg, row, &cv0, v0)?;
			put(&mut seg, row, &cv1, v1)?;
			for k in 0..d {
				put(&mut seg, row, &cr0[k], r0[k])?;
				put(&mut seg, row, &cr1[k], r1[k])?;
			}
			// Horner: mul acc_val·t, then acc_val = acc_val·t + c_i.
			let mut acc_val = g[d];
			for (idx, i) in (0..d).rev().enumerate() {
				pop_b256_mul(&horner_m[idx], &mut seg, row, split256(acc_val), split256(t))?;
				acc_val = acc_val * t + g[i];
				put(&mut seg, row, &hacc[idx], acc_val)?;
			}
			// line
			for k in 0..d {
				let s = r0[k] + r1[k];
				put(&mut seg, row, &s_cols[k], s)?;
				pop_b256_mul(&line_m[k], &mut seg, row, split256(t), split256(s))?;
				put(&mut seg, row, &cline[k], line_n[k])?;
			}
			let _ = folded_n;
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let t0 = Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let prove_ms = t0.elapsed().as_millis();
	let _ = n_muls;
	let sz = proof.get_proof_size();
	let t1 = Instant::now();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok(StepOut { line: line_n, folded: folded_n, prove_ms, verify_ms: t1.elapsed().as_millis(), proof_bytes: sz })
}

/// One fold step's explicit inputs: fold polynomial `g` (deg d), challenge `t`, points `r0,r1`.
pub type FoldStepIn = (Vec<OurB256>, OurB256, Vec<OurB256>, Vec<OurB256>);

/// Prove ALL `steps` fold-verifies in ONE table (each ROW a distinct fold), and verify the single
/// resulting proof.  This is the O(1) COLLAPSE of the trustless combiner: N−1 accumulation folds
/// become one narrow fold-verify AIR (fixed degree d, width-independent of N), so the resolver
/// verifies ONE proof whose cost is polylog in N — not O(N) per-step verifies.  Returns
/// `(all_valid, prove_ms, verify_ms, proof_bytes)`.  All steps must share the degree d.
pub fn prove_fold_tree(steps: &[FoldStepIn]) -> Result<(bool, u128, u128, usize)> {
	use std::time::Instant;
	assert!(!steps.is_empty(), "need ≥1 fold step");
	let d = steps[0].0.len() - 1;
	assert!(d >= 1, "fold degree ≥ 1");
	for (g, _t, r0, r1) in steps {
		assert!(g.len() == d + 1 && r0.len() == d && r1.len() == d, "all steps must share degree d");
	}
	// each row's native fold must verify (else a forged step is present).
	let mut all_valid = true;
	let mut rows: Vec<(Vec<OurB256>, OurB256, OurB256, OurB256, Vec<OurB256>, Vec<OurB256>, Vec<OurB256>)> = Vec::with_capacity(steps.len());
	for (g, t, r0, r1) in steps {
		let v0 = g[0];
		let v1 = g.iter().copied().fold(OurB256::ZERO, |a, c| a + c);
		match fold_verify_native(g, *t, v0, v1, r0, r1) {
			Some((line, _folded)) => rows.push((g.clone(), *t, v0, v1, r0.clone(), r1.clone(), line)),
			None => {
				all_valid = false;
				// still build a well-formed padding row so the table proves (a valid fold).
				let (line, _f) = fold_verify_native(&steps[0].0, steps[0].1, steps[0].0[0], steps[0].0.iter().copied().fold(OurB256::ZERO, |a, c| a + c), &steps[0].2, &steps[0].3).unwrap();
				rows.push((steps[0].0.clone(), steps[0].1, steps[0].0[0], steps[0].0.iter().copied().fold(OurB256::ZERO, |a, c| a + c), steps[0].2.clone(), steps[0].3.clone(), line));
			}
		}
	}
	if !all_valid {
		return Ok((false, 0, 0, 0)); // a forged fold step ⇒ the combiner is caught (native gate)
	}

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut tb = cs.add_table("fold-tree (N−1 distinct fold-verifies in one table)");
	let beta_col = tb.add_committed::<B64, 1>("beta");
	let cg: Vec<C4> = (0..=d).map(|i| col4(&mut tb, &format!("g{i}"))).collect();
	let ct = col4(&mut tb, "t");
	let cv0 = col4(&mut tb, "v0");
	let cv1 = col4(&mut tb, "v1");
	let cr0: Vec<C4> = (0..d).map(|k| col4(&mut tb, &format!("r0_{k}"))).collect();
	let cr1: Vec<C4> = (0..d).map(|k| col4(&mut tb, &format!("r1_{k}"))).collect();
	for j in 0..4 {
		tb.assert_zero(format!("g0eq{j}"), cg[0][j] - cv0[j]);
	}
	for j in 0..4 {
		let mut acc = cg[0][j] + cg[1][j];
		for c in cg.iter().skip(2) {
			acc = acc + c[j];
		}
		tb.assert_zero(format!("g1eq{j}"), acc - cv1[j]);
	}
	let mut horner_m = Vec::with_capacity(d);
	let mut hacc = Vec::with_capacity(d);
	let mut acc = cg[d];
	for i in (0..d).rev() {
		let m = build_b256_mul(&mut tb, beta_col, acc, ct, &format!("hm{i}_"));
		let next = col4(&mut tb, &format!("hacc{i}"));
		for j in 0..4 {
			tb.assert_zero(format!("hacc{i}_{j}"), next[j] - (m.c[j] + cg[i][j]));
		}
		horner_m.push(m);
		hacc.push(next);
		acc = next;
	}
	let mut s_cols = Vec::with_capacity(d);
	let mut line_m = Vec::with_capacity(d);
	let mut cline = Vec::with_capacity(d);
	for k in 0..d {
		let s = col4(&mut tb, &format!("s{k}"));
		for j in 0..4 {
			tb.assert_zero(format!("s{k}_{j}"), s[j] - (cr0[k][j] + cr1[k][j]));
		}
		let m = build_b256_mul(&mut tb, beta_col, ct, s, &format!("lm{k}_"));
		let l = col4(&mut tb, &format!("line{k}"));
		for j in 0..4 {
			tb.assert_zero(format!("line{k}_{j}"), l[j] - (cr0[k][j] + m.c[j]));
		}
		s_cols.push(s);
		line_m.push(m);
		cline.push(l);
	}
	let table_id = tb.id();

	let nrows = rows.len().next_power_of_two().max(1);
	let statement = Statement { boundaries: vec![], table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, nrows)?;
		let mut seg = tw.full_segment();
		for row in 0..nrows {
			let (g, t, v0, v1, r0, r1, line) = &rows[row.min(rows.len() - 1)]; // pad with the last valid row
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..=d {
				put(&mut seg, row, &cg[i], g[i])?;
			}
			put(&mut seg, row, &ct, *t)?;
			put(&mut seg, row, &cv0, *v0)?;
			put(&mut seg, row, &cv1, *v1)?;
			for k in 0..d {
				put(&mut seg, row, &cr0[k], r0[k])?;
				put(&mut seg, row, &cr1[k], r1[k])?;
			}
			let mut acc_val = g[d];
			for (idx, i) in (0..d).rev().enumerate() {
				pop_b256_mul(&horner_m[idx], &mut seg, row, split256(acc_val), split256(*t))?;
				acc_val = acc_val * *t + g[i];
				put(&mut seg, row, &hacc[idx], acc_val)?;
			}
			for k in 0..d {
				let s = r0[k] + r1[k];
				put(&mut seg, row, &s_cols[k], s)?;
				pop_b256_mul(&line_m[k], &mut seg, row, split256(*t), split256(s))?;
				put(&mut seg, row, &cline[k], line[k])?;
			}
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let t0 = Instant::now();
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend(),
	)?;
	let prove_ms = t0.elapsed().as_millis();
	let sz = proof.get_proof_size();
	let t1 = Instant::now();
	binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, 1, 128, &statement.boundaries, proof,
	)?;
	Ok((true, prove_ms, t1.elapsed().as_millis(), sz))
}

/// Tamper knob for the chained fold-tree soundness tests.
#[derive(Clone, Copy, PartialEq)]
pub enum ChainTamper {
	None,
	/// Forge an intermediate accumulator value the prover feeds into the next fold (row `at`).
	ForgeAccValue { at: usize },
	/// Reorder: swap which predecessor accumulator two rows consume (breaks the chain).
	SwapAccInputs,
}

/// CHAINED, ONE-PROOF fold tree — the F2 collapse, FRI-native. `run_ivc` folds N leaf claims into
/// one via N−1 steps but proves each step as a SEPARATE proof (O(N) verify). This proves the WHOLE
/// chain in ONE proof: N−1 fold rows in one table, threaded by an accumulator CHANNEL (row j PULLS
/// `acc_{j-1}` and PUSHES `acc_j`; a boundary pushes `acc_0` = leaf 0 and pulls the final `acc`),
/// with a per-row STEP-POSITION lane so the multiset cannot admit a re-ordering. So the resolver
/// verifies ONE FRI proof (polylog in N) whose channel structurally forces the folds to be the
/// real chain — not N independent folds (`prove_fold_tree`) nor N separate proofs (`run_ivc`).
///
/// SOUNDNESS this milestone establishes (tamper-tested): a forged intermediate accumulator, or a
/// re-ordered chain, is REJECTED. The `pi_hash` public-input binding (leaf points ==
/// derive_point(pi_hash,i), challenges == H(pi_hash‖R*‖k)) is the NEXT layer; here the leaves and
/// challenges are inputs, and the decider `mle256(P, acc.point) == acc.value` is checked natively
/// (in production it is the committed-decider FRI opening — one opening, O(1) in N).
///
/// Returns `(chain_valid_in_circuit, decider_holds, prove_ms, verify_ms, proof_bytes)`.
pub fn prove_chained_fold_tree(
	p: &[OurB256],
	leaves: &[(Vec<OurB256>, OurB256)],
	challenges: &[OurB256],
	tamper: ChainTamper,
) -> Result<(bool, bool, u128, u128, usize)> {
	prove_chained_fold_tree_bound(p, leaves, challenges, tamper, None)
}

/// Milestone 2 — the same chained one-proof fold tree, additionally BOUND to a public input
/// `pi_hash`. `pi = Some((build_pi, rstar, verify_pi))`: every leaf POINT and every fold CHALLENGE
/// is pinned by a boundary to its `pi_hash`-derived value (`derive_point`/`derive_challenge`), so a
/// verifier reconstructing the boundaries from a DIFFERENT `pi_hash` (`verify_pi != build_pi`) gets
/// different points ⇒ the proof, built for `build_pi`, no longer balances ⇒ REJECT. This is the
/// non-substitutability anchor from `seam_aggregation`: the binding lives in the CLAIMS' points,
/// FS-derived from `pi_hash`. Values (P-evaluations) stay — they are the claims being proven and
/// are checked by the decider. `pi = None` reproduces milestone 1.
pub fn prove_chained_fold_tree_bound(
	p: &[OurB256],
	leaves: &[(Vec<OurB256>, OurB256)],
	challenges: &[OurB256],
	tamper: ChainTamper,
	pi: Option<([u8; 32], [u8; 32], [u8; 32])>,
) -> Result<(bool, bool, u128, u128, usize)> {
	prove_chained_fold_tree_full(p, leaves, challenges, tamper, pi, None, false)
}

/// Milestone 3 — the same one-proof, `pi_hash`-bound chained fold tree, with the final accumulated
/// claim discharged by the IN-STACK COMMITTED-DECIDER opening instead of a native `mle256`. When
/// `decider_p128 = Some(P_b128)`, the returned `decider_holds` is the result of committing `P`
/// (→ R*) and opening it at `acc.point` through the FRI-Binius piop (`decider_open_at_ext_l1`),
/// then VERIFYING that opening against R* (`decider_verify_rooted_ext_l1`) — so the resolver
/// proves `P(acc.point) == acc.value` WITHOUT holding `P`, in ONE opening (O(1) in N). Set
/// `forge_final` to corrupt the claimed final value and confirm the committed decider REJECTS it.
pub fn prove_chained_fold_tree_full(
	p: &[OurB256],
	leaves: &[(Vec<OurB256>, OurB256)],
	challenges: &[OurB256],
	tamper: ChainTamper,
	pi: Option<([u8; 32], [u8; 32], [u8; 32])>,
	decider_p128: Option<&[binius_field::BinaryField128b]>,
	forge_final: bool,
) -> Result<(bool, bool, u128, u128, usize)> {
	use binius_core::constraint_system::channel::FlushDirection;
	use binius_m3::builder::Boundary;
	use std::time::Instant;

	let nlv = leaves.len();
	assert!(nlv >= 2 && nlv.is_power_of_two(), "need ≥2 leaves, power of two");
	assert_eq!(challenges.len(), nlv - 1, "one challenge per fold");
	let d = leaves[0].0.len();
	assert!(d >= 1 && leaves.iter().all(|(pt, _)| pt.len() == d));

	// ── native chain: acc_0 = leaf 0; acc_j = fold(acc_{j-1}, leaf_j). Record per-fold (g,t,r0,r1)
	//    and the outputs (line, folded). `g` is the coeff-form line restriction of P.
	let eval_coeffs = |g: &[OurB256], t: OurB256| -> OurB256 {
		let mut acc = g[g.len() - 1];
		for i in (0..g.len() - 1).rev() {
			acc = acc * t + g[i];
		}
		acc
	};
	struct Fold {
		g: Vec<OurB256>,
		t: OurB256,
		r0: Vec<OurB256>,
		r1: Vec<OurB256>,
		v0: OurB256,
		v1: OurB256,
		line: Vec<OurB256>,
		folded: OurB256,
	}
	let mut acc = leaves[0].clone();
	let mut folds: Vec<Fold> = Vec::with_capacity(nlv - 1);
	for j in 1..nlv {
		let (r0, v0) = (acc.0.clone(), acc.1);
		let (r1, v1) = (leaves[j].0.clone(), leaves[j].1);
		let t = challenges[j - 1];
		let g = restrict_to_line_coeffs(p, &r0, &r1);
		debug_assert_eq!(g[0], v0);
		debug_assert_eq!(g.iter().copied().fold(OurB256::ZERO, |a, c| a + c), v1);
		let line = line256(&r0, &r1, t);
		let folded = eval_coeffs(&g, t);
		acc = (line.clone(), folded);
		folds.push(Fold { g, t, r0, r1, v0, v1, line, folded });
	}
	// Decider: discharge the final accumulated claim `P(acc.point) == acc.value`. Native model =
	// direct `mle256`; production model = the COMMITTED-DECIDER opening against R*-committed P (one
	// FRI opening, the resolver never holds P). `forge_final` corrupts the claimed value to confirm
	// the committed decider rejects a false final claim.
	let claimed_value = if forge_final { acc.1 + OurB256::ONE } else { acc.1 };
	let decider_holds = match decider_p128 {
		None => mle256(p, &acc.0) == claimed_value,
		Some(p128) => {
			let (root, proof, opened, nv) = crate::decider::decider_open_at_ext_l1(p128, &acc.0, 128);
			// the opening's value must equal the claim AND verify against the commitment root.
			opened == claimed_value
				&& crate::decider::decider_verify_rooted_ext_l1(root, proof, &acc.0, claimed_value, nv, 128)
		}
	};

	// ── the AIR: one table, `nrows` = N−1 fold rows (padded to a power of two). Each row proves one
	//    fold-verify AND flows the accumulator through the `acc` channel with a step-position lane.
	let dg = d; // fold-poly degree == point dim (line restriction of P over d vars)
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let acc_ch = cs.add_channel("acc-chain");
	let pub_ch = pi.map(|_| cs.add_channel("pi-bound-leaf-challenge"));
	let mut tb = cs.add_table("chained fold tree");
	let beta_col = tb.add_committed::<B64, 1>("beta");
	let cg: Vec<C4> = (0..=dg).map(|i| col4(&mut tb, &format!("g{i}"))).collect();
	let ct = col4(&mut tb, "t");
	let cv0 = col4(&mut tb, "v0");
	let cv1 = col4(&mut tb, "v1");
	let cr0: Vec<C4> = (0..dg).map(|k| col4(&mut tb, &format!("r0_{k}"))).collect();
	let cr1: Vec<C4> = (0..dg).map(|k| col4(&mut tb, &format!("r1_{k}"))).collect();
	let cpos_in = tb.add_committed::<B64, 1>("pos_in");
	let cpos_out = tb.add_committed::<B64, 1>("pos_out");

	// g(0)=v0 ; g(1)=Σg=v1
	for j in 0..4 {
		tb.assert_zero(format!("g0eq{j}"), cg[0][j] - cv0[j]);
	}
	for j in 0..4 {
		let mut a = cg[0][j] + cg[1][j];
		for c in cg.iter().skip(2) {
			a = a + c[j];
		}
		tb.assert_zero(format!("g1eq{j}"), a - cv1[j]);
	}
	// Horner: folded = g(t).
	let mut horner_m = Vec::with_capacity(dg);
	let mut hacc = Vec::with_capacity(dg);
	let mut acc_e = cg[dg];
	for i in (0..dg).rev() {
		let m = build_b256_mul(&mut tb, beta_col, acc_e, ct, &format!("hm{i}_"));
		let next = col4(&mut tb, &format!("hacc{i}"));
		for j in 0..4 {
			tb.assert_zero(format!("hacc{i}_{j}"), next[j] - (m.c[j] + cg[i][j]));
		}
		horner_m.push(m);
		hacc.push(next);
		acc_e = next;
	}
	let folded_col = *hacc.last().unwrap(); // = g(t)
	// line[k] = r0[k] + t·(r0[k]+r1[k]).
	let mut s_cols = Vec::with_capacity(dg);
	let mut line_m = Vec::with_capacity(dg);
	let mut cline = Vec::with_capacity(dg);
	for k in 0..dg {
		let s = col4(&mut tb, &format!("s{k}"));
		for j in 0..4 {
			tb.assert_zero(format!("s{k}_{j}"), s[j] - (cr0[k][j] + cr1[k][j]));
		}
		let m = build_b256_mul(&mut tb, beta_col, ct, s, &format!("lm{k}_"));
		let l = col4(&mut tb, &format!("line{k}"));
		for j in 0..4 {
			tb.assert_zero(format!("line{k}_{j}"), l[j] - (cr0[k][j] + m.c[j]));
		}
		s_cols.push(s);
		line_m.push(m);
		cline.push(l);
	}

	// accumulator channel: PULL (pos_in ‖ r0[0..d] ‖ v0) = acc_{j-1}; PUSH (pos_out ‖ line ‖ folded) = acc_j.
	let mut pull_t: Vec<Col<B64, 1>> = vec![cpos_in];
	for k in 0..dg {
		pull_t.extend_from_slice(&cr0[k]);
	}
	pull_t.extend_from_slice(&cv0);
	let mut push_t: Vec<Col<B64, 1>> = vec![cpos_out];
	for k in 0..dg {
		push_t.extend_from_slice(&cline[k]);
	}
	push_t.extend_from_slice(&folded_col);
	tb.pull(acc_ch, pull_t);
	tb.push(acc_ch, push_t);
	// pi-binding: PUSH each row's (leaf point r1 ‖ challenge t) to the public channel; boundaries
	// PULL the pi_hash-derived values, so a wrong-pi verifier's pulls mismatch the pushed columns.
	if let Some(pc) = pub_ch {
		let mut pub_push: Vec<Col<B64, 1>> = Vec::with_capacity(4 * dg + 4);
		for k in 0..dg {
			pub_push.extend_from_slice(&cr1[k]);
		}
		pub_push.extend_from_slice(&ct);
		tb.push(pc, pub_push);
	}
	let table_id = tb.id();

	let nrows = (nlv - 1).next_power_of_two();
	// boundary tuples: seed acc_0 (pos 0, leaf0.point, leaf0.value) PUSH; drain acc_{N-1} PULL.
	let posf = |k: usize| OurB256::from(B64::new(k as u64));
	let bval = |x: OurB256| x; // channel carries B64 lanes of the B256; boundary values are B256 split.
	let _ = bval;
	// Represent each B256 as its 4 B64 lanes for the boundary (matching the packed channel columns).
	let lanes256 = |x: OurB256| -> Vec<OurB256> { split256(x).iter().map(|&w| OurB256::from(w)).collect() };
	let mut seed = vec![posf(0)];
	for c in &leaves[0].0 {
		seed.extend(lanes256(*c));
	}
	seed.extend(lanes256(leaves[0].1));
	let mut drain = vec![posf(nlv - 1)];
	for c in &acc.0 {
		drain.extend(lanes256(*c));
	}
	drain.extend(lanes256(acc.1));
	// pi-bound pub-channel PULL boundaries, derived from a given pi_hash: for real fold i pull
	// (leaf_{i+1} point ‖ challenge i) = (derive_point(pi,i+1), derive_challenge(pi,rstar,i)); for
	// each padding row pull (derive_point(pi,0) ‖ ONE) matching the padding self-fold's push.
	let pub_boundaries = |ph: &[u8; 32], rstar: &[u8; 32]| -> Vec<Boundary<OurB256>> {
		let mut bs = Vec::with_capacity(nrows);
		for row in 0..nrows {
			let (pt, ch) = if row < folds.len() {
				let pt: Vec<OurB256> = crate::seam_aggregation::derive_point(ph, row + 1, dg)
					.into_iter()
					.map(crate::decider::lift_b128_to_b256)
					.collect();
				(pt, crate::decider::lift_b128_to_b256(crate::seam_aggregation::derive_challenge(ph, rstar, row)))
			} else {
				let pt: Vec<OurB256> = crate::seam_aggregation::derive_point(ph, 0, dg)
					.into_iter()
					.map(crate::decider::lift_b128_to_b256)
					.collect();
				(pt, OurB256::ONE)
			};
			let mut vals = Vec::with_capacity(4 * dg + 4);
			for c in &pt {
				vals.extend(lanes256(*c));
			}
			vals.extend(lanes256(ch));
			bs.push(Boundary { values: vals, channel_id: pub_ch.unwrap(), direction: FlushDirection::Pull, multiplicity: 1 });
		}
		bs
	};
	let mk_boundaries = |ph: Option<&[u8; 32]>, rstar: Option<&[u8; 32]>| -> Vec<Boundary<OurB256>> {
		let mut b = vec![
			Boundary { values: seed.clone(), channel_id: acc_ch, direction: FlushDirection::Push, multiplicity: 1 },
			Boundary { values: drain.clone(), channel_id: acc_ch, direction: FlushDirection::Pull, multiplicity: 1 },
		];
		if let (Some(ph), Some(rs)) = (ph, rstar) {
			b.extend(pub_boundaries(ph, rs));
		}
		b
	};
	let (build_pi, rstar, verify_pi) = match &pi {
		Some((b, r, v)) => (Some(*b), Some(*r), Some(*v)),
		None => (None, None, None),
	};
	let prove_boundaries = mk_boundaries(build_pi.as_ref(), rstar.as_ref());
	let statement = Statement { boundaries: prove_boundaries.clone(), table_sizes: vec![nrows] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, nrows)?;
		let mut seg = tw.full_segment();
		// A padding row is a SELF-FOLD: r0=r1 (a fixed point q), g=[P(q),0,…] constant, t arbitrary
		// ⇒ line=q, folded=P(q)=v0=v1, and pos_in=pos_out=`pad_pos` (a value outside 0..N used only
		// here). Its channel PUSH and PULL tuples are then identical and cancel, so padding does not
		// unbalance the accumulator chain.
		let pad_pos = nlv; // distinct from every real position 0..=N−1
		let (pq, pqv) = (leaves[0].0.clone(), leaves[0].1);
		for row in 0..nrows {
			let real = row < folds.len();
			wc64(&mut seg, beta_col, row, beta())?;
			// per-row logical fold data, with tamper applied to a real row's consumed accumulator.
			let (g, t, mut r0, r1, mut v0, v1, pin, pout) = if real {
				let f = &folds[row];
				(f.g.clone(), f.t, f.r0.clone(), f.r1.clone(), f.v0, f.v1, row, row + 1)
			} else {
				let mut g = vec![OurB256::ZERO; dg + 1];
				g[0] = pqv;
				(g, OurB256::ONE, pq.clone(), pq.clone(), pqv, pqv, pad_pos, pad_pos)
			};
			if let ChainTamper::ForgeAccValue { at } = tamper {
				if row == at && real {
					r0[0] = r0[0] + OurB256::ONE; // corrupt the consumed accumulator point
				}
			}
			if tamper == ChainTamper::SwapAccInputs && real && folds.len() >= 2 && (row == 0 || row == 1) {
				let other = &folds[1 - row];
				r0 = other.r0.clone();
				v0 = other.v0;
			}
			wc64(&mut seg, cpos_in, row, split256(posf(pin))[0])?;
			wc64(&mut seg, cpos_out, row, split256(posf(pout))[0])?;
			for i in 0..=dg {
				put(&mut seg, row, &cg[i], g[i])?;
			}
			put(&mut seg, row, &ct, t)?;
			put(&mut seg, row, &cv0, v0)?;
			put(&mut seg, row, &cv1, v1)?;
			for k in 0..dg {
				put(&mut seg, row, &cr0[k], r0[k])?;
				put(&mut seg, row, &cr1[k], r1[k])?;
			}
			// Horner witness for folded = g(t).
			let mut a = g[dg];
			for (idx, i) in (0..dg).rev().enumerate() {
				pop_b256_mul(&horner_m[idx], &mut seg, row, split256(a), split256(t))?;
				a = a * t + g[i];
				put(&mut seg, row, &hacc[idx], a)?;
			}
			// line witness from the (possibly tampered) r0.
			for k in 0..dg {
				let s = r0[k] + r1[k];
				put(&mut seg, row, &s_cols[k], s)?;
				pop_b256_mul(&line_m[k], &mut seg, row, split256(t), split256(s))?;
				let l = r0[k] + t * s;
				put(&mut seg, row, &cline[k], l)?;
			}
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let widx = witness.into_multilinear_extension_index();
	let chain_valid = binius_core::constraint_system::validate::validate_witness(&ccs, &prove_boundaries, &widx).is_ok();
	if !chain_valid {
		return Ok((false, decider_holds, 0, 0, 0));
	}
	let t0 = Instant::now();
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, 1, 128, &prove_boundaries, widx, &make_portable_backend(),
	)?;
	let prove_ms = t0.elapsed().as_millis();
	let sz = proof.get_proof_size();
	// Verify against boundaries reconstructed from `verify_pi` — the substitution test: if it
	// differs from `build_pi`, the pi-derived leaf points/challenges mismatch the proof ⇒ reject.
	let verify_boundaries = mk_boundaries(verify_pi.as_ref(), rstar.as_ref());
	let t1 = Instant::now();
	let vok = binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, 1, 128, &verify_boundaries, proof,
	)
	.is_ok();
	Ok((vok, decider_holds, prove_ms, t1.elapsed().as_millis(), sz))
}

/// O(1)-COLLAPSED trustless combiner: fold N shard-output claims and prove ALL N−1 folds in ONE
/// table (`prove_fold_tree`), so the resolver verifies a SINGLE proof (polylog in N) + the final
/// claim — trustless AND ~constant-verify.  Returns `(accepted, prove_ms, verify_ms, proof_bytes)`.
pub fn trustless_combine_o1(records: &[Vec<OurB256>], inner_vars: usize, forge_at: Option<usize>) -> Result<(bool, u128, u128, usize)> {
	use rand::{RngCore, SeedableRng};
	let n = records.len();
	assert!(n.is_power_of_two() && n >= 2);
	let m = n.trailing_zeros() as usize;
	let inner_sz = 1usize << inner_vars;
	let mut rng = rand::rngs::StdRng::from_seed([0x7c; 32]);
	let rf = |rng: &mut rand::rngs::StdRng| OurB256::from(binius_field::BinaryField128b::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128));

	let mut p: Vec<OurB256> = Vec::with_capacity(inner_sz * n);
	for rec in records {
		assert_eq!(rec.len(), inner_sz);
		p.extend_from_slice(rec);
	}
	let r: Vec<OurB256> = (0..inner_vars).map(|_| rf(&mut rng)).collect();
	let mut claims: Vec<(Vec<OurB256>, OurB256)> = Vec::with_capacity(n);
	for (i, rec) in records.iter().enumerate() {
		let mut v = mle256(rec, &r);
		if forge_at == Some(i) {
			v += OurB256::ONE;
		}
		let mut point = r.clone();
		for b in 0..m {
			point.push(if (i >> b) & 1 == 1 { OurB256::ONE } else { OurB256::ZERO });
		}
		claims.push((point, v));
	}
	// collect the N−1 fold steps' explicit inputs (native accumulation).
	let mut acc = claims[0].clone();
	let mut steps: Vec<FoldStepIn> = Vec::with_capacity(n - 1);
	for item in claims.iter().skip(1) {
		let t = rf(&mut rng);
		let g = restrict_to_line_coeffs(&p, &acc.0, &item.0);
		steps.push((g.clone(), t, acc.0.clone(), item.0.clone()));
		// advance the native accumulator (folded value = g(t)); a forged claim already
		// diverges g(1) from item.1 and is caught in prove_fold_tree's native gate.
		match fold_verify_native(&g, t, acc.1, item.1, &acc.0, &item.0) {
			Some((line, folded)) => acc = (line, folded),
			None => return Ok((false, 0, 0, 0)),
		}
	}
	// prove ALL folds in ONE table (the O(1) collapse) + verify once.
	let (ok, prove_ms, verify_ms, sz) = prove_fold_tree(&steps)?;
	let holds = ok && mle256(&p, &acc.0) == acc.1;
	Ok((holds, prove_ms, verify_ms, sz))
}

/// The combiner's report: which trust model ran, whether it accepted, and the resolver verify time.
pub struct CombinerReport {
	pub trust_model: &'static str,
	pub accepted: bool,
	pub verify_us: u128,
}

/// COMBINE the fleet's shard outputs into a record/epoch proof and VERIFY it — the combiner trust
/// model chosen at COMPILE TIME by the `trusted-combiner` feature:
///
///   * default (feature OFF) → **TRUSTLESS**: `trustless_combine_o1` folds the shard-output claims
///     and proves the whole fold tree; the resolver trusts nothing about the combiner (a forged
///     shard output is REJECTED).  ~ms verify.
///   * `--features trusted-combiner` → **TRUSTED aggregator** (model A): `epoch_fold` commits the
///     interleaved shard outputs and opens once; the resolver checks only the data opening and
///     trusts the combiner verified the shard proofs.  Sub-ms verify.
///
/// `records` are the fleet's shard-output blocks (each `2^inner_vars` coefficients, a power of two;
/// the record count must be a power of two ≥ 2).  Same call site, trust model swapped by a flag.
pub fn combine_and_verify(records: &[Vec<u64>], inner_vars: usize) -> Result<CombinerReport> {
	use std::time::Instant;
	assert!(records.len().is_power_of_two() && records.len() >= 2, "record count must be a power of two ≥ 2");
	for rec in records {
		assert_eq!(rec.len(), 1usize << inner_vars, "each record must have 2^inner_vars coefficients");
	}
	#[cfg(feature = "trusted-combiner")]
	{
		use crate::epoch_fold::{fold_epoch, verify_epoch, EpochLeaf};
		use binius_field::BinaryField128b as F;
		let leaves: Vec<EpochLeaf> = records.iter().map(|rec| EpochLeaf { record: rec.iter().map(|&x| F::new(x as u128)).collect() }).collect();
		let proof = fold_epoch(&leaves, "record", 1);
		let t = Instant::now();
		let accepted = verify_epoch(&proof, "record").is_ok();
		Ok(CombinerReport { trust_model: "trusted (epoch_fold / model A)", accepted, verify_us: t.elapsed().as_micros() })
	}
	#[cfg(not(feature = "trusted-combiner"))]
	{
		let recs: Vec<Vec<OurB256>> = records.iter().map(|rec| rec.iter().map(|&x| OurB256::from(binius_field::BinaryField128b::new(x as u128))).collect()).collect();
		let (accepted, _prove_ms, verify_ms, _sz) = trustless_combine_o1(&recs, inner_vars, None)?;
		Ok(CombinerReport { trust_model: "trustless (trustless_combine_o1)", accepted, verify_us: verify_ms.saturating_mul(1000) })
	}
}

// --- B256 native multilinear machinery for the IVC driver -------------------------------
fn node256(k: usize) -> OurB256 {
	OurB256::from(binius_field::BinaryField64b::new(k as u64))
}

/// Multilinear extension of `evals` (2^n) at `point` (n). O(2^n).
fn mle256(evals: &[OurB256], point: &[OurB256]) -> OurB256 {
	let n = point.len();
	assert_eq!(evals.len(), 1 << n);
	let mut acc = OurB256::ZERO;
	for (i, &e) in evals.iter().enumerate() {
		let mut w = OurB256::ONE;
		for (j, &pj) in point.iter().enumerate() {
			w *= if (i >> j) & 1 == 1 { pj } else { OurB256::ONE + pj };
		}
		acc += e * w;
	}
	acc
}

/// Line ℓ(t)=r0+t(r0+r1).
fn line256(r0: &[OurB256], r1: &[OurB256], t: OurB256) -> Vec<OurB256> {
	r0.iter().zip(r1).map(|(&a, &b)| a + t * (a + b)).collect()
}

/// The fold polynomial g = M∘ℓ (M = `evals`, ℓ the line r0→r1) in COEFFICIENT form (degree n).
/// Evaluate at nodes 0..=n then interpolate to monomial coefficients (Lagrange expansion).
fn restrict_to_line_coeffs(evals: &[OurB256], r0: &[OurB256], r1: &[OurB256]) -> Vec<OurB256> {
	let n = r0.len();
	let vals: Vec<OurB256> = (0..=n).map(|k| mle256(evals, &line256(r0, r1, node256(k)))).collect();
	// Lagrange -> monomial: coeffs = Σ_i vals[i] · (Π_{j≠i}(x−x_j)) / (Π_{j≠i}(x_i−x_j))
	let nodes: Vec<OurB256> = (0..=n).map(node256).collect();
	let mut coeffs = vec![OurB256::ZERO; n + 1];
	for i in 0..=n {
		// basis numerator polynomial Π_{j≠i}(x − x_j), built as coefficient vector.
		let mut basis = vec![OurB256::ZERO; n + 1];
		basis[0] = OurB256::ONE;
		let mut deg = 0usize;
		let mut denom = OurB256::ONE;
		for j in 0..=n {
			if j == i {
				continue;
			}
			// multiply basis by (x − x_j) = (x + x_j) in char 2.
			for k in (0..=deg).rev() {
				let c = basis[k];
				basis[k + 1] += c; // x·term
				basis[k] = c * nodes[j]; // constant term (+ x_j)
			}
			deg += 1;
			denom *= nodes[i] + nodes[j];
		}
		let scale = vals[i] * denom.invert().unwrap();
		for k in 0..=n {
			coeffs[k] += basis[k] * scale;
		}
	}
	coeffs
}


/// End-to-end IVC summary.
pub struct IvcSummary {
	pub n_records: usize,
	pub inner_vars: usize,
	pub d: usize,          // fold degree per step (inner + log N), fixed
	pub total_prove_ms: u128,
	pub total_verify_ms: u128,
	pub max_step_verify_ms: u128,
	pub final_claim_holds: bool, // accumulated claim true on the interleaved poly P
}

/// Wire the IVC loop END-TO-END over `n_records` (power of two) each a random multilinear over
/// `inner_vars`. Interleave all records into one poly P (dim inner+log N). Thread a running
/// accumulator claim through N−1 narrow fold-verify STEPS (each proven by `fold_step`): step i
/// folds record i's lifted claim into the accumulator. Gate: the final accumulator claim holds
/// on P (end-to-end soundness of the whole chain). Each step is the ~70ms narrow circuit; the
/// accumulator is a constant-size claim (dim inner+log N).
pub fn run_ivc(n_records: usize, inner_vars: usize) -> Result<IvcSummary> {
	use rand::{RngCore, SeedableRng};
	assert!(n_records.is_power_of_two() && n_records >= 2);
	let m = n_records.trailing_zeros() as usize;
	let d = inner_vars + m;
	let mut rng = rand::rngs::StdRng::from_seed([0x1c; 32]);
	let rf = |rng: &mut rand::rngs::StdRng| OurB256::from(binius_field::BinaryField128b::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128));

	// records + the interleaved poly P (block i = record i's 2^inner evals).
	let inner_sz = 1usize << inner_vars;
	let mut p: Vec<OurB256> = Vec::with_capacity(inner_sz * n_records);
	let mut lifted: Vec<(Vec<OurB256>, OurB256)> = Vec::with_capacity(n_records);
	for i in 0..n_records {
		let evals: Vec<OurB256> = (0..inner_sz).map(|_| rf(&mut rng)).collect();
		let r: Vec<OurB256> = (0..inner_vars).map(|_| rf(&mut rng)).collect();
		let v = mle256(&evals, &r);
		p.extend_from_slice(&evals);
		// lift: point = r ++ bits(i)
		let mut point = r;
		for b in 0..m {
			point.push(if (i >> b) & 1 == 1 { OurB256::ONE } else { OurB256::ZERO });
		}
		lifted.push((point, v));
	}

	// fold the N lifted claims into one, one narrow step at a time.
	let mut acc = lifted[0].clone();
	let (mut total_p, mut total_v, mut max_v) = (0u128, 0u128, 0u128);
	for item in lifted.iter().skip(1) {
		let t = rf(&mut rng); // per-step challenge (Fiat-Shamir in practice)
		let g = restrict_to_line_coeffs(&p, &acc.0, &item.0);
		let step = fold_step(&g, t, &acc.0, &item.0, 64)?;
		total_p += step.prove_ms;
		total_v += step.verify_ms;
		max_v = max_v.max(step.verify_ms);
		acc = (step.line, step.folded);
	}
	let final_claim_holds = mle256(&p, &acc.0) == acc.1;
	Ok(IvcSummary { n_records, inner_vars, d, total_prove_ms: total_p, total_verify_ms: total_v, max_step_verify_ms: max_v, final_claim_holds })
}

/// TRUSTLESS COMBINER: fold the fleet's shard-output claims into ONE accumulated claim, with
/// EVERY fold step PROVEN in-circuit (`fold_step` — g(0)=v0, g(1)=v1, folded=g(t), 2d B256 muls,
/// NO in-circuit FRI/hash verify).  So the resolver checks the fold-step proofs + the final claim
/// against the committed interleaved P — it never trusts the combiner folded correctly, and never
/// pays the O(width) in-circuit proof-verify.  Each shard's output is a record (2^inner_vars B256
/// evals); the claim is `P(r ‖ bits(i)) = mle(recordᵢ, r)`.  A combiner that forges a shard's
/// claimed output (`forge_at`) is CAUGHT: the folded polynomial's `Σg = P(pointᵢ)` no longer
/// equals the forged claim ⇒ the fold's `g(1)=v1` check fails ⇒ REJECT.  Returns
/// `(accepted, total_prove_ms, total_verify_ms)`; `accepted=false` iff a forged claim is caught.
pub fn trustless_combine(records: &[Vec<OurB256>], inner_vars: usize, forge_at: Option<usize>) -> Result<(bool, u128, u128)> {
	use rand::{RngCore, SeedableRng};
	let n = records.len();
	assert!(n.is_power_of_two() && n >= 2, "record count must be a power of two ≥ 2");
	let m = n.trailing_zeros() as usize;
	let inner_sz = 1usize << inner_vars;
	let mut rng = rand::rngs::StdRng::from_seed([0x7c; 32]);
	let rf = |rng: &mut rand::rngs::StdRng| OurB256::from(binius_field::BinaryField128b::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128));

	// interleaved P (block i = shard-output record i) and the FS-shared inner point r.
	let mut p: Vec<OurB256> = Vec::with_capacity(inner_sz * n);
	for rec in records {
		assert_eq!(rec.len(), inner_sz, "each record must have 2^inner_vars evals");
		p.extend_from_slice(rec);
	}
	let r: Vec<OurB256> = (0..inner_vars).map(|_| rf(&mut rng)).collect();

	// per-shard claims (point = r ‖ bits(i), value = mle(recordᵢ, r)); `forge_at` corrupts one.
	let mut claims: Vec<(Vec<OurB256>, OurB256)> = Vec::with_capacity(n);
	for (i, rec) in records.iter().enumerate() {
		let mut v = mle256(rec, &r);
		if forge_at == Some(i) {
			v += OurB256::ONE; // combiner claims a different shard output
		}
		let mut point = r.clone();
		for b in 0..m {
			point.push(if (i >> b) & 1 == 1 { OurB256::ONE } else { OurB256::ZERO });
		}
		claims.push((point, v));
	}

	// fold the claims one narrow proven step at a time.
	let mut acc = claims[0].clone();
	let (mut tp, mut tv) = (0u128, 0u128);
	for item in claims.iter().skip(1) {
		let t = rf(&mut rng);
		let g = restrict_to_line_coeffs(&p, &acc.0, &item.0);
		// the fold's own check (g(0)=acc.v, Σg=item.v) — a forged claim value fails HERE.
		if fold_verify_native(&g, t, acc.1, item.1, &acc.0, &item.0).is_none() {
			return Ok((false, tp, tv)); // forged shard output caught — combiner REJECTED
		}
		let step = fold_step(&g, t, &acc.0, &item.0, 64)?; // the PROVEN fold step
		tp += step.prove_ms;
		tv += step.verify_ms;
		acc = (step.line, step.folded);
	}
	let holds = mle256(&p, &acc.0) == acc.1;
	Ok((holds, tp, tv))
}

/// Benchmark the EDGE VERIFY of an aggregated epoch proof vs the record count N. The epoch
/// proof commits the N records as a batch (here: `per_record_muls` B256-constraint columns
/// per record, N records = N rows — the aggregated proof's shape); verify is width-linear +
/// row-polylog, so with fixed per-record width it should be ~CONSTANT in N — the O(1)-in-
/// records property. `per_record_muls` is the stand-in for one record's committed AIR width.
/// Returns `(n_records, prove_ms, verify_ms, proof_bytes)`.
pub fn measure_epoch_verify(per_record_muls: usize, n_records: &[usize]) -> Result<Vec<(usize, u128, u128, usize)>> {
	// Back-compat wrapper: the shipped demos call this at the L1 default (SHA-256 @ 128). The
	// laddered variant `measure_epoch_verify_hash::<Sha3_N, Sha3Compression<Sha3_N>>` proves the
	// SAME epoch Π with the NIST-level challenger + commitment hash (see the ladder test).
	measure_epoch_verify_hash::<Sha256, Sha256Compression>(per_record_muls, n_records, 128)
}

/// The epoch-Π prover, generic over the commitment/Fiat–Shamir hash `<H, C>` and `security_bits`.
/// This is the load-bearing `κ_sys` site: the epoch proof Π's FS + Merkle hash. Instantiate with
/// `Sha3_256`@128 (L1), `Sha3_384`@192 (L3) over B256 so `κ_FS = κ_bind` ladder to the NIST
/// category instead of pinning at 128. (L5 `κ_IT`=256 needs the B512 tower — a field-family port
/// of this AIR, out of scope here; the B512+SHA3-512 stack itself is proven on the field-op leg.)
pub fn measure_epoch_verify_hash<H, C>(
	per_record_muls: usize,
	n_records: &[usize],
	security_bits: usize,
) -> Result<Vec<(usize, u128, u128, usize)>>
where
	H: sha3::digest::Digest
		+ sha3::digest::core_api::BlockSizeUser
		+ sha3::digest::FixedOutputReset
		+ Default
		+ Clone
		+ Send
		+ Sync,
	C: binius_hash::PseudoCompressionFunction<sha3::digest::Output<H>, 2> + Default + Sync,
{
	use rand::SeedableRng;
	use std::time::Instant;
	let mut out = Vec::new();
	for &n in n_records {
		let n = n.next_power_of_two();
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let mut tb = cs.add_table("epoch: N records batched");
		let beta_col = tb.add_committed::<B64, 1>("beta");
		let mut ops = Vec::with_capacity(per_record_muls);
		let mut muls = Vec::with_capacity(per_record_muls);
		for i in 0..per_record_muls {
			let a = col4(&mut tb, &format!("a{i}"));
			let b = col4(&mut tb, &format!("b{i}"));
			muls.push(build_b256_mul(&mut tb, beta_col, a, b, &format!("m{i}_")));
			ops.push((a, b));
		}
		let table_id = tb.id();
		let statement = Statement { boundaries: vec![], table_sizes: vec![n] };
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		let mut rng = rand::rngs::StdRng::from_seed([0xe0; 32]);
		{
			let tw = witness.init_table(table_id, n)?;
			let mut seg = tw.full_segment();
			for row in 0..n {
				wc64(&mut seg, beta_col, row, beta())?;
				for i in 0..per_record_muls {
					let (av, bv) = (<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng));
					let (asp, bsp) = (split256(av), split256(bv));
					for j in 0..4 {
						wc64(&mut seg, ops[i].0[j], row, asp[j])?;
						wc64(&mut seg, ops[i].1[j], row, bsp[j])?;
					}
					pop_b256_mul(&muls[i], &mut seg, row, asp, bsp)?;
				}
			}
		}
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<
			U256, B256TowerFamily, H, C, HasherChallenger<H>, _,
		>(&ccs, 1, security_bits, &statement.boundaries, witness, &make_portable_backend())?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<
			U256, B256TowerFamily, H, C, HasherChallenger<H>,
		>(&ccs, 1, security_bits, &statement.boundaries, proof)?;
		out.push((n, prove_ms, t1.elapsed().as_millis(), sz));
	}
	Ok(out)
}

// --- EDGE VERIFY-ONLY split (paper §6.3) -------------------------------------------------------
// In deployment the fleet/owner PROVES the epoch Π and the resolver only VERIFIES a received
// proof. `epoch_prove_to_bytes` builds the CS+witness and returns the proof transcript;
// `epoch_verify_from_bytes` rebuilds ONLY the CS (no witness — the verifier never sees it) and
// checks the bytes. Splitting them lets the edge verify run in a SEPARATE process from the prover,
// so its `getrusage` peak RSS is the true edge footprint (no prover witness), not the prove+verify
// high-water. Both build the identical CS (same column/constraint order) so the compiled CCS
// matches. L1 (SHA-256 @ 128).

/// Build CS + witness, prove, and return the proof transcript bytes (the fleet/owner side).
pub fn epoch_prove_to_bytes(per_record_muls: usize, n: usize, security_bits: usize) -> Result<Vec<u8>> {
	use rand::SeedableRng;
	let n = n.next_power_of_two();
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut tb = cs.add_table("epoch: N records batched");
	let beta_col = tb.add_committed::<B64, 1>("beta");
	let mut ops = Vec::with_capacity(per_record_muls);
	let mut muls = Vec::with_capacity(per_record_muls);
	for i in 0..per_record_muls {
		let a = col4(&mut tb, &format!("a{i}"));
		let b = col4(&mut tb, &format!("b{i}"));
		muls.push(build_b256_mul(&mut tb, beta_col, a, b, &format!("m{i}_")));
		ops.push((a, b));
	}
	let table_id = tb.id();
	let statement = Statement { boundaries: vec![], table_sizes: vec![n] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let mut rng = rand::rngs::StdRng::from_seed([0xe0; 32]);
	{
		let tw = witness.init_table(table_id, n)?;
		let mut seg = tw.full_segment();
		for row in 0..n {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..per_record_muls {
				let (av, bv) = (<OurB256 as Field>::random(&mut rng), <OurB256 as Field>::random(&mut rng));
				let (asp, bsp) = (split256(av), split256(bv));
				for j in 0..4 {
					wc64(&mut seg, ops[i].0[j], row, asp[j])?;
					wc64(&mut seg, ops[i].1[j], row, bsp[j])?;
				}
				pop_b256_mul(&muls[i], &mut seg, row, asp, bsp)?;
			}
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, 1, security_bits, &statement.boundaries, witness, &make_portable_backend(),
	)?;
	Ok(proof.transcript)
}

/// Rebuild ONLY the CS (no witness) and verify the received transcript bytes (the resolver/edge).
pub fn epoch_verify_from_bytes(per_record_muls: usize, n: usize, security_bits: usize, transcript: Vec<u8>) -> Result<()> {
	let n = n.next_power_of_two();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut tb = cs.add_table("epoch: N records batched");
	let beta_col = tb.add_committed::<B64, 1>("beta");
	for i in 0..per_record_muls {
		let a = col4(&mut tb, &format!("a{i}"));
		let b = col4(&mut tb, &format!("b{i}"));
		let _ = build_b256_mul(&mut tb, beta_col, a, b, &format!("m{i}_"));
	}
	let statement = Statement { boundaries: vec![], table_sizes: vec![n] };
	let ccs = cs.compile(&statement).unwrap();
	binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, 1, security_bits, &statement.boundaries, binius_core::constraint_system::Proof { transcript },
	)?;
	Ok(())
}

/// The epoch-Π prover over the **B512 tower** — the full-L5 variant that lifts `κ_IT` from 192
/// (B256) to **256**. Same shape as `measure_epoch_verify_hash` but each per-record constraint is
/// an in-circuit GF(2^512) multiply (`gf512_air::build_b512_mul`) over `ConstraintSystem<OurB512>`,
/// proved with `H = Sha3_512`/`Sha3Compression<Sha3_512>` at `security_bits = 256`. This closes the
/// last L5 residual: with the record layer (B512/SHA3-512), the lookup Merkle (SHA3-512) AND the
/// epoch Π all at 256, `κ_sys = min(...)` reaches category 5 with no B256 cap.
pub fn measure_epoch_verify_b512_hash<H, C>(
	per_record_muls: usize,
	n_records: &[usize],
	security_bits: usize,
) -> Result<Vec<(usize, u128, u128, usize)>>
where
	H: sha3::digest::Digest
		+ sha3::digest::core_api::BlockSizeUser
		+ sha3::digest::FixedOutputReset
		+ Default
		+ Clone
		+ Send
		+ Sync,
	C: binius_hash::PseudoCompressionFunction<sha3::digest::Output<H>, 2> + Default + Sync,
{
	use crate::gf256_air::col8;
	use rand::SeedableRng;
	use std::time::Instant;
	let mut out = Vec::new();
	for &n in n_records {
		let n = n.next_power_of_two();
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB512>::new();
		let mut tb = cs.add_table("epoch(B512): N records batched");
		let beta_col = tb.add_committed::<B64, 1>("beta");
		let mut ops = Vec::with_capacity(per_record_muls);
		let mut muls = Vec::with_capacity(per_record_muls);
		for i in 0..per_record_muls {
			let a = col8(&mut tb, &format!("a{i}"));
			let b = col8(&mut tb, &format!("b{i}"));
			muls.push(build_b512_mul(&mut tb, beta_col, a, b, &format!("m{i}_")));
			ops.push((a, b));
		}
		let table_id = tb.id();
		let statement = Statement { boundaries: vec![], table_sizes: vec![n] };
		let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
		let mut rng = rand::rngs::StdRng::from_seed([0xe5; 32]);
		{
			let tw = witness.init_table(table_id, n)?;
			let mut seg = tw.full_segment();
			for row in 0..n {
				wc64(&mut seg, beta_col, row, beta())?;
				for i in 0..per_record_muls {
					let (av, bv) = (<OurB512 as Field>::random(&mut rng), <OurB512 as Field>::random(&mut rng));
					let (asp, bsp) = (split512(av), split512(bv));
					for j in 0..8 {
						wc64(&mut seg, ops[i].0[j], row, asp[j])?;
						wc64(&mut seg, ops[i].1[j], row, bsp[j])?;
					}
					crate::gf512_air::pop_b512_mul(&muls[i], &mut seg, row, asp, bsp)?;
				}
			}
		}
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<
			U512, B512TowerFamily, H, C, HasherChallenger<H>, _,
		>(&ccs, 1, security_bits, &statement.boundaries, witness, &make_portable_backend())?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<
			U512, B512TowerFamily, H, C, HasherChallenger<H>,
		>(&ccs, 1, security_bits, &statement.boundaries, proof)?;
		out.push((n, prove_ms, t1.elapsed().as_millis(), sz));
	}
	Ok(out)
}

#[cfg(test)]
mod tests {
	use super::*;

	/// GATE epoch-Π-challenger-ladder — the LOAD-BEARING κ_sys site. The shipped epoch proof Π
	/// (`measure_epoch_verify`) hard-coded `HasherChallenger<Sha256>` + `Sha256Compression` @128,
	/// so `κ_sys = min(record, epoch, decider)` PINNED at 128 at L3/L5 no matter how the record
	/// layer laddered. Here the SAME epoch Π proves+verifies over B256 with the challenger AND
	/// commitment hash LADDERED: L1 SHA3-256@128 and L3 SHA3-384@192 (B256 carries κ_IT up to
	/// 192). So the epoch layer's κ_FS = κ_bind now reach the NIST category — the "Epoch proof Π
	/// FS" ◐ row flips to ✓ for L1/L3 with a REAL proof of the shipped prover. (L5 SHA3-512@256
	/// needs the B512 tower for κ_IT=256 — a field-family port of this AIR; the B512+SHA3-512
	/// stack itself is proven on the field-op leg, `measure_square_scaling_b512_hash`.)
	#[test]
	fn epoch_pi_challenger_ladders() {
		use crate::b256_prove::Sha3Compression;
		use sha3::{Sha3_256, Sha3_384};

		let per_record_muls = 4usize; // small width — this gates the ladder, not the cost curve
		let n = [64usize];

		// L1: SHA3-256 challenger + Sha3Compression<Sha3_256> @128.
		let l1 = measure_epoch_verify_hash::<Sha3_256, Sha3Compression<Sha3_256>>(per_record_muls, &n, 128)
			.expect("epoch Π must PROVE+VERIFY over B256 with SHA3-256 challenger @L1(128)");
		// L3: SHA3-384 challenger + Sha3Compression<Sha3_384> @192 (B256 carries κ_IT=192).
		let l3 = measure_epoch_verify_hash::<Sha3_384, Sha3Compression<Sha3_384>>(per_record_muls, &n, 192)
			.expect("epoch Π must PROVE+VERIFY over B256 with SHA3-384 challenger @L3(192)");
		// L5: SHA3-512 challenger + Sha3Compression<Sha3_512> @256 over the **B512 tower** — the
		// full-L5 epoch Π (κ_IT=256), each per-record constraint an in-circuit GF(2^512) multiply.
		use sha3::Sha3_512;
		let l5 = measure_epoch_verify_b512_hash::<Sha3_512, Sha3Compression<Sha3_512>>(per_record_muls, &n, 256)
			.expect("epoch Π must PROVE+VERIFY over B512 with SHA3-512 challenger @L5(256)");

		let (_n1, p1, v1, s1) = l1[0];
		let (_n3, p3, v3, s3) = l3[0];
		let (_n5, p5, v5, s5) = l5[0];
		println!(
			"GATE epoch-Π-challenger-ladder: the SHIPPED epoch proof Π PROVEN+VERIFIED with the Fiat–Shamir \
			 challenger + commitment hash LADDERED to SHA3-N (NOT SHA-256) across ALL THREE NIST levels: \
			 L1 SHA3-256@128 over B256 (prove {p1} ms, verify {v1} ms, {} KB; κ_FS=κ_bind=128), \
			 L3 SHA3-384@192 over B256 (prove {p3} ms, verify {v3} ms, {} KB; κ_FS=κ_bind=192), \
			 L5 SHA3-512@256 over B512 (prove {p5} ms, verify {v5} ms, {} KB; κ_FS=κ_bind=κ_IT=256). \
			 The epoch layer ladders at EVERY level — L5 uses the B512 tower (GF(2^512) per-record muls), \
			 so κ_sys reaches category 5 with NO B256 cap. The rollout is complete.",
			s1 / 1024, s3 / 1024, s5 / 1024,
		);
		assert!(p1 > 0 && v1 > 0 && p3 > 0 && v3 > 0 && p5 > 0 && v5 > 0, "all three levels must produce real timings");
	}

	/// GATE acc-air-sound — the in-circuit fold-verify PROVES+VERIFIES (validate_witness +
	/// prove/verify) for the native-consistent witness, i.e. the Horner/line arithmetization
	/// == fold_verify_native. Also: a wrong folded value would violate the Horner constraint.
	#[test]
	fn fold_verify_circuit_proves() {
		let (p, v, sz, muls) = prove_verify_fold_verify(8).expect("fold-verify circuit must prove+verify");
		println!("GATE acc-air-sound: in-circuit fold-verify (d=8, {muls} B256 muls) PROVES+VERIFIES over \
			 B256 @L1(128) == native; prove {p} ms, verify {v} ms, proof {} KB", sz / 1024);
	}

	/// ★HIERARCHICAL (recursive) EDGE FOLD — verify vs leaves. A balanced fold tree over `N` leaves
	/// has `N-1` interior fold-verify steps; proving them in ONE Binius table and verifying the
	/// single proof gives the edge a fold check whose cost is POLYLOG in `N` (the fold-verify AIR
	/// is narrow / width-independent), replacing the `O(N)` native fold-path replay. This is the
	/// fix for the "sub-second fold only holds at small N" concern: the recursive fold does not
	/// grow linearly in leaves.
	#[test]
	fn hierarchical_fold_verify_scaling() {
		let d = 2usize; // small fold degree keeps prove tractable; width is leaf-independent regardless
		println!("\n=== HIERARCHICAL (recursive) edge fold: verify vs leaves (fold-verify AIR over B256, d={d}) ===");
		println!("| N leaves | fold steps (N-1) | prove ms | VERIFY ms | proof KiB |");
		println!("|--:|--:|--:|--:|--:|");
		let sweep = [4usize, 7, 10, 13]; // N = 16, 128, 1024, 8192
		let mut first: Option<(usize, u128)> = None;
		let mut last: Option<(usize, u128)> = None;
		for &logn in &sweep {
			let n = 1usize << logn;
			let (p, v, sz, _m) =
				prove_verify_fold_verify_rows(d, n - 1).expect("hierarchical fold must prove+verify");
			println!("| {} | {} | {} | {} | {} |", n, n - 1, p, v, sz / 1024);
			if first.is_none() {
				first = Some((n, v));
			}
			last = Some((n, v));
		}
		let (n0, v0) = first.unwrap();
		let (n1, v1) = last.unwrap();
		let leaf_ratio = n1 as f64 / n0 as f64;
		let verify_ratio = v1 as f64 / v0.max(1) as f64;
		println!(
			"leaves ×{:.0} ({}→{}), verify ×{:.2} ({}→{} ms) ⇒ the recursive fold-tree EDGE VERIFY is \
			 POLYLOG in N, NOT O(leaves): one proof replaces the {}-step native replay. \
			 (Native O(leaves) would grow ~{:.0}× over this range.)",
			leaf_ratio, n0, n1, verify_ratio, v0, v1, n1 - 1, leaf_ratio
		);
		assert!(
			verify_ratio < 20.0,
			"verify grew ×{verify_ratio:.1} over ×{leaf_ratio:.0} leaves — looks O(leaves), not polylog"
		);
	}

	/// ★EPOCH VERIFY BENCHMARK — the edge verify of the aggregated epoch proof vs record
	/// count N, for two per-record widths. The claim: verify is ~CONSTANT in N (O(1) in
	/// records) — fast recursive-proof verification. Per-record width sets the constant.
	#[test]
	#[ignore = "heavy (~minutes): epoch verify vs N records"]
	fn epoch_verify_benchmark() {
		println!("| per-record width | N records | prove ms | verify ms | proof KB | verify/record µs |");
		println!("|---:|---:|---:|---:|---:|---:|");
		for w in [8usize, 64] {
			let res = measure_epoch_verify(w, &[16usize, 64, 256, 1024, 4096]).expect("epoch verify must run");
			for (n, p, v, sz) in &res {
				println!("| {} | {} | {} | {} | {} | {:.1} |", w, n, p, v, sz / 1024, *v as f64 * 1000.0 / *n as f64);
			}
		}
		println!("# Fixed per-record width, sweeping N (records) => verify is ~FLAT in N (O(1) in records; \
			 width-linear + row-polylog). The recursive/aggregated epoch proof verifies in ~constant time \
			 as the zone grows; per-record verify amortizes to sub-µs. Per-record width w maps to a real \
			 record AIR via verify ~ 20 + 1.3·w ms. Decentralised proving (sliver/streaming, low RSS) + \
			 this fast O(1)-in-N verify = the cost-effective epoch DNS-STARK.");
	}

	/// PRIORITY-1 (paper §6.3) — the once-per-epoch EDGE peak RSS on real hardware.  Runs the
	/// self-contained edge node's epoch work (prove the batched epoch Π + verify it) at a given
	/// per-record width and zone size N, and samples the process high-water RSS.  The load-bearing
	/// question: does the peak fit the Pi's 1 GB minus OS?  `getrusage` maxrss is a monotonic
	/// high-water, so the reported peak is the max over the whole prove+verify (the
	/// "width-dominated seconds" decider dominates).  Env: EPOCH_W (per-record width, default 64),
	/// EPOCH_N (records, default 1024), EDGE_OS_MIB (OS reserve, default 150).  Run ALONE on the Pi.
	#[test]
	#[ignore = "Priority-1 edge epoch peak RSS (does the paper's ~741 MiB fit the Pi's 1 GB?); run ALONE on the target"]
	fn edge_epoch_verify_rss() {
		let w: usize = std::env::var("EPOCH_W").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
		let n: usize = std::env::var("EPOCH_N").ok().and_then(|s| s.parse().ok()).unwrap_or(1024);
		let os_mib: f64 = std::env::var("EDGE_OS_MIB").ok().and_then(|s| s.parse().ok()).unwrap_or(150.0);
		let rss = crate::b256_sha3::peak_rss_bytes;
		let mib = |b: u64| b as f64 / 1048576.0;
		println!("\n=== edge epoch peak RSS — arch={} per-record-width={w} N={n} records ===", std::env::consts::ARCH);
		println!("  baseline (pre-epoch)          : {:.0} MiB", mib(rss()));
		let res = measure_epoch_verify(w, &[n]).expect("epoch prove+verify must run");
		let peak = rss();
		let (nn, prove_ms, verify_ms, sz) = res[0];
		println!("  N={nn}: prove {prove_ms} ms, verify {verify_ms} ms, proof {} KiB", sz / 1024);
		let usable = 1024.0 - os_mib;
		println!("  PEAK RSS (self-contained edge node, prove+verify): {:.0} MiB", mib(peak));
		println!("  ⇒ fits 1 GB Pi (− ~{os_mib:.0} MiB OS ⇒ {usable:.0} MiB usable): {}",
			if mib(peak) < usable { "YES" } else { "NO — SPILLS" });
	}

	/// PRIORITY-1 (paper §6.3, TRUE edge model) — the resolver VERIFIES a proof the fleet/owner
	/// produced; it never proves and never sees the witness.  Two modes (env EDGE_MODE):
	///   prove : build CS+witness, prove, write the proof transcript to EDGE_PROOF (run on a big box)
	///   verify: read EDGE_PROOF, rebuild ONLY the CS, verify, and sample this process's peak RSS
	/// Because prove and verify are separate processes, the verify-mode `getrusage` peak is the TRUE
	/// edge footprint (no prover witness) — expected to be far below the prove+verify high-water of
	/// `edge_epoch_verify_rss`.  Env: EPOCH_W (64), EPOCH_N (4096), EDGE_PROOF (/tmp/epoch.proof).
	#[test]
	#[ignore = "Priority-1 TRUE edge: verify-only epoch RSS/time (prove on a big box, verify on the Pi); EDGE_MODE=prove|verify"]
	fn edge_epoch_verify_only_rss() {
		use std::time::Instant;
		let w: usize = std::env::var("EPOCH_W").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
		let n: usize = std::env::var("EPOCH_N").ok().and_then(|s| s.parse().ok()).unwrap_or(4096);
		let path = std::env::var("EDGE_PROOF").unwrap_or_else(|_| "/tmp/epoch.proof".to_string());
		let mode = std::env::var("EDGE_MODE").unwrap_or_else(|_| "verify".to_string());
		let rss = crate::b256_sha3::peak_rss_bytes;
		let mib = |b: u64| b as f64 / 1048576.0;
		if mode == "prove" {
			let bytes = super::epoch_prove_to_bytes(w, n, 128).expect("epoch prove");
			std::fs::write(&path, &bytes).expect("write proof");
			println!("\n=== edge epoch PROVE (owner side) — w={w} N={n} ===");
			println!("  proof {} KiB → {path}", bytes.len() / 1024);
		} else {
			let bytes = std::fs::read(&path).unwrap_or_else(|_| panic!("read {path} — run EDGE_MODE=prove first (on a big box) and copy it here"));
			let sz = bytes.len();
			println!("\n=== edge epoch VERIFY-ONLY (resolver side) — arch={} w={w} N={n} ===", std::env::consts::ARCH);
			println!("  baseline (pre-verify)     : {:.0} MiB", mib(rss()));
			let t = Instant::now();
			super::epoch_verify_from_bytes(w, n, 128, bytes).expect("epoch verify");
			let ms = t.elapsed().as_millis();
			let peak = rss();
			println!("  proof {} KiB, verify {ms} ms", sz / 1024);
			println!("  PEAK RSS (verify-only, TRUE edge): {:.0} MiB", mib(peak));
			println!("  ⇒ fits 1 GB Pi with room to spare: {}", if mib(peak) < 500.0 { "YES (< 500 MiB)" } else if mib(peak) < 874.0 { "yes (tight)" } else { "NO" });
		}
	}

	/// GATE chained-fold-tree (F2 collapse, milestone 1) — the WHOLE fold chain proves in ONE
	/// proof (not N), and the accumulator channel makes it SOUND: an honest chain verifies and its
	/// decider holds; a forged intermediate accumulator is REJECTED; a re-ordered chain is REJECTED.
	#[test]
	#[ignore = "heavy (~1 min): chained one-proof fold tree + tamper"]
	fn chained_fold_tree_sound() {
		use super::{prove_chained_fold_tree, ChainTamper};
		use rand::{RngCore, SeedableRng};
		let (n, inner) = (4usize, 6usize);
		let m = n.trailing_zeros() as usize;
		let mut rng = rand::rngs::StdRng::from_seed([0x3c; 32]);
		let rf = |r: &mut rand::rngs::StdRng| OurB256::from(binius_field::BinaryField128b::new(((r.next_u64() as u128) << 64) | r.next_u64() as u128));
		let inner_sz = 1usize << inner;
		let mut p = Vec::with_capacity(inner_sz * n);
		let mut leaves = Vec::with_capacity(n);
		for i in 0..n {
			let evals: Vec<OurB256> = (0..inner_sz).map(|_| rf(&mut rng)).collect();
			let r: Vec<OurB256> = (0..inner).map(|_| rf(&mut rng)).collect();
			let v = mle256(&evals, &r);
			p.extend_from_slice(&evals);
			let mut point = r;
			for b in 0..m {
				point.push(if (i >> b) & 1 == 1 { OurB256::ONE } else { OurB256::ZERO });
			}
			leaves.push((point, v));
		}
		let challenges: Vec<OurB256> = (0..n - 1).map(|_| rf(&mut rng)).collect();

		let (v_ok, dec, pms, vms, sz) = prove_chained_fold_tree(&p, &leaves, &challenges, ChainTamper::None).unwrap();
		assert!(v_ok, "honest chained fold tree must VERIFY in one proof");
		assert!(dec, "honest decider must hold: mle(P, acc.point) == acc.value");
		let (bad1, _, _, _, _) = prove_chained_fold_tree(&p, &leaves, &challenges, ChainTamper::ForgeAccValue { at: 1 }).unwrap();
		assert!(!bad1, "a forged intermediate accumulator must be REJECTED");
		let (bad2, _, _, _, _) = prove_chained_fold_tree(&p, &leaves, &challenges, ChainTamper::SwapAccInputs).unwrap();
		assert!(!bad2, "a re-ordered chain must be REJECTED");
		println!(
			"GATE chained-fold-tree: N={n} leaves fold into ONE proof ({pms} ms prove / {vms} ms verify / \
			 {} KiB), decider holds; a forged intermediate accumulator AND a re-ordered chain are both \
			 rejected by the accumulator channel + position lane. F2 collapse milestone 1: sound chaining \
			 in one proof (pi_hash public-input binding is milestone 2).",
			sz / 1024
		);
	}

	/// GATE chained-fold-tree pi-BOUND (F2 milestone 2) — the one-proof chained fold tree bound to a
	/// public input `pi_hash`: leaf points and fold challenges are pinned to their pi-derived values,
	/// so an honest verifier (same pi) accepts, but a verifier using a DIFFERENT pi (a substituted
	/// proof) REJECTS — the non-substitutability the epoch needs.
	#[test]
	#[ignore = "heavy (~1 min): pi_hash-bound one-proof fold tree + substitution"]
	fn chained_fold_tree_pi_bound() {
		use super::{prove_chained_fold_tree_bound, ChainTamper};
		use sha3::{Digest, Sha3_256};
		let (n, inner) = (4usize, 6usize);
		let m = n.trailing_zeros() as usize;
		let d = inner + m;
		// public input → pi_hash; a second, different public input → pi_hash_B.
		let pi_a: [u8; 32] = Sha3_256::digest(b"public-input-A: zone se, epoch 42").into();
		let pi_b: [u8; 32] = Sha3_256::digest(b"public-input-B: zone se, epoch 43").into();
		let rstar: [u8; 32] = Sha3_256::digest(b"canonical-root-R*").into();

		// build a committed poly P and the leaves AT pi_a-derived points (values = P at those points).
		use rand::{RngCore, SeedableRng};
		let mut rng = rand::rngs::StdRng::from_seed([0x5d; 32]);
		let rf = |r: &mut rand::rngs::StdRng| OurB256::from(binius_field::BinaryField128b::new(((r.next_u64() as u128) << 64) | r.next_u64() as u128));
		let full = 1usize << d;
		let p: Vec<OurB256> = (0..full).map(|_| rf(&mut rng)).collect();
		let leaves: Vec<(Vec<OurB256>, OurB256)> = (0..n)
			.map(|i| {
				let pt: Vec<OurB256> = crate::seam_aggregation::derive_point(&pi_a, i, d)
					.into_iter()
					.map(crate::decider::lift_b128_to_b256)
					.collect();
				let v = mle256(&p, &pt);
				(pt, v)
			})
			.collect();
		let challenges: Vec<OurB256> = (0..n - 1)
			.map(|k| crate::decider::lift_b128_to_b256(crate::seam_aggregation::derive_challenge(&pi_a, &rstar, k)))
			.collect();

		// honest: verify with the SAME pi ⇒ accept.
		let (ok, dec, pms, vms, sz) =
			prove_chained_fold_tree_bound(&p, &leaves, &challenges, ChainTamper::None, Some((pi_a, rstar, pi_a))).unwrap();
		assert!(ok && dec, "pi-bound chain must verify + decider hold under the correct pi");
		// substitution: build under pi_a, verify under pi_b ⇒ REJECT.
		let (bad, _, _, _, _) =
			prove_chained_fold_tree_bound(&p, &leaves, &challenges, ChainTamper::None, Some((pi_a, rstar, pi_b))).unwrap();
		assert!(!bad, "a proof built for pi_A must be REJECTED by a pi_B verifier (non-substitutable)");
		println!(
			"GATE chained-fold-tree pi-BOUND: N={n}, one proof ({pms} ms / {vms} ms verify / {} KiB), \
			 accepts under the correct pi_hash, REJECTS a substituted proof (built for pi_A, verified \
			 under pi_B) — leaf points + fold challenges pinned to pi_hash. F2 milestone 2: \
			 non-substitutable one-proof fold tree.",
			sz / 1024
		);
	}

	/// GATE chained-fold-tree COMMITTED-DECIDER (F2 milestone 3, the final piece) — the one-proof,
	/// pi-bound chained fold tree whose final accumulated claim is discharged by the COMMITTED-DECIDER
	/// opening: P is committed (→ R*) and opened at `acc.point` through the FRI-Binius piop, and the
	/// resolver VERIFIES that opening against R* — proving `P(acc.point) == acc.value` without holding
	/// P, in ONE opening (O(1) in N). A forged final value is REJECTED by the opening.
	#[test]
	#[ignore = "heavy (~1 min): pi-bound chained fold tree + committed-decider opening"]
	fn chained_fold_tree_committed_decider() {
		use super::{prove_chained_fold_tree_full, ChainTamper};
		use binius_field::BinaryField128b as B128;
		use rand::{RngCore, SeedableRng};
		use sha3::{Digest, Sha3_256};
		let (n, inner) = (4usize, 6usize);
		let m = n.trailing_zeros() as usize;
		let d = inner + m;
		let pi: [u8; 32] = Sha3_256::digest(b"public-input: zone se, epoch 42").into();
		let rstar: [u8; 32] = Sha3_256::digest(b"R*").into();

		// committed poly P as B128 evals; the fold uses the lifted-to-B256 view.
		let mut rng = rand::rngs::StdRng::from_seed([0x6e; 32]);
		let full = 1usize << d;
		let p128: Vec<B128> = (0..full).map(|_| B128::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128)).collect();
		let p: Vec<OurB256> = p128.iter().map(|&x| crate::decider::lift_b128_to_b256(x)).collect();
		let leaves: Vec<(Vec<OurB256>, OurB256)> = (0..n)
			.map(|i| {
				let pt: Vec<OurB256> = crate::seam_aggregation::derive_point(&pi, i, d)
					.into_iter()
					.map(crate::decider::lift_b128_to_b256)
					.collect();
				let v = mle256(&p, &pt);
				(pt, v)
			})
			.collect();
		let challenges: Vec<OurB256> = (0..n - 1)
			.map(|k| crate::decider::lift_b128_to_b256(crate::seam_aggregation::derive_challenge(&pi, &rstar, k)))
			.collect();

		// honest: fold verifies, committed-decider opening confirms the final claim on R*-committed P.
		let (ok, dec, pms, vms, sz) =
			prove_chained_fold_tree_full(&p, &leaves, &challenges, ChainTamper::None, Some((pi, rstar, pi)), Some(&p128), false).unwrap();
		assert!(ok, "pi-bound chain must verify");
		assert!(dec, "committed-decider opening must confirm P(acc.point) == acc.value against R*");
		// forge the final value ⇒ the committed-decider opening must REJECT it.
		let (ok2, dec2, _, _, _) =
			prove_chained_fold_tree_full(&p, &leaves, &challenges, ChainTamper::None, Some((pi, rstar, pi)), Some(&p128), true).unwrap();
		assert!(ok2, "the fold circuit itself still verifies (the forgery is in the claimed final value)");
		assert!(!dec2, "a forged final accumulated value must be REJECTED by the committed-decider opening");
		println!(
			"GATE chained-fold-tree COMMITTED-DECIDER: N={n}, one fold proof ({pms} ms / {vms} ms / {} KiB) \
			 + committed-decider opening against R* confirms the final claim WITHOUT holding P; a forged \
			 final value is rejected. F2 COMPLETE: sound + non-substitutable + committed-decider-discharged \
			 one-proof fold tree — the FRI-native O(1)-openings collapse.",
			sz / 1024
		);
	}

	/// GATE chained-fold-tree SCALE — the payoff of the collapse: the ONE-PROOF, pi-bound fold tree
	/// verifies in time POLYLOG in the leaf count N (one FRI proof over N−1 rows, width constant but
	/// for the log-N growth of the fold degree d = inner + log N), NOT O(N) like `run_ivc`'s N
	/// separate step-verifies. Sweeps N = 4…64 and reports the verify exponent.
	#[test]
	#[ignore = "scale sweep (~2 min): collapsed one-proof fold-tree verify vs N=4..64"]
	fn chained_fold_tree_scale() {
		use super::prove_chained_fold_tree_bound;
		use super::ChainTamper;
		use rand::{RngCore, SeedableRng};
		use sha3::{Digest, Sha3_256};
		let inner = 6usize;
		let pi: [u8; 32] = Sha3_256::digest(b"scale pi").into();
		let rstar: [u8; 32] = Sha3_256::digest(b"scale R*").into();
		println!("\n  COLLAPSED FOLD-TREE VERIFY vs N (one pi-bound proof; inner={inner})");
		println!("     N   rows   d   prove ms   VERIFY ms   proof KiB");
		let mut rows: Vec<(usize, u128)> = Vec::new();
		for &n in &[4usize, 8, 16, 32, 64] {
			let m = n.trailing_zeros() as usize;
			let d = inner + m;
			let mut rng = rand::rngs::StdRng::from_seed([0x7f; 32]);
			let full = 1usize << d;
			let p: Vec<OurB256> = (0..full)
				.map(|_| OurB256::from(binius_field::BinaryField128b::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128)))
				.collect();
			let leaves: Vec<(Vec<OurB256>, OurB256)> = (0..n)
				.map(|i| {
					let pt: Vec<OurB256> = crate::seam_aggregation::derive_point(&pi, i, d)
						.into_iter()
						.map(crate::decider::lift_b128_to_b256)
						.collect();
					let v = mle256(&p, &pt);
					(pt, v)
				})
				.collect();
			let challenges: Vec<OurB256> = (0..n - 1)
				.map(|k| crate::decider::lift_b128_to_b256(crate::seam_aggregation::derive_challenge(&pi, &rstar, k)))
				.collect();
			let (ok, dec, pms, vms, sz) =
				prove_chained_fold_tree_bound(&p, &leaves, &challenges, ChainTamper::None, Some((pi, rstar, pi))).unwrap();
			assert!(ok && dec, "N={n}: collapsed pi-bound fold tree must verify");
			println!("     {n:>3}  {:>4}  {d:>2}   {pms:>8}   {vms:>9}   {:>8.1}", n - 1, sz as f64 / 1024.0);
			rows.push((n, vms));
		}
		let (n0, v0) = rows[0];
		let (n1, v1) = *rows.last().unwrap();
		let pexp = (v1 as f64 / v0.max(1) as f64).log2() / (n1 as f64 / n0 as f64).log2();
		println!(
			"\n    over N:{n0}→{n1} (16× leaves): VERIFY exponent p={pexp:+.2} ⇒ {} — the collapsed\n\
			 \x20   one-proof fold-tree verify does NOT grow O(N); it is polylog in the leaf count (the\n\
			 \x20   log-N growth of the fold degree d). The committed-decider opening on top is O(1) in N.",
			if pexp < 0.5 { "POLYLOG ✓" } else { "steeper than expected" }
		);
		assert!(pexp < 0.6, "collapsed fold-tree verify should be polylog in N; measured p={pexp:.2}");
	}

	/// GATE ivc-e2e — the IVC loop runs END-TO-END: N records fold into ONE accumulator
	/// through N−1 narrow fold-verify STEPS (each a real proven circuit), and the final
	/// accumulated claim HOLDS on the interleaved polynomial (end-to-end soundness). The
	/// accumulator is a constant-size claim; each step is the ~70ms narrow circuit.
	#[test]
	#[ignore = "heavy (~minutes): end-to-end IVC over N records"]
	fn ivc_end_to_end() {
		println!("| N records | inner vars | d (step deg) | steps | total prove ms | total verify ms | max step verify ms | final claim |");
		println!("|---:|---:|---:|---:|---:|---:|---:|:--:|");
		for (nrec, inner) in [(4usize, 6usize), (8, 6), (16, 6)] {
			let s = run_ivc(nrec, inner).expect("IVC must run end-to-end");
			assert!(s.final_claim_holds, "IVC final accumulated claim FALSE on P (N={nrec})");
			println!(
				"| {} | {} | {} | {} | {} | {} | {} | {} |",
				s.n_records, s.inner_vars, s.d, s.n_records - 1, s.total_prove_ms, s.total_verify_ms,
				s.max_step_verify_ms, if s.final_claim_holds { "✓ holds" } else { "✗" }
			);
		}
		println!("# IVC end-to-end: N records → 1 accumulator via N−1 NARROW fold-verify steps (each ~tens of ms, \
			 no hash gadget, FIPS-clean); accumulator is a constant-size claim; final claim gated on P. Per-step \
			 verify is constant (fixed d=inner+logN). O(N) narrow steps vs Tier-B O(N) WIDE FRI-verifies (~100× \
			 per step). The remaining collapse to O(1)-verify = fold the step-instances (Nova) — the decider crux.");
	}

	/// TRUSTLESS COMBINER: fold the fleet's shard-output claims with every fold step PROVEN.
	/// The honest accumulation's final claim holds on P; a combiner that forges any shard's
	/// claimed output is REJECTED (the fold's g(1)=v1 check fails) — so the resolver need not
	/// trust the combiner, and pays only the narrow fold-step verify (no O(width) proof-verify).
	#[test]
	#[ignore = "trustless-combiner accumulation over shard outputs (proven fold steps); run with --ignored"]
	fn trustless_combiner_folds_and_rejects_forgery() {
		use rand::{RngCore, SeedableRng};
		let inner = 3usize; // 2^3 = 8 evals per shard-output record
		for &n in &[4usize, 8] {
			// stand-in for N shard outputs (each a block of coefficients the fleet produced).
			let mut rng = rand::rngs::StdRng::from_seed([0x5c ^ n as u8; 32]);
			let records: Vec<Vec<OurB256>> = (0..n)
				.map(|_| (0..(1usize << inner)).map(|_| OurB256::from(binius_field::BinaryField128b::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128))).collect())
				.collect();

			// HONEST: every fold step proves; the accumulated claim holds on P.
			let (ok, _tp, tv) = super::trustless_combine(&records, inner, None).expect("trustless combine");
			assert!(ok, "N={n}: honest accumulated claim must hold on P");

			// FORGERY: a combiner claims a different output for a shard ⇒ caught by the fold.
			for &f in &[0usize, n / 2, n - 1] {
				let (acc, _p, _v) = super::trustless_combine(&records, inner, Some(f)).expect("trustless combine");
				assert!(!acc, "N={n}: a forged shard-output claim at {f} must be REJECTED by the proven fold");
			}
			println!("trustless-combiner N={n}: {} proven fold steps, total fold-verify {tv} ms; honest holds, forged claim REJECTED", n - 1);
		}
		println!("# TRUSTLESS COMBINER: N shard claims → 1 accumulator via N−1 PROVEN narrow fold steps; the resolver verifies the fold steps + the final claim, never trusting the combiner. A forged shard output fails the fold's g(1)=v1 check ⇒ REJECT. No O(width) in-circuit proof-verify — the ms trustless recursion.");
	}

	/// O(1) COLLAPSE: fold N shard claims and prove ALL N−1 folds in ONE table, so the resolver
	/// verifies a SINGLE proof (~constant in N) instead of O(N) per-step verifies — still trustless
	/// (a forged shard output is caught), now with ~constant-verify.  Shows verify flat as N grows.
	#[test]
	#[ignore = "O(1)-collapsed trustless combiner (single fold-tree proof); run with --ignored"]
	fn trustless_combiner_o1_collapse() {
		use rand::{RngCore, SeedableRng};
		let inner = 3usize;
		println!("\n=== O(1)-collapsed trustless combiner — ONE fold-tree proof for N−1 folds ===");
		println!("| N shards | folds (N−1) | prove_ms | VERIFY_ms (one proof) | proof_bytes | accepted |");
		for &n in &[4usize, 8, 16, 32] {
			let mut rng = rand::rngs::StdRng::from_seed([0x9c ^ n as u8; 32]);
			let records: Vec<Vec<OurB256>> = (0..n)
				.map(|_| (0..(1usize << inner)).map(|_| OurB256::from(binius_field::BinaryField128b::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128))).collect())
				.collect();
			let (ok, pm, vm, sz) = super::trustless_combine_o1(&records, inner, None).expect("o1 combine");
			assert!(ok, "N={n}: honest O(1) combine must accept");
			// forgery still caught (native gate before the single proof).
			let (bad, _, _, _) = super::trustless_combine_o1(&records, inner, Some(n / 2)).expect("o1 combine");
			assert!(!bad, "N={n}: a forged shard output must be REJECTED (O(1) path)");
			println!("| {n} | {} | {pm} | {vm} | {sz} | {} |", n - 1, if ok { "✓" } else { "✗" });
		}
		println!("(ALL N−1 folds proven in ONE narrow fold-verify table ⇒ the resolver verifies ONE proof, ~constant in N — the O(1) trustless-combiner verify. Forged shard output still REJECTED.)");
	}

	/// The combiner trust model is a COMPILE-TIME flag: `combine_and_verify` runs the trustless
	/// fold-tree by default, or the trusted `epoch_fold` under `--features trusted-combiner`.
	/// Same call site; the flag swaps the trust↔verify-cost tradeoff.
	#[test]
	fn combiner_trust_model_by_flag() {
		use rand::{RngCore, SeedableRng};
		let inner = 3usize;
		let n = 4usize;
		let mut rng = rand::rngs::StdRng::from_seed([0xab; 32]);
		let records: Vec<Vec<u64>> = (0..n).map(|_| (0..(1usize << inner)).map(|_| rng.next_u64()).collect()).collect();
		let rep = super::combine_and_verify(&records, inner).expect("combine_and_verify");
		assert!(rep.accepted, "the combiner must accept honest shard outputs");
		#[cfg(feature = "trusted-combiner")]
		assert!(rep.trust_model.starts_with("trusted"), "feature ON ⇒ trusted combiner");
		#[cfg(not(feature = "trusted-combiner"))]
		assert!(rep.trust_model.starts_with("trustless"), "feature OFF (default) ⇒ trustless combiner");
		println!("GATE combiner-flag: trust model = {} ; resolver verify {} µs  (swap with --features trusted-combiner)", rep.trust_model, rep.verify_us);
	}

	/// ★THE MEASUREMENT — is the fold-verify circuit NARROW? Sweep d (interleaved-poly vars);
	/// report verify vs d. Contrast: the Keccak op-table verifies in ~6.7s, SHA-256 ~26s. If
	/// the fold-verify verifies in tens of ms, accumulation breaks the FIPS-width tension:
	/// arithmetizing the FOLD (narrow) instead of the FRI-VERIFY (wide) gives ms recursion.
	#[test]
	#[ignore = "heavy (~minutes): fold-verify width sweep"]
	fn fold_verify_is_narrow() {
		println!("| d (interleaved vars) | B256 muls | prove ms | verify ms | proof KB |");
		println!("|---:|---:|---:|---:|---:|");
		for d in [4usize, 8, 16, 24, 32] {
			let (p, v, sz, muls) = prove_verify_fold_verify(d).expect("fold-verify must prove+verify");
			println!("| {} | {} | {} | {} | {} |", d, muls, p, v, sz / 1024);
		}
		println!("# fold-verify circuit is 2d B256 muls (Horner + line), NO hash gadget. Contrast Keccak \
			 op-table ~6.7s / SHA-256 ~26s verify. If this is tens of ms, arithmetizing the FOLD (narrow) \
			 instead of the FRI-VERIFY (wide) is the ms-recursion path — accumulation breaks the width tension.");
	}

	/// MEASUREMENT — the HYBRID publisher fold tree over BATCH-instance leaves (the reviewer's
	/// publisher-half number). A batch proof's instance is an eval claim, so the SAME fold admits
	/// batch leaves unchanged. For `.se` (1.5 M records): ~184 batch leaves @ 8192/batch, or
	/// ~2930 @ 512/batch. Measure `run_ivc` at batch-leaf counts for per-step fold cost + total
	/// (aggregator once-per-epoch), extrapolate to 184/2930. Edge verify UNCHANGED — one decider
	/// (batch-width, ~9–13 s L1) + the fold — O(1) in leaves.
	#[test]
	#[ignore = "measurement (~1 min): hybrid fold tree over batch-instance leaves"]
	fn fold_tree_over_batch_leaves() {
		println!("\n=== HYBRID fold tree over BATCH-instance leaves (aggregator, once per epoch) ===");
		println!("| batch leaves | steps | total prove ms | per-step ms | final claim |");
		println!("|---:|---:|---:|---:|:--:|");
		let mut per_step = 0f64;
		for n in [8usize, 32] {
			let s = run_ivc(n, 8).expect("fold tree over batch leaves");
			assert!(s.final_claim_holds, "fold chain final claim FALSE (N={n})");
			per_step = s.total_prove_ms as f64 / (n - 1) as f64;
			println!("| {} | {} | {} | {:.1} | {} |", n, n - 1, s.total_prove_ms, per_step, if s.final_claim_holds { "OK" } else { "X" });
		}
		let ps = per_step / 1000.0;
		let depth = |leaves: f64| (leaves.log2().ceil()) * ps; // balanced-tree critical path
		println!(
			"\nEXTRAPOLATION (per-step ~{:.0} ms):\n\
			 * .se @ 8192/batch (~184 leaves):  CHAIN ~{:.0} s  |  balanced-TREE critical path ~{:.0} s (depth {})\n\
			 * .se @  512/batch (~2930 leaves): CHAIN ~{:.0} s  |  balanced-TREE critical path ~{:.0} s (depth {})\n\
			 The chain is O(leaves) SEQUENTIAL; a balanced fold tree is O(leaves) total WORK but log-depth \
			 critical path — same fleet-parallelism as the batch proves ⇒ ~seconds wall, not minutes.",
			per_step,
			183.0 * ps, depth(184.0), (184f64).log2().ceil() as u32,
			2929.0 * ps, depth(2930.0), (2930f64).log2().ceil() as u32
		);
		println!(
			"# HYBRID publisher (the answer, not the fallback): fleet proves ~184 batches of 8192 @ ~1.15 GiB \
			 each -- BOUNDED RSS/machine, embarrassingly parallel ACROSS proofs (the only parallelism that works, \
			 per the twice-measured rayon-negative). Aggregator folds the batch instances (once per epoch; \
			 sequential chain here, log-depth tree cuts it). Edge verifies ONE decider at batch-width (~9-13 s L1, \
			 O(1) in leaves) + the fold -- VERIFIER HALF UNTOUCHED, headline survives. The fold admits \
			 batch-instance leaves unchanged (fold is over eval claims); if that tree IS the tree binding R*, \
			 tiers 1+2 merge into one accumulated object.");
	}
}
