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
use crate::gf256_air::{beta, build_b256_mul, col4, pop_b256_mul, split256, wc64};

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
	use rand::SeedableRng;
	assert!(d >= 1);
	let mut rng = rand::rngs::StdRng::from_seed([0xac; 32]);
	let g: Vec<OurB256> = (0..=d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let t = <OurB256 as Field>::random(&mut rng);
	let r0: Vec<OurB256> = (0..d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let r1: Vec<OurB256> = (0..d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let s = fold_step(&g, t, &r0, &r1)?;
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
pub fn fold_step(g: &[OurB256], t: OurB256, r0: &[OurB256], r1: &[OurB256]) -> Result<StepOut> {
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

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, NROWS)?;
		let mut seg = tw.full_segment();
		for row in 0..NROWS {
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
		let step = fold_step(&g, t, &acc.0, &item.0)?;
		total_p += step.prove_ms;
		total_v += step.verify_ms;
		max_v = max_v.max(step.verify_ms);
		acc = (step.line, step.folded);
	}
	let final_claim_holds = mle256(&p, &acc.0) == acc.1;
	Ok(IvcSummary { n_records, inner_vars, d, total_prove_ms: total_p, total_verify_ms: total_v, max_step_verify_ms: max_v, final_claim_holds })
}

#[cfg(test)]
mod tests {
	use super::*;

	/// GATE acc-air-sound — the in-circuit fold-verify PROVES+VERIFIES (validate_witness +
	/// prove/verify) for the native-consistent witness, i.e. the Horner/line arithmetization
	/// == fold_verify_native. Also: a wrong folded value would violate the Horner constraint.
	#[test]
	fn fold_verify_circuit_proves() {
		let (p, v, sz, muls) = prove_verify_fold_verify(8).expect("fold-verify circuit must prove+verify");
		println!("GATE acc-air-sound: in-circuit fold-verify (d=8, {muls} B256 muls) PROVES+VERIFIES over \
			 B256 @L1(128) == native; prove {p} ms, verify {v} ms, proof {} KB", sz / 1024);
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
}
