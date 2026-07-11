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

/// Prove + verify the in-circuit fold-verify for a degree-`d` fold (d≥1). Returns
/// `(prove_ms, verify_ms, proof_bytes, n_b256_muls)`; gated == `fold_verify_native`.
pub fn prove_verify_fold_verify(d: usize) -> Result<(u128, u128, usize, usize)> {
	use rand::SeedableRng;
	use std::time::Instant;
	assert!(d >= 1);
	let mut rng = rand::rngs::StdRng::from_seed([0xac; 32]);

	let g: Vec<OurB256> = (0..=d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let t = <OurB256 as Field>::random(&mut rng);
	let r0: Vec<OurB256> = (0..d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let r1: Vec<OurB256> = (0..d).map(|_| <OurB256 as Field>::random(&mut rng)).collect();
	let v0 = g[0];
	let v1 = g.iter().copied().fold(OurB256::ZERO, |a, c| a + c);
	let (line_n, folded_n) = fold_verify_native(&g, t, v0, v1, &r0, &r1).expect("native fold must verify");

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
	let sz = proof.get_proof_size();
	let t1 = Instant::now();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((prove_ms, t1.elapsed().as_millis(), sz, n_muls))
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
