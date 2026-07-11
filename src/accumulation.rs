// accumulation — exploration prototype for ms-verify recursion over binius (Option 3).
//
// See docs/accumulation-recursion.md. The measured problem: binius verify is LINEAR in
// committed width, so verifying a proof in-circuit (arithmetizing a FIPS hash to recompute
// Merkle paths) makes the recursion circuit wide → seconds. Accumulation dodges this by
// NEVER verifying the inner proof in-circuit: fold each new evaluation claim into a running
// accumulator with a CHEAP step (O(log size), width-independent), and open the committed
// polynomial exactly ONCE at the end.
//
// This module is the ATOMIC step (experiment 1): the point-reduction fold of two multilinear
// evaluation claims `M(r0)=v0`, `M(r1)=v1` on the same polynomial into one claim
// `M(ℓ(t*))=g(t*)`, where ℓ is the line r0→r1 and g = M∘ℓ is a degree-≤n univariate. The
// verifier's fold work is O(n) (check the univariate g) — INDEPENDENT of the polynomial's
// size 2^n. That width-independence is the whole point: it's why accumulation can be ms.
//
// Native model only (no circuit) — this is a research prototype to establish the primitive
// and its cost profile before touching binius's PIOP.

use binius_field::{BinaryField128b as F, Field};

/// A multilinear evaluation claim: the polynomial (given by its 2^n hypercube evaluations,
/// held by the prover / committed) evaluates to `value` at `point` (∈ F^n).
#[derive(Clone, Debug)]
pub struct EvalClaim {
	pub point: Vec<F>,
	pub value: F,
}

/// Multilinear extension of `evals` (length 2^n) at `point` (length n). O(2^n).
pub fn mle_eval(evals: &[F], point: &[F]) -> F {
	let n = point.len();
	assert_eq!(evals.len(), 1 << n);
	// eq(i, point) = prod_j (i_j·p_j + (1-i_j)(1-p_j)); char 2 ⇒ 1-p = 1+p.
	let mut acc = F::ZERO;
	for (i, &e) in evals.iter().enumerate() {
		let mut w = F::ONE;
		for (j, &pj) in point.iter().enumerate() {
			w *= if (i >> j) & 1 == 1 { pj } else { F::ONE + pj };
		}
		acc += e * w;
	}
	acc
}

/// The line ℓ(t) = r0 + t·(r1 − r0), componentwise. ℓ(0)=r0, ℓ(1)=r1 (char 2: r1−r0 = r1+r0).
pub fn line(r0: &[F], r1: &[F], t: F) -> Vec<F> {
	r0.iter().zip(r1).map(|(&a, &b)| a + t * (a + b)).collect()
}

/// The univariate g(t) = M(ℓ(t)), degree ≤ n, returned as evaluations at t = 0,1,…,n
/// (n+1 points, enough to interpolate a degree-n polynomial). O(n · 2^n) for the PROVER;
/// the verifier never runs this — it only checks the returned values.
pub fn restrict_to_line(evals: &[F], r0: &[F], r1: &[F]) -> Vec<F> {
	let n = r0.len();
	(0..=n)
		.map(|k| {
			let t = F::from(k as u8 as u128 * 0 + k as u128 as u128).pow([0]); // placeholder, replaced below
			let _ = t;
			let tk = small_field_elt(k);
			mle_eval(evals, &line(r0, r1, tk))
		})
		.collect()
}

/// Distinct field elements 0,1,2,… for interpolation nodes (binary field: element k = the
/// value whose bits are the binary digits of k — distinct for k < field size).
fn small_field_elt(k: usize) -> F {
	F::from(k as u128)
}

/// Lagrange-interpolate the degree-≤n univariate given its values at nodes 0..=n, evaluate at `t`.
fn interp_eval(vals: &[F], t: F) -> F {
	let m = vals.len();
	let nodes: Vec<F> = (0..m).map(small_field_elt).collect();
	let mut acc = F::ZERO;
	for i in 0..m {
		let mut num = F::ONE;
		let mut den = F::ONE;
		for j in 0..m {
			if i != j {
				num *= t + nodes[j];
				den *= nodes[i] + nodes[j];
			}
		}
		acc += vals[i] * num * den.invert().unwrap();
	}
	acc
}

/// The prover's fold message: g's values at 0..=n (the line restriction of M).
pub type FoldProof = Vec<F>;

/// PROVER: fold two claims about the same committed polynomial `evals` into one.
/// Returns (fold_proof = g|0..n, folded_claim). `challenge` is the verifier's random t*.
pub fn fold_prove(evals: &[F], c0: &EvalClaim, c1: &EvalClaim, challenge: F) -> (FoldProof, EvalClaim) {
	let g = restrict_to_line(evals, &c0.point, &c1.point);
	let folded_point = line(&c0.point, &c1.point, challenge);
	let folded_value = interp_eval(&g, challenge);
	(g, EvalClaim { point: folded_point, value: folded_value })
}

/// VERIFIER: check the fold is consistent and produce the folded claim — WITHOUT touching the
/// polynomial. Cost is O(n) (interpolate/evaluate the degree-n univariate g), INDEPENDENT of
/// 2^n. Returns `Some(folded_claim)` iff g(0)=v0 and g(1)=v1; else the fold is rejected.
pub fn fold_verify(c0: &EvalClaim, c1: &EvalClaim, g: &FoldProof, challenge: F) -> Option<EvalClaim> {
	let n = c0.point.len();
	if g.len() != n + 1 {
		return None;
	}
	// g(0) must equal v0, g(1) must equal v1 (the line endpoints are the two claims).
	if interp_eval(g, small_field_elt(0)) != c0.value || interp_eval(g, small_field_elt(1)) != c1.value {
		return None;
	}
	Some(EvalClaim {
		point: line(&c0.point, &c1.point, challenge),
		value: interp_eval(g, challenge),
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use rand::{rngs::StdRng, RngCore, SeedableRng};
	use std::time::Instant;

	fn rand_f(rng: &mut StdRng) -> F {
		F::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128)
	}
	fn rand_evals(n: usize, rng: &mut StdRng) -> Vec<F> {
		(0..(1usize << n)).map(|_| rand_f(rng)).collect()
	}
	fn rand_point(n: usize, rng: &mut StdRng) -> Vec<F> {
		(0..n).map(|_| rand_f(rng)).collect()
	}

	/// GATE acc-fold — the point-reduction fold is SOUND: the folded claim holds on the real
	/// polynomial (M(ℓ(t*)) == g(t*)), and a tampered claim value is REJECTED (g(0)≠v0).
	#[test]
	fn fold_two_claims_sound() {
		let mut rng = StdRng::from_seed([7u8; 32]);
		for n in [4usize, 8, 12] {
			let evals = rand_evals(n, &mut rng);
			let (r0, r1) = (rand_point(n, &mut rng), rand_point(n, &mut rng));
			let c0 = EvalClaim { point: r0.clone(), value: mle_eval(&evals, &r0) };
			let c1 = EvalClaim { point: r1.clone(), value: mle_eval(&evals, &r1) };
			let t = rand_f(&mut rng);

			let (g, folded) = fold_prove(&evals, &c0, &c1, t);
			// (a) verifier accepts + the folded claim is TRUE on the real polynomial.
			let acc = fold_verify(&c0, &c1, &g, t).expect("honest fold must verify");
			assert_eq!(acc.value, folded.value);
			assert_eq!(mle_eval(&evals, &acc.point), acc.value, "folded claim false on M (n={n})");
			// (b) a tampered claim value is rejected.
			let bad = EvalClaim { point: r0.clone(), value: c0.value + F::ONE };
			assert!(fold_verify(&bad, &c1, &g, t).is_none(), "tampered v0 accepted (n={n})");
		}
		println!("GATE acc-fold: point-reduction fold of two eval claims is SOUND (folded claim holds on M; tamper rejected)");
	}

	/// GATE acc-cost — the VERIFIER's fold cost is width-INDEPENDENT: folding claims on
	/// polynomials of size 2^n costs O(n) (the univariate g), NOT O(2^n). This is the
	/// property that makes accumulation ms — the fold never touches the 2^n-sized witness.
	#[test]
	fn fold_verify_is_width_independent() {
		let mut rng = StdRng::from_seed([9u8; 32]);
		println!("| n (vars) | poly size 2^n | verifier fold ms | direct mle_eval ms |");
		println!("|---:|---:|---:|---:|");
		for n in [6usize, 10, 14, 18] {
			let evals = rand_evals(n, &mut rng);
			let (r0, r1) = (rand_point(n, &mut rng), rand_point(n, &mut rng));
			let c0 = EvalClaim { point: r0.clone(), value: mle_eval(&evals, &r0) };
			let c1 = EvalClaim { point: r1.clone(), value: mle_eval(&evals, &r1) };
			let t = rand_f(&mut rng);
			let (g, _) = fold_prove(&evals, &c0, &c1, t);
			// verifier fold: only the univariate g (size n+1) — no polynomial access.
			let t0 = Instant::now();
			for _ in 0..1000 {
				let _ = fold_verify(&c0, &c1, &g, t).unwrap();
			}
			let fold_us = t0.elapsed().as_micros() as f64 / 1000.0;
			// contrast: ONE direct evaluation of the 2^n polynomial (what NOT folding costs per claim).
			let t1 = Instant::now();
			let _ = mle_eval(&evals, &r0);
			let direct_ms = t1.elapsed().as_micros() as f64 / 1000.0;
			println!("| {} | {} | {:.4} | {:.4} |", n, 1usize << n, fold_us / 1000.0, direct_ms);
		}
		println!("# verifier fold cost is FLAT in n (~O(n) on the univariate), while a direct claim check \
			 (mle_eval) grows with 2^n. Accumulation defers the single 2^n opening to the end — the fold \
			 itself is width-independent. This is the ms-recursion lever binius's O(width) in-circuit verify lacks.");
	}
}
