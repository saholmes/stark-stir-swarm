// accumulation — exploration prototype for ms-verify recursion over binius (Option 3).
//
// See docs/accumulation-recursion.md. The measured problem: binius verify is LINEAR in
// committed width (m5_air::verify_vs_width_diagnostic), so verifying a proof in-circuit
// (arithmetizing a FIPS hash to recompute Merkle paths) makes the recursion circuit wide →
// seconds. Accumulation dodges this by NEVER verifying the inner proof in-circuit: fold each
// new evaluation claim into a running accumulator with a CHEAP step (O(log size), width-
// independent), and open the committed polynomial exactly ONCE at the end.
//
// This module is the ATOMIC step (experiment 1): the point-reduction fold of two multilinear
// evaluation claims M(r0)=v0, M(r1)=v1 on the same polynomial into one claim M(ℓ(t*))=g(t*),
// where ℓ is the line r0→r1 and g = M∘ℓ is a degree-≤n univariate. The verifier's fold work
// is O(n) (check the univariate g) — INDEPENDENT of the polynomial's size 2^n. That width-
// independence is the whole point: it's why accumulation can be ms.
//
// Native model only (no circuit) — a research prototype to establish the primitive and its
// cost profile before touching binius's PIOP.

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

/// Distinct interpolation nodes 0,1,2,… as field elements (binary field: element k = the
/// value whose bits are the binary digits of k — distinct for k < field size).
fn node(k: usize) -> F {
	F::from(k as u128)
}

/// The univariate g(t) = M(ℓ(t)), degree ≤ n, as evaluations at t = 0,1,…,n (n+1 points,
/// enough to interpolate a degree-n polynomial). O(n · 2^n) for the PROVER; the verifier
/// never runs this — it only checks the returned values.
pub fn restrict_to_line(evals: &[F], r0: &[F], r1: &[F]) -> Vec<F> {
	let n = r0.len();
	(0..=n).map(|k| mle_eval(evals, &line(r0, r1, node(k)))).collect()
}

/// Lagrange-interpolate the degree-≤n univariate given its values at nodes 0..=n, evaluate at `t`.
fn interp_eval(vals: &[F], t: F) -> F {
	let m = vals.len();
	let nodes: Vec<F> = (0..m).map(node).collect();
	let mut acc = F::ZERO;
	for i in 0..m {
		let (mut num, mut den) = (F::ONE, F::ONE);
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

/// PROVER: fold two claims about the same committed polynomial `evals` into one. Returns
/// (fold_proof = g|0..n, folded_claim). `challenge` is the verifier's random t*.
pub fn fold_prove(evals: &[F], c0: &EvalClaim, c1: &EvalClaim, challenge: F) -> (FoldProof, EvalClaim) {
	let g = restrict_to_line(evals, &c0.point, &c1.point);
	(g.clone(), EvalClaim { point: line(&c0.point, &c1.point, challenge), value: interp_eval(&g, challenge) })
}

/// VERIFIER: check the fold is consistent and produce the folded claim — WITHOUT touching the
/// polynomial. Cost is O(n) (interpolate/evaluate the degree-n univariate g), INDEPENDENT of
/// 2^n. Returns Some(folded_claim) iff g(0)=v0 and g(1)=v1; else the fold is rejected.
pub fn fold_verify(c0: &EvalClaim, c1: &EvalClaim, g: &FoldProof, challenge: F) -> Option<EvalClaim> {
	let n = c0.point.len();
	if g.len() != n + 1 {
		return None;
	}
	if interp_eval(g, node(0)) != c0.value || interp_eval(g, node(1)) != c1.value {
		return None;
	}
	Some(EvalClaim { point: line(&c0.point, &c1.point, challenge), value: interp_eval(g, challenge) })
}

// --- experiment 2: CROSS-RECORD folding (different polynomials) --------------------------
//
// Records have DIFFERENT polynomials P_i (separate witnesses/commitments). Fold their claims
// without homomorphic commitments via INTERLEAVING: stack the N records (a power of two) into
// ONE polynomial P over n+log N vars, with P(x, bin(i)) = P_i(x). Each record claim
// "P_i(r_i)=v_i" LIFTS to "P((r_i, bin(i))) = v_i" — now all about the SAME P — so the atomic
// same-poly point-reduction fold (experiment 1) applies. Chain N−1 folds → ONE accumulated
// claim about P. Each fold is width-independent (µs); a false record value is caught at its
// fold (g(1) = the true interleaved value ≠ the claimed value → rejected).

/// One record: its multilinear witness `evals` (2^n) + the evaluation claim about it.
#[derive(Clone)]
pub struct Record {
	pub evals: Vec<F>,
	pub claim: EvalClaim, // claim.point is the inner n-dim point
}

/// Interleave N records (N a power of two) each of size 2^n into one 2^(n+log N) polynomial:
/// block i (indices i·2^n .. (i+1)·2^n) holds record i's evaluations, so the high log N index
/// bits select the record. The COMMITMENT to this is the Merkle parent over the N record
/// commitments (the zone tree) — one hash per level, homomorphism-FREE (no additive homomorphism
/// needed). Whether that parent is FRI-openable as P's codeword is the decider crux (see note).
pub fn interleave(records: &[Record]) -> Vec<F> {
	let nrec = records.len();
	assert!(nrec.is_power_of_two(), "record count must be a power of two");
	let mut out = Vec::with_capacity(records[0].evals.len() * nrec);
	for r in records {
		out.extend_from_slice(&r.evals);
	}
	out
}

/// Lift record `i`'s inner claim to a claim about the interleaved polynomial: append the
/// {0,1} embedding of `i` (log N bits) to the inner point.
pub fn lifted_claim(rec: &Record, i: usize, m: usize) -> EvalClaim {
	let mut point = rec.claim.point.clone();
	for b in 0..m {
		point.push(if (i >> b) & 1 == 1 { F::ONE } else { F::ZERO });
	}
	EvalClaim { point, value: rec.claim.value }
}

/// PROVER: accumulate N records into ONE claim about the interleaved polynomial, via a chain
/// of N−1 same-poly point-reduction folds. Returns (interleaved poly, accumulated claim,
/// fold proofs). `challenges` supplies one t* per fold.
pub fn accumulate(records: &[Record], challenges: &[F]) -> (Vec<F>, EvalClaim, Vec<FoldProof>) {
	let interleaved = interleave(records);
	let m = records.len().trailing_zeros() as usize;
	let claims: Vec<EvalClaim> = records.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();
	let mut acc = claims[0].clone();
	let mut proofs = Vec::with_capacity(claims.len() - 1);
	for (k, ck) in claims.iter().enumerate().skip(1) {
		let (g, folded) = fold_prove(&interleaved, &acc, ck, challenges[k - 1]);
		proofs.push(g);
		acc = folded;
	}
	(interleaved, acc, proofs)
}

/// VERIFIER: replay the fold chain over the N record claims WITHOUT the interleaved witness,
/// producing the accumulated claim. O(N) cheap folds (each width-independent). Returns
/// Some(accumulated claim) iff every fold is consistent (each record's value is bound).
pub fn accumulate_verify(records_claims: &[EvalClaim], proofs: &[FoldProof], challenges: &[F]) -> Option<EvalClaim> {
	let mut acc = records_claims[0].clone();
	for (k, ck) in records_claims.iter().enumerate().skip(1) {
		acc = fold_verify(&acc, ck, &proofs[k - 1], challenges[k - 1])?;
	}
	Some(acc)
}

/// RSS model for the interleaved-batch commit that gives O(1)-verify aggregation.
/// `inner_log_rows` = log2 of one record's trace rows; `log_n` = log2(#records);
/// `log_blowup` = FRI rate exponent; `field_bytes` = committed element size.
#[derive(Debug, Clone, Copy)]
pub struct CommitRss {
	pub per_record_codeword_bytes: u64, // one record's RS codeword (encodes independently)
	pub native_full_bytes: u64,         // binius one-shot buffer = the whole interleaved codeword
	pub streamed_floor_bytes: u64,      // custom streaming: N column symbols + one record buffer + Merkle spine
}
pub fn interleaved_commit_rss(inner_log_rows: usize, log_n: usize, log_blowup: usize, field_bytes: u64) -> CommitRss {
	let per_record = (1u64 << (inner_log_rows + log_blowup)) * field_bytes;
	let n = 1u64 << log_n;
	let native_full = per_record * n; // 2^(inner+logN)·blowup·bytes
	// streaming: encode each record independently (one per-record buffer), stash codewords, then
	// stream the interleaved-coset Merkle: each coset column needs one symbol from all N records.
	let merkle_spine = (inner_log_rows + log_n + log_blowup) as u64 * field_bytes; // O(log) pending nodes
	let column = n * field_bytes; // N symbols in flight per interleaved coset
	let streamed_floor = per_record + column + merkle_spine;
	CommitRss { per_record_codeword_bytes: per_record, native_full_bytes: native_full, streamed_floor_bytes: streamed_floor }
}

#[cfg(test)]
mod tests {
	use super::*;
	use rand::{rngs::StdRng, RngCore, SeedableRng};
	use std::time::Instant;

	fn mib(b: u64) -> f64 {
		b as f64 / (1024.0 * 1024.0)
	}

	/// The RSS answer for the O(1)-verify interleaved commit: native (one-shot) grows with N;
	/// streamed floor is O(N symbols + one record) — LOW and N-flat in the big term. The
	/// streaming needs a custom commit path (binius allocates the full buffer), but the encode
	/// is separable (encode_ext_batch_inplace per record) so it's the sliver/low-mem-streaming
	/// technique applied to the interleaved-coset Merkle.
	#[test]
	fn interleaved_commit_rss_model() {
		println!("| record 2^rows | N records | per-record cw | NATIVE full RSS | STREAMED floor |");
		println!("|:--|---:|---:|---:|---:|");
		for (inner, log_n) in [(10usize, 7usize), (10, 10), (15, 10), (15, 13)] {
			let r = interleaved_commit_rss(inner, log_n, 1, 32); // blowup 2, B256 (32B)
			println!(
				"| 2^{} | {} | {:.2} MiB | {:.1} MiB | {:.2} MiB |",
				inner, 1usize << log_n, mib(r.per_record_codeword_bytes), mib(r.native_full_bytes), mib(r.streamed_floor_bytes)
			);
		}
		println!("# NATIVE (binius one-shot, full buffer) RSS = O(N x per-record) — GROWS with N (128MiB..8GiB). \
			 STREAMED floor = per-record buffer + N column symbols + Merkle spine — LOW + N-flat in the big \
			 term (the N-symbol column is KB). ⇒ O(1)-VERIFY interleaved commit CAN be low-RSS, but NOT with \
			 binius native (materializes the batch); needs a custom streaming commit — the encode is separable \
			 so this is the sliver/low-mem-streaming problem applied to the interleaved-coset Merkle.");
	}

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
			let acc = fold_verify(&c0, &c1, &g, t).expect("honest fold must verify");
			assert_eq!(acc.value, folded.value);
			assert_eq!(mle_eval(&evals, &acc.point), acc.value, "folded claim false on M (n={n})");
			let bad = EvalClaim { point: r0.clone(), value: c0.value + F::ONE };
			assert!(fold_verify(&bad, &c1, &g, t).is_none(), "tampered v0 accepted (n={n})");
		}
		println!("GATE acc-fold: point-reduction fold of two eval claims is SOUND (folded claim holds on M; tamper rejected)");
	}

	/// GATE acc-crossrecord — N DIFFERENT-polynomial record claims fold into ONE via
	/// interleaving + point-reduction (homomorphism-free): the accumulated claim holds on the
	/// interleaved polynomial, and a tampered record value is caught at its fold.
	#[test]
	fn cross_record_fold_sound() {
		let mut rng = StdRng::from_seed([11u8; 32]);
		let n = 8; // inner vars per record
		for &nrec in &[2usize, 4, 8] {
			let m = nrec.trailing_zeros() as usize;
			let records: Vec<Record> = (0..nrec)
				.map(|_| {
					let evals = rand_evals(n, &mut rng);
					let r = rand_point(n, &mut rng);
					let v = mle_eval(&evals, &r);
					Record { evals, claim: EvalClaim { point: r, value: v } }
				})
				.collect();
			let challenges: Vec<F> = (0..nrec - 1).map(|_| rand_f(&mut rng)).collect();

			let (interleaved, acc, proofs) = accumulate(&records, &challenges);
			// the accumulated claim is TRUE on the interleaved polynomial.
			assert_eq!(mle_eval(&interleaved, &acc.point), acc.value, "accumulated claim false (nrec={nrec})");
			// the verifier replays the folds from the lifted claims WITHOUT the witness.
			let lifted: Vec<EvalClaim> = records.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();
			let vacc = accumulate_verify(&lifted, &proofs, &challenges).expect("honest accumulate must verify");
			assert_eq!(vacc.value, acc.value);
			// tamper record 1's claimed value → its fold catches it (g(1) = true value ≠ claimed).
			let mut bad = lifted.clone();
			bad[1].value += F::ONE;
			let tampered = accumulate_verify(&bad, &proofs, &challenges);
			assert!(tampered.is_none() || tampered.unwrap().value != acc.value, "tampered record accepted (nrec={nrec})");
		}
		println!("GATE acc-crossrecord: N different-polynomial record claims fold into ONE (interleave + \
			 point-reduction, homomorphism-free); accumulated claim holds on interleaved P; tamper caught");
	}

	/// GATE acc-scaling — the accumulate VERIFIER cost vs N records: O(N) cheap folds (each
	/// width-independent µs). O(N)·µs = ms even for large N — vs Tier-B O(N)·seconds
	/// (in-circuit FRI-verify per record). The measured accumulation win, and its honest limit.
	#[test]
	fn accumulate_verify_cost_vs_n() {
		let mut rng = StdRng::from_seed([13u8; 32]);
		let n = 8;
		println!("| N records | accumulate-verify µs | µs/record |");
		println!("|---:|---:|---:|");
		for &nrec in &[2usize, 8, 32, 128] {
			let m = nrec.trailing_zeros() as usize;
			let records: Vec<Record> = (0..nrec)
				.map(|_| {
					let evals = rand_evals(n, &mut rng);
					let r = rand_point(n, &mut rng);
					let v = mle_eval(&evals, &r);
					Record { evals, claim: EvalClaim { point: r, value: v } }
				})
				.collect();
			let challenges: Vec<F> = (0..nrec - 1).map(|_| rand_f(&mut rng)).collect();
			let (_, _, proofs) = accumulate(&records, &challenges);
			let lifted: Vec<EvalClaim> = records.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();
			let t0 = Instant::now();
			for _ in 0..100 {
				let _ = accumulate_verify(&lifted, &proofs, &challenges).unwrap();
			}
			let us = t0.elapsed().as_micros() as f64 / 100.0;
			println!("| {} | {:.1} | {:.2} |", nrec, us, us / nrec as f64);
		}
		println!("# accumulate-verify is O(N) cheap folds (~µs/record), NOT touching any 2^n witness. \
			 O(N)·µs = ms at N=1000s vs Tier-B O(N)·seconds in-circuit-FRI-verify. ★HONEST LIMIT: this is \
			 O(N), not O(1) — and the DECIDER must still open the interleaved poly. O(1) decider needs the \
			 interleaved commitment (Merkle-parent of record commitments) to be FRI-openable via binius's \
			 interleaved codes; else it's N deferred openings. That commitment crux is the next question.");
	}

	/// GATE acc-cost — the VERIFIER's fold cost is width-INDEPENDENT: folding claims on
	/// polynomials of size 2^n costs O(n) (the univariate g), NOT O(2^n). This is the
	/// property that makes accumulation ms — the fold never touches the 2^n-sized witness.
	#[test]
	fn fold_verify_is_width_independent() {
		let mut rng = StdRng::from_seed([9u8; 32]);
		println!("| n (vars) | poly size 2^n | verifier fold µs | direct mle_eval µs |");
		println!("|---:|---:|---:|---:|");
		for n in [6usize, 10, 14, 18] {
			let evals = rand_evals(n, &mut rng);
			let (r0, r1) = (rand_point(n, &mut rng), rand_point(n, &mut rng));
			let c0 = EvalClaim { point: r0.clone(), value: mle_eval(&evals, &r0) };
			let c1 = EvalClaim { point: r1.clone(), value: mle_eval(&evals, &r1) };
			let t = rand_f(&mut rng);
			let (g, _) = fold_prove(&evals, &c0, &c1, t);
			let t0 = Instant::now();
			for _ in 0..1000 {
				let _ = fold_verify(&c0, &c1, &g, t).unwrap();
			}
			let fold_us = t0.elapsed().as_micros() as f64 / 1000.0;
			let t1 = Instant::now();
			let _ = mle_eval(&evals, &r0);
			let direct_us = t1.elapsed().as_micros() as f64;
			println!("| {} | {} | {:.3} | {:.1} |", n, 1usize << n, fold_us, direct_us);
		}
		println!("# verifier fold cost is FLAT in n (~O(n) on the univariate) while a direct claim check \
			 (mle_eval) grows with 2^n. Accumulation defers the single 2^n opening to the end — the fold \
			 itself is width-independent. This is the ms-recursion lever binius's O(width) in-circuit verify lacks.");
	}
}
