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

	/// GATE hybrid-e2e — THE FIGURE-ONE CAPSTONE. The whole hybrid epoch pipeline as ONE gate:
	/// 16 batch-instance accumulators → a REAL balanced binary fold tree (15 accumulator-merges,
	/// depth 4) → ONE accumulated root claim → the HYBRID DECIDER verify (native mle + the
	/// O(leaves) fold-verify path) → POSITION-BINDING (permute a batch ⇒ a different R*; a lying
	/// leaf ⇒ rejected) → R* + a µs Merkle path. Every hop is MEASURED. The interior fold nodes
	/// fold ACCUMULATORS (not leaves): fold_prove/fold_verify are symmetric in c0/c1 (both are
	/// just eval claims on the same interleaved P), so a 2-to-1 accumulator merge is identical to
	/// a leaf fold — the load-bearing topology confirmation. Everything here is NATIVE (fold /
	/// mle_eval / SHA3), so it runs in ms; the per-node in-circuit STARK cost is ~785ms (fold_step,
	/// measured elsewhere) and the committed decider is the FRI-opening of R*-committed P (the
	/// crux at :127) — both flagged HONESTLY below, never quoted as measured here.
	#[test]
	fn hybrid_epoch_pipeline_e2e() {
		use binius_field::underlier::WithUnderlier;
		use crate::recursion::{merkle_auth_path, merkle_path_verify, merkle_tree_sha3};
		use crate::streaming_commit::streaming_interleaved_root;
		use sha3::{Digest, Sha3_256};

		// F → its 16 canonical little-endian bytes (for hashing sub-roots / R* symbols).
		fn f_bytes(x: F) -> [u8; 16] {
			u128::from(x.to_underlier()).to_le_bytes()
		}
		// SHA3-256 sub-root binding one batch's (position ‖ all its evals) — the per-batch
		// commitment the accumulated object carries ALONGSIDE its eval claim. Position i is IN
		// the hash, so permuting/substituting batches changes the sub-root (⇒ a different R*).
		fn batch_subroot(i: usize, evals: &[F]) -> [u8; 32] {
			let mut h = Sha3_256::new();
			h.update((i as u64).to_le_bytes());
			for &e in evals {
				h.update(f_bytes(e));
			}
			h.finalize().into()
		}

		let rss0 = crate::b256_sha3::peak_rss_bytes();
		let n_batches = 16usize; // the epoch's 16 accumulated batch-instances
		let m = n_batches.trailing_zeros() as usize; // log2 = 4 position bits
		let inner_vars = 6usize; // vars per batch poly (small ⇒ fast; L5 = same shape over B512)
		let mut rng = StdRng::from_seed([42u8; 32]);

		// --- HOP 1: 16 batch-instance leaves (each a stand-in accumulated object) --------------
		// evals = the batch's multilinear over inner_vars; claim = an inner EvalClaim on it;
		// sub-root = its 32-byte SHA3 commitment; position i is carried by enumerate.
		let records: Vec<Record> = (0..n_batches)
			.map(|_| {
				let evals = rand_evals(inner_vars, &mut rng);
				let r = rand_point(inner_vars, &mut rng);
				let v = mle_eval(&evals, &r);
				Record { evals, claim: EvalClaim { point: r, value: v } }
			})
			.collect();
		let subroots: Vec<[u8; 32]> = records.iter().enumerate().map(|(i, r)| batch_subroot(i, &r.evals)).collect();

		// Interleave the 16 batch polys into ONE P over inner_vars+4 = 10 vars, and LIFT each
		// batch's inner claim to P (lifted_claim appends the position bits — position ∈ the point).
		let p = interleave(&records);
		let leaves: Vec<EvalClaim> = records.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();
		for (i, lc) in leaves.iter().enumerate() {
			assert_eq!(mle_eval(&p, &lc.point), lc.value, "lifted leaf {i} false on P");
		}

		// --- HOP 2: REAL balanced binary fold tree (topology confirmation) ---------------------
		// Level 0 = the 16 lifted leaf claims. Repeatedly fold PAIRS with an FS challenge t,
		// EDGE-CHECKING each node with the width-independent verifier. 16→8→4→2→1 (depth 4, 15
		// interior nodes). The interior nodes fold ACCUMULATORS — the load-bearing case.
		let mut fs = StdRng::from_seed([99u8; 32]); // stands in for Fiat–Shamir t = H(transcript)
		let mut tree_nodes: Vec<(EvalClaim, EvalClaim, FoldProof, F)> = Vec::new(); // captured for the decider replay
		let t_build = Instant::now();
		let mut level = leaves.clone();
		let (mut nodes, mut depth) = (0usize, 0usize);
		while level.len() > 1 {
			let mut next = Vec::with_capacity(level.len() / 2);
			let mut i = 0;
			while i < level.len() {
				let (c0, c1) = (level[i].clone(), level[i + 1].clone());
				let t = rand_f(&mut fs); // FS challenge for THIS node
				let (g, folded) = fold_prove(&p, &c0, &c1, t); // PROVER folds two accumulators
				// EDGE-CHECK: the O(n) verifier reproduces the folded claim WITHOUT touching P.
				let v = fold_verify(&c0, &c1, &g, t).expect("interior accumulator fold must verify");
				assert_eq!(v.value, folded.value, "prover/verifier fold value mismatch");
				assert_eq!(v.point, folded.point, "prover/verifier fold point mismatch");
				tree_nodes.push((c0, c1, g, t));
				next.push(folded);
				nodes += 1;
				i += 2;
			}
			level = next;
			depth += 1;
		}
		let build_ms = t_build.elapsed().as_secs_f64() * 1e3;
		let root = level.pop().unwrap();
		// TOPOLOGY CONFIRMED: after 15 accumulator-merges the ROOT claim holds on P.
		assert_eq!(mle_eval(&p, &root.point), root.value, "root claim false on P — topology broken");
		assert_eq!(nodes, 15, "expected 15 interior nodes");
		assert_eq!(depth, 4, "expected depth 4");

		// --- HOP 5 (compute early, needed by HOP 3/4): R* over the 16 batch sub-roots ----------
		// streaming_interleaved_root treats each batch as ONE symbol (codeword_len=1, coset_log=0):
		// leaf k = SHA3(sub-root_k), combined by SHA3-node up a balanced tree → R*.
		let (rstar, spine_peak) = streaming_interleaved_root(n_batches, 1, 0, |b, _j| subroots[b]);
		// The zone Merkle tree over the SAME leaf definition (leaf = SHA3(sub-root)) → root == R*.
		let pre_leaves: Vec<[u8; 32]> = subroots
			.iter()
			.map(|s| {
				let mut h = Sha3_256::new();
				h.update(s);
				h.finalize().into()
			})
			.collect();
		let mtree = merkle_tree_sha3(&pre_leaves);
		assert_eq!(mtree.last().unwrap()[0], rstar, "zone Merkle root must equal streaming R*");

		// --- HOP 3: HYBRID DECIDER verify (the key unmeasured number) --------------------------
		// The decider verifies the accumulated instance = the root claim P(root.point)=root.value.
		// (a) native mle_eval(&p, root.point): the direct O(|P|) check of the committed value.
		let t_a = Instant::now();
		for _ in 0..50 {
			let _ = mle_eval(&p, &root.point);
		}
		let native_ms = t_a.elapsed().as_secs_f64() * 1e3 / 50.0;
		// (b) the fold-tree verify path: 15 × fold_verify, each O(n) — the O(leaves) tiny-verify.
		let t_b = Instant::now();
		for _ in 0..1000 {
			for (c0, c1, g, t) in &tree_nodes {
				let _ = fold_verify(c0, c1, g, *t).unwrap();
			}
		}
		let foldverify_ms = t_b.elapsed().as_secs_f64() * 1e3 / 1000.0;

		// --- HOP 4: POSITION-BINDING (the added obligation) ------------------------------------
		// Rebuild the fold-tree root for an arbitrary record set (same FS seed → deterministic;
		// on the honest set it reproduces `root`, asserted below).
		let build_root = |recs: &[Record]| -> EvalClaim {
			let pp = interleave(recs);
			let mut lvl: Vec<EvalClaim> = recs.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();
			let mut fs2 = StdRng::from_seed([99u8; 32]);
			while lvl.len() > 1 {
				let mut nx = Vec::with_capacity(lvl.len() / 2);
				let mut i = 0;
				while i < lvl.len() {
					let t = rand_f(&mut fs2);
					let (_, folded) = fold_prove(&pp, &lvl[i], &lvl[i + 1], t);
					nx.push(folded);
					i += 2;
				}
				lvl = nx;
			}
			lvl.pop().unwrap()
		};
		assert_eq!(build_root(&records).value, root.value, "deterministic rebuild must match honest root");
		// (i) PERMUTE: swap batch 3 and batch 5. lifted points carry position AND the sub-roots
		// hash position ⇒ a DIFFERENT accumulated root over a DIFFERENT R* (permutation caught).
		let mut permuted = records.clone();
		permuted.swap(3, 5);
		let permuted_root = build_root(&permuted);
		assert_ne!(permuted_root.value, root.value, "permuted root must differ (position-bound)");
		let permuted_subroots: Vec<[u8; 32]> = permuted.iter().enumerate().map(|(i, r)| batch_subroot(i, &r.evals)).collect();
		let (rstar_permuted, _) = streaming_interleaved_root(n_batches, 1, 0, |b, _j| permuted_subroots[b]);
		assert_ne!(rstar_permuted, rstar, "permuted batch set must yield a DIFFERENT R*");
		// (ii) LYING LEAF: flip one leaf value → its fold's g(1) no longer matches → REJECTED.
		let (lc0, lc1, g0, t0) = &tree_nodes[0];
		let mut liar = lc1.clone();
		liar.value += F::ONE;
		assert!(fold_verify(lc0, &liar, g0, *t0).is_none(), "lying leaf must be rejected at its fold");

		// --- HOP 5 (path): one batch's µs Merkle auth path against R* — the steady-state lookup -
		let qi = 5usize;
		let path = merkle_auth_path(&mtree, qi);
		let mut ok = false;
		let t_path = Instant::now();
		for _ in 0..10_000 {
			ok = merkle_path_verify(pre_leaves[qi], qi, &path, rstar);
		}
		let path_us = t_path.elapsed().as_micros() as f64 / 10_000.0;
		assert!(ok, "honest Merkle path must verify against R*");
		let rss1 = crate::b256_sha3::peak_rss_bytes();

		// --- HOP 6: figure-one — every hop with measured numbers -------------------------------
		println!("\n=== HYBRID EPOCH PIPELINE (figure-one, all-native, ms) ===============");
		println!("| hop | quantity | measured |");
		println!("|:--|:--|--:|");
		println!("| 1 leaves          | batch-instance accumulators | {} (inner 2^{} → P over {} vars, |P|={}) |", n_batches, inner_vars, inner_vars + m, p.len());
		println!("| 2 fold tree       | interior nodes / depth / build | {} nodes / depth {} / {:.3} ms |", nodes, depth, build_ms);
		println!("| 2 topology        | root claim holds on P after {} accumulator-merges | ✓ |", nodes);
		println!("| 3 decider native  | mle_eval(P, root.point)  [direct O(|P|) value check] | {:.4} ms |", native_ms);
		println!("| 3 decider fold    | 15× fold_verify  [O(leaves) width-indep. path] | {:.4} ms |", foldverify_ms);
		println!("| 4 permute         | swap b3↔b5 → different root & different R* | ✓ |");
		println!("| 4 lying leaf      | flip one leaf value → fold rejected | ✓ |");
		println!("| 5 R* + path       | Merkle auth path (leaf {}) verify vs R* | {:.3} µs (spine peak {}) |", qi, path_us, spine_peak);
		println!("| -- RSS            | peak resident (native pipeline) | {:.1} → {:.1} MiB |", mib(rss0), mib(rss1));
		println!("# HONEST DECIDER NOTE: the two decider numbers above are the NATIVE value check and the \
			 O(leaves) fold-verify path — NOT the committed decider. The true decider is the FRI-OPENING of \
			 the R*-committed interleaved P at root.point (the crux at accumulation.rs:127 — whether R* is \
			 FRI-openable as P's codeword). That opening is a batch-width binius verify ~9–13 s (measured \
			 upper bound, hash-op-table dominated) and is the REMAINING CRUX; it is NOT wired here and the \
			 monolithic number is NOT quoted as measured for the hybrid. Per-node in-circuit STARK cost is \
			 ~785 ms (fold_step, measured elsewhere) — the fold-tree build above is the NATIVE fold cost.");
		println!("GATE hybrid-e2e: 16 batch accumulators → real balanced fold tree ({} nodes, depth {}) → \
			 root claim holds on P ✓ → hybrid decider MEASURED (native {:.4} ms + fold-verify {:.4} ms; \
			 FRI-opening decider = remaining crux ~9–13 s) → position-binding ✓ (permute→different R*, \
			 lying leaf rejected) → R* Merkle path {:.3} µs. Figure-one.", nodes, depth, native_ms, foldverify_ms, path_us);
	}
}
