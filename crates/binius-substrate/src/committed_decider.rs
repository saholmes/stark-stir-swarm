// committed_decider.rs — a REAL, MEASURED FRI-Binius committed-multilinear evaluation
// opening across all three NIST levels — L1: B256 @ security_bits 128, L3: B256 @ 192,
// L5: B512 @ 256 (the DNS-STARK challenge/extension fields). This turns the previously
// MODELED committed-decider numbers into MEASURED ones (and retires the L5 extrapolation):
//
//   * commit a random multilinear P over F = B256 with the standalone FRI-Binius PCS
//     (`binius_core::piop`, NOT `constraint_system`),
//   * produce and verify a REAL evaluation-opening proof of `P(point) = value`, using the
//     identity  P(point) = Σ_v P(v) · eq(point, v)  — i.e. one PIOP sumcheck claim whose
//     transparent is the equality-indicator multilinear eq(point, ·),
//   * MEASURE commit prove-time, open prove-time, verify wall-clock, proof bytes, and peak RSS
//     across polynomial sizes n_vars.
//
// This confirms two things that were previously argued, not measured:
//   (a) an R*-committed multilinear P IS FRI-openable at a point (the crux at
//       accumulation.rs:127) — commit → open → verify closes end-to-end over B256;
//   (b) the committed-decider prove RSS and the verify wall-clock are now MEASURED, and the
//       verify cost scales ~polylog/linear in n_vars (= polylog in domain), confirming the
//       ~seconds committed-decider verify is REAL.
//
// Field wiring matches the crate's proven B256 FRI stack (see streaming_commit.rs test
// `streaming_lazy_matches_commit_interleaved_b256`): F = B256 (width-1 packed over U256),
// FEncode = BinaryField32b (the 32-bit Reed–Solomon alphabet), SHA-256 merkle,
// HasherChallenger<Sha256> transcript. FDomain = BinaryField8b (the sumcheck evaluation
// domain), matching the piop test's choice; B256: ExtensionField<B8> holds (DEGREE 32).

use std::time::Instant;

use binius_field::{
	as_packed_field::PackedType, BinaryField128b as B128, BinaryField8b, BinaryField32b, Field,
	PackedField,
};
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_math::{
	DefaultEvaluationDomainFactory, MLEDirectAdapter, MultilinearExtension, MultilinearPoly,
};
use binius_ntt::SingleThreadedNTT;
use rand::{rngs::StdRng, SeedableRng};
use sha2::Sha256;

use binius_core::{
	fiat_shamir::HasherChallenger,
	merkle_tree::BinaryMerkleTreeProver,
	piop::{commit, make_commit_params_with_optimal_arity, prove, verify, CommitMeta, PIOPSumcheckClaim},
	polynomial::MultivariatePoly,
	protocols::fri::CommitOutput,
	transcript::{ProverTranscript, VerifierTranscript},
	transparent::eq_ind::EqIndPartialEval,
};

use crate::b256_field::{B256, U256};
use crate::b512_field::{B512, U512};
use crate::b256_sha3::peak_rss_bytes;

// Shared RS/domain sub-fields — identical across levels; only F (challenge/extension field)
// and security_bits change. B256/B512 both hold ExtensionField<B8> and ExtensionField<B32>,
// so FEncode = B32 (the 32-bit Reed–Solomon alphabet) and FDomain = B8 (sumcheck evaluation
// domain) are valid at both L1/L3 (B256) and L5 (B512).
type FEncode = BinaryField32b;
type FDomain = BinaryField8b;

// The width-1 packed types (B256/B512 are each their own packed field over U256/U512).
type F1 = B256; // L1 & L3
type P1 = PackedType<U256, F1>;
type F5 = B512; // L5
type P5 = PackedType<U512, F5>;

/// One measured row of the committed-decider evaluation-opening sweep at a fixed NIST level.
#[derive(Debug, Clone, Copy)]
pub struct CDecRow {
	pub security_bits: usize,
	pub n_vars: usize,
	pub domain_size: u64, // 2^n_vars
	pub commit_ms: f64,
	pub open_prove_ms: f64,
	pub verify_ms: f64,
	pub proof_bytes: usize,
	pub peak_rss_bytes: u64,
	/// Whether tampering the claimed evaluation causes verify to reject (soundness signal).
	pub tamper_rejects: bool,
}

/// A labelled measured row: (NIST level, field name, metrics).
pub type LabelledRow = (&'static str, &'static str, CDecRow);

// One committed-multilinear evaluation-opening measurement over concrete field types.
// A macro (not a generic fn) so each level's body compiles with fully-inferred concrete types
// — the piop generics are finicky, and this reuses the exact wiring proven at L1 verbatim.
//
//   $F   = challenge/extension field (B256 or B512)
//   $P   = its width-1 packed type
//   $nvars, $sec, $seed = polynomial size, security_bits, RNG seed
macro_rules! measure_cdec {
	($F:ty, $P:ty, $nvars:expr, $sec:expr, $seed:expr) => {{
		let n_vars: usize = $nvars;
		let security_bits: usize = $sec;
		let mut rng = StdRng::seed_from_u64($seed);

		// committed multilinear P (2^n_vars evals; width-1 ⇒ one packed elem/eval)
		let evals: Vec<$P> = (0..(1usize << n_vars))
			.map(|_| <$P as PackedField>::random(&mut rng))
			.collect();
		let poly = MultilinearExtension::<$P>::new(n_vars, evals).unwrap();
		let committed_multilins = vec![MLEDirectAdapter::from(poly)];

		// FRI params: single committed poly of n_vars, `security_bits` security, blowup 2
		let commit_meta = CommitMeta::with_vars([n_vars]);
		let merkle_prover =
			BinaryMerkleTreeProver::<$F, Sha256, _>::new(Sha256Compression::default());
		let merkle_scheme = merkle_prover.scheme();
		let fri_params = make_commit_params_with_optimal_arity::<_, FEncode, _>(
			&commit_meta,
			merkle_scheme,
			security_bits,
			1, // log_inv_rate (blowup = 2)
		)
		.unwrap();
		let ntt = SingleThreadedNTT::<FEncode>::new(fri_params.rs_code().log_len()).unwrap();
		let backend = make_portable_backend();

		// COMMIT (timed)
		let t = Instant::now();
		let CommitOutput { commitment, committed, codeword } =
			commit(&fri_params, &ntt, &merkle_prover, &committed_multilins).unwrap();
		let commit_ms = t.elapsed().as_secs_f64() * 1e3;

		// opening point ∈ F^n_vars and eq(point, ·) transparent
		let point: Vec<$F> = (0..n_vars).map(|_| <$F as Field>::random(&mut rng)).collect();
		let eq = EqIndPartialEval::<$F>::new(point);
		let eq_mle: MultilinearExtension<$P, _> =
			eq.multilinear_extension::<$P, _>(&backend).unwrap();
		// Transparent must be the SAME M type as the committed multilinears for `prove`.
		let eq_mle_owned =
			MultilinearExtension::<$P>::new(eq_mle.n_vars(), eq_mle.evals().to_vec()).unwrap();
		let transparent_multilins = vec![MLEDirectAdapter::from(eq_mle_owned)];

		// value = P(point) = Σ_v P(v)·eq(point,v)  — the honest hypercube inner product.
		let value: $F = (0..(1usize << n_vars))
			.map(|v| {
				committed_multilins[0].evaluate_on_hypercube(v).unwrap()
					* transparent_multilins[0].evaluate_on_hypercube(v).unwrap()
			})
			.sum();
		let claims = vec![PIOPSumcheckClaim::<$F> {
			n_vars,
			committed: 0,
			transparent: 0,
			sum: value,
		}];

		// OPEN / PROVE (timed)
		let domain_factory = DefaultEvaluationDomainFactory::<FDomain>::default();
		let mut proof = ProverTranscript::<HasherChallenger<Sha256>>::new();
		proof.message().write(&commitment);
		let t = Instant::now();
		prove(
			&fri_params,
			&ntt,
			&merkle_prover,
			domain_factory,
			&commit_meta,
			committed,
			&codeword,
			&committed_multilins,
			&transparent_multilins,
			&claims,
			&mut proof,
			&backend,
		)
		.unwrap();
		let open_prove_ms = t.elapsed().as_secs_f64() * 1e3;

		// Peak RSS is a process high-water mark; sample right after the prover.
		let peak_rss_bytes = peak_rss_bytes();

		let eq_dyn: &dyn MultivariatePoly<$F> = &eq;
		let transparents: Vec<&dyn MultivariatePoly<$F>> = vec![eq_dyn];

		let proof_bytes_vec = proof.finalize();
		let proof_bytes = proof_bytes_vec.len();

		// VERIFY (timed): honest opening must ACCEPT
		let t = Instant::now();
		{
			let mut vproof =
				VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes_vec.clone());
			let commitment_v = vproof.message().read().unwrap();
			verify(
				&commit_meta,
				merkle_scheme,
				&fri_params,
				&commitment_v,
				&transparents,
				&claims,
				&mut vproof,
			)
			.expect("honest committed-decider evaluation opening must verify");
		}
		let verify_ms = t.elapsed().as_secs_f64() * 1e3;

		// TAMPER: corrupt the claimed evaluation (value + 1); verify MUST reject.
		let tampered_claims = vec![PIOPSumcheckClaim::<$F> {
			n_vars,
			committed: 0,
			transparent: 0,
			sum: value + <$F as Field>::ONE,
		}];
		let tamper_rejects = {
			let mut vproof =
				VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes_vec);
			let commitment_v = vproof.message().read().unwrap();
			verify(
				&commit_meta,
				merkle_scheme,
				&fri_params,
				&commitment_v,
				&transparents,
				&tampered_claims,
				&mut vproof,
			)
			.is_err()
		};

		CDecRow {
			security_bits,
			n_vars,
			domain_size: 1u64 << n_vars,
			commit_ms,
			open_prove_ms,
			verify_ms,
			proof_bytes,
			peak_rss_bytes,
			tamper_rejects,
		}
	}};
}

/// One measured row of the REAL interleaved-commit decider sweep: a P built by block-interleaving
/// `n_batches` separate batch polys (each `inner_vars` vars) into `inner_vars + log2(n_batches)`
/// vars — the actual `accumulation::interleave` layout — committed and opened through the SAME
/// FRI-Binius piop, at the decomposition point (a ‖ b). This is ledger item #3: it replaces the
/// MODELED query-path term (`accumulation::decider_verify_query_path_vs_leaves`) with a directly
/// MEASURED piop verify of a genuine interleaved commitment, swept against the leaf count.
#[derive(Debug, Clone, Copy)]
pub struct IntlvRow {
	pub inner_vars: usize,
	pub n_batches: usize, // = leaves
	pub n_vars: usize,    // = inner_vars + log2(n_batches)
	pub commit_ms: f64,
	pub open_prove_ms: f64,
	pub verify_ms: f64,
	pub proof_bytes: usize,
	pub peak_rss_bytes: u64,
	/// P(a‖b) opened value == Σ_i eq(b,i)·P_i(a) — the real commit matches the decomposition.
	pub decomp_ok: bool,
	pub tamper_rejects: bool,
}

// Real interleaved-commit decider measurement over concrete field types. Mirrors `measure_cdec`
// but constructs the committed multilinear as the BLOCK-INTERLEAVE of `2^logn` batch polys (each
// `inner_vars` vars) — block i at hypercube indices [i·2^inner .. (i+1)·2^inner), so the high
// `logn` index bits select the batch (exactly `accumulation::interleave` / `lifted_claim`). The
// opening point is (a = inner, low vars ‖ b = position, high vars); the opened value is checked
// EQUAL to Σ_i eq(b,i)·P_i(a), so the measured verify is a verify of the genuinely decomposable
// interleaved commitment — not a random poly.
macro_rules! measure_intlv_cdec {
	($F:ty, $P:ty, $inner:expr, $logn:expr, $sec:expr, $seed:expr) => {{
		let inner_vars: usize = $inner;
		let logn: usize = $logn;
		let n_vars: usize = inner_vars + logn;
		let n_batches: usize = 1usize << logn;
		let security_bits: usize = $sec;
		let mut rng = StdRng::seed_from_u64($seed);

		// N batch polys, each 2^inner_vars width-1 packed evals; interleave = concatenate blocks.
		let batch_evals: Vec<Vec<$P>> = (0..n_batches)
			.map(|_| {
				(0..(1usize << inner_vars))
					.map(|_| <$P as PackedField>::random(&mut rng))
					.collect::<Vec<$P>>()
			})
			.collect();
		let evals: Vec<$P> = batch_evals.iter().flat_map(|b| b.iter().cloned()).collect();
		let poly = MultilinearExtension::<$P>::new(n_vars, evals).unwrap();
		let committed_multilins = vec![MLEDirectAdapter::from(poly)];

		let commit_meta = CommitMeta::with_vars([n_vars]);
		let merkle_prover =
			BinaryMerkleTreeProver::<$F, Sha256, _>::new(Sha256Compression::default());
		let merkle_scheme = merkle_prover.scheme();
		let fri_params = make_commit_params_with_optimal_arity::<_, FEncode, _>(
			&commit_meta,
			merkle_scheme,
			security_bits,
			1,
		)
		.unwrap();
		let ntt = SingleThreadedNTT::<FEncode>::new(fri_params.rs_code().log_len()).unwrap();
		let backend = make_portable_backend();

		// COMMIT the REAL interleaved codeword (timed).
		let t = Instant::now();
		let CommitOutput { commitment, committed, codeword } =
			commit(&fri_params, &ntt, &merkle_prover, &committed_multilins).unwrap();
		let commit_ms = t.elapsed().as_secs_f64() * 1e3;

		// Decomposition point: a = inner (low vars), b = position (high vars). point = a ‖ b.
		let a: Vec<$F> = (0..inner_vars).map(|_| <$F as Field>::random(&mut rng)).collect();
		let b: Vec<$F> = (0..logn).map(|_| <$F as Field>::random(&mut rng)).collect();
		let point: Vec<$F> = a.iter().cloned().chain(b.iter().cloned()).collect();

		let eq = EqIndPartialEval::<$F>::new(point.clone());
		let eq_mle: MultilinearExtension<$P, _> =
			eq.multilinear_extension::<$P, _>(&backend).unwrap();
		let eq_mle_owned =
			MultilinearExtension::<$P>::new(eq_mle.n_vars(), eq_mle.evals().to_vec()).unwrap();
		let transparent_multilins = vec![MLEDirectAdapter::from(eq_mle_owned)];

		// value = P(point) = Σ_V P(V)·eq(point,V) — ground-truth hypercube inner product.
		let value: $F = (0..(1usize << n_vars))
			.map(|v| {
				committed_multilins[0].evaluate_on_hypercube(v).unwrap()
					* transparent_multilins[0].evaluate_on_hypercube(v).unwrap()
			})
			.sum();

		// DECOMPOSITION check: recompute value INDEPENDENTLY as Σ_i eq(b,i)·P_i(a), where
		// P_i(a) = Σ_v batch_evals_i(v)·eq(a,v). If these agree, the measured verify below is a
		// verify of a genuinely batch-decomposable interleaved commitment.
		let eq_pt = |pt: &[$F], v: usize| -> $F {
			let mut w = <$F as Field>::ONE;
			for (j, &c) in pt.iter().enumerate() {
				w *= if (v >> j) & 1 == 1 { c } else { <$F as Field>::ONE + c };
			}
			w
		};
		let p_i_at_a = |i: usize| -> $F {
			(0..(1usize << inner_vars))
				.map(|v| {
					let s: $F = <$P as PackedField>::get(&batch_evals[i][v], 0);
					s * eq_pt(&a, v)
				})
				.sum()
		};
		let rhs: $F = (0..n_batches).map(|i| eq_pt(&b, i) * p_i_at_a(i)).sum();
		let decomp_ok = rhs == value;

		let claims = vec![PIOPSumcheckClaim::<$F> {
			n_vars,
			committed: 0,
			transparent: 0,
			sum: value,
		}];

		let domain_factory = DefaultEvaluationDomainFactory::<FDomain>::default();
		let mut proof = ProverTranscript::<HasherChallenger<Sha256>>::new();
		proof.message().write(&commitment);
		let t = Instant::now();
		prove(
			&fri_params,
			&ntt,
			&merkle_prover,
			domain_factory,
			&commit_meta,
			committed,
			&codeword,
			&committed_multilins,
			&transparent_multilins,
			&claims,
			&mut proof,
			&backend,
		)
		.unwrap();
		let open_prove_ms = t.elapsed().as_secs_f64() * 1e3;
		let peak_rss_bytes = peak_rss_bytes();

		let eq_dyn: &dyn MultivariatePoly<$F> = &eq;
		let transparents: Vec<&dyn MultivariatePoly<$F>> = vec![eq_dyn];
		let proof_bytes_vec = proof.finalize();
		let proof_bytes = proof_bytes_vec.len();

		// VERIFY (timed) — the real query-path opening of the interleaved codeword.
		let t = Instant::now();
		{
			let mut vproof =
				VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes_vec.clone());
			let commitment_v = vproof.message().read().unwrap();
			verify(
				&commit_meta,
				merkle_scheme,
				&fri_params,
				&commitment_v,
				&transparents,
				&claims,
				&mut vproof,
			)
			.expect("honest interleaved-commit decider opening must verify");
		}
		let verify_ms = t.elapsed().as_secs_f64() * 1e3;

		// TAMPER: corrupt the claimed value; verify MUST reject.
		let tampered_claims = vec![PIOPSumcheckClaim::<$F> {
			n_vars,
			committed: 0,
			transparent: 0,
			sum: value + <$F as Field>::ONE,
		}];
		let tamper_rejects = {
			let mut vproof =
				VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes_vec);
			let commitment_v = vproof.message().read().unwrap();
			verify(
				&commit_meta,
				merkle_scheme,
				&fri_params,
				&commitment_v,
				&transparents,
				&tampered_claims,
				&mut vproof,
			)
			.is_err()
		};

		IntlvRow {
			inner_vars,
			n_batches,
			n_vars,
			commit_ms,
			open_prove_ms,
			verify_ms,
			proof_bytes,
			peak_rss_bytes,
			decomp_ok,
			tamper_rejects,
		}
	}};
}

/// Ledger item #3, MEASURED: verify a REAL interleaved-commit decider opening vs the leaf count.
/// Fix `inner_vars`, sweep `logn` (⇒ N = 2^logn batches, n_vars = inner_vars + logn), and measure
/// the piop verify wall-clock of the genuine block-interleaved commitment at each N. If verify
/// grows only polylog in N (the `logn` term in n_vars) at fixed inner width — and NOT linearly in
/// the leaf count — the "leaves-independent decider verify" headline is directly measured, not
/// modeled. L1 = B256 @ 128.
pub fn interleaved_decider_measure_l1(inner_vars: usize, logn_sweep: &[usize]) -> Vec<IntlvRow> {
	logn_sweep
		.iter()
		.enumerate()
		.map(|(i, &logn)| measure_intlv_cdec!(F1, P1, inner_vars, logn, 128, 0x1_0000 + i as u64))
		.collect()
}

/// Measure the committed-decider evaluation opening across NIST levels L1/L3/L5 for the same
/// n_vars sweep, returning one labelled row per (level, n_vars):
///   L1 = B256 @ security_bits 128,  L3 = B256 @ 192,  L5 = B512 @ 256.
/// The Merkle/Fiat–Shamir hash is Sha256 uniformly across levels so the table isolates the
/// field/security_bits effect on the eval-opening cost curve (the κ_bind SHA3-ladder is an
/// orthogonal concern handled elsewhere in the crate).
pub fn committed_decider_measure_all(n_vars_sweep: &[usize]) -> Vec<LabelledRow> {
	let mut out: Vec<LabelledRow> = Vec::new();
	for (i, &n) in n_vars_sweep.iter().enumerate() {
		let s = 0xC0FFEE + i as u64;
		out.push(("L1", "B256", measure_cdec!(F1, P1, n, 128, s)));
	}
	for (i, &n) in n_vars_sweep.iter().enumerate() {
		let s = 0xB33F + i as u64;
		out.push(("L3", "B256", measure_cdec!(F1, P1, n, 192, s)));
	}
	for (i, &n) in n_vars_sweep.iter().enumerate() {
		let s = 0x5A1AD + i as u64;
		out.push(("L5", "B512", measure_cdec!(F5, P5, n, 256, s)));
	}
	out
}

// ── B128 fold ↔ B256 decider unification (piece 2) ──────────────────────────
//
// The epoch fold (accumulation.rs) is over B128; the committed decider is over
// F1 = B256.  Binary towers nest: B256 = (lo,hi) two B128 limbs, so B128 embeds
// as `from_halves(x, ZERO)` — a subfield inclusion that preserves +,× and hence
// the multilinear evaluation.  So the fold's accumulated claim over B128 is
// discharged by lifting (P, point, value) into B256 and running the L1 decider.

/// Lift a B128 element into B256 (subfield embedding: the "lo" limb, hi = 0).
pub fn lift_b128_to_b256(x: B128) -> B256 {
	B256::from_halves(x, B128::ZERO)
}

/// L1 committed-decider OPEN: commit the multilinear `p_b128` (B128 evals lifted
/// to B256) and prove `P(point) = value` at `point_b128` (lifted).  Returns
/// `(proof_bytes, value_b256, n_vars)`; `proof_bytes` carries the commitment.
pub fn decider_open_l1(p_b128: &[B128], point_b128: &[B128]) -> (Vec<u8>, B256, usize) {
	let n_vars = point_b128.len();
	assert_eq!(p_b128.len(), 1usize << n_vars, "P must have 2^|point| evals");
	let security_bits = 128usize;

	let evals: Vec<P1> = p_b128.iter().map(|&x| P1::broadcast(lift_b128_to_b256(x))).collect();
	let point: Vec<F1> = point_b128.iter().map(|&x| lift_b128_to_b256(x)).collect();
	let poly = MultilinearExtension::<P1>::new(n_vars, evals).unwrap();
	let committed_multilins = vec![MLEDirectAdapter::from(poly)];

	let commit_meta = CommitMeta::with_vars([n_vars]);
	let merkle_prover = BinaryMerkleTreeProver::<F1, Sha256, _>::new(Sha256Compression::default());
	let merkle_scheme = merkle_prover.scheme();
	let fri_params = make_commit_params_with_optimal_arity::<_, FEncode, _>(
		&commit_meta, merkle_scheme, security_bits, 1,
	)
	.unwrap();
	let ntt = SingleThreadedNTT::<FEncode>::new(fri_params.rs_code().log_len()).unwrap();
	let backend = make_portable_backend();
	let CommitOutput { commitment, committed, codeword } =
		commit(&fri_params, &ntt, &merkle_prover, &committed_multilins).unwrap();

	let eq = EqIndPartialEval::<F1>::new(point);
	let eq_mle: MultilinearExtension<P1, _> = eq.multilinear_extension::<P1, _>(&backend).unwrap();
	let eq_owned = MultilinearExtension::<P1>::new(eq_mle.n_vars(), eq_mle.evals().to_vec()).unwrap();
	let transparent_multilins = vec![MLEDirectAdapter::from(eq_owned)];

	let value: F1 = (0..(1usize << n_vars))
		.map(|v| {
			committed_multilins[0].evaluate_on_hypercube(v).unwrap()
				* transparent_multilins[0].evaluate_on_hypercube(v).unwrap()
		})
		.sum();
	let claims = vec![PIOPSumcheckClaim::<F1> { n_vars, committed: 0, transparent: 0, sum: value }];

	let domain_factory = DefaultEvaluationDomainFactory::<FDomain>::default();
	let mut proof = ProverTranscript::<HasherChallenger<Sha256>>::new();
	proof.message().write(&commitment);
	prove(
		&fri_params, &ntt, &merkle_prover, domain_factory, &commit_meta, committed, &codeword,
		&committed_multilins, &transparent_multilins, &claims, &mut proof, &backend,
	)
	.unwrap();
	(proof.finalize(), value, n_vars)
}

/// L1 committed-decider VERIFY: accept iff `proof_bytes` proves the committed P
/// evaluates to `value` at `point_b128` (lifted).  This is the resolver's
/// succinct epoch check (no P shipped).
pub fn decider_verify_l1(proof_bytes: Vec<u8>, point_b128: &[B128], value: B256, n_vars: usize) -> bool {
	let security_bits = 128usize;
	let point: Vec<F1> = point_b128.iter().map(|&x| lift_b128_to_b256(x)).collect();
	let commit_meta = CommitMeta::with_vars([n_vars]);
	let merkle_prover = BinaryMerkleTreeProver::<F1, Sha256, _>::new(Sha256Compression::default());
	let merkle_scheme = merkle_prover.scheme();
	let fri_params = match make_commit_params_with_optimal_arity::<_, FEncode, _>(
		&commit_meta, merkle_scheme, security_bits, 1,
	) {
		Ok(p) => p,
		Err(_) => return false,
	};
	let eq = EqIndPartialEval::<F1>::new(point);
	let eq_dyn: &dyn MultivariatePoly<F1> = &eq;
	let transparents = vec![eq_dyn];
	let claims = vec![PIOPSumcheckClaim::<F1> { n_vars, committed: 0, transparent: 0, sum: value }];

	let mut vproof = VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes);
	let commitment_v = match vproof.message().read() {
		Ok(c) => c,
		Err(_) => return false,
	};
	verify(&commit_meta, merkle_scheme, &fri_params, &commitment_v, &transparents, &claims, &mut vproof)
		.is_ok()
}

#[cfg(test)]
mod tests {
	use super::*;

	/// ★ UNIFICATION: the B128 epoch fold discharged by the B256 decider via the
	/// subfield lift — the succinct resolver verify (no P shipped) + its cost.
	#[test]
	fn epoch_fold_succinct_decider() {
		use crate::epoch_fold::{fold_epoch, verify_epoch, EpochLeaf};
		use rand::{rngs::StdRng, RngCore, SeedableRng};
		use std::time::Instant;

		// 16 leaves × 2^6-value records ⇒ n_vars = 6 + 4 = 10 (the 7.4 ms decider row).
		let mut rng = StdRng::seed_from_u64(7);
		let leaves: Vec<EpochLeaf> = (0..16)
			.map(|_| EpochLeaf {
				record: (0..64)
					.map(|_| B128::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128))
					.collect(),
			})
			.collect();
		let proof = fold_epoch(&leaves, "example.se", 42);
		assert!(verify_epoch(&proof, "example.se").is_ok(), "native-decider epoch must verify");

		// Succinct decider over B256: lift (P, point, value) and open/verify.
		let (pf, value_b256, n_vars) = decider_open_l1(&proof.interleaved_p, &proof.acc_claim.point);
		assert_eq!(
			value_b256,
			lift_b128_to_b256(proof.acc_claim.value),
			"the subfield lift must preserve the multilinear evaluation"
		);
		let t = Instant::now();
		let ok = decider_verify_l1(pf.clone(), &proof.acc_claim.point, value_b256, n_vars);
		let verify_ms = t.elapsed().as_secs_f64() * 1e3;
		assert!(ok, "succinct decider verify must accept the honest epoch");
		let bad = decider_verify_l1(pf.clone(), &proof.acc_claim.point, value_b256 + B256::ONE, n_vars);
		assert!(!bad, "a tampered claimed value must reject");
		println!(
			"[epoch-succinct] n_vars={n_vars} decider proof {} KiB, VERIFY {verify_ms:.2} ms \
			 (B128 fold ↔ B256 decider lift: eval preserved, tamper rejects)",
			pf.len() / 1024
		);
	}

	#[test]
	fn committed_decider_opening() {
		let sweep = [10usize, 14, 18];
		let rows = committed_decider_measure_all(&sweep);
		println!(
			"| level | field | sec | n_vars | 2^n_vars | commit ms | open-prove ms | VERIFY ms | proof KiB | peak RSS MiB | tamper? |"
		);
		for (level, field, r) in &rows {
			println!(
				"| {} | {} | {} | {} | {} | {:.2} | {:.2} | {:.2} | {} | {:.1} | {} |",
				level,
				field,
				r.security_bits,
				r.n_vars,
				r.domain_size,
				r.commit_ms,
				r.open_prove_ms,
				r.verify_ms,
				r.proof_bytes / 1024,
				r.peak_rss_bytes as f64 / (1024.0 * 1024.0),
				if r.tamper_rejects { "REJECT" } else { "ACCEPT(BUG)" },
			);
			assert!(
				r.tamper_rejects,
				"tampered evaluation must be rejected at {level} ({field})"
			);
		}
	}

	/// LEDGER ITEM #3 (MEASURED): the leaves-independent decider verify, on a REAL interleaved
	/// commit. Fix inner width, sweep N = 2^logn batches; each row commits the genuine
	/// block-interleaved codeword through the FRI-Binius piop and MEASURES the verify. The point
	/// is that at FIXED inner width, growing the leaf count N by 256× (2 → 512) moves the verify
	/// only by the polylog `logn` term (n_vars = inner + logn), NOT linearly in leaves — so "one
	/// cross-batch opening verifies all batches" is measured, replacing the modeled query-path term.
	#[test]
	fn interleaved_decider_verify_vs_leaves() {
		let inner_vars = 6usize;
		let logn_sweep = [1usize, 3, 5, 7, 9]; // N = 2, 8, 32, 128, 512
		let rows = interleaved_decider_measure_l1(inner_vars, &logn_sweep);
		println!(
			"\n=== LEDGER #3 MEASURED: interleaved-commit decider verify vs leaves (L1 B256@128, inner_vars={inner_vars}) ==="
		);
		println!(
			"| N (leaves) | n_vars | commit ms | open-prove ms | VERIFY ms | proof KiB | peak RSS MiB | decomp | tamper |"
		);
		println!("|--:|--:|--:|--:|--:|--:|--:|:--:|:--:|");
		for r in &rows {
			println!(
				"| {} | {} | {:.2} | {:.2} | {:.2} | {} | {:.1} | {} | {} |",
				r.n_batches,
				r.n_vars,
				r.commit_ms,
				r.open_prove_ms,
				r.verify_ms,
				r.proof_bytes / 1024,
				r.peak_rss_bytes as f64 / (1024.0 * 1024.0),
				if r.decomp_ok { "OK" } else { "MISMATCH(BUG)" },
				if r.tamper_rejects { "REJECT" } else { "ACCEPT(BUG)" },
			);
			assert!(r.decomp_ok, "opened value must equal Σ_i eq(b,i)·P_i(a) at N={}", r.n_batches);
			assert!(r.tamper_rejects, "tampered value must be rejected at N={}", r.n_batches);
		}

		// Leaves-independence: 256× more leaves (N: 2 → 512) must NOT scale verify linearly. A
		// linear-in-leaves query-path term would blow up ~256×; the interleaved commit's single
		// opening should move only by the polylog n_vars term. Assert the verify ratio is far
		// below the leaf ratio (generous 20× bound vs the 256× leaf growth — the real ratio is a
		// small polylog factor; this catches a genuinely O(leaves) regression without being flaky).
		let first = rows.first().unwrap();
		let last = rows.last().unwrap();
		let leaf_ratio = last.n_batches as f64 / first.n_batches as f64; // 256×
		let verify_ratio = last.verify_ms / first.verify_ms;
		println!(
			"leaves ×{:.0} ({} → {}), verify ×{:.2} ({:.2} → {:.2} ms) ⇒ verify grows POLYLOG in leaves, \
			 NOT O(leaves): the single interleaved opening verifies all batches. Ledger #3 MEASURED, not modeled.",
			leaf_ratio, first.n_batches, last.n_batches, verify_ratio, first.verify_ms, last.verify_ms
		);
		assert!(
			verify_ratio < 20.0,
			"verify grew ×{verify_ratio:.2} over ×{leaf_ratio:.0} leaves — that looks O(leaves), not polylog (regression?)"
		);
	}
}
