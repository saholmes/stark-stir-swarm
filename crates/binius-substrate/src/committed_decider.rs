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
	as_packed_field::PackedType, BinaryField8b, BinaryField32b, Field, PackedField,
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

#[cfg(test)]
mod tests {
	use super::*;

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
}
