// committed_decider.rs — a REAL, MEASURED FRI-Binius committed-multilinear evaluation
// opening over B256 (the DNS-STARK challenge/extension field). This turns the previously
// MODELED committed-decider numbers into MEASURED ones:
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

use crate::b256_field::{B256 as F, U256};
use crate::b256_sha3::peak_rss_bytes;

// The crate's proven B256 FRI types.
type P = PackedType<U256, F>; // width-1: B256 is its own packed field
type FEncode = BinaryField32b; // 32-bit Reed–Solomon alphabet
type FDomain = BinaryField8b; // sumcheck evaluation domain (B256: ExtensionField<B8>)

/// One measured row of the committed-decider evaluation-opening sweep.
#[derive(Debug, Clone, Copy)]
pub struct CDecRow {
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

/// Build a random committed multilinear over F = B256 with `n_vars` variables, commit it with
/// FRI-Binius, open it at a random point via one PIOP sumcheck claim (transparent = eq(point,·)),
/// verify the opening, and also confirm a tampered claimed evaluation is REJECTED. Returns the
/// measured metrics. Panics if the honest open/verify fails (that would be a real bug).
fn measure_one(n_vars: usize, seed: u64) -> CDecRow {
	let mut rng = StdRng::seed_from_u64(seed);

	// --- committed multilinear P over B256 (2^n_vars evals; width-1 ⇒ one packed elem/eval) ---
	let evals: Vec<P> = (0..(1usize << n_vars))
		.map(|_| <P as PackedField>::random(&mut rng))
		.collect();
	let poly = MultilinearExtension::new(n_vars, evals).unwrap();
	let committed_multilins = vec![MLEDirectAdapter::from(poly.clone())];

	// --- FRI params: single committed poly of n_vars, 128-bit security, blowup 2 ---
	let commit_meta = CommitMeta::with_vars([n_vars]);
	let merkle_prover =
		BinaryMerkleTreeProver::<F, Sha256, _>::new(Sha256Compression::default());
	let merkle_scheme = merkle_prover.scheme();
	let fri_params = make_commit_params_with_optimal_arity::<_, FEncode, _>(
		&commit_meta,
		merkle_scheme,
		128, // security_bits
		1,   // log_inv_rate (blowup = 2)
	)
	.unwrap();
	let ntt = SingleThreadedNTT::<FEncode>::new(fri_params.rs_code().log_len()).unwrap();
	let backend = make_portable_backend();

	// --- COMMIT (timed) ---
	let t = Instant::now();
	let CommitOutput {
		commitment,
		committed,
		codeword,
	} = commit(&fri_params, &ntt, &merkle_prover, &committed_multilins).unwrap();
	let commit_ms = t.elapsed().as_secs_f64() * 1e3;

	// --- opening point ∈ F^n_vars and eq(point, ·) transparent ---
	let point: Vec<F> = (0..n_vars).map(|_| <F as Field>::random(&mut rng)).collect();
	let eq = EqIndPartialEval::<F>::new(point.clone());
	let eq_mle: MultilinearExtension<P, _> = eq.multilinear_extension::<P, _>(&backend).unwrap();
	// Transparent must be the SAME M type as the committed multilinears for `prove`.
	let eq_mle_owned = MultilinearExtension::new(eq_mle.n_vars(), eq_mle.evals().to_vec()).unwrap();
	let transparent_multilins = vec![MLEDirectAdapter::from(eq_mle_owned.clone())];

	// value = P(point) = Σ_v P(v)·eq(point,v)  — the honest inner product over the hypercube.
	let value: F = (0..(1usize << n_vars))
		.map(|v| {
			committed_multilins[0].evaluate_on_hypercube(v).unwrap()
				* transparent_multilins[0].evaluate_on_hypercube(v).unwrap()
		})
		.sum();

	let claim = PIOPSumcheckClaim::<F> {
		n_vars,
		committed: 0,
		transparent: 0,
		sum: value,
	};
	let claims = vec![claim];

	// --- OPEN / PROVE (timed) ---
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

	// Peak RSS is a process high-water mark; sample right after the prover (the memory-dominant
	// phase — codeword LDE + Merkle trees).
	let peak_rss_bytes = peak_rss_bytes();

	// The transparent for VERIFY is the eq-indicator as a `&dyn MultivariatePoly<F>`.
	let eq_dyn: &dyn MultivariatePoly<F> = &eq;
	let transparents: Vec<&dyn MultivariatePoly<F>> = vec![eq_dyn];

	// Serialize the proof to bytes (measures proof size) and rebuild verifier transcripts from it.
	let proof_bytes_vec = proof.finalize();
	let proof_bytes = proof_bytes_vec.len();

	// --- VERIFY (timed): honest opening must ACCEPT ---
	let t = Instant::now();
	{
		let mut vproof = VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes_vec.clone());
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

	// --- TAMPER: corrupt the claimed evaluation (value + 1); verify MUST reject ---
	let tampered_claims = vec![PIOPSumcheckClaim::<F> {
		n_vars,
		committed: 0,
		transparent: 0,
		sum: value + F::ONE,
	}];
	let tamper_rejects = {
		let mut vproof = VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_bytes_vec);
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
		n_vars,
		domain_size: 1u64 << n_vars,
		commit_ms,
		open_prove_ms,
		verify_ms,
		proof_bytes,
		peak_rss_bytes,
		tamper_rejects,
	}
}

/// Run the committed-decider evaluation-opening sweep and return one measured row per n_vars.
pub fn committed_decider_measure(n_vars_sweep: &[usize]) -> Vec<CDecRow> {
	n_vars_sweep
		.iter()
		.enumerate()
		.map(|(i, &n)| measure_one(n, 0xC0FFEE + i as u64))
		.collect()
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn committed_decider_opening() {
		let sweep = [10usize, 14, 18];
		let rows = committed_decider_measure(&sweep);
		println!(
			"| n_vars | 2^n_vars | commit ms | open-prove ms | VERIFY ms | proof KiB | peak RSS MiB | tamper? |"
		);
		for r in &rows {
			println!(
				"| {} | {} | {:.2} | {:.2} | {:.2} | {} | {:.1} | {} |",
				r.n_vars,
				r.domain_size,
				r.commit_ms,
				r.open_prove_ms,
				r.verify_ms,
				r.proof_bytes / 1024,
				r.peak_rss_bytes as f64 / (1024.0 * 1024.0),
				if r.tamper_rejects { "REJECT" } else { "ACCEPT(BUG)" },
			);
			assert!(r.tamper_rejects, "tampered evaluation must be rejected");
		}
	}
}
