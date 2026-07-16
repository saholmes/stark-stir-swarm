// decider.rs — the committed-decider evaluation opening as callable (non-test)
// open/verify functions, and the B128↔B256 subfield lift that lets the epoch
// fold (over B128, accumulation.rs) be discharged by the FRI-Binius decider
// (over F1 = B256).  See docs/recursion-fold-epoch-integration.md.
//
// Binary towers nest: B256 = BinaryTowerField256b = (lo, hi) two B128 limbs, so
// B128 embeds via `from_halves(x, B128::ZERO)` — a subfield inclusion that
// preserves +,× and hence the multilinear evaluation.  So the fold's B128
// accumulated claim (P, point, value) is opened/verified by lifting into B256.
//
// The cost curve (verify ~ms, proof ~KiB, polylog in domain) is measured in
// `committed_decider.rs`.

use binius_core::{
    fiat_shamir::HasherChallenger,
    merkle_tree::BinaryMerkleTreeProver,
    piop::{commit, make_commit_params_with_optimal_arity, prove, verify, CommitMeta, PIOPSumcheckClaim},
    polynomial::MultivariatePoly,
    protocols::fri::CommitOutput,
    transcript::{ProverTranscript, VerifierTranscript},
    transparent::eq_ind::EqIndPartialEval,
};
use binius_field::{
    as_packed_field::PackedType, BinaryField128b as B128, BinaryField32b, BinaryField8b, Field,
    PackedField,
};
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_math::{
    DefaultEvaluationDomainFactory, MLEDirectAdapter, MultilinearExtension, MultilinearPoly,
};
use binius_ntt::SingleThreadedNTT;
use sha2::Sha256;

use crate::b256_field::{B256, U256};

// Shared RS/domain sub-fields (valid at L1/L3 over B256).
type FEncode = BinaryField32b;
type FDomain = BinaryField8b;
type F1 = B256;
type P1 = PackedType<U256, F1>;

const SECURITY_BITS_L1: usize = 128;

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

    let evals: Vec<P1> = p_b128.iter().map(|&x| P1::broadcast(lift_b128_to_b256(x))).collect();
    let point: Vec<F1> = point_b128.iter().map(|&x| lift_b128_to_b256(x)).collect();
    let poly = MultilinearExtension::<P1>::new(n_vars, evals).unwrap();
    let committed_multilins = vec![MLEDirectAdapter::from(poly)];

    let commit_meta = CommitMeta::with_vars([n_vars]);
    let merkle_prover = BinaryMerkleTreeProver::<F1, Sha256, _>::new(Sha256Compression::default());
    let merkle_scheme = merkle_prover.scheme();
    let fri_params = make_commit_params_with_optimal_arity::<_, FEncode, _>(
        &commit_meta, merkle_scheme, SECURITY_BITS_L1, 1,
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
/// evaluates to `value` at `point_b128` (lifted).  The resolver's succinct
/// epoch check (no P shipped).
pub fn decider_verify_l1(proof_bytes: Vec<u8>, point_b128: &[B128], value: B256, n_vars: usize) -> bool {
    let point: Vec<F1> = point_b128.iter().map(|&x| lift_b128_to_b256(x)).collect();
    let commit_meta = CommitMeta::with_vars([n_vars]);
    let merkle_prover = BinaryMerkleTreeProver::<F1, Sha256, _>::new(Sha256Compression::default());
    let merkle_scheme = merkle_prover.scheme();
    let fri_params = match make_commit_params_with_optimal_arity::<_, FEncode, _>(
        &commit_meta, merkle_scheme, SECURITY_BITS_L1, 1,
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
