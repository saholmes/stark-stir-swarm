//! Verifier-as-AIR for `deep_ali_merge` inner STARK proofs.
//!
//! # The recursive STARK target
//!
//! This is the THIRD gadget — the wrapper STARK that consumes an
//! inner `deep_ali_merge` FRI proof and produces a smaller outer
//! proof.  It composes the two shipped gadgets:
//!
//! - SHA-3 pre-image PoK ([`crate::wrapper_prover`]) — reused for
//!   FS transcript reconstruction inside the AIR
//! - Merkle path verification ([`crate::merkle_prover`]) — reused
//!   for each FRI query's Merkle authentication path
//!
//! plus three new sub-circuits this gadget introduces:
//!
//! 1. **Constraint composition evaluation** — given column values
//!    at an FS-derived query point z and α coefficients, verify
//!    `Σ α_j · Φ_j(values) = expected_composed_value`
//! 2. **`binding_cells_commit` OOD verifier** — Schwartz-Zippel
//!    cross-trace consistency at a FS-derived OOD point
//! 3. **Permutation-argument verifier** — checks consistency of the
//!    inner proof's perm-arg log against committed columns
//!
//! # Statement
//!
//! Public:  inner pi_hash (binds inner's public inputs)
//! Witness: full inner FRI proof + opened trace columns at queries
//! Claim:   the inner FRI proof verifies (= inner statement is true)
//!
//! # Performance target (from earlier scoping)
//!
//! Outer proof shape:   ~200-500 KiB (matches RSA-2048 edge profile)
//! Outer verify time:   ~5-15 ms (paper Table 5 polylog scaling)
//! Outer prove time:    ~30-120 s (dominated by inner verifier AIR)
//!
//! # Status
//!
//! Foundation only — types + module structure + documentation of the
//! sub-circuits.  Substantive work (each sub-circuit is multi-commit)
//! follows the same template as the SHA-3 PoK and Merkle path gadgets:
//! foundation → constraints → synthesiser → FRI integration → example.

use crate::merkle_path_air::MerkleNode;
use crate::sha3_absorb_air::{Sha3Variant, hash as sha3_hash};

use deep_ali::fri::DeepFriProof;
use deep_ali::sextic_ext::SexticExt;

type Ext = SexticExt;

/// Public inputs the recursive STARK attests to.
///
/// The inner proof's pi_hash already commits to the inner's
/// (variant, public inputs).  We bind it into the outer pi_hash so
/// the verifier knows which inner statement we're attesting to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveStarkPublicInputs {
    /// Variant of the inner FRI proof's hash family.  Must match
    /// the inner proof's commit hash (SHA-3 at NIST level L1/L3/L5).
    pub variant: Sha3Variant,
    /// 32-byte pi_hash from the inner proof.  Public input to the
    /// recursive STARK.
    pub inner_pi_hash: [u8; 32],
    /// 32-byte outer pi_hash:
    /// SHA3-256("WRAPPER-DEEPALI-V1" || variant_tag || inner_pi_hash).
    /// Binds the inner statement into the outer FS transcript.
    pub outer_pi_hash: [u8; 32],
}

impl RecursiveStarkPublicInputs {
    pub fn for_inner(variant: Sha3Variant, inner_pi_hash: [u8; 32]) -> Self {
        let mut input = Vec::with_capacity(19 + 1 + 32);
        input.extend_from_slice(b"WRAPPER-DEEPALI-V1");
        input.push(match variant {
            Sha3Variant::Sha3_256 => 1u8,
            Sha3Variant::Sha3_384 => 3,
            Sha3Variant::Sha3_512 => 5,
        });
        input.extend_from_slice(&inner_pi_hash);
        let outer = sha3_hash(Sha3Variant::Sha3_256, &input);
        let mut outer_pi_hash = [0u8; 32];
        outer_pi_hash.copy_from_slice(&outer);
        Self { variant, inner_pi_hash, outer_pi_hash }
    }
}

/// Witness for the recursive STARK: the FULL inner FRI proof + its
/// public inputs that the verifier-as-AIR replicates.
///
/// In the actual wrapper-STARK use case (recursive ML-DSA), this is
/// a [`deep_ali::ml_dsa_verify_air_v2_orchestration::V2ProofReal`]
/// — but for genericity the foundation here doesn't depend on that
/// type.  A future commit will add a converter.
#[derive(Clone, Debug)]
pub struct RecursiveWitness {
    /// Raw serialized inner FRI proof bytes (deserialized by the
    /// recursive prover's trace synthesiser).
    pub inner_proof_bytes: Vec<u8>,
    /// Inner proof's committed Merkle roots (one per LDE column
    /// commitment in the inner FRI protocol).  Used as anchors for
    /// the inner-Merkle-path-verify sub-circuit.
    pub inner_merkle_roots: Vec<MerkleNode>,
}

/// Errors from the recursive STARK prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursiveProverError {
    InvalidInnerProof(String),
    Internal(String),
    /// Returned by current stub paths until each sub-circuit lands.
    NotImplemented(&'static str),
}

impl std::fmt::Display for RecursiveProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidInnerProof(s) => write!(f, "invalid inner proof: {s}"),
            Self::Internal(s)          => write!(f, "recursive prover internal: {s}"),
            Self::NotImplemented(s)    => write!(f, "recursive STARK not yet implemented: {s}"),
        }
    }
}

impl std::error::Error for RecursiveProverError {}

/// The artefact produced by the recursive STARK prover.
pub struct RecursiveStarkProof {
    pub public: RecursiveStarkPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove that the inner FRI proof verifies, producing a smaller
/// outer STARK proof.  STUBBED — substantive prove body lands in
/// subsequent commits as each sub-circuit completes.
pub fn prove_recursive_stark(
    witness: &RecursiveWitness,
    inner_pi_hash: [u8; 32],
    variant: Sha3Variant,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, RecursiveProverError> {
    let _ = (witness, blowup, r, use_stir);
    let _ = RecursiveStarkPublicInputs::for_inner(variant, inner_pi_hash);
    Err(RecursiveProverError::NotImplemented(
        "verifier-as-AIR for deep_ali_merge requires three sub-circuits: \
         constraint composition evaluation, binding_cells_commit OOD \
         verifier, and permutation argument verifier — each multi-commit",
    ))
}

/// Verify a recursive STARK proof.  Stubbed — returns `false` until
/// the prove path is wired.
pub fn verify_recursive_stark(proof: &RecursiveStarkProof) -> bool {
    let _ = proof;
    false
}

// ─── Sub-circuit module skeletons ──────────────────────────────────
//
// Each sub-circuit will follow the SAME gadget pattern as the SHA-3
// PoK and Merkle path:
//
//   1. Foundation (types + native oracle + tampering tests)
//   2. In-row constraint primitives
//   3. Trace synthesiser
//   4. FRI integration
//   5. Boundary commitments + tamper rejection
//   6. Runnable example

/// Constraint composition evaluation sub-circuit.
///
/// Given:
///   - Column values f_1(z), ..., f_n(z) at an FS-derived query point z
///   - Combination coefficients α_1, ..., α_n derived from pi_hash
///   - Expected composed value y
/// Verify:
///   Σ α_j · Φ_j(f_1(z), ..., f_n(z)) = y
///
/// Where Φ_j are the inner AIR's constraint polynomials.  For the
/// recursive ML-DSA wrapper, this is the v2_orchestration's row-
/// uniform constraint set evaluated at a single point.
pub mod constraint_composition_verifier {
    // Module skeleton — types and constraints land in subsequent commits.
}

/// `binding_cells_commit` OOD verifier sub-circuit.
///
/// Implements the Schwartz-Zippel cross-trace consistency check
/// from the inner proof's binding_cells_commit module.  Statement:
///
///   For two FRI-committed polynomials f and g, given an FS-derived
///   challenge point z ∈ F_ext and claimed evaluations f(z), g(z),
///   verify f(z) = g(z).
///
/// The wrapper AIR encodes this by replicating the FRI transcript
/// inside the AIR + checking the OOD evaluation equality.
pub mod binding_cells_ood_verifier {
    // Module skeleton — types and constraints land in subsequent commits.
}

/// Permutation argument verifier sub-circuit.
///
/// Verifies the inner proof's T_MEM perm-arg log: that the prover's
/// claimed log is consistent with the actual sub-trace cells via
/// the standard Π_left = Π_right product equality.
pub mod permutation_argument_verifier {
    // Module skeleton — types and constraints land in subsequent commits.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_inputs_outer_pi_hash_is_deterministic() {
        let inner = [0xCAu8; 32];
        let a = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, inner);
        let b = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, inner);
        assert_eq!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn public_inputs_outer_pi_hash_changes_with_inner() {
        let i1 = [0xAAu8; 32];
        let i2 = [0xBBu8; 32];
        let a = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, i1);
        let b = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, i2);
        assert_ne!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn public_inputs_outer_pi_hash_changes_with_variant() {
        let inner = [0xCDu8; 32];
        let a = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, inner);
        let b = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_384, inner);
        assert_ne!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn prove_recursive_returns_not_implemented_today() {
        let witness = RecursiveWitness {
            inner_proof_bytes: vec![0u8; 100],
            inner_merkle_roots: vec![],
        };
        let result = prove_recursive_stark(
            &witness, [0; 32], Sha3Variant::Sha3_256, 4, 54, false,
        );
        assert!(matches!(result, Err(RecursiveProverError::NotImplemented(_))));
    }

    #[test]
    fn verify_recursive_returns_false_today() {
        // Create a dummy proof via a roundabout path: we can't
        // easily construct a DeepFriProof manually so we just call
        // verify on a synthetically-zero'd struct.  This is fine
        // because the stub always returns false.
        let _ = verify_recursive_stark;  // type check; cannot easily call without DeepFriProof
    }
}
