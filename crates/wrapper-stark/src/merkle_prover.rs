//! Paper-grade Merkle path STARK prover — wires the composed Merkle +
//! sponge_air constraint set through `deep_ali::fri::deep_fri_prove`
//! to produce a `DeepFriProof<SexticExt>` attesting that the prover
//! knows a leaf + authentication path that hashes to the public root.
//!
//! # Status
//!
//! Types + signatures + structural tests for the prover scaffold.
//! The substantive `prove_merkle_path` body lands in the next commit
//! — it composes three constraint families into the FRI input's
//! c_eval polynomial:
//!
//! 1. **Selection constraints** (in-row, degree 2): `merkle_hop_
//!    selection_constraints` fired at hop rows only
//! 2. **Sponge sub-AIR constraints** (in-row, degree ≤ 3): the row-
//!    uniform sponge constraints fired at sponge sub-rows
//! 3. **Cross-row bindings** (degree 1 Copy): `merkle_cross_row_
//!    constraints` fired at the specific row pairs they reference
//!
//! Each family needs FS-derived α coefficients (separate seeds derived
//! from pi_hash) so the verifier can reproduce them.  All three sum
//! into one c_eval that `deep_fri_prove` consumes.

use deep_ali::fri::DeepFriProof;
use deep_ali::sextic_ext::SexticExt;

use crate::merkle_path_air::{MerkleNode, MerklePathClaim};
use crate::sha3_absorb_air::{Sha3Variant, hash as sha3_hash};

type Ext = SexticExt;

/// Public inputs the Merkle path STARK attests to.  Statement:
/// > *I know a leaf L and authentication path π such that hashing L
/// > up the tree using π by the bits of `leaf_index` yields `root`.*
///
/// The leaf and path are private witness — only `(variant, root,
/// leaf_index)` is public.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePathPublicInputs {
    pub variant: Sha3Variant,
    pub root: MerkleNode,
    pub leaf_index: u64,
    /// 32-byte pi_hash:
    /// SHA3-256("WRAPPER-MERKLE-V1" || variant_tag || root || leaf_index_le).
    /// Binds the public statement into the FS transcript.
    pub pi_hash: [u8; 32],
}

impl MerklePathPublicInputs {
    pub fn for_root(variant: Sha3Variant, root: MerkleNode, leaf_index: u64) -> Self {
        assert_eq!(root.0.len(), variant.output_bytes(),
            "root length must match variant.output_bytes()");
        let mut input = Vec::with_capacity(17 + 1 + root.0.len() + 8);
        input.extend_from_slice(b"WRAPPER-MERKLE-V1");
        input.push(match variant {
            Sha3Variant::Sha3_256 => 1u8,
            Sha3Variant::Sha3_384 => 3,
            Sha3Variant::Sha3_512 => 5,
        });
        input.extend_from_slice(&root.0);
        input.extend_from_slice(&leaf_index.to_le_bytes());
        let pi = sha3_hash(Sha3Variant::Sha3_256, &input);
        let mut pi_hash = [0u8; 32];
        pi_hash.copy_from_slice(&pi);
        Self { variant, root, leaf_index, pi_hash }
    }
}

/// Errors from the Merkle path STARK prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MerklePathProverError {
    InvalidClaim(String),
    Internal(String),
    /// Body not yet wired — types ship in this commit; FRI integration
    /// lands in the next.
    NotImplemented(&'static str),
}

impl std::fmt::Display for MerklePathProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidClaim(s) => write!(f, "invalid Merkle claim: {s}"),
            Self::Internal(s) => write!(f, "merkle prover internal: {s}"),
            Self::NotImplemented(s) => write!(f, "merkle prover not yet implemented: {s}"),
        }
    }
}

impl std::error::Error for MerklePathProverError {}

/// The artefact returned by `prove_merkle_path`.  Pair with
/// `MerklePathPublicInputs` for verification.
pub struct MerklePathProof {
    pub public: MerklePathPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub depth: usize,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove that the prover knows a leaf + authentication path matching
/// the public (root, leaf_index).  **Stubbed**: returns NotImplemented
/// until the c_eval composition body lands.
///
/// # Arguments
///
/// - `claim`: includes the witness leaf + path + the expected root
/// - `blowup`: FRI blowup (production 32; smoke 4)
/// - `r`: FRI query count (paper Table 2: 54/79/105 for L1/L3/L5)
/// - `use_stir`: STIR (true) vs DEEP-FRI (false)
pub fn prove_merkle_path(
    claim: &MerklePathClaim,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<MerklePathProof, MerklePathProverError> {
    claim.check_shape().map_err(MerklePathProverError::InvalidClaim)?;
    let _ = (blowup, r, use_stir);
    Err(MerklePathProverError::NotImplemented(
        "c_eval composition for selection + sponge + cross-row constraint families pending",
    ))
}

/// Verify a Merkle path STARK proof.  Stubbed — returns `false` until
/// the prove path is wired.
pub fn verify_merkle_path(proof: &MerklePathProof) -> bool {
    let _ = proof;
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle_path_air::{merkle_build_and_open};

    fn fake_leaf(variant: Sha3Variant, byte: u8) -> MerkleNode {
        MerkleNode(vec![byte; variant.output_bytes()])
    }

    #[test]
    fn public_inputs_pi_hash_is_deterministic() {
        let root = fake_leaf(Sha3Variant::Sha3_256, 0xAB);
        let a = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, root.clone(), 5);
        let b = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, root, 5);
        assert_eq!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn public_inputs_pi_hash_changes_with_root() {
        let r1 = fake_leaf(Sha3Variant::Sha3_256, 0xAB);
        let r2 = fake_leaf(Sha3Variant::Sha3_256, 0xCD);
        let a = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, r1, 5);
        let b = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, r2, 5);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn public_inputs_pi_hash_changes_with_index() {
        let root = fake_leaf(Sha3Variant::Sha3_256, 0xAB);
        let a = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, root.clone(), 5);
        let b = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, root, 6);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn public_inputs_pi_hash_changes_with_variant() {
        let r1 = fake_leaf(Sha3Variant::Sha3_256, 0xAB);
        let r2 = fake_leaf(Sha3Variant::Sha3_384, 0xAB);
        let a = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_256, r1, 0);
        let b = MerklePathPublicInputs::for_root(Sha3Variant::Sha3_384, r2, 0);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn prove_returns_not_implemented_today() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0x10 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 2);
        let result = prove_merkle_path(&claim, 4, 54, false);
        assert!(matches!(result, Err(MerklePathProverError::NotImplemented(_))));
    }

    #[test]
    fn prove_rejects_malformed_claim() {
        let variant = Sha3Variant::Sha3_256;
        // Claim with mismatched root length.
        let bad_claim = MerklePathClaim {
            variant,
            root: MerkleNode(vec![0; 5]),  // wrong length
            leaf_index: 0,
            leaf: fake_leaf(variant, 0xFF),
            path: vec![],
        };
        let result = prove_merkle_path(&bad_claim, 4, 54, false);
        assert!(matches!(result, Err(MerklePathProverError::InvalidClaim(_))));
    }
}
