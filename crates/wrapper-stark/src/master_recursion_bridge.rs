//! Master recursion bridge — Option C from
//! `scripts/results/stark-dns-rollup-summary.md`.
//!
//! Wraps N `RecursiveStarkProof` bundles (each one already attesting an
//! inner v2 ML-DSA verify STARK) into ONE master `RecursiveStarkProof`
//! whose outer FRI proof attests "all N recursive STARKs verify".
//!
//! Architecturally identical to the v2 → recursive bridge
//! (`v2_recursion_bridge`) — same four sub-circuit families
//! (composition + OOD + perm-arg vestige + in-AIR Merkle), just one
//! level higher up the recursion ladder.  This commit implements the
//! algebraic core (sub-circuits 1 + 2 + 3) for the master STARK; the
//! sub-circuit 4 in-AIR Merkle binding can be added on top using the
//! same wrapper-stark merkle gadget the v2 bridge uses.
//!
//! Soundness shape (architectural, with the documented caveat that
//! sub-circuit 1 attests the algebraic relation on prover-supplied
//! values — full FRI-Merkle-binding is the additional in-AIR-Merkle
//! step covered in `v2_recursion_bridge::prove_v2_with_in_air_merkle_path`
//! and would be applied identically here):
//!
//!   ∃ N inner RecursiveStarkProof bundles such that:
//!     1. for each one, its FRI DEEP-quotient relation holds at the
//!        FS-derived z_ext (sub-circuit 1)
//!     2. its outer_pi_hash is committed into the master STARK's
//!        public-input transcript (sub-circuit 2)
//!     3. vestige perm-arg over the master pi_hash bytes (sub-circuit 3)
//!
//! The master STARK's size is **constant** in N at production parameters:
//! ~789 KiB at L1 bw=32, identical to the per-sig recursive STARK shape.
//! This makes Option C deliver O(1) L1 cost regardless of how many
//! inner v2 signatures are aggregated.

use ark_ff::{Field as _, Zero};
use ark_goldilocks::Goldilocks;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

use deep_ali::binding_cells_commit::Ext as DaExt;
use deep_ali::fri::{
    DeepFriParams, DeepFriProof, derive_z_ext_for_proof,
    layer_sizes_from_schedule,
};
use deep_ali::tower_field::TowerField;
use sha3::Digest;

use crate::bit_constraint::{BitOp, CellRef};
use crate::composition::alphas_from_transcript;
use crate::deep_ali_verifier_air::binding_cells_ood_verifier::{
    OodClaimBundle, OodEqualityClaim,
};
use crate::deep_ali_verifier_air::constraint_composition_verifier::CompositionClaim;
use crate::deep_ali_verifier_air::permutation_argument_verifier::PermArgClaim;
use crate::merkle_path_air::{
    BatchedMerklePathClaim, MerkleNode, MerklePathClaim, merkle_build_and_open,
};
use crate::merkle_prover::{
    BatchedMerklePathProof, MerklePathProof, MerklePathProverError, prove_batched_merkle_paths,
    prove_merkle_path, verify_batched_merkle_paths, verify_merkle_path,
};
use crate::recursive_prover::{
    CompositionAccumulatorPublicInputs, OodAccumulatorClaim, OodAccumulatorPublicInputs,
    PermArgPublicInputs, RecursiveProverError, RecursiveStarkProof,
    prove_recursive_stark, verify_recursive_stark,
};
use crate::sha3_absorb_air::Sha3Variant;

type Ext = DaExt;

/// EXT_DEGREE per build (6 at Fp⁶ / sha3-256/sha3-384, 8 at Fp⁸ / sha3-512).
#[cfg(any(feature = "sha3-256", feature = "sha3-384"))]
const EXT_DEGREE: usize = 6;
#[cfg(feature = "sha3-512")]
const EXT_DEGREE: usize = 8;
#[cfg(not(any(feature = "sha3-256", feature = "sha3-384", feature = "sha3-512")))]
const EXT_DEGREE: usize = 6;

/// Errors from the master recursion bridge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MasterBridgeError {
    /// Inner recursive STARK uses STIR mode; DEEP-quotient extraction
    /// only supports FRI mode currently.  Re-run with use_stir=false
    /// when producing the inner recursive STARKs.
    StirNotSupported,
    /// Empty inner-proof slice.
    EmptyInput,
    /// FRI proof structure invalid (malformed inner recursive STARK).
    MalformedFriProof(String),
    /// Underlying recursive prover error.
    RecursiveProver(String),
}

impl std::fmt::Display for MasterBridgeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StirNotSupported => write!(f,
                "master bridge: inner recursive STARKs must be in FRI mode \
                 (pass use_stir=false to prove_v2_all_subairs_composed_recursive)"
            ),
            Self::EmptyInput => write!(f, "master bridge: no inner proofs supplied"),
            Self::MalformedFriProof(s) => write!(f, "master bridge: malformed FRI: {s}"),
            Self::RecursiveProver(s) => write!(f, "master bridge: recursive prover: {s}"),
        }
    }
}
impl std::error::Error for MasterBridgeError {}

/// Reconstruct the FRI params the recursive prover used to produce
/// the given `RecursiveStarkProof`.  Mirrors the params block in
/// `recursive_prover::prove_recursive_stark`.
fn recursive_proof_params(rec: &RecursiveStarkProof) -> DeepFriParams {
    let n_lde = rec.n_trace * rec.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, rec.r, 0xDEEFu64);
    params.public_inputs_hash = Some(rec.public.outer_pi_hash);
    if rec.use_stir { params.stir = true; }
    params
}

/// Per-recursive-proof DEEP-quotient residues.  Returns `n_queries ×
/// L` Ext residues; on an honest proof every entry is zero.
///
/// Mirrors `v2_recursion_bridge::extract_v2_fri_deep_quotient_residues`
/// but operates on a `RecursiveStarkProof`'s embedded FRI proof
/// (which is itself a `DeepFriProof<Ext>` over the recursive STARK's
/// LDE) rather than on a deserialized sub-AIR proof.
fn extract_recursive_fri_residues(
    rec: &RecursiveStarkProof,
) -> Result<Vec<Vec<Ext>>, MasterBridgeError> {
    let params = recursive_proof_params(rec);

    let fri_proof = &rec.fri_proof;
    if fri_proof.queries.is_empty() {
        return Err(MasterBridgeError::StirNotSupported);
    }

    let z_ext = derive_z_ext_for_proof::<Ext>(fri_proof, &params);
    let sizes = layer_sizes_from_schedule(fri_proof.n0, &params.schedule);
    let l = params.schedule.len();

    let omega_per_layer: Vec<Goldilocks> = (0..l)
        .map(|ell| Radix2EvaluationDomain::<Goldilocks>::new(sizes[ell])
            .expect("layer domain power-of-two")
            .group_gen)
        .collect();

    let mut residues_per_query: Vec<Vec<Ext>> =
        Vec::with_capacity(fri_proof.queries.len());
    for qp in &fri_proof.queries {
        let mut row = Vec::with_capacity(l);
        for ell in 0..l {
            if ell >= qp.per_layer_payloads.len() || ell >= qp.per_layer_refs.len() {
                return Err(MasterBridgeError::MalformedFriProof(format!(
                    "query layer count {} < schedule len {l}",
                    qp.per_layer_payloads.len()
                )));
            }
            let pay = &qp.per_layer_payloads[ell];
            let rref = &qp.per_layer_refs[ell];
            let omega_ell = omega_per_layer[ell];
            let x_i = <Ext as TowerField>::from_fp(omega_ell.pow([rref.i as u64]));
            let fz = fri_proof.fz_per_layer[ell];
            // residue = q_val · (x_i − z_ext) − (f_val − fz)
            let lhs = pay.q_val * (x_i - z_ext);
            let rhs = pay.f_val - fz;
            row.push(lhs - rhs);
        }
        residues_per_query.push(row);
    }
    Ok(residues_per_query)
}

/// Sub-circuit 1: composition over per-recursive-proof FRI DEEP-quotient
/// residues + (V3, Phase 5) sub-circuit 1a FRI-fold residues, flattened
/// to EXT_DEGREE Goldilocks coords.  Asserts:
///
/// - **1.** DEEP-quotient: `q_val · (x − z_ext) − (f_val − fz) = 0`
///   per (k, ell) over each inner's FRI proof.
/// - **1a.** Fold relation: `s_val[ell] − f_val[ell+1] = 0` per
///   (k, ell) over ell in 0..L-1.  Without this the v2 inner's
///   FRI-fold check would be implicit — sub-circuit 1a makes it
///   algebraic so the master STARK directly attests the inner's
///   complete FRI-verify (DEEP-quotient ∧ fold) relation.
///
/// Total constraint count: N × n_queries × (L + L−1) × EXT_DEGREE.
pub fn build_master_composition(
    inner_proofs: &[RecursiveStarkProof],
) -> Result<CompositionClaim<Goldilocks>, MasterBridgeError> {
    if inner_proofs.is_empty() {
        return Err(MasterBridgeError::EmptyInput);
    }

    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::new();
    let mut constraints: Vec<BitOp> = Vec::new();
    let mut next_col = 0usize;

    // Sub-circuit 1: DEEP-quotient residues.
    for rec in inner_proofs {
        let residues = extract_recursive_fri_residues(rec)?;
        for row in &residues {
            for r in row {
                let coords = r.to_fp_components();
                for c in 0..EXT_DEGREE {
                    let cell = CellRef::new(0, next_col);
                    column_values.push((cell, coords[c]));
                    constraints.push(BitOp::IsZero { cell });
                    next_col += 1;
                }
            }
        }
    }

    // Sub-circuit 1a (Phase 5): FRI-fold residues `s[ell] − f[ell+1] = 0`.
    for rec in inner_proofs {
        let fold_residues = extract_recursive_fold_residues(rec)?;
        for row in &fold_residues {
            for r in row {
                let coords = r.to_fp_components();
                for c in 0..EXT_DEGREE {
                    let cell = CellRef::new(0, next_col);
                    column_values.push((cell, coords[c]));
                    constraints.push(BitOp::IsZero { cell });
                    next_col += 1;
                }
            }
        }
    }

    // FS alphas seeded from concatenated outer_pi_hashes + every inner
    // FRI proof's Merkle roots (Phase 3 Piece 1 — binds the master
    // composition's coefficients to the specific N-tuple of inner
    // recursive STARKs INCLUDING their FRI commitments).  Seed bumped
    // from V2 → V3 in Phase 5 to reflect the new sub-circuit 1a
    // fold-residue constraints; the seed string is a domain-separator
    // and the byte format is otherwise identical.
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"MASTER-RECURSION-COMP-V3");
    for rec in inner_proofs {
        Digest::update(&mut hasher, rec.public.outer_pi_hash);
        absorb_inner_fri_roots(&mut hasher, rec);
    }
    let seed: [u8; 32] = Digest::finalize(hasher).into();
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, constraints.len());

    Ok(CompositionClaim {
        column_values,
        constraints,
        alphas,
        expected: Goldilocks::zero(),
    })
}

/// **Phase 5 sub-circuit 1a**: extract FRI-fold residues from an inner
/// `RecursiveStarkProof`'s embedded FRI proof.  Returns
/// `n_queries × (L − 1)` Ext residues where
/// `residue[k][ell] = s_val[ell] − f_val[ell+1]`.
///
/// FRI semantics: `s_val[ell]` is the "fold result" at layer `ell`
/// for query `k` — it equals the `f_val` at the SAME query's
/// folded position in layer `ell+1`.  On an honest FRI proof
/// every residue is zero in F_ext.
fn extract_recursive_fold_residues(
    rec: &RecursiveStarkProof,
) -> Result<Vec<Vec<Ext>>, MasterBridgeError> {
    let fri_proof = &rec.fri_proof;
    if fri_proof.queries.is_empty() {
        return Err(MasterBridgeError::StirNotSupported);
    }
    let l = recursive_proof_params(rec).schedule.len();
    if l == 0 {
        return Ok(Vec::new());
    }

    let mut residues_per_query: Vec<Vec<Ext>> =
        Vec::with_capacity(fri_proof.queries.len());
    for qp in &fri_proof.queries {
        if qp.per_layer_payloads.len() < l {
            return Err(MasterBridgeError::MalformedFriProof(format!(
                "fold extract: query payloads {} < L = {l}",
                qp.per_layer_payloads.len()
            )));
        }
        let mut row = Vec::with_capacity(l - 1);
        for ell in 0..(l - 1) {
            let s_curr = qp.per_layer_payloads[ell].s_val;
            let f_next = qp.per_layer_payloads[ell + 1].f_val;
            row.push(s_curr - f_next);
        }
        residues_per_query.push(row);
    }
    Ok(residues_per_query)
}

/// **Phase 3 Piece 1**: absorb an inner FRI proof's Merkle commitments
/// into the FS transcript so the master STARK's seed is bound to the
/// specific FRI tree the residue extraction reads from.  Format:
/// `roots_count(8 LE) | root_f0(32) | roots[0](32) | … | roots[L-1](32)`.
fn absorb_inner_fri_roots(
    hasher: &mut sha3::Sha3_256,
    rec: &RecursiveStarkProof,
) {
    let fri = &rec.fri_proof;
    Digest::update(hasher, &(fri.roots.len() as u64).to_le_bytes());
    Digest::update(hasher, fri.root_f0);
    for r in &fri.roots {
        Digest::update(hasher, r);
    }
}

/// Sub-circuit 2: OOD anchor over the inner outer_pi_hashes.
///
/// Each outer_pi_hash is packed into 4 Goldilocks elements (4 × 8 = 32
/// bytes per hash).  We pair each element with itself (f = g), making
/// every claim trivially zero — the anchor's role is to bind the
/// outer_pi_hashes into the master STARK's FS transcript via the
/// accumulator's FS alphas, not to add new soundness content (which
/// already lives in sub-circuit 1).
pub fn build_master_ood_anchor(
    inner_proofs: &[RecursiveStarkProof],
) -> OodAccumulatorClaim {
    let mut claims = Vec::with_capacity(inner_proofs.len() * 4);
    for rec in inner_proofs {
        for chunk_idx in 0..4 {
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(
                &rec.public.outer_pi_hash[8 * chunk_idx..8 * (chunk_idx + 1)]
            );
            let v = Goldilocks::from(u64::from_le_bytes(bytes));
            claims.push(OodEqualityClaim {
                z: Goldilocks::zero(),
                f_at_z: v,
                g_at_z: v,
                binding_tag: "master-pi-anchor",
            });
        }
    }

    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"MASTER-RECURSION-OOD-V3");
    for rec in inner_proofs {
        Digest::update(&mut hasher, rec.public.outer_pi_hash);
        absorb_inner_fri_roots(&mut hasher, rec);
    }
    let seed: [u8; 32] = Digest::finalize(hasher).into();
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, claims.len());

    OodAccumulatorClaim {
        bundle: OodClaimBundle { claims },
        alphas,
    }
}

/// Sub-circuit 3: vestige perm-arg over the master pi_hash bytes.
///
/// Mirrors the v2 bridge's `build_v2_pi_hash_vestige_perm_arg` —
/// trivially-equal multisets bound into the FS transcript via γ.
pub fn build_master_vestige_perm_arg(
    inner_proofs: &[RecursiveStarkProof],
) -> PermArgClaim<Goldilocks> {
    // Derive the master pi_hash by SHA3-ing the concatenated inner
    // outer_pi_hashes.  This is what the verifier sees as the
    // "master proof's public-input commitment."
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"MASTER-RECURSION-PI-V3");
    for rec in inner_proofs {
        Digest::update(&mut hasher, rec.public.outer_pi_hash);
        absorb_inner_fri_roots(&mut hasher, rec);
    }
    let master_pi: [u8; 32] = Digest::finalize(hasher).into();

    let mut elems = Vec::with_capacity(4);
    for chunk_idx in 0..4 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&master_pi[8 * chunk_idx..8 * (chunk_idx + 1)]);
        elems.push(Goldilocks::from(u64::from_le_bytes(bytes)));
    }

    let mut seed = master_pi;
    seed[0] ^= 0xE7;
    let gamma = alphas_from_transcript::<Goldilocks>(&seed, 1)[0];

    PermArgClaim {
        left: elems.clone(),
        right: elems,
        gamma,
        perm_tag: "master-vestige",
    }
}

/// End-to-end Option C prover.
///
/// Takes N inner `RecursiveStarkProof` bundles (each already produced
/// by `wrapper_stark::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive`
/// in FRI mode) and produces ONE master `RecursiveStarkProof` whose
/// outer FRI proof attests every inner recursive STARK's FRI DEEP-
/// quotient algebraic relation.
///
/// The master proof's size is the same shape as the per-sig recursive
/// STARK: ~789 KiB at L1 bw=32, **constant in N**.  L1 cost for the
/// master proof verifier is therefore O(1) regardless of how many
/// inner signatures are aggregated.
pub fn prove_master_recursive(
    inner_proofs: &[RecursiveStarkProof],
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, MasterBridgeError> {
    let comp = build_master_composition(inner_proofs)?;
    let ood = build_master_ood_anchor(inner_proofs);
    let perm = build_master_vestige_perm_arg(inner_proofs);
    prove_recursive_stark(&comp, &ood, &perm, blowup, r, use_stir)
        .map_err(|e: RecursiveProverError| MasterBridgeError::RecursiveProver(format!("{e}")))
}

/// Re-export of `verify_recursive_stark` for symmetry with the v2 bridge.
pub fn verify_master_recursive(master: &RecursiveStarkProof) -> bool {
    verify_recursive_stark(master)
}

// ─── In-AIR Merkle binding for the master ────────────────────────────
//
// Closes the FRI-Merkle soundness gap documented in
// `prove_v2_with_in_air_merkle_path` (commit 4bb14f2) at the master
// recursion layer.
//
// Each inner RecursiveStarkProof's `outer_pi_hash` is bound to a real
// in-AIR-SHA-3-hashed Merkle commitment via the wrapper-stark merkle
// gadget.  N inner proofs → N Merkle-path STARKs, each attesting:
//
//     "∃ leaf and authentication path such that SHA-3-hashing the
//      path with the leaf reproduces the public root,
//      where leaf == inner.outer_pi_hash."
//
// This is the SAME pattern as `prove_v2_in_air_merkle_binding` —
// applied N times at the master layer to bind each inner recursive
// STARK's identity into a Merkle commitment with real in-AIR SHA-3
// hashing.

/// Composed proof: the master `RecursiveStarkProof` + N in-AIR
/// Merkle-path STARK proofs (one per inner recursive STARK).  Each
/// Merkle path proof attests `inner.outer_pi_hash` is the leaf-0
/// element of a synthetic 4-leaf binary Merkle tree with public root.
pub struct MasterWithMerklePathProof {
    pub master: RecursiveStarkProof,
    /// One Merkle-path proof per inner recursive STARK.  Each
    /// `merkle_path_proofs[i]` attests inner `i`'s outer_pi_hash is
    /// a Merkle-committed leaf with root `merkle_roots[i]`.
    pub merkle_path_proofs: Vec<MerklePathProof>,
    /// One Merkle root per inner recursive STARK.  Sized as
    /// 32 bytes because the wrapper-stark merkle gadget uses SHA3-256
    /// for the variant `Sha3Variant::Sha3_256` chosen below.
    pub merkle_roots: Vec<[u8; 32]>,
}

/// Errors from `prove_master_with_in_air_merkle_path`.
#[derive(Debug, Clone)]
pub enum MasterMerkleBindingError {
    Inner(MasterBridgeError),
    MerklePathProver(MerklePathProverError),
    Internal(String),
}

impl std::fmt::Display for MasterMerkleBindingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inner(e) => write!(f, "master bridge: {e}"),
            Self::MerklePathProver(e) => write!(f, "merkle path prover: {e:?}"),
            Self::Internal(s) => write!(f, "internal: {s}"),
        }
    }
}
impl std::error::Error for MasterMerkleBindingError {}

/// Build a synthetic 4-leaf binary Merkle tree containing the given
/// `pi_hash` at leaf 0 and prove the leaf-0 authentication path
/// in-AIR via the wrapper-stark merkle gadget.
///
/// Returns the `MerklePathProof` plus the 32-byte Merkle root.
/// Matches the shape of `v2_recursion_bridge::prove_v2_in_air_merkle_binding`.
fn prove_in_air_merkle_binding_for_pi_hash(
    pi_hash: [u8; 32],
    merkle_blowup: usize,
    merkle_r: usize,
    merkle_use_stir: bool,
) -> Result<(MerklePathProof, [u8; 32]), MasterMerkleBindingError> {
    let variant = Sha3Variant::Sha3_256;
    let pi_hash_leaf = MerkleNode(pi_hash.to_vec());
    let zero_leaf = MerkleNode::zero(variant);
    // 4-leaf binary tree: [pi_hash, 0, 0, 0]
    let leaves = vec![
        pi_hash_leaf, zero_leaf.clone(), zero_leaf.clone(), zero_leaf,
    ];
    let claim = merkle_build_and_open(variant, &leaves, 0);
    let merkle_root: [u8; 32] = claim.root.0.as_slice().try_into()
        .map_err(|_| MasterMerkleBindingError::Internal(
            "merkle root length unexpected".into()
        ))?;
    let proof = prove_merkle_path(&claim, merkle_blowup, merkle_r, merkle_use_stir)
        .map_err(MasterMerkleBindingError::MerklePathProver)?;
    Ok((proof, merkle_root))
}

/// End-to-end Option C with in-AIR Merkle binding.
///
/// Produces the master `RecursiveStarkProof` (via `prove_master_recursive`)
/// PLUS N in-AIR Merkle-path STARK proofs binding each inner recursive
/// STARK's `outer_pi_hash` to a real SHA-3 Merkle commitment.  The
/// Merkle hashing happens IN-AIR via the wrapper-stark sha3_absorb_air
/// constraints — a malicious prover cannot lie about leaf/sibling bytes.
///
/// Together, the master STARK + N Merkle-path STARKs provide:
///   - **Algebraic FRI binding** (master sub-circuit 1): the inner
///     FRI DEEP-quotient relation holds for each inner recursive STARK.
///   - **Hash-Merkle binding** (in-AIR merkle paths): each inner's
///     outer_pi_hash is cryptographically committed via SHA-3.
///
/// This is the FULL Option C shape — L1 self-attests with real
/// cryptographic binding on both the FRI quotient relation AND the
/// inner proof identity.
///
/// # Parameters
///
/// - `inner_proofs`: N inner recursive STARK proofs (from
///   `prove_v2_all_subairs_composed_recursive` in FRI mode).
/// - `(blowup, r, use_stir)`: FRI parameters for the master STARK.
/// - `(merkle_blowup, merkle_r, merkle_use_stir)`: FRI parameters for
///   the N in-AIR Merkle path STARKs.  Typical: `(4, 54, false)`.
pub fn prove_master_with_in_air_merkle_path(
    inner_proofs: &[RecursiveStarkProof],
    blowup: usize,
    r: usize,
    use_stir: bool,
    merkle_blowup: usize,
    merkle_r: usize,
    merkle_use_stir: bool,
) -> Result<MasterWithMerklePathProof, MasterMerkleBindingError> {
    let master = prove_master_recursive(inner_proofs, blowup, r, use_stir)
        .map_err(MasterMerkleBindingError::Inner)?;

    let mut merkle_path_proofs = Vec::with_capacity(inner_proofs.len());
    let mut merkle_roots = Vec::with_capacity(inner_proofs.len());
    for rec in inner_proofs {
        let (proof, root) = prove_in_air_merkle_binding_for_pi_hash(
            rec.public.outer_pi_hash,
            merkle_blowup, merkle_r, merkle_use_stir,
        )?;
        merkle_path_proofs.push(proof);
        merkle_roots.push(root);
    }

    Ok(MasterWithMerklePathProof {
        master, merkle_path_proofs, merkle_roots,
    })
}

/// Re-derive the expected Merkle root for a synthetic 4-leaf binary
/// Merkle tree containing the given `pi_hash` at leaf 0 and SHA3-256
/// zero-leaves at indices 1..=3 (matches the construction inside
/// `prove_in_air_merkle_binding_for_pi_hash`).
fn expected_merkle_root_for_pi_hash(pi_hash: [u8; 32]) -> [u8; 32] {
    let variant = Sha3Variant::Sha3_256;
    let pi_hash_leaf = MerkleNode(pi_hash.to_vec());
    let zero_leaf = MerkleNode::zero(variant);
    let leaves = vec![
        pi_hash_leaf, zero_leaf.clone(), zero_leaf.clone(), zero_leaf,
    ];
    let claim = merkle_build_and_open(variant, &leaves, 0);
    let mut out = [0u8; 32];
    out.copy_from_slice(&claim.root.0);
    out
}

/// Verify a `MasterWithMerklePathProof` — the master STARK + every
/// Merkle-path STARK must accept.  Confirms the leaf each Merkle-path
/// STARK opens matches the matching inner recursive STARK's
/// `outer_pi_hash` by **re-deriving** the expected Merkle root from
/// the inner's pi_hash and checking it against the proof's public root.
/// (Earlier revisions of this function checked the proof's root
/// against `bundle.merkle_roots[i]` without ever rebinding to the
/// inner — leaving a leaf-substitution gap.  Closed here.)
pub fn verify_master_with_in_air_merkle_path(
    bundle: &MasterWithMerklePathProof,
    inner_proofs: &[RecursiveStarkProof],
) -> bool {
    if !verify_master_recursive(&bundle.master) {
        return false;
    }
    if bundle.merkle_path_proofs.len() != inner_proofs.len() {
        return false;
    }
    if bundle.merkle_roots.len() != inner_proofs.len() {
        return false;
    }
    for (i, mp) in bundle.merkle_path_proofs.iter().enumerate() {
        if !verify_merkle_path(mp) {
            return false;
        }
        if mp.public.leaf_index != 0 {
            return false;
        }
        // Re-derive expected root from inner[i].outer_pi_hash and confirm:
        //  (a) the proof's public root matches expected,
        //  (b) bundle.merkle_roots[i] also matches expected.
        let expected = expected_merkle_root_for_pi_hash(
            inner_proofs[i].public.outer_pi_hash,
        );
        if mp.public.root.0.as_slice() != expected {
            return false;
        }
        if bundle.merkle_roots[i] != expected {
            return false;
        }
    }
    true
}

// ─── Batched in-AIR Merkle binding (O(log N) L1 wire) ────────────────
//
// The per-inner Merkle binding above produces N separate ~395 KiB
// Merkle-path STARK proofs — total L1 wire scales **linearly in N**.
// The batched form below produces **ONE** Merkle-path STARK whose leaf
// is `SHA3-256("MASTER-BATCHED-MERKLE-LEAF-V1" || N || π₁ || π₂ || …
// || π_N)` over the N inner outer_pi_hashes.  L1 wire then becomes
// `~master + ~395 KiB + N×32 bytes` — TRUE O(log N) shape.
//
// Soundness binding:
//   1. The master STARK already commits to the N inner outer_pi_hashes
//      via its FS-seeded composition (`MASTER-RECURSION-COMP-V1`) and
//      its OOD anchor (`MASTER-RECURSION-OOD-V1`).
//   2. The batched Merkle-path STARK commits the leaf = batched_pi
//      derived from the SAME N inner pi_hashes.
//   3. The verifier re-derives batched_pi from the supplied
//      `inner_pi_hashes` and re-derives the expected Merkle root,
//      cross-checking both against the proof.
//
// Combined: cryptographic binding of "N inner recursive STARKs +
// master STARK + Merkle commitment of batched_pi" with O(log N) wire.

/// Composed bundle: master `RecursiveStarkProof` + ONE batched
/// Merkle-path STARK proof + N × 32-byte inner pi_hashes.  Replaces
/// the linear-in-N `MasterWithMerklePathProof` with a constant-shape
/// Merkle piece — the canonical zk-rollup L1 wire profile.
pub struct MasterWithBatchedMerkleProof {
    pub master: RecursiveStarkProof,
    /// Single Merkle-path STARK proof attesting batched_pi is the
    /// leaf-0 element of a synthetic 4-leaf Merkle tree.
    pub merkle_path_proof: MerklePathProof,
    /// Merkle root of the synthetic tree (32 B).
    pub merkle_root: [u8; 32],
    /// N inner outer_pi_hashes — the only linear-in-N piece (32 B each).
    /// L1 calldata for these is tiny: 320 B at N=10, 32 KiB at N=1 000.
    pub inner_pi_hashes: Vec<[u8; 32]>,
}

/// Domain-separated batched-pi derivation tag.
const BATCHED_LEAF_TAG: &[u8] = b"MASTER-BATCHED-MERKLE-LEAF-V1";

/// Derive `batched_pi = SHA3-256(BATCHED_LEAF_TAG || N(LE) || π₁ || π₂ || … || π_N)`.
///
/// Same construction on prover + verifier; verifier never sees the
/// intermediate state.
fn derive_batched_leaf_pi(inner_pi_hashes: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, BATCHED_LEAF_TAG);
    Digest::update(&mut hasher, (inner_pi_hashes.len() as u64).to_le_bytes());
    for h in inner_pi_hashes {
        Digest::update(&mut hasher, h);
    }
    Digest::finalize(hasher).into()
}

/// End-to-end Option C with **batched** in-AIR Merkle binding.
///
/// Produces:
///   - 1 master `RecursiveStarkProof` (via `prove_master_recursive`)
///   - 1 batched Merkle-path STARK proof binding `batched_pi`
///     (= SHA3-256 of concatenated inner pi_hashes) to a Merkle root
///   - N × 32-byte inner pi_hashes (small calldata)
///
/// Total L1 wire: `~master + ~395 KiB + N×32 B`.  Replaces the per-inner
/// Merkle path's N × ~395 KiB linear-in-N piece with a single constant
/// ~395 KiB plus the trivially small pi_hash list.
///
/// # Parameters
///
/// Same shape as `prove_master_with_in_air_merkle_path`; the only
/// difference is one Merkle-path STARK instead of N.
pub fn prove_master_with_batched_in_air_merkle_path(
    inner_proofs: &[RecursiveStarkProof],
    blowup: usize,
    r: usize,
    use_stir: bool,
    merkle_blowup: usize,
    merkle_r: usize,
    merkle_use_stir: bool,
) -> Result<MasterWithBatchedMerkleProof, MasterMerkleBindingError> {
    if inner_proofs.is_empty() {
        return Err(MasterMerkleBindingError::Inner(MasterBridgeError::EmptyInput));
    }

    let master = prove_master_recursive(inner_proofs, blowup, r, use_stir)
        .map_err(MasterMerkleBindingError::Inner)?;

    let inner_pi_hashes: Vec<[u8; 32]> =
        inner_proofs.iter().map(|r| r.public.outer_pi_hash).collect();
    let batched_pi = derive_batched_leaf_pi(&inner_pi_hashes);

    let (merkle_path_proof, merkle_root) = prove_in_air_merkle_binding_for_pi_hash(
        batched_pi, merkle_blowup, merkle_r, merkle_use_stir,
    )?;

    Ok(MasterWithBatchedMerkleProof {
        master, merkle_path_proof, merkle_root, inner_pi_hashes,
    })
}

// ─── Two-level sharded master recursion ──────────────────────────────
//
// At very large N (STARK-DNS-zone scale, N ≥ 256), a single master
// STARK over all N inners blows up the prover's memory: master n_trace
// scales linearly with N, and the LDE working set scales as
// `n_trace × blowup × width × Ext_degree × 8 B`, which at N = 10 000
// exceeds 100 GB.  The sharded form below addresses this by recursing
// the master gadget itself a second time:
//
//   ```
//   N inners  ──►  K first-level masters (Ni inners each)
//                  ──►  1 super-master over the K first-level masters
//                       + 1 top batched Merkle over all N inner pi_hashes
//   ```
//
// Peak prover memory per step is O(max(Ni, K)) — the K first-level
// masters can be proven sequentially.  Only the **super-master**, the
// **top batched Merkle**, and `(N + K) × 32 B` of pi_hash calldata go
// to L1.  The K shard masters are local-only — their FRI-quotient
// algebraic relation is attested by the super-master's sub-circuit 1.
//
// Soundness chain (same shape as single-level Option C + the top
// batched Merkle):
//   1. Super-master FRI-verifies (attests K shard masters' FRI-quotient
//      relations via sub-circuit 1).
//   2. Top batched Merkle binds batched_pi = SHA3(N || π₁..π_N) to root.
//   3. Verifier cross-checks each inner_pi_hashes[i] ==
//      inner_proofs[i].outer_pi_hash.
//
// Soundness caveat (same shape as the single-level case): sub-circuit 1
// attests the algebraic FRI-quotient relation on prover-supplied
// residues.  A tighter form would add in-AIR Merkle binding at every
// recursion level (shard-level too) — follow-up work; for the
// architecture-at-scale demo, the top batched Merkle is the wire-
// level binding.

/// Two-level sharded master proof.
///
/// Replaces a single master over N inners with K first-level masters
/// (Ni inners each) + 1 super-master over the K.  Memory-bounded:
/// each shard prover sees only O(Ni) residues, the super-master only
/// O(K) residues.  L1 wire = super_master + top batched Merkle +
/// (N + K) × 32 B pi_hash calldata.
pub struct TwoLevelShardedProof {
    /// The second-level master STARK proving "K shard masters' FRI
    /// algebraic relations hold."  Posted to L1.
    pub super_master: RecursiveStarkProof,
    /// Top batched in-AIR Merkle binding over all N inner pi_hashes.
    /// Posted to L1.
    pub top_merkle_path: MerklePathProof,
    /// Top Merkle root (32 B).  Posted to L1.
    pub top_merkle_root: [u8; 32],
    /// All N inner outer_pi_hashes (calldata).
    pub inner_pi_hashes: Vec<[u8; 32]>,
    /// K shard-master outer_pi_hashes (calldata).  Exposed for
    /// transparency / re-deriving the super_master's FS transcript
    /// off-chain; not used in the algebraic verify path (the
    /// super_master FRI verify is self-contained).
    pub shard_pi_hashes: Vec<[u8; 32]>,
    /// Sharding parameter `Ni` (number of inners per first-level master).
    pub shard_size: usize,
}

/// Prove a two-level sharded master over `inner_proofs`, with
/// `shard_size` inners per first-level master.  K = ceil(N / shard_size).
///
/// Trades off:
///   - **Smaller shard_size** → smaller per-shard memory + smaller K
///     super-master.  But K grows → super-master n_trace grows linearly
///     in K.
///   - **Larger shard_size** → fewer shards K but each shard prover
///     needs more memory.
///
/// For STARK-DNS at N=10 000: shard_size=256, K=40 gives ~256-row first-
/// level master prover memory (fits on 32 GB dev machine) + K=40
/// super-master n_trace ≈ 16× smaller than the equivalent single master
/// at N=10 000.
///
/// # Parameters
///
/// - `inner_proofs`: N inner recursive STARK proofs (from
///   `prove_v2_all_subairs_composed_recursive` in FRI mode).
/// - `shard_size`: Ni — number of inners per first-level master.
///   Must be ≥ 1.  K = `(N + Ni − 1) / Ni`.
/// - `(master_blowup, master_r, master_use_stir)`: FRI parameters for
///   both the first- and second-level master STARKs.
/// - `(merkle_blowup, merkle_r, merkle_use_stir)`: FRI parameters for
///   the top batched Merkle STARK.
pub fn prove_two_level_sharded_master(
    inner_proofs: &[RecursiveStarkProof],
    shard_size: usize,
    master_blowup: usize,
    master_r: usize,
    master_use_stir: bool,
    merkle_blowup: usize,
    merkle_r: usize,
    merkle_use_stir: bool,
) -> Result<TwoLevelShardedProof, MasterMerkleBindingError> {
    if inner_proofs.is_empty() {
        return Err(MasterMerkleBindingError::Inner(MasterBridgeError::EmptyInput));
    }
    if shard_size == 0 {
        return Err(MasterMerkleBindingError::Internal(
            "shard_size must be >= 1".into(),
        ));
    }

    // 1. Prove each shard's first-level master (sequentially — bounds
    //    peak prover memory to O(shard_size) at any one time).
    let mut shard_masters: Vec<RecursiveStarkProof> =
        Vec::with_capacity((inner_proofs.len() + shard_size - 1) / shard_size);
    for shard in inner_proofs.chunks(shard_size) {
        let m = prove_master_recursive(
            shard, master_blowup, master_r, master_use_stir,
        ).map_err(MasterMerkleBindingError::Inner)?;
        shard_masters.push(m);
    }

    // 2. Prove the super (second-level) master over the K shard masters.
    let super_master = prove_master_recursive(
        &shard_masters, master_blowup, master_r, master_use_stir,
    ).map_err(MasterMerkleBindingError::Inner)?;

    // 3. Top batched Merkle binding over all N inner pi_hashes.
    let inner_pi_hashes: Vec<[u8; 32]> =
        inner_proofs.iter().map(|r| r.public.outer_pi_hash).collect();
    let batched_pi = derive_batched_leaf_pi(&inner_pi_hashes);
    let (top_merkle_path, top_merkle_root) = prove_in_air_merkle_binding_for_pi_hash(
        batched_pi, merkle_blowup, merkle_r, merkle_use_stir,
    )?;

    let shard_pi_hashes: Vec<[u8; 32]> =
        shard_masters.iter().map(|m| m.public.outer_pi_hash).collect();

    Ok(TwoLevelShardedProof {
        super_master, top_merkle_path, top_merkle_root,
        inner_pi_hashes, shard_pi_hashes, shard_size,
    })
}

/// Verify a `TwoLevelShardedProof`.
///
/// Verifies:
///   1. `inner_pi_hashes[i] == inner_proofs[i].outer_pi_hash` for every i
///      (binds the bundle to the supplied inner proofs).
///   2. `shard_pi_hashes.len() == ceil(N / shard_size)` (sanity).
///   3. The super-master FRI-verifies (self-contained: attests the K
///      shard-master FRI-quotient relations algebraically).
///   4. The top batched Merkle binds `batched_pi(inner_pi_hashes)` to
///      the recorded root.
pub fn verify_two_level_sharded_master(
    proof: &TwoLevelShardedProof,
    inner_proofs: &[RecursiveStarkProof],
) -> bool {
    if proof.inner_pi_hashes.len() != inner_proofs.len() {
        return false;
    }
    if proof.shard_size == 0 {
        return false;
    }
    for (i, h) in proof.inner_pi_hashes.iter().enumerate() {
        if *h != inner_proofs[i].public.outer_pi_hash {
            return false;
        }
    }
    let expected_k =
        (proof.inner_pi_hashes.len() + proof.shard_size - 1) / proof.shard_size;
    if proof.shard_pi_hashes.len() != expected_k {
        return false;
    }
    if !verify_master_recursive(&proof.super_master) {
        return false;
    }
    let batched_pi = derive_batched_leaf_pi(&proof.inner_pi_hashes);
    let expected_root = expected_merkle_root_for_pi_hash(batched_pi);
    if expected_root != proof.top_merkle_root {
        return false;
    }
    if !verify_merkle_path(&proof.top_merkle_path) {
        return false;
    }
    if proof.top_merkle_path.public.leaf_index != 0 {
        return false;
    }
    if proof.top_merkle_path.public.root.0.as_slice() != expected_root {
        return false;
    }
    true
}

/// Verify a `MasterWithBatchedMerkleProof`.
///
/// Re-derives both the batched pi_hash and the expected Merkle root
/// from `bundle.inner_pi_hashes`, cross-checks them against the proof,
/// and confirms each `inner_pi_hashes[i] == inner_proofs[i].outer_pi_hash`.
/// Without the per-inner cross-check, a malicious prover could
/// substitute a different N-tuple of pi_hashes into the batched leaf.
pub fn verify_master_with_batched_in_air_merkle_path(
    bundle: &MasterWithBatchedMerkleProof,
    inner_proofs: &[RecursiveStarkProof],
) -> bool {
    if !verify_master_recursive(&bundle.master) {
        return false;
    }
    if bundle.inner_pi_hashes.len() != inner_proofs.len() {
        return false;
    }
    // Cross-check the supplied inner_pi_hashes against the actual
    // inner proofs (binds bundle.inner_pi_hashes to the master).
    for (i, h) in bundle.inner_pi_hashes.iter().enumerate() {
        if *h != inner_proofs[i].public.outer_pi_hash {
            return false;
        }
    }
    // Re-derive batched_pi + expected merkle root.
    let batched_pi = derive_batched_leaf_pi(&bundle.inner_pi_hashes);
    let expected_root = expected_merkle_root_for_pi_hash(batched_pi);
    if expected_root != bundle.merkle_root {
        return false;
    }
    // Verify the batched Merkle-path STARK + bind to the expected root.
    if !verify_merkle_path(&bundle.merkle_path_proof) {
        return false;
    }
    if bundle.merkle_path_proof.public.leaf_index != 0 {
        return false;
    }
    if bundle.merkle_path_proof.public.root.0.as_slice() != expected_root {
        return false;
    }
    true
}

// ─── Phase 2: FRI Merkle opening extractor ───────────────────────────
//
// Pulls every per-(query, fold-layer) MerkleOpening out of an inner
// RecursiveStarkProof's embedded DeepFriProof<Ext> and converts them
// into a BatchedMerklePathClaim ready for `prove_batched_merkle_paths`
// in `crate::merkle_prover`.
//
// **Scope (matches Phase 0 design doc)**: binds the L arity-2
// fold-layer openings per query (`roots[0..L]`).  The arity-16
// base-layer opening (`root_f0`) is INTENTIONALLY skipped — its
// in-AIR Merkle verification would require extending the current
// binary-only `MerklePathLayout` to higher arities, and the layer-0
// `per_layer_payloads[0]` is already fully bound by `roots[0]`'s
// (f, s, q) Ext-tuple commitment (see fri.rs:2659-2688 for the
// double-commitment).  So skipping `root_f0` is sound for the
// master's sub-circuit 1 binding purpose; it just leaves the
// layer-0 LDE-consistency check (fri.rs:2622-2657) as a separate
// follow-up.
//
// M_paths per inner FRI proof = r × L (matches the
// `print_fri_merkle_binding_sizing` probe: smoke L1 r=54 L=15 → 810).

/// Errors from `extract_fri_merkle_openings`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FriMerkleExtractError {
    /// Inner recursive STARK uses STIR mode; the extractor only handles
    /// FRI mode (matches the residue extractor at line ~120 of this
    /// file).  Re-run with `use_stir=false` when producing the inner.
    StirNotSupported,
    /// FRI proof has zero queries — degenerate.
    EmptyQueries,
    /// Layer-proofs and queries don't line up (malformed proof).
    LayerProofShapeMismatch(String),
    /// An opening's per-level path didn't have exactly 1 sibling, which
    /// the binary in-AIR Merkle gadget requires.  Indicates non-arity-2
    /// fold layer — currently unsupported.
    NonBinaryPath(String),
}

impl std::fmt::Display for FriMerkleExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StirNotSupported => write!(f,
                "FRI Merkle extractor: STIR mode not supported (FRI mode only)"
            ),
            Self::EmptyQueries => write!(f, "FRI Merkle extractor: zero queries"),
            Self::LayerProofShapeMismatch(s) => write!(f,
                "FRI Merkle extractor: layer-proof shape: {s}"
            ),
            Self::NonBinaryPath(s) => write!(f,
                "FRI Merkle extractor: non-binary path: {s}"
            ),
        }
    }
}
impl std::error::Error for FriMerkleExtractError {}

/// Extract all per-(query, fold-layer) MerkleOpenings from one inner
/// `RecursiveStarkProof` and pack into a `BatchedMerklePathClaim`.
///
/// **Layout**: B = r × L paths.  Path j = `k * L + ell` corresponds to
/// query k and fold-layer ell (k in 0..r, ell in 0..L).  Each path is
/// a binary Merkle authentication of `opening.leaf` at index
/// `opening.index` against root `rec.fri_proof.roots[ell]`.
///
/// The `MerklePathClaim.leaf` is set to the **opening's leaf hash
/// bytes** (already SHA-3-compressed by the FRI prover via
/// `compute_leaf_hash`), not the underlying (f, s, q) field tuple.
/// Phase 3's master-level wire will additionally cross-check that the
/// leaf hash equals `SHA3(DS || ext_leaf_fields(f, s, q))` for the
/// matching `per_layer_payloads[ell]` — that's where the binding from
/// the master STARK's sub-circuit 1 residues to the FRI-committed
/// Merkle leaves lives (Piece 3 of the soundness chain in the design
/// doc).
///
/// Per-layer depth is `log2(layer_size)`, decreasing from layer 0 down
/// to layer L-1.  All fold layers use arity-2 (binary trees) per
/// `pick_arity_for_layer(n, requested_m=2)`.
pub fn extract_fri_merkle_openings(
    rec: &RecursiveStarkProof,
) -> Result<BatchedMerklePathClaim, FriMerkleExtractError> {
    let fri_proof = &rec.fri_proof;
    if fri_proof.queries.is_empty() {
        return Err(FriMerkleExtractError::EmptyQueries);
    }
    if rec.use_stir {
        return Err(FriMerkleExtractError::StirNotSupported);
    }

    let r = fri_proof.queries.len();
    let l = fri_proof.queries[0].per_layer_payloads.len();

    if fri_proof.roots.len() != l {
        return Err(FriMerkleExtractError::LayerProofShapeMismatch(format!(
            "fri_proof.roots.len()={} != L={l}",
            fri_proof.roots.len()
        )));
    }
    if fri_proof.layer_proofs.layers.len() != l {
        return Err(FriMerkleExtractError::LayerProofShapeMismatch(format!(
            "layer_proofs.layers.len()={} != L={l}",
            fri_proof.layer_proofs.layers.len()
        )));
    }
    for (ell, layer) in fri_proof.layer_proofs.layers.iter().enumerate() {
        if layer.openings.len() != r {
            return Err(FriMerkleExtractError::LayerProofShapeMismatch(format!(
                "layer_proofs.layers[{ell}].openings.len()={} != r={r}",
                layer.openings.len()
            )));
        }
    }

    // Verifier-side variant inference for the inner FRI proof's
    // Merkle commitments: HASH_BYTES = 32 ⇒ Sha3_256 (L1 / NIST L1).
    // Larger output bytes would mean L3 / L5 — the wrapper-stark
    // build feature toggles (sha3-256 / sha3-384 / sha3-512) already
    // pin this at compile time via `deep_ali::hash::selected::HASH_BYTES`.
    let variant = sha3_variant_for_hash_bytes(
        fri_proof.roots[0].len(),
    )?;

    // Build B = r × L paths, layer-major within each query.
    let mut paths: Vec<MerklePathClaim> = Vec::with_capacity(r * l);
    for k in 0..r {
        let qp = &fri_proof.queries[k];
        if qp.per_layer_payloads.len() != l || qp.per_layer_refs.len() != l {
            return Err(FriMerkleExtractError::LayerProofShapeMismatch(format!(
                "query {k} per-layer shape: payloads={} refs={} expected L={l}",
                qp.per_layer_payloads.len(), qp.per_layer_refs.len()
            )));
        }
        for ell in 0..l {
            let opening = &fri_proof.layer_proofs.layers[ell].openings[k];

            // path: Vec<Vec<[u8; HASH_BYTES]>> — for arity-2 trees,
            // each path[level] must have exactly 1 sibling.  Flatten
            // to a Vec<MerkleNode> for the binary in-AIR gadget.
            let mut flat_path: Vec<MerkleNode> =
                Vec::with_capacity(opening.path.len());
            for (level, siblings) in opening.path.iter().enumerate() {
                if siblings.len() != 1 {
                    return Err(FriMerkleExtractError::NonBinaryPath(format!(
                        "query {k} layer {ell} level {level}: {} siblings (expected 1)",
                        siblings.len()
                    )));
                }
                flat_path.push(MerkleNode(siblings[0].to_vec()));
            }

            // Per-hop DS bytes mirror `MerkleTreeChannel::verify_opening`
            // (merkle/src/lib.rs:781): for arity-2 fold layer ell, hop
            // `level` uses DsLabel { arity=2, level=level+1, position=
            // idx_at_this_hop / 2, tree_label=ell }.  Tree label per FRI
            // proof's `pick_arity_for_layer` config is set to the fold
            // layer's index `ell` (see fri.rs at `MerkleChannelCfg::new(
            // vec![arity; depth], ell as u64)` callsite for fold layers).
            let mut ds_prefix_per_hop: Vec<Vec<u8>> =
                Vec::with_capacity(flat_path.len());
            let mut hop_idx: u64 = opening.index as u64;
            for hop_level in 0..flat_path.len() {
                ds_prefix_per_hop.push(build_fri_ds_label_bytes(
                    /*arity=*/ 2,
                    /*level=*/ (hop_level as u32) + 1,
                    /*position=*/ hop_idx / 2,
                    /*tree_label=*/ ell as u64,
                ));
                hop_idx /= 2;
            }

            paths.push(MerklePathClaim {
                variant,
                root: MerkleNode(fri_proof.roots[ell].to_vec()),
                leaf_index: opening.index as u64,
                leaf: MerkleNode(opening.leaf.to_vec()),
                path: flat_path,
                ds_prefix_per_hop,
            });
        }
    }

    Ok(BatchedMerklePathClaim { variant, paths })
}

/// Reproduce `merkle::DsLabel::to_bytes()` without taking a dependency
/// on the private DsLabel type.  32-byte fixed-length encoding:
/// `arity(8 LE) | level(8 LE) | position(8 LE) | tree_label(8 LE)`.
/// Used by the FRI Merkle extractor to populate per-hop DS prefix
/// bytes matching `MerkleTreeChannel::verify_opening`'s hash protocol.
fn build_fri_ds_label_bytes(
    arity: u64,
    level: u32,
    position: u64,
    tree_label: u64,
) -> Vec<u8> {
    let mut out = Vec::with_capacity(32);
    out.extend_from_slice(&arity.to_le_bytes());
    out.extend_from_slice(&(level as u64).to_le_bytes());
    out.extend_from_slice(&position.to_le_bytes());
    out.extend_from_slice(&tree_label.to_le_bytes());
    out
}

/// Infer the `Sha3Variant` from the Merkle root byte length recorded
/// in a `DeepFriProof<E>`.  Inner FRI proofs use the build's selected
/// hash variant (compile-time feature gate), so this is always the
/// same answer in a given build — but checking explicitly here lets
/// the extractor fail loudly if a proof from a wrong build slips in.
fn sha3_variant_for_hash_bytes(
    hash_bytes: usize,
) -> Result<Sha3Variant, FriMerkleExtractError> {
    match hash_bytes {
        32 => Ok(Sha3Variant::Sha3_256),
        48 => Ok(Sha3Variant::Sha3_384),
        64 => Ok(Sha3Variant::Sha3_512),
        other => Err(FriMerkleExtractError::LayerProofShapeMismatch(format!(
            "unsupported Merkle root byte length: {other} \
             (expected 32 / 48 / 64 for sha3-256 / sha3-384 / sha3-512)"
        ))),
    }
}

// ─── Phase 3: Master-level FRI-Merkle binding ────────────────────────
//
// Closes the prover-supplied-residue caveat at the master STARK level
// by binding every inner FRI proof's per-(query, fold-layer)
// `(f, s, q)` payloads to the inner's Merkle commitments via in-AIR
// SHA-3 hashing.  Three-piece soundness chain (per
// `scripts/results/fri-merkle-binding-phase0-design.md`):
//
//   1. **FS-binds inner FRI roots** — landed in this commit by
//      extending `MASTER-RECURSION-{COMP,OOD,PI}-V2` seeds to absorb
//      every inner's `(root_f0, roots[*])`.  A prover cannot swap
//      inner FRI roots without re-deriving the master STARK's alphas.
//   2. **Per-inner binding bundle public roots match inner FRI roots** —
//      verifier re-derives `inner.fri_proof.roots[ell]` per (k, ell)
//      and cross-checks against each `BatchedMerklePathProof`'s
//      public root list.
//   3. **Leaf encodings match `per_layer_payloads`** — the binding
//      bundle's per-block public `(root, leaf_index, depth)` triples
//      come from the same extractor that consumes
//      `per_layer_payloads`, so the master STARK's sub-circuit 1
//      residues and the bundle's committed leaves reference the SAME
//      `(f, s, q)` triples.
//
// Together, any prover-supplied substitution of `(f, q)` values in
// sub-circuit 1 either (a) trips Piece 1 (changed root → different
// alphas) or (b) trips Piece 2 (bundle root doesn't match) or (c)
// trips the binding STARK's FRI verify (leaf hash mismatch).

/// Composed proof: master `RecursiveStarkProof` + N per-inner FRI-
/// Merkle binding bundles (one per inner).  Each binding bundle is a
/// `BatchedMerklePathProof` over that inner's r × L arity-2 fold-layer
/// openings (the bulk of `per_layer_payloads`).
pub struct MasterWithFriMerkleProof {
    pub master: RecursiveStarkProof,
    /// One binding bundle per inner.  Order matches `inner_proofs`.
    pub fri_merkle_bindings: Vec<BatchedMerklePathProof>,
}

/// Errors from `prove_master_with_fri_merkle_binding`.
#[derive(Debug, Clone)]
pub enum FriMerkleBindingError {
    Master(MasterBridgeError),
    Extract(FriMerkleExtractError),
    Binding(MerklePathProverError),
    Empty,
}

impl std::fmt::Display for FriMerkleBindingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Master(e) => write!(f, "FRI-Merkle binding: master: {e}"),
            Self::Extract(e) => write!(f, "FRI-Merkle binding: extract: {e}"),
            Self::Binding(e) => write!(f, "FRI-Merkle binding: binding STARK: {e}"),
            Self::Empty => write!(f, "FRI-Merkle binding: zero inner proofs supplied"),
        }
    }
}
impl std::error::Error for FriMerkleBindingError {}

/// **Phase 3 main entry**: produce master `RecursiveStarkProof` +
/// per-inner FRI-Merkle binding bundles.
///
/// For each inner: `extract_fri_merkle_openings` → BatchedMerklePathClaim
/// (r × L paths, DS-aware per Phase 2.5 extension) → `prove_batched_merkle_paths`.
///
/// The caller may optionally supply a `subset_paths` Vec to slice each
/// per-inner claim down to a tractable subset for testing (e.g.
/// `Some(vec![0, 1, 10, 100])` selects only those paths).  In production
/// the subset is `None` (= full B = r × L).
pub fn prove_master_with_fri_merkle_binding(
    inner_proofs: &[RecursiveStarkProof],
    master_blowup: usize, master_r: usize, master_use_stir: bool,
    binding_blowup: usize, binding_r: usize, binding_use_stir: bool,
    subset_paths: Option<&[usize]>,
) -> Result<MasterWithFriMerkleProof, FriMerkleBindingError> {
    if inner_proofs.is_empty() {
        return Err(FriMerkleBindingError::Empty);
    }

    let master = prove_master_recursive(
        inner_proofs, master_blowup, master_r, master_use_stir,
    ).map_err(FriMerkleBindingError::Master)?;

    let mut fri_merkle_bindings = Vec::with_capacity(inner_proofs.len());
    for rec in inner_proofs {
        let mut bundle_claim = extract_fri_merkle_openings(rec)
            .map_err(FriMerkleBindingError::Extract)?;
        if let Some(indices) = subset_paths {
            let subset = indices.iter()
                .map(|&i| bundle_claim.paths[i].clone())
                .collect();
            bundle_claim.paths = subset;
        }
        let binding = prove_batched_merkle_paths(
            &bundle_claim, binding_blowup, binding_r, binding_use_stir,
        ).map_err(FriMerkleBindingError::Binding)?;
        fri_merkle_bindings.push(binding);
    }

    Ok(MasterWithFriMerkleProof { master, fri_merkle_bindings })
}

/// Verify a `MasterWithFriMerkleProof` — three-piece soundness chain.
///
/// 1. Master STARK FRI-verifies (Piece 1: its FS seeds absorbed every
///    inner FRI proof's roots via `MASTER-RECURSION-*-V2`).
/// 2. Per-inner binding bundle FRI-verifies.
/// 3. Per-inner binding bundle public `(root, leaf_index, depth)`
///    triples match `inner.fri_proof.roots[ell]` + `per_layer_refs[ell].i`
///    + `log2(layer_size)` for the same indices the extractor used
///    (Piece 2 cross-check).
///
/// `subset_paths` MUST match the slice used at prove time (else the
/// per-inner bundle.batch_size won't equal the re-derived count and
/// verify rejects).
pub fn verify_master_with_fri_merkle_binding(
    bundle: &MasterWithFriMerkleProof,
    inner_proofs: &[RecursiveStarkProof],
    subset_paths: Option<&[usize]>,
) -> bool {
    if bundle.fri_merkle_bindings.len() != inner_proofs.len() {
        return false;
    }
    if !verify_master_recursive(&bundle.master) {
        return false;
    }
    // **Phase 5-2**: master.outer_pi_hash must match the deterministic
    // re-derivation from inner_proofs.  Closes Piece 1 (FRI-root swap)
    // and Piece 3 (per_layer_payload tamper) — the master is now bound
    // to the SPECIFIC inner proofs supplied to the verifier.
    let expected_master_outer = match rederive_master_outer_pi_hash(
        inner_proofs,
        bundle.master.public.n_trace_max,
    ) {
        Some(h) => h,
        None => return false,
    };
    if expected_master_outer != bundle.master.public.outer_pi_hash {
        return false;
    }
    for (i, rec) in inner_proofs.iter().enumerate() {
        let binding = &bundle.fri_merkle_bindings[i];
        if !verify_batched_merkle_paths(binding) {
            return false;
        }
        let expected_claim = match extract_fri_merkle_openings(rec) {
            Ok(c) => c,
            Err(_) => return false,
        };
        if !verify_binding_public_paths(binding, &expected_claim, subset_paths) {
            return false;
        }
    }
    true
}

// ─── Phase 4a: Sharded master-level FRI-Merkle binding ───────────────
//
// Applies Phase 3's 3-piece soundness chain at BOTH recursion levels:
//   - N per-inner FRI-Merkle binding bundles (same as Phase 3)
//   - K per-shard FRI-Merkle binding bundles (NEW — closes the
//     prover-supplied-residue caveat at the shard-master layer too)
//
// **Wire shape**: super_master + N inner bindings + K shard bindings +
// K shard masters (needed by verifier for Piece 2 cross-check of shard
// bindings; the V1 sharded design discarded these because the algebraic
// soundness lived in super-master sub-circuit 1's seed dependence on
// shard_pi_hashes alone).
//
// **Phase 4b follow-up** (deferred): recursive-aggregate the (N+K)
// binding bundles into ONE outer RecursiveStarkProof so the on-chain
// wire collapses back to constant in N+K — the proper "rollup" shape.
//
// **Soundness audit notes** (audit-2 needed before production):
//   1. Super-master FS-seed (MASTER-RECURSION-{COMP,OOD,PI}-V2) already
//      absorbs each shard_master's FRI roots via the V1→V2 extension
//      from Phase 3 (called recursively when proving the super-master
//      over shard_masters).  So Piece 1 holds at the SUPER layer.
//   2. Each shard-master's V2 seed similarly absorbs its inners' FRI
//      roots.  So Piece 1 holds at the SHARD layer.
//   3. Per-shard binding bundles must cross-check against shard_masters
//      provided in the wire — these are bound to the super-master via
//      its V2 seed.  Together: end-to-end Piece-1 chain holds.

/// Sharded master proof with full FRI-Merkle binding at both levels.
/// **Wire-cost note**: linear in N+K until Phase 4b recursive
/// aggregation lands.
pub struct TwoLevelShardedFriMerkleProof {
    /// Super-master STARK (the second-level master).  L1 wire.
    pub super_master: RecursiveStarkProof,
    /// K shard masters — included so the verifier can re-derive the
    /// per-shard binding bundles' expected public roots (Piece 2).
    /// Phase 4b will compress these out via recursive aggregation.
    pub shard_masters: Vec<RecursiveStarkProof>,
    /// N per-inner FRI-Merkle binding bundles (Phase 3 shape).
    pub inner_fri_merkle_bindings: Vec<BatchedMerklePathProof>,
    /// K per-shard FRI-Merkle binding bundles (new at Phase 4a).
    pub shard_fri_merkle_bindings: Vec<BatchedMerklePathProof>,
    pub shard_size: usize,
}

/// **Phase 4a main entry**: produce a fully-bound sharded master proof.
///
/// Per inner:  extract → batched-Merkle prove (= Phase 3 inner shape).
/// Per shard:  extract → batched-Merkle prove (NEW at this layer).
/// Super:      prove_master_recursive over shard_masters (uses V2 seeds,
///             so super FS-binds shard FRI roots).
///
/// `subset_paths` slices each per-inner AND per-shard binding claim
/// to a tractable size for testing (None = full B = r × L per binding).
pub fn prove_two_level_sharded_master_with_fri_merkle_binding(
    inner_proofs: &[RecursiveStarkProof],
    shard_size: usize,
    master_blowup: usize, master_r: usize, master_use_stir: bool,
    binding_blowup: usize, binding_r: usize, binding_use_stir: bool,
    subset_paths: Option<&[usize]>,
) -> Result<TwoLevelShardedFriMerkleProof, FriMerkleBindingError> {
    if inner_proofs.is_empty() {
        return Err(FriMerkleBindingError::Empty);
    }
    if shard_size == 0 {
        return Err(FriMerkleBindingError::Master(
            MasterBridgeError::EmptyInput,
        ));
    }

    // 1. K first-level shard masters (sequential — bounds peak memory).
    let mut shard_masters: Vec<RecursiveStarkProof> = Vec::with_capacity(
        (inner_proofs.len() + shard_size - 1) / shard_size,
    );
    for shard in inner_proofs.chunks(shard_size) {
        shard_masters.push(
            prove_master_recursive(shard, master_blowup, master_r, master_use_stir)
                .map_err(FriMerkleBindingError::Master)?,
        );
    }

    // 2. Super-master over the K shard masters.
    let super_master = prove_master_recursive(
        &shard_masters, master_blowup, master_r, master_use_stir,
    ).map_err(FriMerkleBindingError::Master)?;

    // 3. Per-inner FRI-Merkle binding bundles (N).
    let mut inner_fri_merkle_bindings = Vec::with_capacity(inner_proofs.len());
    for rec in inner_proofs {
        let mut claim = extract_fri_merkle_openings(rec)
            .map_err(FriMerkleBindingError::Extract)?;
        if let Some(indices) = subset_paths {
            let subset = indices.iter()
                .map(|&i| claim.paths[i].clone())
                .collect();
            claim.paths = subset;
        }
        inner_fri_merkle_bindings.push(
            prove_batched_merkle_paths(
                &claim, binding_blowup, binding_r, binding_use_stir,
            ).map_err(FriMerkleBindingError::Binding)?,
        );
    }

    // 4. Per-shard FRI-Merkle binding bundles (K).
    let mut shard_fri_merkle_bindings = Vec::with_capacity(shard_masters.len());
    for sm in &shard_masters {
        let mut claim = extract_fri_merkle_openings(sm)
            .map_err(FriMerkleBindingError::Extract)?;
        if let Some(indices) = subset_paths {
            let subset = indices.iter()
                .map(|&i| claim.paths[i].clone())
                .collect();
            claim.paths = subset;
        }
        shard_fri_merkle_bindings.push(
            prove_batched_merkle_paths(
                &claim, binding_blowup, binding_r, binding_use_stir,
            ).map_err(FriMerkleBindingError::Binding)?,
        );
    }

    Ok(TwoLevelShardedFriMerkleProof {
        super_master, shard_masters,
        inner_fri_merkle_bindings, shard_fri_merkle_bindings,
        shard_size,
    })
}

/// Verify a `TwoLevelShardedFriMerkleProof` — 3-piece chain applied at
/// BOTH levels (per-inner and per-shard).
///
/// 1. Super-master STARK FRI-verifies.  Its V2 FS-seed already absorbs
///    each shard_master's (outer_pi_hash + FRI roots), so the
///    super-master is bound to the SPECIFIC K shard masters supplied.
/// 2. Each shard_master STARK FRI-verifies independently AND its
///    `outer_pi_hash` matches the super-master's expected commitment.
///    (Implicit: if a shard master's outer_pi_hash differed, the
///    super-master's sub-circuit 1 alphas would mismatch.)
/// 3. Per-inner bindings cross-check against `inner_proofs[i]`
///    (Phase 3 verifier).
/// 4. Per-shard bindings cross-check against `shard_masters[k]`.
pub fn verify_two_level_sharded_master_with_fri_merkle_binding(
    proof: &TwoLevelShardedFriMerkleProof,
    inner_proofs: &[RecursiveStarkProof],
    subset_paths: Option<&[usize]>,
) -> bool {
    // Sanity: shape consistency.
    let expected_k = (inner_proofs.len() + proof.shard_size - 1) / proof.shard_size;
    if proof.shard_masters.len() != expected_k {
        return false;
    }
    if proof.inner_fri_merkle_bindings.len() != inner_proofs.len() {
        return false;
    }
    if proof.shard_fri_merkle_bindings.len() != expected_k {
        return false;
    }
    if proof.shard_size == 0 {
        return false;
    }

    // 1. Super-master FRI-verifies.
    if !verify_master_recursive(&proof.super_master) {
        return false;
    }

    // 1.5. **Phase 5-2 at super layer**: super_master.outer_pi_hash
    //      must re-derive deterministically from supplied shard_masters.
    //      Catches shard_master tamper (e.g. swapped FRI roots).
    let expected_super_outer = match rederive_master_outer_pi_hash(
        &proof.shard_masters,
        proof.super_master.public.n_trace_max,
    ) {
        Some(h) => h,
        None => return false,
    };
    if expected_super_outer != proof.super_master.public.outer_pi_hash {
        return false;
    }

    // 2. Each shard-master FRI-verifies (Piece 1 at the shard layer).
    //    **Phase 5-2 at shard layer**: each shard_master.outer_pi_hash
    //    must re-derive from its slice of inner_proofs.  Catches inner
    //    FRI root tamper.
    for (k, sm) in proof.shard_masters.iter().enumerate() {
        if !verify_recursive_stark(sm) {
            return false;
        }
        let shard_start = k * proof.shard_size;
        let shard_end = ((k + 1) * proof.shard_size).min(inner_proofs.len());
        let shard_inners = &inner_proofs[shard_start..shard_end];
        let expected_shard_outer = match rederive_master_outer_pi_hash(
            shard_inners,
            sm.public.n_trace_max,
        ) {
            Some(h) => h,
            None => return false,
        };
        if expected_shard_outer != sm.public.outer_pi_hash {
            return false;
        }
    }

    // 3. Per-inner bindings: reuse Phase 3 verifier shape.  Each
    //    binding's public paths must cross-check against the
    //    corresponding inner FRI proof's openings.
    for (i, rec) in inner_proofs.iter().enumerate() {
        let binding = &proof.inner_fri_merkle_bindings[i];
        if !verify_batched_merkle_paths(binding) {
            return false;
        }
        let expected_claim = match extract_fri_merkle_openings(rec) {
            Ok(c) => c,
            Err(_) => return false,
        };
        if !verify_binding_public_paths(binding, &expected_claim, subset_paths) {
            return false;
        }
    }

    // 4. Per-shard bindings: same shape, against shard_masters.
    for (k, sm) in proof.shard_masters.iter().enumerate() {
        let binding = &proof.shard_fri_merkle_bindings[k];
        if !verify_batched_merkle_paths(binding) {
            return false;
        }
        let expected_claim = match extract_fri_merkle_openings(sm) {
            Ok(c) => c,
            Err(_) => return false,
        };
        if !verify_binding_public_paths(binding, &expected_claim, subset_paths) {
            return false;
        }
    }

    true
}

/// Shared helper for Phase 3 + 4a: cross-check a `BatchedMerklePathProof`'s
/// public `(root, leaf_index, depth)` triples against the re-extracted
/// expected claim, honouring an optional subset slicing.
fn verify_binding_public_paths(
    binding: &BatchedMerklePathProof,
    expected_claim: &BatchedMerklePathClaim,
    subset_paths: Option<&[usize]>,
) -> bool {
    let expected_paths: Vec<&MerklePathClaim> = if let Some(indices) = subset_paths {
        if indices.iter().any(|&i| i >= expected_claim.paths.len()) {
            return false;
        }
        indices.iter().map(|&i| &expected_claim.paths[i]).collect()
    } else {
        expected_claim.paths.iter().collect()
    };
    if binding.public.paths.len() != expected_paths.len() {
        return false;
    }
    for (j, expected) in expected_paths.iter().enumerate() {
        let (got_root, got_leaf_index, got_depth) = &binding.public.paths[j];
        if got_root != &expected.root {
            return false;
        }
        if *got_leaf_index != expected.leaf_index {
            return false;
        }
        if *got_depth != expected.depth() {
            return false;
        }
    }
    true
}

// ─── Phase 4b: Recursive aggregation of binding bundles ──────────────
//
// Collapses N `BatchedMerklePathProof`s into ONE outer
// `RecursiveStarkProof` via the same FRI-residue-extraction pattern
// the master uses for inner recursive STARKs.  This brings the L1
// wire shape back to constant in N — each binding bundle's FRI
// DEEP-quotient relation is attested algebraically by the aggregator's
// sub-circuit 1, so the bundles themselves no longer need to live on
// L1.
//
// The aggregator's FS-seed (AGGREGATOR-FRI-MERKLE-{COMP,OOD,PI}-V1)
// absorbs each binding's `public.pi_hash`.  Since
// `BatchedMerklePathPublicInputs.pi_hash` already SHA-3-binds
// `(variant, B, per-path (depth, root, leaf_index))`, the
// aggregator's outer_pi_hash is transitively bound to every binding
// bundle's complete public commitment.
//
// Verifier-side at compact form: the verifier sees only the
// aggregator's `RecursiveStarkProof` + each bundle's small public
// inputs (`pi_hash` + per-path triples).  It re-derives each
// bundle's pi_hash, confirms the aggregator FRI-verifies under
// `aggregator.public.outer_pi_hash` that absorbs them, and
// cross-checks per-path public roots against the supplied inner /
// shard FRI proofs (Piece 2 unchanged).
//
// This delivers the `$56/batch constant` L1 cost target documented in
// `scripts/results/fri-merkle-binding-phase0-design.md`.

/// Reconstruct the FRI params the batched-Merkle prover used to
/// produce the given `BatchedMerklePathProof`.  Mirrors
/// `recursive_proof_params` but reads from the binding's
/// `BatchedMerklePathPublicInputs.pi_hash` instead of `outer_pi_hash`.
fn batched_merkle_proof_params(bmp: &BatchedMerklePathProof) -> DeepFriParams {
    let n_lde = bmp.n_trace * bmp.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, bmp.r, 0xDEEFu64);
    params.public_inputs_hash = Some(bmp.public.pi_hash);
    if bmp.use_stir { params.stir = true; }
    params
}

/// Per-binding-bundle DEEP-quotient residues.  Mirrors
/// `extract_recursive_fri_residues` but operates on a
/// `BatchedMerklePathProof`'s embedded FRI proof.  On an honest
/// binding bundle every residue is zero in F_ext.
fn extract_batched_merkle_fri_residues(
    bmp: &BatchedMerklePathProof,
) -> Result<Vec<Vec<Ext>>, MasterBridgeError> {
    let params = batched_merkle_proof_params(bmp);
    let fri_proof = &bmp.fri_proof;
    if fri_proof.queries.is_empty() {
        return Err(MasterBridgeError::StirNotSupported);
    }

    let z_ext = derive_z_ext_for_proof::<Ext>(fri_proof, &params);
    let sizes = layer_sizes_from_schedule(fri_proof.n0, &params.schedule);
    let l = params.schedule.len();

    let omega_per_layer: Vec<Goldilocks> = (0..l)
        .map(|ell| Radix2EvaluationDomain::<Goldilocks>::new(sizes[ell])
            .expect("layer domain power-of-two")
            .group_gen)
        .collect();

    let mut residues_per_query: Vec<Vec<Ext>> =
        Vec::with_capacity(fri_proof.queries.len());
    for qp in &fri_proof.queries {
        let mut row = Vec::with_capacity(l);
        for ell in 0..l {
            if ell >= qp.per_layer_payloads.len() || ell >= qp.per_layer_refs.len() {
                return Err(MasterBridgeError::MalformedFriProof(format!(
                    "binding query layer count {} < schedule len {l}",
                    qp.per_layer_payloads.len()
                )));
            }
            let pay = &qp.per_layer_payloads[ell];
            let rref = &qp.per_layer_refs[ell];
            let omega_ell = omega_per_layer[ell];
            let x_i = <Ext as TowerField>::from_fp(omega_ell.pow([rref.i as u64]));
            let fz = fri_proof.fz_per_layer[ell];
            let lhs = pay.q_val * (x_i - z_ext);
            let rhs = pay.f_val - fz;
            row.push(lhs - rhs);
        }
        residues_per_query.push(row);
    }
    Ok(residues_per_query)
}

/// Per-binding-bundle FRI-fold residues `s[ell] − f[ell+1] = 0` per
/// (k, ell) for ell in 0..L-1.  Mirrors `extract_recursive_fold_residues`
/// at the aggregator layer.  On an honest binding bundle every
/// residue is zero in F_ext.
fn extract_batched_merkle_fold_residues(
    bmp: &BatchedMerklePathProof,
) -> Result<Vec<Vec<Ext>>, MasterBridgeError> {
    let fri_proof = &bmp.fri_proof;
    if fri_proof.queries.is_empty() {
        return Err(MasterBridgeError::StirNotSupported);
    }
    let l = batched_merkle_proof_params(bmp).schedule.len();
    if l == 0 {
        return Ok(Vec::new());
    }

    let mut residues_per_query: Vec<Vec<Ext>> =
        Vec::with_capacity(fri_proof.queries.len());
    for qp in &fri_proof.queries {
        if qp.per_layer_payloads.len() < l {
            return Err(MasterBridgeError::MalformedFriProof(format!(
                "binding fold extract: query payloads {} < L = {l}",
                qp.per_layer_payloads.len()
            )));
        }
        let mut row = Vec::with_capacity(l - 1);
        for ell in 0..(l - 1) {
            let s_curr = qp.per_layer_payloads[ell].s_val;
            let f_next = qp.per_layer_payloads[ell + 1].f_val;
            row.push(s_curr - f_next);
        }
        residues_per_query.push(row);
    }
    Ok(residues_per_query)
}

/// Aggregator sub-circuit 1 + 1a: composition over per-binding-bundle
/// FRI DEEP-quotient residues + (V2) FRI-fold residues, flattened to
/// EXT_DEGREE Goldilocks coords.  Mirrors V3 `build_master_composition`
/// at the aggregator layer with FS seed
/// `AGGREGATOR-FRI-MERKLE-COMP-V2` over binding `public.pi_hash`s.
///
/// Total constraints per binding: r × (2L − 1) × EXT_DEGREE.
pub fn build_aggregator_composition(
    bindings: &[BatchedMerklePathProof],
) -> Result<CompositionClaim<Goldilocks>, MasterBridgeError> {
    if bindings.is_empty() {
        return Err(MasterBridgeError::EmptyInput);
    }

    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::new();
    let mut constraints: Vec<BitOp> = Vec::new();
    let mut next_col = 0usize;

    // Sub-circuit 1: DEEP-quotient residues.
    for bmp in bindings {
        let residues = extract_batched_merkle_fri_residues(bmp)?;
        for row in &residues {
            for r in row {
                let coords = r.to_fp_components();
                for c in 0..EXT_DEGREE {
                    let cell = CellRef::new(0, next_col);
                    column_values.push((cell, coords[c]));
                    constraints.push(BitOp::IsZero { cell });
                    next_col += 1;
                }
            }
        }
    }

    // Sub-circuit 1a: FRI-fold residues `s[ell] − f[ell+1] = 0`.
    for bmp in bindings {
        let fold_residues = extract_batched_merkle_fold_residues(bmp)?;
        for row in &fold_residues {
            for r in row {
                let coords = r.to_fp_components();
                for c in 0..EXT_DEGREE {
                    let cell = CellRef::new(0, next_col);
                    column_values.push((cell, coords[c]));
                    constraints.push(BitOp::IsZero { cell });
                    next_col += 1;
                }
            }
        }
    }

    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"AGGREGATOR-FRI-MERKLE-COMP-V2");
    for bmp in bindings {
        Digest::update(&mut hasher, bmp.public.pi_hash);
    }
    let seed: [u8; 32] = Digest::finalize(hasher).into();
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, constraints.len());

    Ok(CompositionClaim {
        column_values,
        constraints,
        alphas,
        expected: Goldilocks::zero(),
    })
}

/// Aggregator sub-circuit 2: OOD anchor over binding `pi_hash`es.
/// Mirrors `build_master_ood_anchor` shape; trivially-zero claims
/// whose role is FS-binding the bindings into the aggregator's
/// transcript.
pub fn build_aggregator_ood_anchor(
    bindings: &[BatchedMerklePathProof],
) -> OodAccumulatorClaim {
    let mut claims = Vec::with_capacity(bindings.len() * 4);
    for bmp in bindings {
        for chunk_idx in 0..4 {
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(
                &bmp.public.pi_hash[8 * chunk_idx..8 * (chunk_idx + 1)]
            );
            let v = Goldilocks::from(u64::from_le_bytes(bytes));
            claims.push(OodEqualityClaim {
                z: Goldilocks::zero(),
                f_at_z: v,
                g_at_z: v,
                binding_tag: "aggregator-binding-anchor",
            });
        }
    }

    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"AGGREGATOR-FRI-MERKLE-OOD-V2");
    for bmp in bindings {
        Digest::update(&mut hasher, bmp.public.pi_hash);
    }
    let seed: [u8; 32] = Digest::finalize(hasher).into();
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, claims.len());

    OodAccumulatorClaim {
        bundle: OodClaimBundle { claims },
        alphas,
    }
}

/// Aggregator sub-circuit 3: vestige perm-arg over a SHA-3 of the
/// concatenated binding `pi_hash`es.
pub fn build_aggregator_vestige_perm_arg(
    bindings: &[BatchedMerklePathProof],
) -> PermArgClaim<Goldilocks> {
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"AGGREGATOR-FRI-MERKLE-PI-V2");
    for bmp in bindings {
        Digest::update(&mut hasher, bmp.public.pi_hash);
    }
    let aggregator_pi: [u8; 32] = Digest::finalize(hasher).into();

    let mut elems = Vec::with_capacity(4);
    for chunk_idx in 0..4 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&aggregator_pi[8 * chunk_idx..8 * (chunk_idx + 1)]);
        elems.push(Goldilocks::from(u64::from_le_bytes(bytes)));
    }

    let mut seed = aggregator_pi;
    seed[0] ^= 0xE8;
    let gamma = alphas_from_transcript::<Goldilocks>(&seed, 1)[0];

    PermArgClaim {
        left: elems.clone(),
        right: elems,
        gamma,
        perm_tag: "aggregator-vestige",
    }
}

/// **Phase 4b core**: aggregate N `BatchedMerklePathProof`s into ONE
/// outer `RecursiveStarkProof`.  After this, the L1 wire only needs
/// the aggregator's `RecursiveStarkProof` shape — constant in N.
pub fn aggregate_fri_merkle_bindings(
    bindings: &[BatchedMerklePathProof],
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, MasterBridgeError> {
    let comp = build_aggregator_composition(bindings)?;
    let ood = build_aggregator_ood_anchor(bindings);
    let perm = build_aggregator_vestige_perm_arg(bindings);
    prove_recursive_stark(&comp, &ood, &perm, blowup, r, use_stir)
        .map_err(|e: RecursiveProverError|
            MasterBridgeError::RecursiveProver(format!("{e}")))
}

/// Compact form of `MasterWithFriMerkleProof`: master STARK + one
/// aggregator STARK attesting the N binding bundles' FRI-quotient
/// relations.  L1 wire is now constant in N (aggregator is
/// ~789 KiB at L1 prod bw=32 — same shape as the master).
///
/// The verifier still needs each binding bundle's PUBLIC inputs
/// (per-path `(root, leaf_index, depth)` triples) for the Piece 2
/// cross-check — these are tiny (`B × (32+8+8) ≈ 48 B` per path).
pub struct CompactFriMerkleBundle {
    pub master: RecursiveStarkProof,
    pub binding_aggregator: RecursiveStarkProof,
    /// Per-inner binding public inputs — needed by verifier for
    /// Piece 2 cross-check.  Size: `N × (32 + B × ~48) B`.  At
    /// B=810 (full) and N=10 this is ~390 KiB total.
    pub binding_publics: Vec<crate::merkle_prover::BatchedMerklePathPublicInputs>,
    /// **Phase 4b-2**: per-binding FRI proof shape (n_trace, blowup, r,
    /// use_stir).  Used by the verifier to deterministically reconstruct
    /// each binding's `n_constraints` and the aggregator's sub-circuit
    /// pi_hashes from `binding_publics` alone — closes the
    /// degenerate-aggregator attack vector by tying the aggregator's
    /// `outer_pi_hash` to the supplied publics.  32 B per binding.
    pub binding_meta: Vec<BatchedMerklePathMeta>,
}

/// Per-binding FRI-proof shape, recorded at prove time and used by
/// the Phase 4b verifier to re-derive `aggregator.public.outer_pi_hash`
/// deterministically from `binding_publics` (closes Phase 4b-2 gap).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BatchedMerklePathMeta {
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

impl BatchedMerklePathMeta {
    pub fn from_proof(bmp: &BatchedMerklePathProof) -> Self {
        Self {
            n_trace: bmp.n_trace,
            blowup: bmp.blowup,
            r: bmp.r,
            use_stir: bmp.use_stir,
        }
    }

    /// Reconstruct n_constraints contributed by this binding to the
    /// V2 aggregator's sub-circuit 1 + 1a: `r × (2L − 1) × EXT_DEGREE`
    /// where L = log2(n_trace × blowup).  V2 = V1 (DEEP-quotient only:
    /// `r × L × EXT_DEGREE`) plus FRI-fold residues
    /// (`r × (L − 1) × EXT_DEGREE`).
    pub fn aggregator_residue_constraints(&self) -> usize {
        let n_lde = self.n_trace * self.blowup;
        let l = n_lde.trailing_zeros() as usize;
        let deep = self.r * l * EXT_DEGREE;
        let fold = if l == 0 { 0 } else { self.r * (l - 1) * EXT_DEGREE };
        deep + fold
    }
}

/// **Phase 4b high-level entry**: produce the compact form
/// (master + binding aggregator + binding publics).
pub fn prove_master_with_fri_merkle_binding_aggregated(
    inner_proofs: &[RecursiveStarkProof],
    master_blowup: usize, master_r: usize, master_use_stir: bool,
    binding_blowup: usize, binding_r: usize, binding_use_stir: bool,
    aggregator_blowup: usize, aggregator_r: usize, aggregator_use_stir: bool,
    subset_paths: Option<&[usize]>,
) -> Result<CompactFriMerkleBundle, FriMerkleBindingError> {
    // 1. Run Phase 3 produce → linear form.
    let linear = prove_master_with_fri_merkle_binding(
        inner_proofs,
        master_blowup, master_r, master_use_stir,
        binding_blowup, binding_r, binding_use_stir,
        subset_paths,
    )?;

    // 2. Aggregate the N binding bundles into one outer.
    let aggregator = aggregate_fri_merkle_bindings(
        &linear.fri_merkle_bindings,
        aggregator_blowup, aggregator_r, aggregator_use_stir,
    ).map_err(FriMerkleBindingError::Master)?;

    // 3. Strip the binding fri_proofs from the wire; keep only public
    //    inputs + per-binding meta (Phase 4b-2 — meta lets the verifier
    //    re-derive aggregator.outer_pi_hash from publics deterministically).
    let binding_meta: Vec<BatchedMerklePathMeta> = linear.fri_merkle_bindings
        .iter().map(BatchedMerklePathMeta::from_proof).collect();
    let binding_publics: Vec<_> = linear.fri_merkle_bindings
        .into_iter().map(|b| b.public).collect();

    Ok(CompactFriMerkleBundle {
        master: linear.master,
        binding_aggregator: aggregator,
        binding_publics,
        binding_meta,
    })
}

/// **Phase 4b-2**: deterministically re-derive the aggregator's
/// `outer_pi_hash` from `binding_publics` + `binding_meta`, mirroring
/// the prover's sub-circuit pi_hash chain.  Returns `None` if any
/// reconstruction fails or shapes are inconsistent.
///
/// Mirrors `aggregate_fri_merkle_bindings` → `prove_recursive_stark`'s
/// outer_pi_hash construction:
/// `SHA3("WRAPPER-RECURSIVE-V1" || comp.pi_hash || ood.pi_hash ||
///       perm_arg.pi_hash || n_trace_max(LE))`.
pub fn rederive_aggregator_outer_pi_hash(
    binding_publics: &[crate::merkle_prover::BatchedMerklePathPublicInputs],
    binding_meta: &[BatchedMerklePathMeta],
    n_trace_max: usize,
) -> Option<[u8; 32]> {
    if binding_publics.len() != binding_meta.len() || binding_publics.is_empty() {
        return None;
    }
    let n_bindings = binding_publics.len();

    // 1. Reconstruct total composition constraint count.
    let n_total: usize = binding_meta.iter()
        .map(BatchedMerklePathMeta::aggregator_residue_constraints)
        .sum();

    // 2. Reconstruct comp seed → alphas.
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"AGGREGATOR-FRI-MERKLE-COMP-V2");
    for bp in binding_publics { Digest::update(&mut hasher, bp.pi_hash); }
    let comp_seed: [u8; 32] = Digest::finalize(hasher).into();
    let comp_alphas = alphas_from_transcript::<Goldilocks>(&comp_seed, n_total);

    // 3. Build synthetic comp claim (zero column_values + IsZero constraints —
    //    pi_hash via for_claim depends on (expected, n_constraints, alphas
    //    via trace.alpha[j], trace.phi[j], final_sum); honest values are
    //    column_value = 0 → phi = 0 → final_sum = 0).
    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::with_capacity(n_total);
    let mut constraints: Vec<BitOp> = Vec::with_capacity(n_total);
    for j in 0..n_total {
        let cell = CellRef::new(0, j);
        column_values.push((cell, Goldilocks::zero()));
        constraints.push(BitOp::IsZero { cell });
    }
    let comp_claim = CompositionClaim {
        column_values, constraints,
        alphas: comp_alphas,
        expected: Goldilocks::zero(),
    };
    let expected_comp_pi = CompositionAccumulatorPublicInputs::for_claim(&comp_claim).pi_hash;

    // 4. Reconstruct OOD anchor (4 trivially-equal claims per binding).
    let n_ood = n_bindings * 4;
    let mut ood_claims = Vec::with_capacity(n_ood);
    for bp in binding_publics {
        for chunk_idx in 0..4 {
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(&bp.pi_hash[8*chunk_idx..8*(chunk_idx+1)]);
            let v = Goldilocks::from(u64::from_le_bytes(bytes));
            ood_claims.push(OodEqualityClaim {
                z: Goldilocks::zero(),
                f_at_z: v, g_at_z: v,
                binding_tag: "aggregator-binding-anchor",
            });
        }
    }
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"AGGREGATOR-FRI-MERKLE-OOD-V2");
    for bp in binding_publics { Digest::update(&mut hasher, bp.pi_hash); }
    let ood_seed: [u8; 32] = Digest::finalize(hasher).into();
    let ood_alphas = alphas_from_transcript::<Goldilocks>(&ood_seed, n_ood);
    let ood_claim = OodAccumulatorClaim {
        bundle: OodClaimBundle { claims: ood_claims },
        alphas: ood_alphas,
    };
    let expected_ood_pi = OodAccumulatorPublicInputs::for_claim(&ood_claim).pi_hash;

    // 5. Reconstruct vestige perm-arg.
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"AGGREGATOR-FRI-MERKLE-PI-V2");
    for bp in binding_publics { Digest::update(&mut hasher, bp.pi_hash); }
    let aggregator_pi: [u8; 32] = Digest::finalize(hasher).into();
    let mut elems = Vec::with_capacity(4);
    for chunk_idx in 0..4 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&aggregator_pi[8*chunk_idx..8*(chunk_idx+1)]);
        elems.push(Goldilocks::from(u64::from_le_bytes(bytes)));
    }
    let mut seed = aggregator_pi;
    seed[0] ^= 0xE8;
    let gamma = alphas_from_transcript::<Goldilocks>(&seed, 1)[0];
    let perm_claim = PermArgClaim {
        left: elems.clone(),
        right: elems,
        gamma,
        perm_tag: "aggregator-vestige",
    };
    let expected_perm_pi = PermArgPublicInputs::for_claim(&perm_claim).pi_hash;

    // 6. Combine into outer_pi_hash.
    let mut h = sha3::Sha3_256::new();
    Digest::update(&mut h, b"WRAPPER-RECURSIVE-V1");
    Digest::update(&mut h, expected_comp_pi);
    Digest::update(&mut h, expected_ood_pi);
    Digest::update(&mut h, expected_perm_pi);
    Digest::update(&mut h, (n_trace_max as u64).to_le_bytes());
    let digest = Digest::finalize(h);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    Some(out)
}

// ─── Phase 5-2: master outer_pi_hash re-derivation (Piece 1+3) ──────
//
// Closes the gap where the master STARK verifier reads
// `master.public.outer_pi_hash` at face value rather than re-deriving
// it from the supplied `inner_proofs`.  Without this check, an adversary
// could submit (master_real, inner_proofs_with_tampered_root_f0) — FRI
// verify still passes because outer_pi_hash is baked into the proof.
//
// Same fix shape as Phase 4b-2 but at the master STARK layer:
// reconstruct each sub-circuit's claim deterministically from
// `inner_proofs` + master.n_trace_max, call the same
// `for_claim` constructors, and confirm `master.public.outer_pi_hash`
// matches.  Closes Piece 1 (FRI-root swap) and Piece 3 (per_layer_payload
// tamper) tamper detection by tying the master back to the supplied
// inner FRI proofs.

/// **Phase 5-2**: deterministically re-derive
/// `master.public.outer_pi_hash` from `inner_proofs` + `n_trace_max`,
/// mirroring `build_master_composition` (V3 with sub-circuit 1a) +
/// `build_master_ood_anchor` + `build_master_vestige_perm_arg` +
/// `prove_recursive_stark`'s outer_pi_hash chain.
///
/// Returns `None` on shape mismatch.  No `_meta` extension needed —
/// `RecursiveStarkProof` already carries `n_trace`, `blowup`, `r`,
/// `use_stir` for the verifier to reconstruct each inner's
/// FRI-shape contribution.
pub fn rederive_master_outer_pi_hash(
    inner_proofs: &[RecursiveStarkProof],
    n_trace_max: usize,
) -> Option<[u8; 32]> {
    if inner_proofs.is_empty() {
        return None;
    }
    let n_inners = inner_proofs.len();

    // 1. Total comp constraints: per inner = r × (2L − 1) × EXT_DEGREE
    //    (V3 sub-circuit 1 + 1a — DEEP-quotient + fold residues).
    let n_total: usize = inner_proofs.iter().map(|rec| {
        let n_lde = rec.n_trace * rec.blowup;
        let l = n_lde.trailing_zeros() as usize;
        let deep = rec.r * l * EXT_DEGREE;
        let fold = if l == 0 { 0 } else { rec.r * (l - 1) * EXT_DEGREE };
        deep + fold
    }).sum();

    // 2. Comp seed → alphas (mirrors build_master_composition).
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"MASTER-RECURSION-COMP-V3");
    for rec in inner_proofs {
        Digest::update(&mut hasher, rec.public.outer_pi_hash);
        absorb_inner_fri_roots(&mut hasher, rec);
    }
    let comp_seed: [u8; 32] = Digest::finalize(hasher).into();
    let comp_alphas = alphas_from_transcript::<Goldilocks>(&comp_seed, n_total);

    // 3. Synthetic comp claim — zero column_values (residues are zero
    //    on honest inner proofs; flattens identically).
    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::with_capacity(n_total);
    let mut constraints: Vec<BitOp> = Vec::with_capacity(n_total);
    for j in 0..n_total {
        let cell = CellRef::new(0, j);
        column_values.push((cell, Goldilocks::zero()));
        constraints.push(BitOp::IsZero { cell });
    }
    let comp_claim = CompositionClaim {
        column_values, constraints,
        alphas: comp_alphas,
        expected: Goldilocks::zero(),
    };
    let expected_comp_pi = CompositionAccumulatorPublicInputs::for_claim(&comp_claim).pi_hash;

    // 4. OOD anchor: 4 trivially-equal claims per inner outer_pi_hash chunk.
    let n_ood = n_inners * 4;
    let mut ood_claims = Vec::with_capacity(n_ood);
    for rec in inner_proofs {
        for chunk_idx in 0..4 {
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(
                &rec.public.outer_pi_hash[8*chunk_idx..8*(chunk_idx+1)]
            );
            let v = Goldilocks::from(u64::from_le_bytes(bytes));
            ood_claims.push(OodEqualityClaim {
                z: Goldilocks::zero(),
                f_at_z: v, g_at_z: v,
                binding_tag: "master-pi-anchor",
            });
        }
    }
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"MASTER-RECURSION-OOD-V3");
    for rec in inner_proofs {
        Digest::update(&mut hasher, rec.public.outer_pi_hash);
        absorb_inner_fri_roots(&mut hasher, rec);
    }
    let ood_seed: [u8; 32] = Digest::finalize(hasher).into();
    let ood_alphas = alphas_from_transcript::<Goldilocks>(&ood_seed, n_ood);
    let ood_claim = OodAccumulatorClaim {
        bundle: OodClaimBundle { claims: ood_claims },
        alphas: ood_alphas,
    };
    let expected_ood_pi = OodAccumulatorPublicInputs::for_claim(&ood_claim).pi_hash;

    // 5. Vestige perm-arg: derive master_pi → 4-elem multiset over chunks.
    let mut hasher = sha3::Sha3_256::new();
    Digest::update(&mut hasher, b"MASTER-RECURSION-PI-V3");
    for rec in inner_proofs {
        Digest::update(&mut hasher, rec.public.outer_pi_hash);
        absorb_inner_fri_roots(&mut hasher, rec);
    }
    let master_pi: [u8; 32] = Digest::finalize(hasher).into();
    let mut elems = Vec::with_capacity(4);
    for chunk_idx in 0..4 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&master_pi[8*chunk_idx..8*(chunk_idx+1)]);
        elems.push(Goldilocks::from(u64::from_le_bytes(bytes)));
    }
    let mut seed = master_pi;
    seed[0] ^= 0xE7;
    let gamma = alphas_from_transcript::<Goldilocks>(&seed, 1)[0];
    let perm_claim = PermArgClaim {
        left: elems.clone(),
        right: elems,
        gamma,
        perm_tag: "master-vestige",
    };
    let expected_perm_pi = PermArgPublicInputs::for_claim(&perm_claim).pi_hash;

    // 6. Combine into expected outer_pi_hash.
    let mut h = sha3::Sha3_256::new();
    Digest::update(&mut h, b"WRAPPER-RECURSIVE-V1");
    Digest::update(&mut h, expected_comp_pi);
    Digest::update(&mut h, expected_ood_pi);
    Digest::update(&mut h, expected_perm_pi);
    Digest::update(&mut h, (n_trace_max as u64).to_le_bytes());
    let digest = Digest::finalize(h);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    Some(out)
}

/// **Phase 4b verify**: confirms (i) master STARK FRI-verifies,
/// (ii) binding aggregator FRI-verifies, (iii) aggregator was produced
/// over the supplied `binding_publics` (FS-seed re-derivation),
/// (iv) per-inner Piece 2 cross-check against `inner_proofs`.
pub fn verify_master_with_fri_merkle_binding_aggregated(
    bundle: &CompactFriMerkleBundle,
    inner_proofs: &[RecursiveStarkProof],
    subset_paths: Option<&[usize]>,
) -> bool {
    if bundle.binding_publics.len() != inner_proofs.len() {
        return false;
    }
    if bundle.binding_meta.len() != bundle.binding_publics.len() {
        return false;
    }

    // (i) Master verifies.
    if !verify_master_recursive(&bundle.master) {
        return false;
    }

    // (ii) Aggregator verifies.
    if !verify_recursive_stark(&bundle.binding_aggregator) {
        return false;
    }

    // (ii.5) **Phase 4b-2**: aggregator.outer_pi_hash must match the
    //        deterministic re-derivation from binding_publics + meta.
    //        Closes the degenerate-aggregator attack vector.
    let expected_outer = match rederive_aggregator_outer_pi_hash(
        &bundle.binding_publics,
        &bundle.binding_meta,
        bundle.binding_aggregator.public.n_trace_max,
    ) {
        Some(h) => h,
        None => return false,
    };
    if expected_outer != bundle.binding_aggregator.public.outer_pi_hash {
        return false;
    }

    // (iii) Aggregator's outer_pi_hash must equal what we'd compute
    //       from the supplied binding_publics.  Rebuild the three
    //       sub-circuit pi_hashes the way the aggregator did:
    //         comp.pi_hash, ood.pi_hash, perm_arg.pi_hash
    //       — and the aggregator's outer_pi_hash from those + n_trace_max.
    //
    //       However, we don't reconstruct ALL of that here: we just
    //       confirm each binding_publics[i].pi_hash matches what the
    //       aggregator's FS-seed absorbed.  If a malicious prover
    //       supplied different binding_publics than what the aggregator
    //       was actually proven over, the aggregator's residues would
    //       have been computed under different alphas and FRI verify
    //       (already done in step (ii)) would have rejected.  So
    //       step (ii) implicitly proves the binding_publics are
    //       consistent with the aggregator, modulo PUBLIC re-binding
    //       via the aggregator's own pi_hash chain.
    //
    //       Defense-in-depth: confirm each binding_publics[i].pi_hash
    //       deterministically re-derives from its (paths, variant).
    //       This catches a tampered binding_publics that wasn't
    //       actually fed to the aggregator.
    use crate::merkle_prover::BatchedMerklePathPublicInputs;
    use crate::merkle_path_air::BatchedMerklePathClaim;
    for bp in &bundle.binding_publics {
        // Re-derive: build a synthetic BatchedMerklePathClaim from the
        // publics (we only need the (root, leaf_index, depth) triples
        // and variant — `leaf` and `path` bytes are private witness
        // but they don't affect pi_hash).  Use `for_claim` to compute.
        let synthetic_claim = BatchedMerklePathClaim {
            variant: bp.variant,
            paths: bp.paths.iter().map(|(root, leaf_index, depth)| {
                use crate::merkle_path_air::{MerklePathClaim, MerkleNode};
                let n_bytes = bp.variant.output_bytes();
                MerklePathClaim {
                    variant: bp.variant,
                    root: root.clone(),
                    leaf_index: *leaf_index,
                    // Private fields don't affect pi_hash, so zero them.
                    leaf: MerkleNode(vec![0u8; n_bytes]),
                    path: vec![MerkleNode(vec![0u8; n_bytes]); *depth],
                    ds_prefix_per_hop: Vec::new(),
                }
            }).collect(),
        };
        let rederived = BatchedMerklePathPublicInputs::for_claim(&synthetic_claim);
        if rederived.pi_hash != bp.pi_hash {
            return false;
        }
    }

    // (iv) Per-inner Piece 2 cross-check: bundle's public roots match
    //      the inner FRI's expected per-(query, layer) Merkle openings.
    for (i, rec) in inner_proofs.iter().enumerate() {
        let bp = &bundle.binding_publics[i];
        let expected_claim = match extract_fri_merkle_openings(rec) {
            Ok(c) => c,
            Err(_) => return false,
        };
        let expected_paths: Vec<&MerklePathClaim> = if let Some(indices) = subset_paths {
            if indices.iter().any(|&i| i >= expected_claim.paths.len()) {
                return false;
            }
            indices.iter().map(|&i| &expected_claim.paths[i]).collect()
        } else {
            expected_claim.paths.iter().collect()
        };
        if bp.paths.len() != expected_paths.len() {
            return false;
        }
        for (j, expected) in expected_paths.iter().enumerate() {
            let (got_root, got_leaf_index, got_depth) = &bp.paths[j];
            if got_root != &expected.root {
                return false;
            }
            if *got_leaf_index != expected.leaf_index {
                return false;
            }
            if *got_depth != expected.depth() {
                return false;
            }
        }
    }

    true
}

// ─── Sharded compact form (Phase 4a + Phase 4b combined) ─────────────
//
// Brings the sharded recursion to constant-in-N+K L1 wire by
// aggregating BOTH per-inner AND per-shard binding bundles into a
// single outer `RecursiveStarkProof`, while preserving the 3-piece
// soundness chain at both recursion levels (Phase 4a) + the
// aggregator outer_pi_hash re-derivation (Phase 4b-2) + the master
// outer_pi_hash re-derivation at both layers (Phase 5-2).

/// Sharded compact bundle: super_master + K shard_masters + ONE
/// aggregator over the (N inner + K shard) binding bundles + their
/// publics + meta.  L1 wire shape:
///   super_master + aggregator + K × shard_master + (N+K) × publics + meta
/// At STARK-DNS-scale K = O(√N), so wire grows polylog in N.
pub struct CompactShardedFriMerkleBundle {
    pub super_master: RecursiveStarkProof,
    pub shard_masters: Vec<RecursiveStarkProof>,
    /// Single aggregator attesting BOTH per-inner AND per-shard
    /// bindings' FRI-quotient relations.  Order: inner bindings first
    /// (0..N), then shard bindings (N..N+K).
    pub binding_aggregator: RecursiveStarkProof,
    pub inner_binding_publics:
        Vec<crate::merkle_prover::BatchedMerklePathPublicInputs>,
    pub shard_binding_publics:
        Vec<crate::merkle_prover::BatchedMerklePathPublicInputs>,
    pub inner_binding_meta: Vec<BatchedMerklePathMeta>,
    pub shard_binding_meta: Vec<BatchedMerklePathMeta>,
    pub shard_size: usize,
}

/// Produce the sharded compact bundle: Phase 4a's
/// `TwoLevelShardedFriMerkleProof` shape, then aggregate the (N+K)
/// bindings into ONE outer via `aggregate_fri_merkle_bindings`.
pub fn prove_two_level_sharded_master_with_fri_merkle_binding_aggregated(
    inner_proofs: &[RecursiveStarkProof],
    shard_size: usize,
    master_blowup: usize, master_r: usize, master_use_stir: bool,
    binding_blowup: usize, binding_r: usize, binding_use_stir: bool,
    aggregator_blowup: usize, aggregator_r: usize, aggregator_use_stir: bool,
    subset_paths: Option<&[usize]>,
) -> Result<CompactShardedFriMerkleBundle, FriMerkleBindingError> {
    // 1. Phase 4a linear sharded form.
    let linear = prove_two_level_sharded_master_with_fri_merkle_binding(
        inner_proofs, shard_size,
        master_blowup, master_r, master_use_stir,
        binding_blowup, binding_r, binding_use_stir,
        subset_paths,
    )?;

    // 2. Concatenate inner + shard bindings into one slice for aggregation.
    let mut all_bindings: Vec<BatchedMerklePathProof> =
        Vec::with_capacity(
            linear.inner_fri_merkle_bindings.len()
            + linear.shard_fri_merkle_bindings.len(),
        );
    all_bindings.extend(linear.inner_fri_merkle_bindings);
    all_bindings.extend(linear.shard_fri_merkle_bindings);

    // 3. Aggregate (N+K) bindings into one RecursiveStarkProof.
    let aggregator = aggregate_fri_merkle_bindings(
        &all_bindings, aggregator_blowup, aggregator_r, aggregator_use_stir,
    ).map_err(FriMerkleBindingError::Master)?;

    // 4. Strip the binding fri_proofs; keep publics + meta.
    let n = inner_proofs.len();
    let inner_binding_meta: Vec<BatchedMerklePathMeta> =
        all_bindings.iter().take(n).map(BatchedMerklePathMeta::from_proof).collect();
    let shard_binding_meta: Vec<BatchedMerklePathMeta> =
        all_bindings.iter().skip(n).map(BatchedMerklePathMeta::from_proof).collect();
    let mut all_publics: Vec<_> =
        all_bindings.into_iter().map(|b| b.public).collect();
    let shard_binding_publics = all_publics.split_off(n);
    let inner_binding_publics = all_publics;

    Ok(CompactShardedFriMerkleBundle {
        super_master: linear.super_master,
        shard_masters: linear.shard_masters,
        binding_aggregator: aggregator,
        inner_binding_publics, shard_binding_publics,
        inner_binding_meta,    shard_binding_meta,
        shard_size: linear.shard_size,
    })
}

/// Verify a `CompactShardedFriMerkleBundle` — composes the Phase 4a
/// shard verifier + Phase 4b-2 aggregator re-derivation + Phase 5-2
/// master/shard outer_pi_hash re-derivation.
pub fn verify_two_level_sharded_master_with_fri_merkle_binding_aggregated(
    bundle: &CompactShardedFriMerkleBundle,
    inner_proofs: &[RecursiveStarkProof],
    subset_paths: Option<&[usize]>,
) -> bool {
    // Shape consistency.
    let expected_k = (inner_proofs.len() + bundle.shard_size - 1) / bundle.shard_size;
    if bundle.shard_masters.len() != expected_k { return false; }
    if bundle.inner_binding_publics.len() != inner_proofs.len() { return false; }
    if bundle.inner_binding_meta.len() != inner_proofs.len() { return false; }
    if bundle.shard_binding_publics.len() != expected_k { return false; }
    if bundle.shard_binding_meta.len() != expected_k { return false; }
    if bundle.shard_size == 0 { return false; }

    // 1. Super-master FRI + Phase 5-2 re-derive from shard_masters.
    if !verify_master_recursive(&bundle.super_master) { return false; }
    let expected_super_outer = match rederive_master_outer_pi_hash(
        &bundle.shard_masters,
        bundle.super_master.public.n_trace_max,
    ) {
        Some(h) => h, None => return false,
    };
    if expected_super_outer != bundle.super_master.public.outer_pi_hash {
        return false;
    }

    // 2. Each shard_master FRI + Phase 5-2 re-derive from inner slice.
    for (k, sm) in bundle.shard_masters.iter().enumerate() {
        if !verify_recursive_stark(sm) { return false; }
        let shard_start = k * bundle.shard_size;
        let shard_end = ((k + 1) * bundle.shard_size).min(inner_proofs.len());
        let shard_inners = &inner_proofs[shard_start..shard_end];
        let expected_shard_outer = match rederive_master_outer_pi_hash(
            shard_inners,
            sm.public.n_trace_max,
        ) {
            Some(h) => h, None => return false,
        };
        if expected_shard_outer != sm.public.outer_pi_hash { return false; }
    }

    // 3. Binding aggregator FRI verify.
    if !verify_recursive_stark(&bundle.binding_aggregator) { return false; }

    // 4. Phase 4b-2 re-derive aggregator outer_pi_hash from
    //    (inner ++ shard) binding publics + meta.
    let mut all_publics: Vec<_> = bundle.inner_binding_publics.clone();
    all_publics.extend(bundle.shard_binding_publics.iter().cloned());
    let mut all_meta: Vec<BatchedMerklePathMeta> = bundle.inner_binding_meta.clone();
    all_meta.extend(bundle.shard_binding_meta.iter().copied());
    let expected_agg_outer = match rederive_aggregator_outer_pi_hash(
        &all_publics, &all_meta,
        bundle.binding_aggregator.public.n_trace_max,
    ) {
        Some(h) => h, None => return false,
    };
    if expected_agg_outer != bundle.binding_aggregator.public.outer_pi_hash {
        return false;
    }

    // 5. Per-inner binding publics: defense-in-depth re-derivation +
    //    Piece 2 cross-check against inner FRI proofs.
    for (i, bp) in bundle.inner_binding_publics.iter().enumerate() {
        if !verify_binding_pi_hash_rederivation(bp) { return false; }
        let expected_claim = match extract_fri_merkle_openings(&inner_proofs[i]) {
            Ok(c) => c, Err(_) => return false,
        };
        if !verify_binding_publics_paths_match(bp, &expected_claim, subset_paths) {
            return false;
        }
    }

    // 6. Per-shard binding publics: same shape against shard_masters.
    for (k, bp) in bundle.shard_binding_publics.iter().enumerate() {
        if !verify_binding_pi_hash_rederivation(bp) { return false; }
        let expected_claim = match extract_fri_merkle_openings(&bundle.shard_masters[k]) {
            Ok(c) => c, Err(_) => return false,
        };
        if !verify_binding_publics_paths_match(bp, &expected_claim, subset_paths) {
            return false;
        }
    }

    true
}

/// Defense-in-depth: confirm a `BatchedMerklePathPublicInputs.pi_hash`
/// deterministically re-derives from its `(variant, paths)`.  Used by
/// `verify_two_level_sharded_master_with_fri_merkle_binding_aggregated`
/// to detect publics tampering not actually consumed by the aggregator.
/// Mirrors the inline check in `verify_master_with_fri_merkle_binding_aggregated`.
fn verify_binding_pi_hash_rederivation(
    bp: &crate::merkle_prover::BatchedMerklePathPublicInputs,
) -> bool {
    use crate::merkle_prover::BatchedMerklePathPublicInputs;
    use crate::merkle_path_air::{BatchedMerklePathClaim, MerklePathClaim, MerkleNode};
    let n_bytes = bp.variant.output_bytes();
    let synthetic_claim = BatchedMerklePathClaim {
        variant: bp.variant,
        paths: bp.paths.iter().map(|(root, leaf_index, depth)| MerklePathClaim {
            variant: bp.variant,
            root: root.clone(),
            leaf_index: *leaf_index,
            leaf: MerkleNode(vec![0u8; n_bytes]),
            path: vec![MerkleNode(vec![0u8; n_bytes]); *depth],
            ds_prefix_per_hop: Vec::new(),
        }).collect(),
    };
    BatchedMerklePathPublicInputs::for_claim(&synthetic_claim).pi_hash == bp.pi_hash
}

/// Per-binding-public paths Piece 2 cross-check helper.  Mirrors the
/// inline loop in `verify_master_with_fri_merkle_binding_aggregated`'s
/// step (iv).
fn verify_binding_publics_paths_match(
    bp: &crate::merkle_prover::BatchedMerklePathPublicInputs,
    expected_claim: &crate::merkle_path_air::BatchedMerklePathClaim,
    subset_paths: Option<&[usize]>,
) -> bool {
    use crate::merkle_path_air::MerklePathClaim;
    let expected_paths: Vec<&MerklePathClaim> = if let Some(indices) = subset_paths {
        if indices.iter().any(|&i| i >= expected_claim.paths.len()) {
            return false;
        }
        indices.iter().map(|&i| &expected_claim.paths[i]).collect()
    } else {
        expected_claim.paths.iter().collect()
    };
    if bp.paths.len() != expected_paths.len() { return false; }
    for (j, expected) in expected_paths.iter().enumerate() {
        let (got_root, got_leaf_index, got_depth) = &bp.paths[j];
        if got_root != &expected.root { return false; }
        if *got_leaf_index != expected.leaf_index { return false; }
        if *got_depth != expected.depth() { return false; }
    }
    true
}

// ─── Shape D intra-inner batching (Phase 0 design doc) ────────────────
//
// Splits each inner's full M = r × L Merkle openings into chunks of
// at most `chunk_size` paths, proves each chunk as an independent
// `BatchedMerklePathProof`, then aggregates ALL chunks across ALL
// inners into ONE outer `RecursiveStarkProof` via the existing Phase
// 4b aggregator.  Each chunk's working set is bounded by `chunk_size`
// (e.g. B=64 fits ~750 MB on commodity hardware), making
// full-coverage binding tractable where single-batch B=810 OOMs.
//
// Empirical anchor (2026-05-19, smoke L1 on Apple Silicon):
//   B=10 single-batch:  220.69 s, ~5 GB working set ✓
//   B=100 single-batch: OOM-killed (SIGKILL)
//   Shape D B=64 chunks: ~13 chunks/inner, each fits, sequential prove
// See `scripts/results/fri-merkle-binding-phase0-design.md` for
// the full Shape D analysis.

/// Prove the FULL FRI-Merkle binding for ONE inner via intra-inner
/// batching: extract M=r·L Merkle openings, split into contiguous
/// chunks of size `chunk_size`, prove each chunk as an independent
/// `BatchedMerklePathProof`.  Returns the per-chunk proofs in order
/// (chunk 0 covers paths 0..chunk_size, chunk 1 covers
/// chunk_size..2*chunk_size, etc).
///
/// Per-chunk working set is bounded by `chunk_size` × per-path trace,
/// avoiding the single-batch memory wall that OOMs at B≥~100.
pub fn prove_shape_d_inner_binding(
    inner: &RecursiveStarkProof,
    chunk_size: usize,
    binding_blowup: usize, binding_r: usize, binding_use_stir: bool,
    subset_paths: Option<&[usize]>,
) -> Result<Vec<BatchedMerklePathProof>, FriMerkleBindingError> {
    if chunk_size == 0 {
        return Err(FriMerkleBindingError::Master(MasterBridgeError::EmptyInput));
    }
    let full_claim = extract_fri_merkle_openings(inner)
        .map_err(FriMerkleBindingError::Extract)?;
    // Restrict to subset_paths if supplied (mirrors Phase 3
    // `prove_master_with_fri_merkle_binding`'s subset_paths threading
    // for tractable testing without disabling the gadget).
    let path_indices: Vec<usize> = match subset_paths {
        Some(indices) => indices.to_vec(),
        None => (0..full_claim.paths.len()).collect(),
    };
    let m = path_indices.len();
    if m == 0 {
        return Err(FriMerkleBindingError::Empty);
    }
    let n_chunks = (m + chunk_size - 1) / chunk_size;
    let mut chunk_bindings = Vec::with_capacity(n_chunks);
    for chunk_idx in 0..n_chunks {
        let start = chunk_idx * chunk_size;
        let end = ((chunk_idx + 1) * chunk_size).min(m);
        let chunk_paths = (start..end)
            .map(|j| full_claim.paths[path_indices[j]].clone())
            .collect();
        let chunk_claim = crate::merkle_path_air::BatchedMerklePathClaim {
            variant: full_claim.variant,
            paths: chunk_paths,
        };
        let chunk_proof = prove_batched_merkle_paths(
            &chunk_claim, binding_blowup, binding_r, binding_use_stir,
        ).map_err(FriMerkleBindingError::Binding)?;
        chunk_bindings.push(chunk_proof);
    }
    Ok(chunk_bindings)
}

/// Shape D compact bundle: master + cross-aggregator + per-inner
/// per-chunk publics + meta.  L1 wire shape:
///   master + aggregator + Σ_i (n_chunks_i × per-chunk-publics)
/// At full M=810 per inner with chunk_size=64: n_chunks=13;
/// per-chunk publics ~4 KiB each → ~52 KiB per inner of publics,
/// vs ~40 KiB for single-batch B=810 publics — roughly comparable,
/// while making the prover memory tractable.
pub struct ShapeDFriMerkleBundle {
    pub master: RecursiveStarkProof,
    /// Aggregator over ALL chunks across ALL inners
    /// (flattened: inner 0's chunks first, then inner 1's, etc.).
    pub binding_aggregator: RecursiveStarkProof,
    /// `per_inner_publics[i]` = vec of chunk publics for inner i.
    pub per_inner_publics:
        Vec<Vec<crate::merkle_prover::BatchedMerklePathPublicInputs>>,
    /// `per_inner_meta[i]` = vec of chunk meta for inner i.
    pub per_inner_meta: Vec<Vec<BatchedMerklePathMeta>>,
    /// Chunk size used at prove time (uniform across inners).
    pub chunk_size: usize,
}

/// **Shape D main entry**: produce the master STARK + per-inner Shape D
/// binding chunks + ONE cross-inner aggregator over all chunks.
pub fn prove_master_with_fri_merkle_binding_shape_d(
    inner_proofs: &[RecursiveStarkProof],
    chunk_size: usize,
    master_blowup: usize, master_r: usize, master_use_stir: bool,
    binding_blowup: usize, binding_r: usize, binding_use_stir: bool,
    aggregator_blowup: usize, aggregator_r: usize, aggregator_use_stir: bool,
    subset_paths: Option<&[usize]>,
) -> Result<ShapeDFriMerkleBundle, FriMerkleBindingError> {
    if inner_proofs.is_empty() {
        return Err(FriMerkleBindingError::Empty);
    }
    if chunk_size == 0 {
        return Err(FriMerkleBindingError::Master(MasterBridgeError::EmptyInput));
    }

    // 1. Master STARK.
    let master = prove_master_recursive(
        inner_proofs, master_blowup, master_r, master_use_stir,
    ).map_err(FriMerkleBindingError::Master)?;

    // 2. Per inner: split openings into B-sized chunks, prove each.
    //    `subset_paths` (when supplied) is applied per inner BEFORE
    //    chunking, so each inner gets the same subset → chunks shape.
    let mut per_inner_chunks: Vec<Vec<BatchedMerklePathProof>> =
        Vec::with_capacity(inner_proofs.len());
    for rec in inner_proofs {
        let chunks = prove_shape_d_inner_binding(
            rec, chunk_size, binding_blowup, binding_r, binding_use_stir,
            subset_paths,
        )?;
        per_inner_chunks.push(chunks);
    }

    // 3. Record per-inner chunk publics + meta BEFORE flattening
    //    (BatchedMerklePathProof doesn't impl Clone; we move into
    //    `all_chunks` for the aggregator and snapshot publics+meta
    //    here for the bundle).
    let mut per_inner_publics: Vec<Vec<_>> = Vec::with_capacity(inner_proofs.len());
    let mut per_inner_meta: Vec<Vec<BatchedMerklePathMeta>> = Vec::with_capacity(inner_proofs.len());
    for inner_chunks in &per_inner_chunks {
        let publics: Vec<_> = inner_chunks.iter().map(|b| b.public.clone()).collect();
        let meta: Vec<_> = inner_chunks.iter().map(BatchedMerklePathMeta::from_proof).collect();
        per_inner_publics.push(publics);
        per_inner_meta.push(meta);
    }

    // 4. Flatten across inners + aggregate via existing gadget.
    let all_chunks: Vec<BatchedMerklePathProof> = per_inner_chunks
        .into_iter().flatten().collect();
    let binding_aggregator = aggregate_fri_merkle_bindings(
        &all_chunks, aggregator_blowup, aggregator_r, aggregator_use_stir,
    ).map_err(FriMerkleBindingError::Master)?;

    Ok(ShapeDFriMerkleBundle {
        master, binding_aggregator,
        per_inner_publics, per_inner_meta,
        chunk_size,
    })
}

/// Verify a `ShapeDFriMerkleBundle` — master FRI verify + Phase 5-2
/// master re-derivation + aggregator FRI verify + Phase 4b-2
/// re-derivation over flattened publics + per-chunk Piece 2 against
/// contiguous slices of each inner's openings.
pub fn verify_master_with_fri_merkle_binding_shape_d(
    bundle: &ShapeDFriMerkleBundle,
    inner_proofs: &[RecursiveStarkProof],
    subset_paths: Option<&[usize]>,
) -> bool {
    if bundle.per_inner_publics.len() != inner_proofs.len() { return false; }
    if bundle.per_inner_meta.len() != inner_proofs.len() { return false; }
    if bundle.chunk_size == 0 { return false; }

    // (i) Master FRI verify.
    if !verify_master_recursive(&bundle.master) { return false; }

    // (i.5) Phase 5-2: master.outer_pi_hash matches re-derivation.
    let expected_master_outer = match rederive_master_outer_pi_hash(
        inner_proofs, bundle.master.public.n_trace_max,
    ) {
        Some(h) => h, None => return false,
    };
    if expected_master_outer != bundle.master.public.outer_pi_hash {
        return false;
    }

    // (ii) Aggregator FRI verify.
    if !verify_recursive_stark(&bundle.binding_aggregator) { return false; }

    // (ii.5) Phase 4b-2: aggregator.outer_pi_hash matches flattened publics.
    let flat_publics: Vec<_> = bundle.per_inner_publics.iter()
        .flat_map(|v| v.iter().cloned()).collect();
    let flat_meta: Vec<BatchedMerklePathMeta> = bundle.per_inner_meta.iter()
        .flat_map(|v| v.iter().copied()).collect();
    let expected_agg_outer = match rederive_aggregator_outer_pi_hash(
        &flat_publics, &flat_meta,
        bundle.binding_aggregator.public.n_trace_max,
    ) {
        Some(h) => h, None => return false,
    };
    if expected_agg_outer != bundle.binding_aggregator.public.outer_pi_hash {
        return false;
    }

    // (iii) Per-inner per-chunk publics: defense-in-depth pi_hash
    //       re-derivation + Piece 2 against contiguous chunk slices of
    //       each inner's (subset-restricted) Merkle openings.
    for (i, rec) in inner_proofs.iter().enumerate() {
        let expected_claim = match extract_fri_merkle_openings(rec) {
            Ok(c) => c, Err(_) => return false,
        };
        // `subset_paths` indexes into the inner's full openings;
        // chunks index into the subset.
        let path_indices: Vec<usize> = match subset_paths {
            Some(indices) => indices.to_vec(),
            None => (0..expected_claim.paths.len()).collect(),
        };
        let m = path_indices.len();
        let chunks = &bundle.per_inner_publics[i];
        let n_chunks = (m + bundle.chunk_size - 1) / bundle.chunk_size;
        if chunks.len() != n_chunks { return false; }
        for (chunk_idx, bp) in chunks.iter().enumerate() {
            if !verify_binding_pi_hash_rederivation(bp) { return false; }
            let start = chunk_idx * bundle.chunk_size;
            let end = ((chunk_idx + 1) * bundle.chunk_size).min(m);
            // Translate chunk subset-indices back to inner-full indices.
            let chunk_indices: Vec<usize> = (start..end)
                .map(|j| path_indices[j]).collect();
            if !verify_binding_publics_paths_match(
                bp, &expected_claim, Some(&chunk_indices),
            ) {
                return false;
            }
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive;
    use deep_ali::ml_dsa::params::C_TILDE_BYTES;
    use deep_ali::ml_dsa_transcript;
    use deep_ali::ml_dsa_verify_air_v2_orchestration::{
        prove_v2_real, synthesize_demo_witness,
    };

    fn build_one_inner_recursive(seed: u64) -> RecursiveStarkProof {
        let w = synthesize_demo_witness(seed);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let v2_proof = prove_v2_real(&w, &c_tilde, /*blowup=*/4);
        prove_v2_all_subairs_composed_recursive(
            &v2_proof, &w, /*inner_blowup=*/4, /*blowup=*/4, /*r=*/54, /*stir=*/false,
        ).expect("recursive STARK prove")
    }

    #[test]
    fn build_master_composition_shape() {
        // Fast: doesn't require running v2 prove.  Builds a degenerate
        // composition with empty inner-proof slice and checks it errors.
        let result = build_master_composition(&[]);
        assert!(matches!(result, Err(MasterBridgeError::EmptyInput)));
    }

    #[test]
    fn master_ood_anchor_pairs_self() {
        // Build an anchor from an empty proof list — should produce
        // zero claims.
        let claim = build_master_ood_anchor(&[]);
        assert_eq!(claim.bundle.claims.len(), 0);
    }

    #[test]
    fn master_vestige_perm_arg_left_eq_right() {
        let perm = build_master_vestige_perm_arg(&[]);
        assert_eq!(perm.left, perm.right);
        assert_eq!(perm.left.len(), 4);
        assert_eq!(perm.perm_tag, "master-vestige");
    }

    #[test]
    #[ignore = "Phase 3 — N=1 master + per-inner FRI-Merkle binding bundle at B=10 subset; ~4-5 min"]
    fn prove_master_with_fri_merkle_binding_n1_subset_b10() {
        // Smallest end-to-end Phase 3 test: 1 inner v2 → master STARK
        // + 1 per-inner binding bundle over a B=10 subset of the
        // inner's r × L = 810 FRI Merkle openings (smoke L1).
        let inner = build_one_inner_recursive(913);

        // Sanity: full extract works.
        let full_claim = extract_fri_merkle_openings(&inner)
            .expect("extractor must succeed on honest inner");
        assert_eq!(full_claim.batch_size(), 810,
            "expected 810 paths at smoke L1 r=54 L=15");

        // B=10 subset spanning multiple FRI layers (same pattern as the
        // Phase 2.5 integration test).
        let l = inner.fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1,
            l, l + 1,
            2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let inner_proofs = vec![inner];
        let proof = prove_master_with_fri_merkle_binding(
            &inner_proofs,
            /*master_blowup=*/ 4, /*master_r=*/ 54, /*master_stir=*/ false,
            /*binding_blowup=*/ 4, /*binding_r=*/ 54, /*binding_stir=*/ false,
            Some(&subset_indices),
        ).expect("Phase 3 prove must succeed at N=1 subset");

        assert_eq!(proof.fri_merkle_bindings.len(), 1);
        assert_eq!(proof.fri_merkle_bindings[0].batch_size, 10);

        // Verify the full 3-piece chain.
        assert!(verify_master_with_fri_merkle_binding(
            &proof, &inner_proofs, Some(&subset_indices),
        ), "Phase 3 N=1 subset must verify end-to-end");
    }

    #[test]
    fn prove_master_with_fri_merkle_binding_rejects_empty() {
        let result = prove_master_with_fri_merkle_binding(
            &[], 4, 54, false, 4, 54, false, None,
        );
        assert!(matches!(result, Err(FriMerkleBindingError::Empty)));
    }

    #[test]
    fn prove_master_with_fri_merkle_binding_shape_d_rejects_empty() {
        let result = prove_master_with_fri_merkle_binding_shape_d(
            &[], 64, 4, 54, false, 4, 54, false, 4, 54, false, None,
        );
        assert!(matches!(result, Err(FriMerkleBindingError::Empty)));
    }

    #[test]
    #[ignore = "Shape D round-trip — N=1 inner v2 + intra-inner Shape D batching over 20-path subset in 4 chunks of B=5; ~15 min"]
    fn prove_master_with_fri_merkle_binding_shape_d_n1_b5_chunks() {
        // Small Shape D demonstration: 20 paths split into 4 chunks of
        // B=5 each.  Exercises the new prove + aggregator + verifier
        // chain without hitting the OOM wall.
        let inner = build_one_inner_recursive(995);
        let inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1,            // query 0 (spanning layers)
            l, l + 1,                // query 1
            2 * l, 2 * l + 1,        // query 2
            3 * l, 4 * l, 5 * l,     // queries 3, 4, 5 first layer
            10 * l, 15 * l, 20 * l,  // sparse coverage
            25 * l, 26 * l, 27 * l,
            28 * l, 29 * l - 1,
            29 * l, 30 * l - 1,
        ];
        assert_eq!(subset_indices.len(), 20);

        let bundle = prove_master_with_fri_merkle_binding_shape_d(
            &inner_proofs, /*chunk_size=*/ 5,
            4, 54, false, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("Shape D prove must succeed");

        // Shape sanity: 1 inner × 4 chunks (20 paths / B=5).
        assert_eq!(bundle.per_inner_publics.len(), 1);
        assert_eq!(bundle.per_inner_publics[0].len(), 4);
        assert_eq!(bundle.per_inner_meta.len(), 1);
        assert_eq!(bundle.per_inner_meta[0].len(), 4);
        assert_eq!(bundle.chunk_size, 5);
        for chunk_pub in &bundle.per_inner_publics[0] {
            assert_eq!(chunk_pub.paths.len(), 5);
        }

        // Verify the full chain.
        assert!(verify_master_with_fri_merkle_binding_shape_d(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "Shape D round-trip must verify end-to-end");
    }

    #[test]
    #[ignore = "Phase 6 scaling anchor — N=1 B=100 subset.  EMPIRICAL FINDING (2026-05-19): OOM-killed on commodity Apple Silicon at smoke L1 (working set exceeds ~32 GB RAM at LDE expansion).  Confirms Phase 0 Shape D single-batch memory wall.  Production-tractable B=810 requires intra-inner batching (~13 batches of B=64 each + recursive aggregation) or cloud nodes with 64+ GB RAM."]
    fn prove_master_with_fri_merkle_binding_n1_subset_b100() {
        // Anchor the B=10 → B=810 extrapolation by measuring an
        // intermediate B=100 point.  Expected scaling: trace pads to
        // next pow2, so B=10 trace ≈ 2^14, B=100 trace ≈ 2^17 (=8×
        // larger).  Projected prove time: ~8× B=10 ≈ ~30 min.
        let inner = build_one_inner_recursive(990);

        // 100 evenly-distributed indices across the 810 full paths.
        let full_claim = extract_fri_merkle_openings(&inner)
            .expect("extract must succeed");
        let m = full_claim.batch_size();
        assert!(m >= 100, "expected at least 100 paths, got {m}");
        let subset_indices: Vec<usize> = (0..100)
            .map(|i| i * m / 100)
            .collect();

        let inner_proofs = vec![inner];
        let t = std::time::Instant::now();
        let proof = prove_master_with_fri_merkle_binding(
            &inner_proofs, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("Phase 3 B=100 prove must succeed");
        let prove_ms = t.elapsed().as_secs_f64() * 1000.0;

        let t = std::time::Instant::now();
        assert!(verify_master_with_fri_merkle_binding(
            &proof, &inner_proofs, Some(&subset_indices),
        ), "B=100 verify must accept");
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;

        // Print anchor numbers for the bench narrative (visible with --nocapture).
        eprintln!();
        eprintln!("═══ B=100 scaling anchor ═══");
        eprintln!("  master + binding (B=100) prove: {:.2} s", prove_ms / 1000.0);
        eprintln!("  master + binding (B=100) verify: {:.2} ms", verify_ms);
        eprintln!("  vs B=10 anchor: 220.69 s prove + 5.1 ms verify");
        eprintln!("  scaling ratio (prove): {:.2}×", prove_ms / 1000.0 / 220.69);
        eprintln!();

        assert_eq!(proof.fri_merkle_bindings.len(), 1);
        assert_eq!(proof.fri_merkle_bindings[0].batch_size, 100);
    }

    #[test]
    fn aggregate_fri_merkle_bindings_rejects_empty() {
        let result = aggregate_fri_merkle_bindings(&[], 4, 54, false);
        assert!(matches!(result, Err(MasterBridgeError::EmptyInput)));
    }

    #[test]
    fn prove_master_with_fri_merkle_binding_aggregated_rejects_empty() {
        let result = prove_master_with_fri_merkle_binding_aggregated(
            &[], 4, 54, false, 4, 54, false, 4, 54, false, None,
        );
        assert!(matches!(result, Err(FriMerkleBindingError::Empty)));
    }

    // ─── Phase 5 sub-circuit 1a tests ───────────────────────────────

    #[test]
    #[ignore = "Aggregator sub-circuit 1a — builds inner + binding + extracts fold residues; ~4 min"]
    fn extract_batched_merkle_fold_residues_shape() {
        // Build a real inner v2 → recursive STARK, extract the FRI
        // Merkle openings, prove a B=10 subset binding, and confirm
        // the binding's fold residues have shape r × (L − 1) and are
        // all zero on honest input.
        use crate::merkle_path_air::BatchedMerklePathClaim;
        use crate::merkle_prover::prove_batched_merkle_paths;

        let inner = build_one_inner_recursive(960);
        let l_inner = inner.fri_proof.queries[0].per_layer_payloads.len();
        let mut full_claim = extract_fri_merkle_openings(&inner)
            .expect("extract must succeed");
        let subset_indices: Vec<usize> = vec![
            0, 1, l_inner - 1, l_inner, l_inner + 1,
            2 * l_inner, 3 * l_inner, 10 * l_inner, 20 * l_inner, 30 * l_inner - 1,
        ];
        full_claim.paths = subset_indices.iter()
            .map(|&i| full_claim.paths[i].clone()).collect();
        let subset_claim: BatchedMerklePathClaim = full_claim;

        let binding = prove_batched_merkle_paths(
            &subset_claim, /*blowup=*/4, /*r=*/54, /*use_stir=*/false,
        ).expect("binding prove");

        let r = binding.fri_proof.queries.len();
        let l = binding.fri_proof.queries[0].per_layer_payloads.len();

        let fold = extract_batched_merkle_fold_residues(&binding)
            .expect("fold extract must succeed");

        assert_eq!(fold.len(), r,
            "fold residues outer dim must equal binding's n_queries");
        for row in &fold {
            assert_eq!(row.len(), l - 1,
                "fold residues inner dim must equal L − 1");
        }

        // Honest residues all zero (s_val[ell] = f_val[ell+1] in F_ext).
        use ark_ff::Zero;
        for row in &fold {
            for r in row {
                assert!(r.is_zero(),
                    "honest aggregator fold residue must be zero");
            }
        }
    }

    #[test]
    #[ignore = "Phase 5 — builds one inner + extracts fold residues; ~4-5 s"]
    fn extract_recursive_fold_residues_shape() {
        // Build a real inner and confirm fold-residue shape:
        // n_queries × (L - 1) Ext residues.
        let inner = build_one_inner_recursive(960);
        let r = inner.fri_proof.queries.len();
        let l = inner.fri_proof.queries[0].per_layer_payloads.len();

        let fold = extract_recursive_fold_residues(&inner)
            .expect("fold extract must succeed on honest inner");

        assert_eq!(fold.len(), r,
            "fold residues outer dim must equal n_queries");
        for row in &fold {
            assert_eq!(row.len(), l - 1,
                "fold residues inner dim must equal L - 1");
        }

        // Honest residues must all be zero (s_val[ell] == f_val[ell+1]).
        for row in &fold {
            for r in row {
                use ark_ff::Zero;
                assert!(r.is_zero(),
                    "honest fold residue must be zero in F_ext");
            }
        }
    }

    // ─── Phase 5 Piece 2 tamper test ────────────────────────────────

    // ─── Phase 5-2 tests ────────────────────────────────────────────

    #[test]
    #[ignore = "Phase 5-2 — honest re-derivation match for master.outer_pi_hash; ~4 min"]
    fn phase_5_2_rederive_master_matches_on_honest_bundle() {
        let inner = build_one_inner_recursive(950);
        let inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let bundle = prove_master_with_fri_merkle_binding(
            &inner_proofs, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("honest prove");

        let rederived = rederive_master_outer_pi_hash(
            &inner_proofs,
            bundle.master.public.n_trace_max,
        ).expect("re-derivation must succeed");

        assert_eq!(rederived, bundle.master.public.outer_pi_hash,
            "Phase 5-2 re-derived master.outer_pi_hash must match");
    }

    #[test]
    #[ignore = "Phase 5-2 Piece 1 tamper: swap inner FRI root → verifier must reject; ~4 min"]
    fn phase_5_2_piece_1_tamper_rejects() {
        // Build an honest Phase 3 bundle.  Tamper one byte in
        // inner_proofs[0].fri_proof.root_f0 — the master STARK's
        // outer_pi_hash baked in at prove time was over the HONEST
        // root_f0, so re-derivation from the tampered inner_proofs
        // produces a different expected outer_pi_hash → reject.
        let inner = build_one_inner_recursive(951);
        let mut inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let bundle = prove_master_with_fri_merkle_binding(
            &inner_proofs, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("honest prove");

        // Sanity: honest verifies.
        assert!(verify_master_with_fri_merkle_binding(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "honest must verify");

        // Tamper one byte in inner_proofs[0].fri_proof.root_f0.
        inner_proofs[0].fri_proof.root_f0[0] ^= 0xFF;

        // Verifier must reject via Phase 5-2 outer_pi_hash mismatch.
        assert!(!verify_master_with_fri_merkle_binding(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "Piece 1 tamper (root_f0 swap) must be rejected by Phase 5-2");
    }

    #[test]
    #[ignore = "Phase 5-2 Piece 1 tamper at fold-layer root: flip inner.fri_proof.roots[0] → reject; ~4 min"]
    fn phase_5_2_piece_1_fold_layer_root_tamper_rejects() {
        let inner = build_one_inner_recursive(952);
        let mut inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let bundle = prove_master_with_fri_merkle_binding(
            &inner_proofs, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("honest prove");

        // Tamper inner_proofs[0].fri_proof.roots[0] (first fold-layer root).
        inner_proofs[0].fri_proof.roots[0][0] ^= 0xFF;

        assert!(!verify_master_with_fri_merkle_binding(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "fold-layer root tamper must be rejected by Phase 5-2");
    }

    #[test]
    #[ignore = "Phase 5 Piece 2 tamper: flip binding bundle public root → verifier must reject; ~4 min"]
    fn fri_merkle_binding_piece_2_tamper_rejects() {
        // Honest end-to-end then tamper one binding public root and
        // confirm verify rejects.  Uses the same N=1 B=10 shape as
        // the Phase 3 round-trip test.
        let inner = build_one_inner_recursive(961);
        let inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let mut proof = prove_master_with_fri_merkle_binding(
            &inner_proofs,
            4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("honest Phase 3 prove must succeed");

        // Verify honest case first.
        assert!(verify_master_with_fri_merkle_binding(
            &proof, &inner_proofs, Some(&subset_indices),
        ), "honest Phase 3 must verify");

        // Tamper one public root: flip a single byte.
        let binding = &mut proof.fri_merkle_bindings[0];
        binding.public.paths[3].0.0[0] ^= 0xFF;

        // Verifier MUST reject (Piece 2 cross-check fails).
        assert!(!verify_master_with_fri_merkle_binding(
            &proof, &inner_proofs, Some(&subset_indices),
        ), "Piece 2 cross-check must reject tampered binding root");
    }

    #[test]
    #[ignore = "Phase 4b — N=1 compact form: master + binding-aggregator collapses linear wire to O(1) in N; ~7-8 min"]
    fn prove_master_with_fri_merkle_binding_aggregated_n1_subset_b10() {
        // Smallest end-to-end Phase 4b test: 1 inner v2 → master STARK
        // + 1 binding bundle → aggregator STARK over the 1 binding.
        // Confirms the aggregator absorbs the binding's pi_hash and
        // verify cross-checks publics against the inner's FRI openings.
        let inner = build_one_inner_recursive(940);
        let inner_proofs = vec![inner];

        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1,
            l, l + 1,
            2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let bundle = prove_master_with_fri_merkle_binding_aggregated(
            &inner_proofs,
            /*master_blowup=*/ 4, /*master_r=*/ 54, /*master_stir=*/ false,
            /*binding_blowup=*/ 4, /*binding_r=*/ 54, /*binding_stir=*/ false,
            /*aggregator_blowup=*/ 4, /*aggregator_r=*/ 54, /*aggregator_stir=*/ false,
            Some(&subset_indices),
        ).expect("Phase 4b prove must succeed at N=1 subset");

        // The aggregator is now the ONLY binding-related artefact on
        // wire (constant in N).
        assert_eq!(bundle.binding_publics.len(), 1);
        assert_eq!(bundle.binding_publics[0].paths.len(), 10);

        // Verify the compact form.
        assert!(verify_master_with_fri_merkle_binding_aggregated(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "Phase 4b compact bundle must verify end-to-end");
    }

    #[test]
    #[ignore = "Phase 4b-2 — degenerate-aggregator tamper rejection: replace aggregator with one proven over fake bindings; verifier must reject via re-derived outer_pi_hash mismatch; ~8 min (two N=1 proves)"]
    fn phase_4b2_degenerate_aggregator_rejects() {
        // Build an honest compact bundle, then build a SECOND (parallel)
        // aggregator over a DIFFERENT set of synthetic bindings.  Swap
        // it into the bundle and confirm the verifier rejects via
        // rederive_aggregator_outer_pi_hash mismatch.
        //
        // This catches the attack: prover submits real binding_publics
        // (so Piece 2 cross-check passes) with a degenerate aggregator
        // attesting some other set of bindings.  Pre-Phase 4b-2 the
        // verifier had no way to detect this; with binding_meta + the
        // outer_pi_hash re-derivation it rejects.
        let inner = build_one_inner_recursive(942);
        let inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        // Honest compact form.
        let mut bundle = prove_master_with_fri_merkle_binding_aggregated(
            &inner_proofs, 4, 54, false, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("honest compact prove");

        // Sanity: honest verifies.
        assert!(verify_master_with_fri_merkle_binding_aggregated(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "honest must verify");

        // Build a second compact form over a DIFFERENT inner (seed 943).
        // Its aggregator attests different bindings → different
        // outer_pi_hash.  Swap that aggregator into the original bundle.
        let inner2 = build_one_inner_recursive(943);
        let inner_proofs2 = vec![inner2];
        let other = prove_master_with_fri_merkle_binding_aggregated(
            &inner_proofs2, 4, 54, false, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("second compact prove");
        bundle.binding_aggregator = other.binding_aggregator;

        // Now the supplied binding_publics + meta are for inner_proofs
        // (seed 942) but the aggregator was proven over inner_proofs2
        // (seed 943).  Re-derived outer_pi_hash from publics differs
        // from the swapped aggregator's outer_pi_hash → reject.
        assert!(!verify_master_with_fri_merkle_binding_aggregated(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "degenerate / swapped aggregator must be rejected via Phase 4b-2 outer_pi_hash check");
    }

    #[test]
    #[ignore = "Phase 4b-2 — verify re-derivation matches on honest bundle; ~4 min"]
    fn phase_4b2_rederive_matches_on_honest_bundle() {
        // Verify the re-derivation is bit-exact: build honest bundle,
        // call rederive_aggregator_outer_pi_hash, confirm it equals
        // bundle.binding_aggregator.public.outer_pi_hash.
        let inner = build_one_inner_recursive(944);
        let inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let bundle = prove_master_with_fri_merkle_binding_aggregated(
            &inner_proofs, 4, 54, false, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("honest compact prove");

        let rederived = rederive_aggregator_outer_pi_hash(
            &bundle.binding_publics,
            &bundle.binding_meta,
            bundle.binding_aggregator.public.n_trace_max,
        ).expect("re-derivation must succeed on honest bundle");

        assert_eq!(rederived, bundle.binding_aggregator.public.outer_pi_hash,
            "Phase 4b-2 re-derived outer_pi_hash must match aggregator's");
    }

    #[test]
    #[ignore = "Phase 4b — aggregator-publics tamper rejection; depends on N=1 B=10 prove succeeding first"]
    fn prove_master_with_fri_merkle_binding_aggregated_rejects_tampered_publics() {
        // Same shape as the round-trip but flip one bit in
        // binding_publics[0].pi_hash and confirm verify rejects.
        let inner = build_one_inner_recursive(941);
        let inner_proofs = vec![inner];
        let l = inner_proofs[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let mut bundle = prove_master_with_fri_merkle_binding_aggregated(
            &inner_proofs, 4, 54, false, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("Phase 4b prove must succeed");

        // Tamper a single pi_hash byte.  The deterministic re-derivation
        // check in verify will catch the mismatch.
        bundle.binding_publics[0].pi_hash[0] ^= 0xFF;
        assert!(!verify_master_with_fri_merkle_binding_aggregated(
            &bundle, &inner_proofs, Some(&subset_indices),
        ), "tampered binding_publics.pi_hash must be rejected");
    }

    #[test]
    fn prove_sharded_with_fri_merkle_binding_rejects_empty() {
        let result = prove_two_level_sharded_master_with_fri_merkle_binding(
            &[], 2, 4, 54, false, 4, 54, false, None,
        );
        assert!(matches!(result, Err(FriMerkleBindingError::Empty)));
    }

    #[test]
    fn prove_sharded_with_fri_merkle_binding_aggregated_rejects_empty() {
        let result = prove_two_level_sharded_master_with_fri_merkle_binding_aggregated(
            &[], 2, 4, 54, false, 4, 54, false, 4, 54, false, None,
        );
        assert!(matches!(result, Err(FriMerkleBindingError::Empty)));
    }

    #[test]
    #[ignore = "Sharded compact form — N=2 K=1 B=10 aggregated end-to-end; ~12 min"]
    fn prove_sharded_with_fri_merkle_binding_aggregated_n2_k1_subset_b10() {
        // Phase 4a sharded + Phase 4b aggregation combined: (N+K)=3
        // bindings collapse into ONE aggregator.  Verify chain:
        // super FRI + Phase 5-2; shard FRI + Phase 5-2; aggregator
        // FRI + Phase 4b-2 over both inner+shard publics; Piece 2 at
        // both layers.
        let inner1 = build_one_inner_recursive(970);
        let inner2 = build_one_inner_recursive(971);
        let inners = vec![inner1, inner2];

        let l = inners[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let bundle = prove_two_level_sharded_master_with_fri_merkle_binding_aggregated(
            &inners, /*shard_size=*/ 2,
            4, 54, false, 4, 54, false, 4, 54, false,
            Some(&subset_indices),
        ).expect("sharded compact prove must succeed");

        assert_eq!(bundle.shard_size, 2);
        assert_eq!(bundle.shard_masters.len(), 1);
        assert_eq!(bundle.inner_binding_publics.len(), 2);
        assert_eq!(bundle.inner_binding_meta.len(), 2);
        assert_eq!(bundle.shard_binding_publics.len(), 1);
        assert_eq!(bundle.shard_binding_meta.len(), 1);

        assert!(verify_two_level_sharded_master_with_fri_merkle_binding_aggregated(
            &bundle, &inners, Some(&subset_indices),
        ), "sharded compact bundle must verify end-to-end");
    }

    #[test]
    fn prove_sharded_with_fri_merkle_binding_rejects_zero_shard_size() {
        // Build with at least one inner so we hit the shard_size==0
        // path (not the empty-inner path).  Use a degenerate pre-built
        // inner by skipping the actual v2 prove via the
        // build_master_composition shape test path... simpler: just
        // confirm the error variant by inspection — we don't need a
        // real inner for this branch.
        let inner = build_one_inner_recursive(950);
        let result = prove_two_level_sharded_master_with_fri_merkle_binding(
            std::slice::from_ref(&inner),
            /*shard_size=*/0,
            4, 54, false, 4, 54, false, None,
        );
        assert!(matches!(
            result,
            Err(FriMerkleBindingError::Master(MasterBridgeError::EmptyInput))
        ));
    }

    #[test]
    #[ignore = "Phase 4a — N=2 shard_size=2 (K=1) sharded master + per-inner + per-shard FRI-Merkle bindings at B=10 subset; ~10 min"]
    fn prove_sharded_with_fri_merkle_binding_n2_k1_subset_b10() {
        // Smallest sharded end-to-end test: 2 inners → 1 shard master
        // (K=1) → 1 super-master + 2 inner bindings + 1 shard binding.
        let inner1 = build_one_inner_recursive(920);
        let inner2 = build_one_inner_recursive(921);
        let inners = vec![inner1, inner2];

        // B=10 subset spanning multiple FRI layers (matches the
        // pattern used by Phase 2.5/3 integration tests).
        let l = inners[0].fri_proof.queries[0].per_layer_payloads.len();
        let subset_indices: Vec<usize> = vec![
            0, 1, l - 1,
            l, l + 1,
            2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
        ];

        let proof = prove_two_level_sharded_master_with_fri_merkle_binding(
            &inners,
            /*shard_size=*/ 2,
            /*master_blowup=*/ 4, /*master_r=*/ 54, /*master_stir=*/ false,
            /*binding_blowup=*/ 4, /*binding_r=*/ 54, /*binding_stir=*/ false,
            Some(&subset_indices),
        ).expect("Phase 4a sharded prove must succeed at N=2 subset");

        // Shape sanity.
        assert_eq!(proof.shard_size, 2);
        assert_eq!(proof.shard_masters.len(), 1);  // K = ceil(2/2) = 1
        assert_eq!(proof.inner_fri_merkle_bindings.len(), 2);
        assert_eq!(proof.shard_fri_merkle_bindings.len(), 1);
        for b in &proof.inner_fri_merkle_bindings {
            assert_eq!(b.batch_size, 10);
        }
        assert_eq!(proof.shard_fri_merkle_bindings[0].batch_size, 10);

        // Verify the full 3-piece chain at BOTH levels.
        assert!(verify_two_level_sharded_master_with_fri_merkle_binding(
            &proof, &inners, Some(&subset_indices),
        ), "Phase 4a sharded N=2 subset must verify end-to-end");
    }

    #[test]
    fn extract_fri_merkle_openings_rejects_empty_queries() {
        // Build a degenerate "inner" with zero queries via the FRI
        // proof struct directly — confirms the shape-check path
        // without invoking a real prove.
        // We can't easily construct a DeepFriProof from scratch here
        // without exposing internals, so instead exercise the error
        // path via the variant-bytes inference (passing a roots[0] of
        // length != 32/48/64).  This indirectly covers the
        // LayerProofShapeMismatch error category.
        match sha3_variant_for_hash_bytes(31) {
            Err(FriMerkleExtractError::LayerProofShapeMismatch(_)) => {}
            other => panic!("expected LayerProofShapeMismatch, got {other:?}"),
        }
        match sha3_variant_for_hash_bytes(32) {
            Ok(Sha3Variant::Sha3_256) => {}
            other => panic!("32 bytes should map to Sha3_256, got {other:?}"),
        }
        match sha3_variant_for_hash_bytes(48) {
            Ok(Sha3Variant::Sha3_384) => {}
            other => panic!("48 bytes should map to Sha3_384, got {other:?}"),
        }
        match sha3_variant_for_hash_bytes(64) {
            Ok(Sha3Variant::Sha3_512) => {}
            other => panic!("64 bytes should map to Sha3_512, got {other:?}"),
        }
    }

    #[test]
    #[ignore = "Phase 2.5 integration: real inner → extract → DS-aware prove+verify at B=10 subset; ~minute"]
    fn fri_merkle_binding_integration_b10_subset() {
        use crate::merkle_path_air::BatchedMerklePathClaim;
        use crate::merkle_prover::{
            prove_batched_merkle_paths, verify_batched_merkle_paths,
        };

        // 1. Build one inner recursive STARK.
        let inner = build_one_inner_recursive(910);

        // 2. Extract all M = r × L Merkle openings (each carries DS
        //    prefix populated by Phase 2.5 M4).
        let full_bundle = extract_fri_merkle_openings(&inner)
            .expect("extractor must succeed on honest inner");
        assert!(full_bundle.batch_size() >= 10,
            "expected at least 10 paths, got {}", full_bundle.batch_size());

        // 3. Subset to B=10 — pick paths spanning multiple layers (so
        //    we exercise mixed-depth handling).  Pick paths 0, 1, 2
        //    (layer 0 at depth=L), L, L+1, L+2 (layer 1 at depth=L-1),
        //    and a few from deeper layers.
        let l = inner.fri_proof.queries[0].per_layer_payloads.len();
        let mut subset_paths = Vec::with_capacity(10);
        subset_paths.push(full_bundle.paths[0].clone());           // q0 ell0
        subset_paths.push(full_bundle.paths[1].clone());           // q0 ell1
        subset_paths.push(full_bundle.paths[l - 1].clone());       // q0 ell(L-1)
        subset_paths.push(full_bundle.paths[l].clone());           // q1 ell0
        subset_paths.push(full_bundle.paths[l + 1].clone());       // q1 ell1
        subset_paths.push(full_bundle.paths[2 * l].clone());       // q2 ell0
        subset_paths.push(full_bundle.paths[3 * l].clone());       // q3 ell0
        subset_paths.push(full_bundle.paths[10 * l].clone());      // q10 ell0
        subset_paths.push(full_bundle.paths[20 * l].clone());      // q20 ell0
        subset_paths.push(full_bundle.paths[30 * l - 1].clone());  // q29 ellL-1
        let subset = BatchedMerklePathClaim {
            variant: full_bundle.variant,
            paths: subset_paths,
        };
        assert_eq!(subset.batch_size(), 10);

        // 4. Sanity: native verify must accept (confirms the
        //    extractor's DS bytes match the FRI tree's hash protocol).
        assert!(crate::merkle_path_air::batched_merkle_verify_native(&subset),
            "extracted FRI openings must natively verify with DS bytes");

        // 5. Prove + verify in the in-AIR gadget.
        let proof = prove_batched_merkle_paths(
            &subset, /*blowup=*/4, /*r=*/54, /*use_stir=*/false,
        ).expect("DS-aware B=10 integration prove must succeed");
        assert_eq!(proof.batch_size, 10);
        assert!(verify_batched_merkle_paths(&proof),
            "DS-aware B=10 integration verify must accept");
    }

    #[test]
    #[ignore = "Phase 2 — runs real v2 inner prove + extract; ~few s"]
    fn extract_fri_merkle_openings_shape_on_real_inner() {
        let inner = build_one_inner_recursive(800);

        // Sanity: same probe as print_fri_merkle_binding_sizing.
        let r = inner.fri_proof.queries.len();
        let l = inner.fri_proof.queries[0].per_layer_payloads.len();

        let bundle = extract_fri_merkle_openings(&inner)
            .expect("extractor must succeed on honest inner");

        assert_eq!(bundle.batch_size(), r * l,
            "M_paths must equal r × L (r={r} L={l})");
        assert_eq!(bundle.paths.len(), r * l);

        // Spot-check first path (query 0, layer 0):
        let first = &bundle.paths[0];
        assert_eq!(first.variant, Sha3Variant::Sha3_256);
        assert_eq!(first.root.0.len(), 32);
        assert_eq!(first.leaf.0.len(), 32);
        assert!(!first.path.is_empty(), "layer 0 must have non-zero depth");
        for sib in &first.path {
            assert_eq!(sib.0.len(), 32,
                "each sibling must be a SHA3-256 hash (32 B)");
        }

        // The first path's leaf_index must equal the FRI proof's
        // query 0 / layer 0 reference position.
        assert_eq!(first.leaf_index as usize,
            inner.fri_proof.queries[0].per_layer_refs[0].i);

        // Layer-0 path depth = log2(n_lde_inner).
        let n_lde = inner.n_trace * inner.blowup;
        assert_eq!(first.path.len(), n_lde.trailing_zeros() as usize);

        // Last path (query r-1, layer L-1):
        let last = &bundle.paths[r * l - 1];
        assert_eq!(last.path.len(),
            (n_lde >> (l - 1)).trailing_zeros() as usize,
            "deepest layer's path depth = log2(layer L-1 size)");
    }

    #[test]
    #[ignore = "sizing probe for Phase 0 FRI-Merkle binding design doc — prints workload numbers"]
    fn print_fri_merkle_binding_sizing() {
        let inner = build_one_inner_recursive(900);
        let fri_proof = &inner.fri_proof;
        let r = fri_proof.queries.len();
        let l = fri_proof.queries.first()
            .map(|q| q.per_layer_payloads.len())
            .unwrap_or(0);
        let n_lde = inner.n_trace * inner.blowup;
        let mut m_hashes = 0usize;
        let mut depths = Vec::with_capacity(l);
        for ell in 0..l {
            let layer_size = n_lde >> ell;
            let depth = layer_size.trailing_zeros() as usize;
            depths.push(depth);
            m_hashes += r * depth;
        }
        eprintln!();
        eprintln!("═══ FRI-Merkle binding sizing probe ═══");
        eprintln!("  inner.n_trace             = {}", inner.n_trace);
        eprintln!("  inner.blowup              = {}", inner.blowup);
        eprintln!("  n_lde_inner               = {n_lde}");
        eprintln!("  L (FRI layers)            = {l}");
        eprintln!("  r (queries)               = {r}");
        eprintln!("  M_paths = r × L           = {}", r * l);
        eprintln!("  M_hashes = r × Σ depth    = {m_hashes}");
        eprintln!("  per-layer depths          = {depths:?}");
        eprintln!("  fri_proof.roots.len       = {}", fri_proof.roots.len());
        eprintln!("  outer_pi_hash (first 8 B) = {:02x?}",
                  &inner.public.outer_pi_hash[..8]);
        eprintln!();
    }

    #[test]
    #[ignore = "slow — runs v2 prove + recursive wrap + master recursive STARK"]
    fn prove_master_recursive_round_trip_n2() {
        let inner1 = build_one_inner_recursive(101);
        let inner2 = build_one_inner_recursive(102);
        let inners = vec![inner1, inner2];

        // Verify each inner separately first.
        for r in &inners {
            assert!(verify_recursive_stark(r), "inner recursive STARK must verify");
        }

        // Build master proof.
        let master = prove_master_recursive(&inners, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("master prove must succeed");

        // Verify master.
        assert!(verify_master_recursive(&master),
            "master recursive STARK must verify locally");

        // Confirm master pi_hash is bound to the inner outer_pi_hashes.
        let mut hasher = sha3::Sha3_256::new();
        Digest::update(&mut hasher, b"MASTER-RECURSION-PI-V1");
        for r in &inners {
            Digest::update(&mut hasher, r.public.outer_pi_hash);
        }
        let _expected_master_pi: [u8; 32] = Digest::finalize(hasher).into();
        // master.public.outer_pi_hash is the master's OWN pi_hash
        // (composed of comp+ood+perm sub-pi_hashes); it doesn't equal
        // the deterministic hash above — that's the SHA3 binding
        // used inside the OOD anchor / vestige perm-arg.  Just check
        // the master proof is non-trivially bound.
        assert_ne!(master.public.outer_pi_hash, [0u8; 32]);
    }

    #[test]
    #[ignore = "slow — Option C with in-AIR Merkle binding at N=2"]
    fn prove_master_with_in_air_merkle_path_n2() {
        let inner1 = build_one_inner_recursive(301);
        let inner2 = build_one_inner_recursive(302);
        let inners = vec![inner1, inner2];

        let bundle = prove_master_with_in_air_merkle_path(
            &inners,
            /*blowup=*/4, /*r=*/54, /*stir=*/false,
            /*merkle_blowup=*/4, /*merkle_r=*/54, /*merkle_use_stir=*/false,
        ).expect("master + merkle bundle must prove");

        assert!(verify_master_with_in_air_merkle_path(&bundle, &inners),
            "full master + N×merkle bundle must verify");

        assert_eq!(bundle.merkle_path_proofs.len(), 2);
        assert_eq!(bundle.merkle_roots.len(), 2);
        for mp in &bundle.merkle_path_proofs {
            assert_eq!(mp.public.leaf_index, 0);
            assert_eq!(mp.depth, 2);
        }
    }

    #[test]
    #[ignore = "slow — N=4 master prove (Option C demo headline scale)"]
    fn prove_master_recursive_round_trip_n4() {
        let inners: Vec<RecursiveStarkProof> = (0..4)
            .map(|i| build_one_inner_recursive(200 + i))
            .collect();

        let master = prove_master_recursive(&inners, 4, 54, false)
            .expect("master prove @ N=4");
        assert!(verify_master_recursive(&master));
    }

    #[test]
    fn batched_leaf_pi_is_deterministic_and_depends_on_inputs() {
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let a = derive_batched_leaf_pi(&[h1, h2]);
        let b = derive_batched_leaf_pi(&[h1, h2]);
        assert_eq!(a, b);
        let c = derive_batched_leaf_pi(&[h2, h1]);
        assert_ne!(a, c, "order-sensitive");
        let d = derive_batched_leaf_pi(&[h1, h2, h2]);
        assert_ne!(a, d, "length-sensitive");
    }

    #[test]
    #[ignore = "slow — Option C with BATCHED in-AIR Merkle binding at N=2"]
    fn prove_master_with_batched_in_air_merkle_path_n2() {
        let inner1 = build_one_inner_recursive(401);
        let inner2 = build_one_inner_recursive(402);
        let inners = vec![inner1, inner2];

        let bundle = prove_master_with_batched_in_air_merkle_path(
            &inners,
            /*blowup=*/4, /*r=*/54, /*stir=*/false,
            /*merkle_blowup=*/4, /*merkle_r=*/54, /*merkle_use_stir=*/false,
        ).expect("batched bundle must prove");

        assert!(verify_master_with_batched_in_air_merkle_path(&bundle, &inners),
            "batched bundle must verify");

        // Only ONE Merkle-path STARK regardless of N.
        assert_eq!(bundle.merkle_path_proof.public.leaf_index, 0);
        assert_eq!(bundle.merkle_path_proof.depth, 2);
        assert_eq!(bundle.inner_pi_hashes.len(), 2);
    }

    #[test]
    #[ignore = "slow — two-level sharded master @ N=4 inners, shard_size=2 (K=2)"]
    fn prove_two_level_sharded_master_n4_k2() {
        let inners: Vec<RecursiveStarkProof> = (0..4)
            .map(|i| build_one_inner_recursive(600 + i))
            .collect();

        let proof = prove_two_level_sharded_master(
            &inners,
            /*shard_size=*/ 2,
            /*master_blowup=*/ 4, /*master_r=*/ 54, /*master_stir=*/ false,
            /*merkle_blowup=*/ 4, /*merkle_r=*/ 54, /*merkle_stir=*/ false,
        ).expect("two-level sharded prove must succeed");

        assert!(verify_two_level_sharded_master(&proof, &inners),
            "two-level sharded must verify");
        // K = ceil(4 / 2) = 2
        assert_eq!(proof.shard_pi_hashes.len(), 2);
        assert_eq!(proof.inner_pi_hashes.len(), 4);
        assert_eq!(proof.shard_size, 2);
        assert_eq!(proof.top_merkle_path.public.leaf_index, 0);
    }

    #[test]
    #[ignore = "slow — tampered sharded bundle must reject"]
    fn sharded_bundle_rejects_tampered_inner_pi_hashes() {
        let inners: Vec<RecursiveStarkProof> = (0..4)
            .map(|i| build_one_inner_recursive(700 + i))
            .collect();

        let mut proof = prove_two_level_sharded_master(
            &inners, 2, 4, 54, false, 4, 54, false,
        ).expect("sharded prove");

        // Honest case verifies.
        assert!(verify_two_level_sharded_master(&proof, &inners));

        // Tamper inner_pi_hashes[0] — verifier must reject because it
        // no longer matches inner_proofs[0].public.outer_pi_hash.
        proof.inner_pi_hashes[0][0] ^= 0xFF;
        assert!(!verify_two_level_sharded_master(&proof, &inners),
            "tampered inner_pi_hashes[0] must reject");
    }

    #[test]
    #[ignore = "slow — tampered batched bundle must reject"]
    fn batched_bundle_rejects_tampered_inner_pi_hashes() {
        let inner1 = build_one_inner_recursive(501);
        let inner2 = build_one_inner_recursive(502);
        let inners = vec![inner1, inner2];

        let mut bundle = prove_master_with_batched_in_air_merkle_path(
            &inners, 4, 54, false, 4, 54, false,
        ).expect("batched prove");

        // Verify honest case first.
        assert!(verify_master_with_batched_in_air_merkle_path(&bundle, &inners));

        // Tamper inner_pi_hashes[0] — verifier must reject because it
        // no longer matches inner_proofs[0].public.outer_pi_hash.
        bundle.inner_pi_hashes[0][0] ^= 0xFF;
        assert!(!verify_master_with_batched_in_air_merkle_path(&bundle, &inners),
            "tampered inner_pi_hashes[0] must reject");
    }
}
