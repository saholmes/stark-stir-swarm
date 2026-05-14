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

use ark_ff::{One, Zero};

use deep_ali::fri::{
    deep_fri_prove, deep_fri_verify, DeepFriParams, DeepFriProof, FriDomain,
};
use deep_ali::sextic_ext::SexticExt;
use deep_ali::trace_import::lde_trace_columns;

use crate::composition::alphas_from_transcript;
use crate::fri_bridge::compute_single_row_indicator_lde;
use crate::merkle_path_air::{
    MerkleCrossRowConstraint, MerkleNode, MerklePathClaim, MerkleSpongeLayout,
    hop_current_col, hop_index_bit_col, hop_left_col, hop_right_col, hop_sibling_col,
    merkle_cross_row_constraints, synthesize_merkle_sponge_trace,
};
use crate::row_uniform::UniformAirConstraints;
use crate::sha3_absorb_air::{Sha3Variant, hash as sha3_hash};

type FBase = ark_goldilocks::Goldilocks;
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
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(MerklePathProverError::Internal(format!(
            "blowup must be power-of-2 >= 2; got {blowup}"
        )));
    }

    // 1. Synthesise composed trace.
    let layout = MerkleSpongeLayout::new(claim.variant, claim.depth(), 0);
    let (trace, computed_root) = synthesize_merkle_sponge_trace(claim, &layout)
        .map_err(|e| MerklePathProverError::Internal(format!("synthesis: {e}")))?;
    if computed_root != claim.root {
        return Err(MerklePathProverError::InvalidClaim(
            "synthesised root != claim's expected root (witness mismatch)".into()
        ));
    }

    // 2. Build public inputs + derive FS seeds.
    let public = MerklePathPublicInputs::for_root(
        claim.variant, claim.root.clone(), claim.leaf_index,
    );
    let mut seed_sponge_sel = public.pi_hash;  seed_sponge_sel[0] ^= 0xB1;
    let mut seed_sponge_alw = public.pi_hash;  seed_sponge_alw[0] ^= 0xB2;
    let mut seed_selection  = public.pi_hash;  seed_selection[0]  ^= 0xB3;
    let mut seed_cross_row  = public.pi_hash;  seed_cross_row[0]  ^= 0xB4;

    // 3. Convert UniformTrace to column-major Goldilocks, padded to
    //    next power of 2 rows.
    let width = layout.row_width();
    let n_trace = trace.n_rows.next_power_of_two();
    let n_lde = n_trace * blowup;
    let mut columns: Vec<Vec<FBase>> = Vec::with_capacity(width);
    for col in 0..width {
        let mut col_vec = Vec::with_capacity(n_trace);
        for row in 0..trace.n_rows {
            col_vec.push(FBase::from(trace.get(row, col) as u64));
        }
        for _ in trace.n_rows..n_trace {
            col_vec.push(FBase::from(0u64));
        }
        columns.push(col_vec);
    }

    // 4. LDE each column.
    let lde: Vec<Vec<FBase>> = lde_trace_columns(&columns, n_trace, blowup)
        .map_err(|e| MerklePathProverError::Internal(format!("LDE: {e}")))?;

    // 5. Build the sponge constraint set + derive its alphas.
    let air = UniformAirConstraints::for_schema(&layout.schema);
    let alphas_sponge_sel = alphas_from_transcript::<FBase>(&seed_sponge_sel, air.selected.len());
    let alphas_sponge_alw = alphas_from_transcript::<FBase>(&seed_sponge_alw, air.always.len());

    // 6. Compute c_eval per LDE row.  Three contribution sources:
    //    (a) sponge selected constraints (gated by sponge selectors)
    //    (b) sponge always constraints   (booleanity + threading)
    //    (c) merkle selection constraints (gated by hop-row indicators)
    //    (d) merkle cross-row constraints (gated by hop-row indicators,
    //        with cross-row reads at +blowup LDE step)
    let mut c_eval = vec![FBase::zero(); n_lde];

    // Sponge contributions.
    for r_idx in 0..n_lde {
        let mut acc = FBase::zero();
        for (j, c) in air.selected.iter().enumerate() {
            let alpha = alphas_sponge_sel[j];
            let sel_col = layout.schema.selector(c.selector);
            let sel_val = lde[sel_col][r_idx];
            let phi = eval_sponge_selected_op(&c.op, &lde, r_idx, n_lde, blowup);
            acc += alpha * sel_val * phi;
        }
        for (k, c) in air.always.iter().enumerate() {
            let alpha = alphas_sponge_alw[k];
            let phi = eval_sponge_always_op(&c.op, &lde, r_idx, n_lde, blowup);
            acc += alpha * phi;
        }
        c_eval[r_idx] = acc;
    }

    // Merkle selection contributions: at each hop row, add alpha *
    // indicator * (LeftSelect + RightSelect per bit).  Selection
    // shape: left - current - bit · (sibling - current).
    let n_hash_bits = claim.variant.output_bits();
    let alphas_selection = alphas_from_transcript::<FBase>(
        &seed_selection, layout.depth * 2 * n_hash_bits,
    );
    let mut alpha_idx = 0usize;
    for hop_idx in 0..layout.depth {
        let hop_row = layout.hop_starts[hop_idx];
        let indicator = compute_single_row_indicator_lde(hop_row, n_trace, blowup);
        let schema = &layout.schema;
        let bit_col = hop_index_bit_col(schema);
        for i in 0..n_hash_bits {
            let curr_col = hop_current_col(schema, i);
            let sib_col  = hop_sibling_col(schema, i);
            let l_col    = hop_left_col(schema, i);
            let r_col    = hop_right_col(schema, n_hash_bits, i);
            let alpha_l = alphas_selection[alpha_idx]; alpha_idx += 1;
            let alpha_r = alphas_selection[alpha_idx]; alpha_idx += 1;
            for r_idx in 0..n_lde {
                let ind = indicator[r_idx];
                if ind.is_zero() { continue; }
                let cur  = lde[curr_col][r_idx];
                let sib  = lde[sib_col][r_idx];
                let bit  = lde[bit_col][r_idx];
                let l_v  = lde[l_col][r_idx];
                let r_v  = lde[r_col][r_idx];
                // left  - cur - bit · (sib - cur)
                let phi_l = l_v - cur - bit * (sib - cur);
                // right - sib - bit · (cur - sib)
                let phi_r = r_v - sib - bit * (cur - sib);
                c_eval[r_idx] += alpha_l * ind * phi_l;
                c_eval[r_idx] += alpha_r * ind * phi_r;
            }
        }
    }

    // Merkle cross-row contributions: each constraint is Copy-shaped
    // between cells at row_a and row_b.  At LDE row r = row_a*blowup,
    // we want trace[row_a][col_a] = trace[row_b][col_b].  In LDE
    // arithmetic: lde[col_a][r] = lde[col_b][r + (row_b-row_a)*blowup]
    // cyclically.  Gated by indicator at row_a.
    let cross = merkle_cross_row_constraints(&layout);
    let alphas_xrow = alphas_from_transcript::<FBase>(&seed_cross_row, cross.len());
    // Pre-compute indicators per distinct anchor row to avoid recomputing.
    use std::collections::HashMap;
    let mut indicators: HashMap<usize, Vec<FBase>> = HashMap::new();
    for c in &cross {
        let anchor_row = match c {
            MerkleCrossRowConstraint::SpongeInputLeft  { absorb_row, .. } => *absorb_row,
            MerkleCrossRowConstraint::SpongeInputRight { absorb_row, .. } => *absorb_row,
            MerkleCrossRowConstraint::SpongeOutputThreading { final_iota_row, .. } => *final_iota_row,
        };
        indicators.entry(anchor_row)
            .or_insert_with(|| compute_single_row_indicator_lde(anchor_row, n_trace, blowup));
    }
    for (j, c) in cross.iter().enumerate() {
        let alpha = alphas_xrow[j];
        let (anchor_row, col_a, col_b, row_b) = match c {
            MerkleCrossRowConstraint::SpongeInputLeft { sponge_block_col, hop_left_col: l, absorb_row, hop_row } =>
                (*absorb_row, *sponge_block_col, *l, *hop_row),
            MerkleCrossRowConstraint::SpongeInputRight { sponge_block_col, hop_right_col: r_col, absorb_row, hop_row } =>
                (*absorb_row, *sponge_block_col, *r_col, *hop_row),
            MerkleCrossRowConstraint::SpongeOutputThreading { state_out_col, next_current_col, final_iota_row, next_hop_row } =>
                (*final_iota_row, *state_out_col, *next_current_col, *next_hop_row),
        };
        let ind = &indicators[&anchor_row];
        // shift = (row_b - anchor_row) * blowup (can be negative).
        let shift_signed = (row_b as i64 - anchor_row as i64) * blowup as i64;
        for r_idx in 0..n_lde {
            let ind_v = ind[r_idx];
            if ind_v.is_zero() { continue; }
            let r_b = (((r_idx as i64 + shift_signed).rem_euclid(n_lde as i64)) as usize) % n_lde;
            let a_val = lde[col_a][r_idx];
            let b_val = lde[col_b][r_b];
            c_eval[r_idx] += alpha * ind_v * (a_val - b_val);
        }
    }

    // 7. Build FRI domain + params + prove.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.pi_hash);
    if use_stir { params.stir = true; }

    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    Ok(MerklePathProof {
        public, fri_proof,
        depth: claim.depth(), n_trace, blowup, r, use_stir,
    })
}

/// Verify a Merkle path STARK proof.
pub fn verify_merkle_path(proof: &MerklePathProof) -> bool {
    let n_lde = proof.n_trace * proof.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, proof.r, 0xDEEFu64);
    params.public_inputs_hash = Some(proof.public.pi_hash);
    if proof.use_stir { params.stir = true; }
    deep_fri_verify::<Ext>(&params, &proof.fri_proof)
}

// ─── LDE constraint evaluators ──────────────────────────────────────
//
// Same shapes as `fri_bridge::eval_op_at_lde` but inlined here for the
// merkle prover's c_eval composition.

fn eval_sponge_selected_op(
    op: &crate::row_uniform::RowUniformOp,
    lde: &[Vec<FBase>],
    r: usize, n_lde: usize, blowup: usize,
) -> FBase {
    eval_row_uniform_op(op, lde, r, n_lde, blowup)
}

fn eval_sponge_always_op(
    op: &crate::row_uniform::RowUniformOp,
    lde: &[Vec<FBase>],
    r: usize, n_lde: usize, blowup: usize,
) -> FBase {
    eval_row_uniform_op(op, lde, r, n_lde, blowup)
}

fn eval_row_uniform_op(
    op: &crate::row_uniform::RowUniformOp,
    lde: &[Vec<FBase>],
    r: usize, n_lde: usize, blowup: usize,
) -> FBase {
    use crate::row_uniform::RowUniformOp;
    use ark_ff::Field;
    let two = FBase::one() + FBase::one();
    match *op {
        RowUniformOp::Xor { c, a, b } => {
            let a = lde[a.0][r]; let b = lde[b.0][r]; let c = lde[c.0][r];
            c - (a + b - two * a * b)
        }
        RowUniformOp::And { c, a, b } => {
            let a = lde[a.0][r]; let b = lde[b.0][r]; let c = lde[c.0][r];
            c - a * b
        }
        RowUniformOp::Not { c, a } => {
            let a = lde[a.0][r]; let c = lde[c.0][r];
            c - (FBase::one() - a)
        }
        RowUniformOp::Copy { c, a } => lde[c.0][r] - lde[a.0][r],
        RowUniformOp::XorConst { c, a, k } => {
            let a = lde[a.0][r]; let c = lde[c.0][r];
            let k = FBase::from(k as u64);
            c - (a + k - two * a * k)
        }
        RowUniformOp::Boolean { b } => {
            let b = lde[b.0][r];
            b * (b - FBase::one())
        }
        RowUniformOp::NextRowCopy { dst, src } => {
            let next_r = (r + blowup) % n_lde;
            lde[dst.0][next_r] - lde[src.0][r]
        }
    }
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
    #[ignore = "slow — exercises full FRI prove + verify round-trip"]
    fn round_trip_merkle_path_depth_2_smoke() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0x10 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 2);
        let proof = prove_merkle_path(&claim, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("prove must succeed on valid claim");
        assert!(verify_merkle_path(&proof),
            "honest prove + verify round-trip must accept");
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
