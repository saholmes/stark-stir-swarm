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
use crate::sha3_absorb_air::lane_to_bits;
use crate::merkle_path_air::{
    BatchedMerklePathClaim, BatchedMerklePathLayout,
    MerkleCrossRowConstraint, MerkleNode, MerklePathClaim, MerkleSpongeLayout,
    hop_current_col, hop_index_bit_col, hop_left_col, hop_right_col, hop_sibling_col,
    merkle_cross_row_constraints, synthesize_batched_merkle_sponge_trace,
    synthesize_merkle_sponge_trace,
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
            MerkleCrossRowConstraint::SpongeInputDsByte { absorb_row, .. } => *absorb_row,
        };
        indicators.entry(anchor_row)
            .or_insert_with(|| compute_single_row_indicator_lde(anchor_row, n_trace, blowup));
    }
    for (j, c) in cross.iter().enumerate() {
        let alpha = alphas_xrow[j];
        // DS-byte variant evaluates as `lde[col][r] - constant`; the
        // other three are pair-shaped `lde[col_a][r] - lde[col_b][r+shift]`.
        if let Some((anchor_row, col, ds_bit)) = c.as_ds_byte() {
            let ind = &indicators[&anchor_row];
            let constant = FBase::from(ds_bit as u64);
            for r_idx in 0..n_lde {
                let ind_v = ind[r_idx];
                if ind_v.is_zero() { continue; }
                c_eval[r_idx] += alpha * ind_v * (lde[col][r_idx] - constant);
            }
            continue;
        }
        let (anchor_row, col_a, col_b, row_b) = match c {
            MerkleCrossRowConstraint::SpongeInputLeft { sponge_block_col, hop_left_col: l, absorb_row, hop_row } =>
                (*absorb_row, *sponge_block_col, *l, *hop_row),
            MerkleCrossRowConstraint::SpongeInputRight { sponge_block_col, hop_right_col: r_col, absorb_row, hop_row } =>
                (*absorb_row, *sponge_block_col, *r_col, *hop_row),
            MerkleCrossRowConstraint::SpongeOutputThreading { state_out_col, next_current_col, final_iota_row, next_hop_row } =>
                (*final_iota_row, *state_out_col, *next_current_col, *next_hop_row),
            MerkleCrossRowConstraint::SpongeInputDsByte { .. } => unreachable!(),
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

    // 6b. Root-binding boundary: at the LAST final-ι row of the LAST
    //     hop, state_out's first N bits must equal the public root's
    //     bits.  Without this, the proof only attests to "some chain
    //     hashed to some root"; this boundary pins it to claim.root
    //     so the verifier knows it's THEIR root.
    let last_iota_row = layout.sponge_final_iota_row(claim.depth() - 1);
    let mut seed_root = public.pi_hash;  seed_root[0] ^= 0xB5;
    let alpha_root = alphas_from_transcript::<FBase>(&seed_root, 1)[0];
    let root_indicator = compute_single_row_indicator_lde(last_iota_row, n_trace, blowup);
    let output_lanes = claim.variant.output_bits() / 64;
    for lane in 0..output_lanes {
        let mut lane_u64 = 0u64;
        for j in 0..8 {
            lane_u64 |= (claim.root.0[8 * lane + j] as u64) << (8 * j);
        }
        let expected_bits = lane_to_bits(lane_u64);
        for bit in 0..64 {
            let col = layout.schema.state_out_bit(lane, bit);
            let expected = FBase::from(expected_bits[bit] as u64);
            for r_idx in 0..n_lde {
                let ind = root_indicator[r_idx];
                if ind.is_zero() { continue; }
                c_eval[r_idx] += alpha_root * ind * (lde[col][r_idx] - expected);
            }
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

// ─── Phase 1: Batched Merkle path STARK prover/verifier ──────────────
//
// Wraps `BatchedMerklePathClaim` (B Merkle paths under one variant)
// into a single DeepFriProof<Ext>.  The composed c_eval is the sum of
// per-block c_eval contributions — each block reuses the same selection
// + sponge + cross-row + root-binding machinery as `prove_merkle_path`,
// with row offsets read from `BatchedMerklePathLayout::blocks[j]`.
//
// Public inputs commit to ALL B per-path `(root, leaf_index, depth)`
// triples via a domain-separated SHA-3 hash so the verifier can
// reconstruct the same FS transcript.
//
// **Stage 3 milestone**: types + signatures only; prover/verifier
// bodies land in Stage 4 (next commit).  Calling either currently
// returns `MerklePathProverError::NotImplemented`.

/// Public inputs for a batched Merkle path STARK proof.  Statement:
/// > *I know B (leaf_j, path_j) pairs such that, for each j, hashing
/// > leaf_j up its tree using path_j by the bits of leaf_index_j
/// > yields root_j.*
///
/// All leaves and paths are private witness.  Per-path
/// `(root, leaf_index, depth)` triples are public.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchedMerklePathPublicInputs {
    pub variant: Sha3Variant,
    /// Per-sub-claim (root, leaf_index, depth) triples — public.
    pub paths: Vec<(MerkleNode, u64, usize)>,
    /// SHA3-256("WRAPPER-BATCHED-MERKLE-V1" || variant_tag || B(LE) ||
    ///   for j in 0..B: depth_j(LE) || root_j || leaf_index_j(LE)).
    /// Binds every per-path public statement into the FS transcript.
    pub pi_hash: [u8; 32],
}

impl BatchedMerklePathPublicInputs {
    /// Build public inputs from a `BatchedMerklePathClaim`.  Hash binds
    /// every (root, leaf_index, depth) triple under a unique
    /// domain-separated tag distinct from the single-path one.
    pub fn for_claim(claim: &BatchedMerklePathClaim) -> Self {
        let variant_tag: u8 = match claim.variant {
            Sha3Variant::Sha3_256 => 1,
            Sha3Variant::Sha3_384 => 3,
            Sha3Variant::Sha3_512 => 5,
        };
        let n_bytes = claim.variant.output_bytes();
        let b = claim.paths.len();

        let mut input = Vec::with_capacity(
            25 + 1 + 8 + b * (8 + n_bytes + 8),
        );
        input.extend_from_slice(b"WRAPPER-BATCHED-MERKLE-V1");
        input.push(variant_tag);
        input.extend_from_slice(&(b as u64).to_le_bytes());

        let mut paths = Vec::with_capacity(b);
        for sub in &claim.paths {
            input.extend_from_slice(&(sub.depth() as u64).to_le_bytes());
            input.extend_from_slice(&sub.root.0);
            input.extend_from_slice(&sub.leaf_index.to_le_bytes());
            paths.push((sub.root.clone(), sub.leaf_index, sub.depth()));
        }

        let pi = sha3_hash(Sha3Variant::Sha3_256, &input);
        let mut pi_hash = [0u8; 32];
        pi_hash.copy_from_slice(&pi);
        Self { variant: claim.variant, paths, pi_hash }
    }

    pub fn batch_size(&self) -> usize { self.paths.len() }
}

/// The artefact returned by `prove_batched_merkle_paths`.  Pair with
/// `BatchedMerklePathPublicInputs` for verification.
pub struct BatchedMerklePathProof {
    pub public: BatchedMerklePathPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    /// Batch size B.
    pub batch_size: usize,
    /// Padded composed trace height (power of two).
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove that the prover knows B (leaf, path) pairs matching the
/// public (root, leaf_index, depth) triples.  Produces ONE
/// `DeepFriProof<Ext>` over the composed B-block trace.
///
/// c_eval composition (per block, summed):
///   (a) sponge selected + always constraints — uniform across all
///       LDE rows; fired wherever a sponge sub-row sits.
///   (b) merkle selection constraints (left/right per index bit) —
///       gated by each hop row's indicator.
///   (c) merkle cross-row bindings (sponge input ← left||right,
///       sponge output → next hop's current) — gated by anchor rows.
///   (d) root-binding boundary at each block's last final-ι row
///       (block's `state_out`'s first N bits must equal block's
///       public root).
///
/// FS seeds derived from `BatchedMerklePathPublicInputs.pi_hash` with
/// per-domain offsets distinct from the single-path Merkle STARK's
/// (0xC1..0xC5 vs single-path's 0xB1..0xB5).
pub fn prove_batched_merkle_paths(
    claim: &BatchedMerklePathClaim,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<BatchedMerklePathProof, MerklePathProverError> {
    use crate::merkle_path_air::batched_merkle_cross_row_constraints;

    claim.check_shape().map_err(MerklePathProverError::InvalidClaim)?;
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(MerklePathProverError::Internal(format!(
            "blowup must be power-of-2 >= 2; got {blowup}"
        )));
    }

    // 1. Synthesise the composed batched trace + cross-check every
    //    block's emitted root against its claimed root.
    let layout = BatchedMerklePathLayout::new(claim, /*row_offset=*/0);
    let (trace, emitted_roots) = synthesize_batched_merkle_sponge_trace(claim, &layout)
        .map_err(|e| MerklePathProverError::Internal(format!("synthesis: {e}")))?;
    for (j, (sub, emitted)) in claim.paths.iter().zip(&emitted_roots).enumerate() {
        if *emitted != sub.root {
            return Err(MerklePathProverError::InvalidClaim(format!(
                "synthesised root for block {j} != claim's expected root",
            )));
        }
    }

    // 2. Build public inputs + derive FS seeds (distinct from
    //    single-path domain).
    let public = BatchedMerklePathPublicInputs::for_claim(claim);
    let mut seed_sponge_sel = public.pi_hash;  seed_sponge_sel[0] ^= 0xC1;
    let mut seed_sponge_alw = public.pi_hash;  seed_sponge_alw[0] ^= 0xC2;
    let mut seed_selection  = public.pi_hash;  seed_selection[0]  ^= 0xC3;
    let mut seed_cross_row  = public.pi_hash;  seed_cross_row[0]  ^= 0xC4;
    let mut seed_root       = public.pi_hash;  seed_root[0]       ^= 0xC5;

    // 3. Column-major + pad to next pow2.
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

    // 5. Sponge sub-AIR alphas (uniform across all LDE rows; same
    //    shape regardless of B).  Schema is shared across all blocks.
    let schema = &layout.blocks[0].schema;
    let air = UniformAirConstraints::for_schema(schema);
    let alphas_sponge_sel =
        alphas_from_transcript::<FBase>(&seed_sponge_sel, air.selected.len());
    let alphas_sponge_alw =
        alphas_from_transcript::<FBase>(&seed_sponge_alw, air.always.len());

    let mut c_eval = vec![FBase::zero(); n_lde];

    // 5a. Sponge contributions — uniform across the whole composed
    //     trace.  These naturally cover sub-rows of EVERY block; idle
    //     padding rows beyond the unpadded trace contribute zero
    //     because selectors there are zero (the schema's selector
    //     columns were zero-padded at step 3).
    for r_idx in 0..n_lde {
        let mut acc = FBase::zero();
        for (j, c) in air.selected.iter().enumerate() {
            let alpha = alphas_sponge_sel[j];
            let sel_col = schema.selector(c.selector);
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

    // 6. Merkle selection contributions — one alpha pair per
    //    (block, hop, bit).  Total = Σ_b depth_b × 2 × N.
    let n_hash_bits = claim.variant.output_bits();
    let total_selection_alphas: usize = layout.blocks.iter()
        .map(|b| b.depth * 2 * n_hash_bits)
        .sum();
    let alphas_selection =
        alphas_from_transcript::<FBase>(&seed_selection, total_selection_alphas);
    let mut alpha_idx = 0usize;
    for block in &layout.blocks {
        let block_schema = &block.schema;
        let bit_col = hop_index_bit_col(block_schema);
        for hop_idx in 0..block.depth {
            let hop_row = block.hop_starts[hop_idx];
            let indicator = compute_single_row_indicator_lde(hop_row, n_trace, blowup);
            for i in 0..n_hash_bits {
                let curr_col = hop_current_col(block_schema, i);
                let sib_col  = hop_sibling_col(block_schema, i);
                let l_col    = hop_left_col(block_schema, i);
                let r_col    = hop_right_col(block_schema, n_hash_bits, i);
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
                    let phi_l = l_v - cur - bit * (sib - cur);
                    let phi_r = r_v - sib - bit * (cur - sib);
                    c_eval[r_idx] += alpha_l * ind * phi_l;
                    c_eval[r_idx] += alpha_r * ind * phi_r;
                }
            }
        }
    }
    debug_assert_eq!(alpha_idx, total_selection_alphas);

    // 7. Cross-row contributions — one alpha per cross-row constraint
    //    across all blocks.  Each constraint addresses absolute rows;
    //    indicator is anchored at the constraint's anchor row.
    //
    // Phase 2.5: route through the DS-aware batched constraint emitter
    // when ANY block carries DS prefixes (all-or-nothing per block).
    use crate::merkle_path_air::batched_merkle_cross_row_constraints_with_ds;
    let cross = batched_merkle_cross_row_constraints_with_ds(claim, &layout)
        .map_err(MerklePathProverError::Internal)?;
    let alphas_xrow = alphas_from_transcript::<FBase>(&seed_cross_row, cross.len());
    use std::collections::HashMap;
    let mut indicators: HashMap<usize, Vec<FBase>> = HashMap::new();
    for c in &cross {
        let anchor_row = match c {
            MerkleCrossRowConstraint::SpongeInputLeft  { absorb_row, .. } => *absorb_row,
            MerkleCrossRowConstraint::SpongeInputRight { absorb_row, .. } => *absorb_row,
            MerkleCrossRowConstraint::SpongeOutputThreading { final_iota_row, .. } => *final_iota_row,
            MerkleCrossRowConstraint::SpongeInputDsByte { absorb_row, .. } => *absorb_row,
        };
        indicators.entry(anchor_row)
            .or_insert_with(|| compute_single_row_indicator_lde(anchor_row, n_trace, blowup));
    }
    for (j, c) in cross.iter().enumerate() {
        let alpha = alphas_xrow[j];
        // Phase 2.5: DS-byte variant evaluates as `lde[col][r] - constant`.
        if let Some((anchor_row, col, ds_bit)) = c.as_ds_byte() {
            let ind = &indicators[&anchor_row];
            let constant = FBase::from(ds_bit as u64);
            for r_idx in 0..n_lde {
                let ind_v = ind[r_idx];
                if ind_v.is_zero() { continue; }
                c_eval[r_idx] += alpha * ind_v * (lde[col][r_idx] - constant);
            }
            continue;
        }
        let (anchor_row, col_a, col_b, row_b) = match c {
            MerkleCrossRowConstraint::SpongeInputLeft { sponge_block_col, hop_left_col: l, absorb_row, hop_row } =>
                (*absorb_row, *sponge_block_col, *l, *hop_row),
            MerkleCrossRowConstraint::SpongeInputRight { sponge_block_col, hop_right_col: r_col, absorb_row, hop_row } =>
                (*absorb_row, *sponge_block_col, *r_col, *hop_row),
            MerkleCrossRowConstraint::SpongeOutputThreading { state_out_col, next_current_col, final_iota_row, next_hop_row } =>
                (*final_iota_row, *state_out_col, *next_current_col, *next_hop_row),
            MerkleCrossRowConstraint::SpongeInputDsByte { .. } => unreachable!(),
        };
        let ind = &indicators[&anchor_row];
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

    // 8. Root-binding boundary — per block, pin each block's
    //    state_out's first N bits to that block's claim.root.  One
    //    alpha per block (the per-bit identity is encoded as 64-bit
    //    lane sums via the shared seed).
    let output_lanes = claim.variant.output_bits() / 64;
    let alphas_root = alphas_from_transcript::<FBase>(
        &seed_root, claim.paths.len(),
    );
    for (j, block) in layout.blocks.iter().enumerate() {
        let last_iota_row = block.sponge_final_iota_row(block.depth - 1);
        let root_indicator = compute_single_row_indicator_lde(last_iota_row, n_trace, blowup);
        let block_root = &claim.paths[j].root.0;
        let alpha = alphas_root[j];
        for lane in 0..output_lanes {
            let mut lane_u64 = 0u64;
            for k in 0..8 {
                lane_u64 |= (block_root[8 * lane + k] as u64) << (8 * k);
            }
            let expected_bits = lane_to_bits(lane_u64);
            for bit in 0..64 {
                let col = block.schema.state_out_bit(lane, bit);
                let expected = FBase::from(expected_bits[bit] as u64);
                for r_idx in 0..n_lde {
                    let ind = root_indicator[r_idx];
                    if ind.is_zero() { continue; }
                    c_eval[r_idx] += alpha * ind * (lde[col][r_idx] - expected);
                }
            }
        }
    }

    // 9. Build FRI domain + params + prove.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.pi_hash);
    if use_stir { params.stir = true; }

    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    let _ = (One::one as fn() -> FBase,);  // keep ark_ff::One in-scope
    Ok(BatchedMerklePathProof {
        public, fri_proof,
        batch_size: claim.paths.len(),
        n_trace, blowup, r, use_stir,
    })
}

/// Verify a batched Merkle path STARK proof.  Reproduces FS-derived
/// alphas via `proof.public.pi_hash` and runs `deep_fri_verify`.
pub fn verify_batched_merkle_paths(proof: &BatchedMerklePathProof) -> bool {
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

    /// Bench: measure prove / verify / proof-size for the Merkle path
    /// gadget at the depth controlled by `BENCH_MERKLE_DEPTH` (default 2).
    /// Other env vars: BENCH_BLOWUP, BENCH_R, BENCH_STIR.
    /// Prints a CSV-friendly line for the bench script to scrape.
    #[test]
    #[ignore = "bench — invoke via scripts/bench-merkle-stark.sh"]
    fn bench_merkle_path_stark() {
        use std::time::Instant;
        use ark_serialize::CanonicalSerialize;

        let depth_log2: usize = std::env::var("BENCH_MERKLE_DEPTH")
            .ok().and_then(|s| s.parse().ok()).unwrap_or(2);
        let n_leaves = 1usize << depth_log2;
        let blowup: usize = std::env::var("BENCH_BLOWUP")
            .ok().and_then(|s| s.parse().ok()).unwrap_or(4);
        let r: usize = std::env::var("BENCH_R")
            .ok().and_then(|s| s.parse().ok()).unwrap_or(54);
        let use_stir: bool = std::env::var("BENCH_STIR")
            .ok().as_deref() == Some("1");
        let ldt_label = if use_stir { "stir" } else { "fri" };

        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..n_leaves as u8)
            .map(|i| fake_leaf(variant, 0x30 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, n_leaves / 2);

        let t0 = Instant::now();
        let proof = prove_merkle_path(&claim, blowup, r, use_stir)
            .expect("prove must succeed");
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

        // 3 verify runs, take median.
        let mut samples = Vec::with_capacity(3);
        for _ in 0..3 {
            let t = Instant::now();
            assert!(verify_merkle_path(&proof));
            samples.push(t.elapsed().as_secs_f64() * 1000.0);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let verify_ms = samples[1];

        let mut buf = Vec::new();
        proof.fri_proof.serialize_compressed(&mut buf).unwrap();
        let proof_kib = buf.len() as f64 / 1024.0;

        println!(
            "merkle_stark variant=L1 depth={} blowup={blowup} r={r} ldt={ldt_label} \
             prove_ms={prove_ms:.0} verify_ms={verify_ms:.2} \
             proof_kib={proof_kib:.1} n_trace={n_trace}",
            depth_log2, n_trace = proof.n_trace,
        );
    }

    #[test]
    #[ignore = "slow — exercises root-binding soundness"]
    fn round_trip_rejects_tampered_root_claim() {
        // Tamper the claimed root in the public inputs.  The
        // root-binding boundary commits state_out at the last final-ι
        // row to the original root, so the verifier rejects when
        // shown a different root with the same proof.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0x20 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 1);
        let mut proof = prove_merkle_path(&claim, 4, 54, false)
            .expect("prove must succeed");
        // Tamper the public root + re-derive pi_hash.
        proof.public.root.0[0] ^= 0xFF;
        proof.public = MerklePathPublicInputs::for_root(
            proof.public.variant, proof.public.root.clone(),
            proof.public.leaf_index,
        );
        assert!(!verify_merkle_path(&proof),
            "verifier must reject when claimed root doesn't match trace");
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
            ds_prefix_per_hop: Vec::new(),
        };
        let result = prove_merkle_path(&bad_claim, 4, 54, false);
        assert!(matches!(result, Err(MerklePathProverError::InvalidClaim(_))));
    }

    // ─── Phase 1 Stage 3: BatchedMerklePath API structural tests ────

    fn batched_b2_demo_claim() -> BatchedMerklePathClaim {
        let variant = Sha3Variant::Sha3_256;
        let leaves_a = vec![fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
                            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD)];
        let leaves_b = vec![fake_leaf(variant, 0x11), fake_leaf(variant, 0x22),
                            fake_leaf(variant, 0x33), fake_leaf(variant, 0x44)];
        BatchedMerklePathClaim {
            variant,
            paths: vec![
                merkle_build_and_open(variant, &leaves_a, 1),
                merkle_build_and_open(variant, &leaves_b, 3),
            ],
        }
    }

    #[test]
    fn batched_public_inputs_pi_hash_is_deterministic() {
        let claim = batched_b2_demo_claim();
        let a = BatchedMerklePathPublicInputs::for_claim(&claim);
        let b = BatchedMerklePathPublicInputs::for_claim(&claim);
        assert_eq!(a.pi_hash, b.pi_hash);
        assert_eq!(a.batch_size(), 2);
    }

    #[test]
    fn batched_public_inputs_pi_hash_changes_with_path_order() {
        let mut a = batched_b2_demo_claim();
        let mut b = batched_b2_demo_claim();
        b.paths.swap(0, 1);  // swap path order — pi_hash must change.
        let pa = BatchedMerklePathPublicInputs::for_claim(&a);
        let pb = BatchedMerklePathPublicInputs::for_claim(&b);
        assert_ne!(pa.pi_hash, pb.pi_hash,
            "swapping the path order must change pi_hash (order-sensitive)");
        let _ = (&mut a, &mut b);
    }

    #[test]
    fn batched_public_inputs_pi_hash_changes_with_root() {
        let mut claim = batched_b2_demo_claim();
        let a = BatchedMerklePathPublicInputs::for_claim(&claim);
        claim.paths[0].root.0[0] ^= 0xFF;  // flip one byte of root.
        let b = BatchedMerklePathPublicInputs::for_claim(&claim);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn batched_public_inputs_pi_hash_distinct_from_single_path_tag() {
        // Build a B=1 batched claim and a single-path claim with the
        // same (root, leaf_index) — pi_hashes must differ (different
        // domain-separation tags).
        let variant = Sha3Variant::Sha3_256;
        let leaves = vec![fake_leaf(variant, 1), fake_leaf(variant, 2)];
        let single = merkle_build_and_open(variant, &leaves, 0);
        let batched = BatchedMerklePathClaim {
            variant, paths: vec![single.clone()],
        };
        let single_pub = MerklePathPublicInputs::for_root(
            variant, single.root, single.leaf_index,
        );
        let batched_pub = BatchedMerklePathPublicInputs::for_claim(&batched);
        assert_ne!(single_pub.pi_hash, batched_pub.pi_hash,
            "single-path and B=1 batched pi_hashes must differ \
             (different domain separation tags)");
    }

    #[test]
    fn batched_prove_rejects_invalid_claim() {
        let mut bad = batched_b2_demo_claim();
        bad.paths[0].leaf_index = 1u64 << 60;  // doesn't fit depth bits.
        let r = prove_batched_merkle_paths(&bad, 4, 54, false);
        assert!(matches!(r, Err(MerklePathProverError::InvalidClaim(_))));
    }

    #[test]
    fn batched_prove_rejects_tampered_root_before_fri() {
        // Synthesis cross-checks emitted vs claimed root before
        // building FRI input — a tampered root must produce an
        // InvalidClaim error with a recognisable substring.
        let mut bad = batched_b2_demo_claim();
        bad.paths[0].root.0[0] ^= 0xFF;
        let r = prove_batched_merkle_paths(&bad, 4, 54, false);
        match r {
            Err(MerklePathProverError::InvalidClaim(ref s))
                if s.contains("synthesised root") => {}
            _ => panic!("expected InvalidClaim about synthesised root"),
        }
    }

    #[test]
    fn batched_round_trip_b2_smoke_fri() {
        let claim = batched_b2_demo_claim();
        let proof = prove_batched_merkle_paths(
            &claim, /*blowup=*/4, /*r=*/54, /*stir=*/false,
        ).expect("honest B=2 batched prove must succeed");
        assert_eq!(proof.batch_size, 2);
        assert!(proof.n_trace.is_power_of_two());
        assert!(verify_batched_merkle_paths(&proof),
            "honest B=2 batched round-trip must verify");
    }

    #[test]
    fn batched_round_trip_b3_mixed_depth_smoke_fri() {
        // B=3 with mixed depths 2 + 3 + 2 — the prover must handle
        // distinct per-block geometries.
        let variant = Sha3Variant::Sha3_256;
        let leaves_d2 = vec![fake_leaf(variant, 0x10), fake_leaf(variant, 0x20),
                             fake_leaf(variant, 0x30), fake_leaf(variant, 0x40)];
        let leaves_d3: Vec<MerkleNode> = (0..8)
            .map(|i| fake_leaf(variant, 0x80 | i as u8))
            .collect();
        let leaves_d2b = vec![fake_leaf(variant, 0xF1), fake_leaf(variant, 0xF2),
                              fake_leaf(variant, 0xF3), fake_leaf(variant, 0xF4)];
        let claim = BatchedMerklePathClaim {
            variant,
            paths: vec![
                merkle_build_and_open(variant, &leaves_d2,  0),
                merkle_build_and_open(variant, &leaves_d3,  5),
                merkle_build_and_open(variant, &leaves_d2b, 2),
            ],
        };
        let proof = prove_batched_merkle_paths(&claim, 4, 54, false)
            .expect("B=3 mixed-depth prove must succeed");
        assert!(verify_batched_merkle_paths(&proof),
            "B=3 mixed-depth round-trip must verify");
    }

    #[test]
    fn batched_proof_rejects_pi_hash_tamper() {
        // Tampering the public pi_hash should make FRI re-derive a
        // different transcript and reject the proof.
        let claim = batched_b2_demo_claim();
        let mut proof = prove_batched_merkle_paths(&claim, 4, 54, false)
            .expect("honest prove");
        proof.public.pi_hash[0] ^= 0x01;
        assert!(!verify_batched_merkle_paths(&proof),
            "tampered pi_hash must cause FRI to reject");
    }

    #[test]
    fn batched_verify_signature_composes() {
        // Cheap type-assembly spot check — independent of the heavy
        // FRI round-trip above.
        let claim = batched_b2_demo_claim();
        let public = BatchedMerklePathPublicInputs::for_claim(&claim);
        assert_eq!(public.paths.len(), 2);
        assert_eq!(public.batch_size(), 2);
    }

    // ─── Phase 2.5 Milestone 5: DS-aware round-trip tests ─────────

    fn fake_ds_bytes_p25(arity: u64, level: u32, position: u64, tree_label: u64) -> Vec<u8> {
        let mut out = Vec::with_capacity(32);
        out.extend_from_slice(&arity.to_le_bytes());
        out.extend_from_slice(&(level as u64).to_le_bytes());
        out.extend_from_slice(&position.to_le_bytes());
        out.extend_from_slice(&tree_label.to_le_bytes());
        out
    }

    #[test]
    fn ds_aware_single_path_round_trip_b2() {
        use crate::merkle_path_air::merkle_build_and_open_with_ds;
        // B=2 with DS-prefixed Merkle trees mimicking FRI's arity-2
        // fold-layer protocol.  tree_label varies per block (=fold
        // layer index).
        let variant = Sha3Variant::Sha3_256;
        let leaves_a = vec![fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
                            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD)];
        let leaves_b = vec![fake_leaf(variant, 0x11), fake_leaf(variant, 0x22),
                            fake_leaf(variant, 0x33), fake_leaf(variant, 0x44)];
        let ds_a = vec![fake_ds_bytes_p25(2, 1, 0, 0), fake_ds_bytes_p25(2, 2, 0, 0)];
        let ds_b = vec![fake_ds_bytes_p25(2, 1, 1, 1), fake_ds_bytes_p25(2, 2, 0, 1)];
        let claim_a = merkle_build_and_open_with_ds(variant, &leaves_a, 1, &ds_a);
        let claim_b = merkle_build_and_open_with_ds(variant, &leaves_b, 3, &ds_b);
        let batched = BatchedMerklePathClaim {
            variant, paths: vec![claim_a, claim_b],
        };

        let proof = prove_batched_merkle_paths(&batched, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("DS-aware B=2 batched prove must succeed");
        assert!(verify_batched_merkle_paths(&proof),
            "DS-aware B=2 batched round-trip must verify");
        assert_eq!(proof.batch_size, 2);
    }

    #[test]
    fn ds_aware_batched_rejects_pi_hash_tamper() {
        use crate::merkle_path_air::merkle_build_and_open_with_ds;
        let variant = Sha3Variant::Sha3_256;
        let leaves = vec![fake_leaf(variant, 0xA1), fake_leaf(variant, 0xB2),
                          fake_leaf(variant, 0xC3), fake_leaf(variant, 0xD4)];
        let ds = vec![fake_ds_bytes_p25(2, 1, 0, 5), fake_ds_bytes_p25(2, 2, 0, 5)];
        let claim = merkle_build_and_open_with_ds(variant, &leaves, 2, &ds);
        let batched = BatchedMerklePathClaim {
            variant, paths: vec![claim],
        };
        let mut proof = prove_batched_merkle_paths(&batched, 4, 54, false)
            .expect("honest DS-aware prove");
        proof.public.pi_hash[0] ^= 0x01;
        assert!(!verify_batched_merkle_paths(&proof),
            "tampered pi_hash must cause FRI to reject");
    }
}
