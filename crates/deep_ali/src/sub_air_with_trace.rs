//! Trace-bound prove/verify wrapper for v2 sub-AIRs.
//!
//! Closes the malicious-prover soundness gap (audit doc gap #5) by
//! adding a parallel trace LDE Merkle commitment alongside the FRI's
//! `c_eval` commitment, opening trace cells at every FRI query
//! position, and having the verifier re-evaluate the constraint
//! formula at the queried trace cells.
//!
//! ## Soundness
//!
//! For each FRI query position `x ∈ H_0` (the LDE domain), the
//! verifier checks `c_eval(x) · Z_H(x) = Σ α_j · Φ_j(trace[x], x)`.
//! For an honest prover with valid AIR, this holds at all `x`.  For a
//! malicious prover with an invalid trace (some `j, i` such that
//! `Φ_j(trace[i], i) ≠ 0` for `i ∈ H ⊂ H_0`), the check fails at any
//! queried `x = i`.  With `r` queries at rate `ρ`, soundness ≥
//! `1 − ρ^r`.  At `r=54, ρ=1/32`: 270 bits.  At `r=79`: 395.  At
//! `r=105`: 525.  Comfortably above NIST PQ Level 1/3/5 targets.
//!
//! ## Binding
//!
//! The trace_root is bound into pi_hash via `augment_pi_hash` BEFORE
//! the FRI's FS challenges are derived, so the prover cannot adjust
//! the trace post-commitment.

#![allow(non_snake_case, dead_code)]

use ark_ff::{Field, One as _, Zero as _};
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

use merkle::{
    MerkleChannelCfg, MerkleOpening, MerkleTreeChannel, compute_leaf_hash,
};
use hash::selected::{HASH_BYTES, SelectedHasher};
use sha3::{Digest as _, Sha3_256};

use crate::fri::{deep_fri_prove, deep_fri_verify, DeepFriProof, FriDomain};
use crate::tower_field::TowerField;

// ─── F_ext selection (matches orchestration's `Ext`) ──────────────

#[cfg(any(feature = "sha3-256", feature = "sha3-384"))]
pub type Ext = crate::sextic_ext::SexticExt;

#[cfg(feature = "sha3-512")]
pub type Ext = crate::octic_ext::OcticExt;

#[cfg(not(any(feature = "sha3-256", feature = "sha3-384", feature = "sha3-512")))]
pub type Ext = crate::sextic_ext::SexticExt;

// ─── Augmented proof bundle ───────────────────────────────────────

/// One trace opening at a queried LDE position: cell values + Merkle
/// path proof against `trace_root`.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct TraceOpening {
    /// W F-values: trace cells at the queried row, one per column.
    pub cells: Vec<F>,
    /// Merkle path from the cells' leaf hash to `trace_root`.
    pub merkle: MerkleOpening,
}

/// Augmented proof bundle: standard FRI proof + parallel trace
/// commitment + per-query trace openings (cur and nxt rows).
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SubAirProofWithTrace {
    /// Serialized `DeepFriProof<Ext>`.
    pub fri_proof_bytes: Vec<u8>,
    /// Merkle root over trace LDE rows.
    pub trace_root: [u8; HASH_BYTES],
    /// Trace cells + paths at queried positions (one per FRI query).
    pub openings_cur: Vec<TraceOpening>,
    /// Trace cells + paths at `(queried_pos + blowup) mod n_lde`.
    /// Needed for `eval_per_row(cur, nxt, row)`.
    pub openings_nxt: Vec<TraceOpening>,
}

// ─── Helpers ──────────────────────────────────────────────────────

fn merkle_depth(leaves: usize, arity: usize) -> usize {
    assert!(arity >= 2);
    let mut depth = 1usize;
    let mut cur = leaves;
    while cur > arity {
        cur = (cur + arity - 1) / arity;
        depth += 1;
    }
    depth
}

fn pick_arity(n: usize) -> usize {
    if n % 16 == 0 { 16 }
    else if n % 8 == 0 { 8 }
    else if n % 4 == 0 { 4 }
    else if n % 2 == 0 { 2 }
    else { 1 }  // shouldn't happen for power-of-two LDE sizes
}

/// Tree config for the trace LDE Merkle tree.  Distinct
/// `tree_label` (0xAA) from FRI's f0 tree (0xFF) avoids any
/// cross-tree confusion.
fn trace_tree_cfg(n_lde: usize) -> MerkleChannelCfg {
    let arity = pick_arity(n_lde).max(2);
    let depth = merkle_depth(n_lde, arity);
    MerkleChannelCfg::new(vec![arity; depth], 0xAA_AA_AA_AA)
}

/// Domain-separated tag absorbed into the trace Merkle hashing.
/// Uses the level-matched `SelectedHasher` so `[u8; HASH_BYTES]`
/// has the correct width at every NIST PQ level.
fn trace_tree_tag(n_lde: usize, width: usize, domain_sep: &[u8]) -> [u8; HASH_BYTES] {
    let mut h = SelectedHasher::new();
    h.update(b"deep_ali/sub_air_with_trace/v1");
    h.update(domain_sep);
    h.update(&(n_lde as u64).to_le_bytes());
    h.update(&(width as u64).to_le_bytes());
    let out = h.finalize();
    let mut tag = [0u8; HASH_BYTES];
    tag.copy_from_slice(out.as_slice());
    tag
}

/// Bind `trace_root` into the FS challenge derivation.
pub fn augment_pi_hash(
    pi_hash: &[u8; 32],
    trace_root: &[u8; HASH_BYTES],
    domain_sep: &[u8],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"deep_ali/sub_air_with_trace/aug_pi_hash/v1");
    h.update(domain_sep);
    h.update(pi_hash);
    h.update(trace_root.as_ref());
    h.finalize().into()
}

/// LDE-domain element at index `i`: ω_{n_lde}^i.
pub fn lde_omega_pow(i: usize, n_lde: usize) -> F {
    let dom = GeneralEvaluationDomain::<F>::new(n_lde).expect("LDE domain power-of-two");
    dom.element(i)
}

/// Z_H(x) = x^{n_trace} − 1.
pub fn z_h_at(x: F, n_trace: usize) -> F {
    x.pow(&[n_trace as u64]) - F::one()
}

/// Build the trace LDE Merkle tree (packed leaves: W F-values per row).
/// Returns the root and the populated tree (kept for `open` calls).
fn commit_trace_lde(
    lde: &[Vec<F>],
    domain_sep: &[u8],
) -> ([u8; HASH_BYTES], MerkleTreeChannel) {
    let n_lde = lde[0].len();
    let width = lde.len();
    let cfg = trace_tree_cfg(n_lde);
    let tag = trace_tree_tag(n_lde, width, domain_sep);
    let mut tree = MerkleTreeChannel::new(cfg, tag);
    for i in 0..n_lde {
        let leaf: Vec<F> = (0..width).map(|c| lde[c][i]).collect();
        tree.push_leaf(&leaf);
    }
    let root = tree.finalize();
    (root, tree)
}

pub fn serialize_proof(proof: &SubAirProofWithTrace) -> Vec<u8> {
    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).expect("serialize");
    buf
}

pub fn deserialize_proof(bytes: &[u8]) -> Result<SubAirProofWithTrace, String> {
    SubAirProofWithTrace::deserialize_with_mode(bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| format!("deserialize sub-air proof: {e:?}"))
}

fn serialize_fri(proof: &DeepFriProof<Ext>) -> Vec<u8> {
    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).expect("serialize FRI");
    buf
}

fn deserialize_fri(bytes: &[u8]) -> Result<DeepFriProof<Ext>, String> {
    DeepFriProof::<Ext>::deserialize_with_mode(bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| format!("deserialize FRI: {e:?}"))
}

/// Extract the LDE query positions from a FRI or STIR proof.
///
/// In FRI mode, query positions are stored as `queries[k].per_layer_refs[0].i`
/// (the f0-layer index = LDE position).  In STIR mode, the proof's
/// `queries` vector is empty; the proximity-test queries live in
/// `stir_proximity_queries[k].raw_query_index`.  This helper unifies
/// both modes so the trace-opening loop in `prove_one_sub_air_*` works
/// in either LDT mode.
///
/// Returns `Err` if neither source has any queries (catches the
/// silent-skip soundness gap that the empty-queries guard was added
/// for — but allows STIR proofs through cleanly).
pub fn extract_query_positions(fri_proof: &DeepFriProof<Ext>) -> Result<Vec<usize>, String> {
    if !fri_proof.queries.is_empty() {
        Ok(fri_proof.queries.iter().map(|q| q.per_layer_refs[0].i).collect())
    } else if let Some(prox) = &fri_proof.stir_proximity_queries {
        if prox.is_empty() {
            return Err("sub-air verify: both FRI queries and STIR proximity queries are empty \
                        — no per-query trace-cell soundness check possible".into());
        }
        Ok(prox.iter().map(|p| p.raw_query_index).collect())
    } else {
        Err("sub-air verify: FRI queries vector is empty AND no STIR proximity queries present \
             — proof structure is invalid or both LDT modes were skipped".into())
    }
}

/// Extract the (LDE position, c_eval value) for query `k` from a
/// FRI or STIR proof.  Used by `verify_one_sub_air_with_trace`'s
/// per-query constraint check: `c_eval(x) · Z_H(x) == Σ α_j Φ_j(trace[x], x)`.
///
/// In FRI mode: `c_eval(x) = queries[k].per_layer_payloads[0].f_val` (Ext).
///
/// In STIR mode: `c_eval(x) = Ext::from_fp(stir_proximity_queries[k]
/// .fiber_f_vals[j])` where `j = (raw_query_index - base_index) /
/// n_next`.  Both arrays are bound to `proof.root_f0` via the f0
/// packed-Merkle commitment in `f0_packed_opening`, which the
/// outer `deep_fri_verify` separately checks.  Schwartz-Zippel
/// soundness for the per-query constraint check is identical in
/// both modes.
pub fn extract_query_position_and_c_eval(
    fri_proof: &DeepFriProof<Ext>,
    k: usize,
    n0: usize,
    m0: usize,
) -> Result<(usize, Ext), String> {
    if !fri_proof.queries.is_empty() {
        let q = &fri_proof.queries[k];
        let pos = q.per_layer_refs[0].i;
        let c_eval = q.per_layer_payloads[0].f_val;
        Ok((pos, c_eval))
    } else if let Some(prox) = &fri_proof.stir_proximity_queries {
        let pq = &prox[k];
        let pos = pq.raw_query_index;
        let n_next = n0 / m0;
        let base_index = pos % n_next;
        let j_for_raw = (pos - base_index) / n_next;
        if j_for_raw >= pq.fiber_f_vals.len() {
            return Err(format!(
                "STIR query {k}: fiber index {j_for_raw} out of bounds (fiber len = {})",
                pq.fiber_f_vals.len()
            ));
        }
        let c_eval = Ext::from_fp(pq.fiber_f_vals[j_for_raw]);
        Ok((pos, c_eval))
    } else {
        Err(format!("query {k}: no FRI nor STIR query data available"))
    }
}

// ─── Prove ────────────────────────────────────────────────────────

/// FS-derive constraint composition coefficients α_j ∈ F from
/// `aug_pi_hash` with `domain_sep` (matches orchestration's
/// `comb_coeffs` shape but consumes the augmented pi_hash so the
/// trace_root binds before α is sampled).
pub fn comb_coeffs_aug(
    num: usize,
    aug_pi_hash: &[u8; 32],
    domain_sep: &[u8],
) -> Vec<F> {
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    let mut shake = sha3::Shake256::default();
    shake.update(b"deep_ali/sub_air_with_trace/comb_coeffs/v1");
    shake.update(domain_sep);
    shake.update(aug_pi_hash);
    let mut reader = shake.finalize_xof();
    (0..num)
        .map(|_| {
            let mut buf = [0u8; 8];
            reader.read(&mut buf);
            F::from(u64::from_le_bytes(buf))
        })
        .collect()
}

/// Prove a single sub-AIR with a trace Merkle commitment bound to
/// pi_hash.  Mirrors the existing `prove_one_sub_air` but additionally
/// commits the trace LDE and opens trace cells at every FRI query.
///
/// `domain_sep` distinguishes sub-AIRs (e.g. `b"v17"`, `b"intt:0"`,
/// `b"t_mem"`).
///
/// `c_eval_fn(lde, n_trace, blowup, comb_coeffs)` produces the
/// constraint composition `c_eval` on the LDE, using the supplied
/// `comb_coeffs` (FS-derived from the AUGMENTED pi_hash, so they're
/// unpredictable until after the prover commits trace_root).
pub fn prove_one_sub_air_with_trace(
    trace: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    num_constraints: usize,
    c_eval_fn: impl FnOnce(&[Vec<F>], usize, usize, &[F]) -> Vec<F>,
    fri_params_fn: impl FnOnce(usize, [u8; 32]) -> crate::fri::DeepFriParams,
) -> SubAirProofWithTrace {
    let n0 = n_trace * blowup;
    let lde = crate::trace_import::lde_trace_columns(trace, n_trace, blowup)
        .expect("LDE construction");

    // 1. Commit trace LDE.
    let (trace_root, tree) = commit_trace_lde(&lde, domain_sep);

    // 2. Augment pi_hash so FRI's FS challenges depend on trace_root.
    let aug_pi_hash = augment_pi_hash(&pi_hash, &trace_root, domain_sep);

    // 3. Derive comb_coeffs from aug_pi_hash (binds trace_root before α).
    let comb_coeffs = comb_coeffs_aug(num_constraints, &aug_pi_hash, domain_sep);

    // 4. Compute c_eval and run FRI under aug_pi_hash.
    let c_eval = c_eval_fn(&lde, n_trace, blowup, &comb_coeffs);
    let domain = FriDomain::new_radix2(n0);
    let params = fri_params_fn(n0, aug_pi_hash);
    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    // 4. Open trace at each queried position (cur + nxt for eval_per_row).
    //    `extract_query_positions` returns positions from FRI mode's
    //    `queries[k].per_layer_refs[0].i` or STIR mode's
    //    `stir_proximity_queries[k].raw_query_index`.
    let positions = extract_query_positions(&fri_proof)
        .expect("FRI/STIR proof has at least one query position");
    let n_queries = positions.len();
    let mut openings_cur = Vec::with_capacity(n_queries);
    let mut openings_nxt = Vec::with_capacity(n_queries);
    let width = lde.len();
    for &pos in &positions {
        let nxt_pos = (pos + blowup) % n0;
        let cur_cells: Vec<F> = (0..width).map(|c| lde[c][pos]).collect();
        let nxt_cells: Vec<F> = (0..width).map(|c| lde[c][nxt_pos]).collect();
        openings_cur.push(TraceOpening { cells: cur_cells, merkle: tree.open(pos) });
        openings_nxt.push(TraceOpening { cells: nxt_cells, merkle: tree.open(nxt_pos) });
    }

    SubAirProofWithTrace {
        fri_proof_bytes: serialize_fri(&fri_proof),
        trace_root,
        openings_cur,
        openings_nxt,
    }
}

/// Variant of `prove_one_sub_air_with_trace` that returns the LDE and
/// the committed Merkle tree alongside the proof.  Use this when the
/// caller needs to open *additional* trace rows (e.g. cross-region
/// bindings for F2b) at known positions after the FRI proof is built.
///
/// The returned tree shares its commitment with `proof.trace_root`,
/// so subsequent `tree.open(pos)` calls produce openings the verifier
/// can authenticate via `verify_trace_row_at_raw_position`.
pub fn prove_one_sub_air_with_trace_capturing(
    trace: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    num_constraints: usize,
    c_eval_fn: impl FnOnce(&[Vec<F>], usize, usize, &[F]) -> Vec<F>,
    fri_params_fn: impl FnOnce(usize, [u8; 32]) -> crate::fri::DeepFriParams,
) -> (SubAirProofWithTrace, Vec<Vec<F>>, MerkleTreeChannel) {
    let n0 = n_trace * blowup;
    let lde = crate::trace_import::lde_trace_columns(trace, n_trace, blowup)
        .expect("LDE construction");

    let (trace_root, tree) = commit_trace_lde(&lde, domain_sep);
    let aug_pi_hash = augment_pi_hash(&pi_hash, &trace_root, domain_sep);
    let comb_coeffs = comb_coeffs_aug(num_constraints, &aug_pi_hash, domain_sep);
    let c_eval = c_eval_fn(&lde, n_trace, blowup, &comb_coeffs);
    let domain = FriDomain::new_radix2(n0);
    let params = fri_params_fn(n0, aug_pi_hash);
    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    let positions = extract_query_positions(&fri_proof)
        .expect("FRI/STIR proof has at least one query position");
    let mut openings_cur = Vec::with_capacity(positions.len());
    let mut openings_nxt = Vec::with_capacity(positions.len());
    let width = lde.len();
    for &pos in &positions {
        let nxt_pos = (pos + blowup) % n0;
        let cur_cells: Vec<F> = (0..width).map(|c| lde[c][pos]).collect();
        let nxt_cells: Vec<F> = (0..width).map(|c| lde[c][nxt_pos]).collect();
        openings_cur.push(TraceOpening { cells: cur_cells, merkle: tree.open(pos) });
        openings_nxt.push(TraceOpening { cells: nxt_cells, merkle: tree.open(nxt_pos) });
    }

    let proof = SubAirProofWithTrace {
        fri_proof_bytes: serialize_fri(&fri_proof),
        trace_root,
        openings_cur,
        openings_nxt,
    };
    (proof, lde, tree)
}

/// Open the trace at raw row `raw_row` (LDE position `raw_row * blowup`).
/// Returns a `TraceOpening` the verifier can authenticate against
/// `trace_root` via `verify_trace_row_at_raw_position`.
///
/// Used for F2b cross-region bindings — opens specific cells in
/// committed sub-traces so the verifier can check cross-region
/// equality without re-running the FRI.
pub fn open_trace_row_at_raw_position(
    lde: &[Vec<F>],
    tree: &MerkleTreeChannel,
    raw_row: usize,
    blowup: usize,
) -> TraceOpening {
    let pos = raw_row * blowup;
    let width = lde.len();
    let cells: Vec<F> = (0..width).map(|c| lde[c][pos]).collect();
    TraceOpening {
        cells,
        merkle: tree.open(pos),
    }
}

/// Verify a `TraceOpening` produced by `open_trace_row_at_raw_position`.
///
/// Checks: (a) opening's Merkle index equals `raw_row * blowup`,
/// (b) the cells hash to the committed leaf, and (c) the Merkle
/// path authenticates against `trace_root` (using the same cfg/tag
/// the prover used).  Returns the cells on success.
pub fn verify_trace_row_at_raw_position<'a>(
    opening: &'a TraceOpening,
    trace_root: &[u8; HASH_BYTES],
    raw_row: usize,
    blowup: usize,
    n_lde: usize,
    width: usize,
    domain_sep: &[u8],
) -> Result<&'a [F], String> {
    let pos = raw_row * blowup;
    if opening.merkle.index != pos {
        return Err(format!(
            "cross-binding opening: Merkle index {} ≠ expected raw_row·blowup = {pos}",
            opening.merkle.index
        ));
    }
    if opening.cells.len() != width {
        return Err(format!(
            "cross-binding opening: cells len {} ≠ expected width {width}",
            opening.cells.len()
        ));
    }
    let cfg = trace_tree_cfg(n_lde);
    let tag = trace_tree_tag(n_lde, width, domain_sep);
    let leaf = compute_leaf_hash(&cfg, pos, &opening.cells);
    if leaf != opening.merkle.leaf {
        return Err("cross-binding opening: cells hash ≠ committed leaf".into());
    }
    if !MerkleTreeChannel::verify_opening(&cfg, *trace_root, &opening.merkle, &tag) {
        return Err("cross-binding opening: Merkle path failed".into());
    }
    Ok(&opening.cells)
}

// ─── Verify ───────────────────────────────────────────────────────

/// Verify a sub-AIR proof produced by `prove_one_sub_air_with_trace`.
///
/// `eval_per_row_fn(cur_cells, nxt_cells, trace_row) -> Vec<F>` is the
/// AIR-specific constraint emitter; the verifier re-evaluates it at
/// the queried trace cells and compares against `c_eval(x) · Z_H(x)`.
pub fn verify_one_sub_air_with_trace(
    proof: &SubAirProofWithTrace,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    width: usize,
    num_constraints: usize,
    eval_per_row_fn: impl Fn(&[F], &[F], usize) -> Vec<F>,
    fri_params_fn: impl Fn(usize, [u8; 32]) -> crate::fri::DeepFriParams,
) -> Result<(), String> {
    let n0 = n_trace * blowup;
    let aug_pi_hash = augment_pi_hash(&pi_hash, &proof.trace_root, domain_sep);

    // 1. Verify FRI under aug_pi_hash.
    let fri_proof = deserialize_fri(&proof.fri_proof_bytes)?;
    let params = fri_params_fn(n0, aug_pi_hash);
    if !deep_fri_verify::<Ext>(&params, &fri_proof) {
        return Err("FRI verify rejected".into());
    }

    // 1b. Extract query positions from FRI or STIR proof.  Returns
    // `Err` if both `queries` and `stir_proximity_queries` are empty
    // — defense-in-depth against a malformed proof that would
    // silently skip ALL per-query trace-cell soundness checks.
    //
    // Both FRI mode (`fri_proof.queries[k].per_layer_refs[0].i`) and
    // STIR mode (`fri_proof.stir_proximity_queries[k].raw_query_index`)
    // are now supported transparently.
    let positions = extract_query_positions(&fri_proof)?;
    let n_queries = positions.len();
    let m0 = params.schedule.first().copied().unwrap_or(2);

    // 2. Recompute combination coefficients (must match prover's α).
    let comb_coeffs = comb_coeffs_aug(num_constraints, &aug_pi_hash, domain_sep);
    if comb_coeffs.len() != num_constraints {
        return Err(format!(
            "comb_coeffs length {} ≠ num_constraints {num_constraints}",
            comb_coeffs.len()
        ));
    }

    // 3. Per-query: verify trace openings + check c_eval · Z_H = phi.
    if proof.openings_cur.len() != n_queries || proof.openings_nxt.len() != n_queries {
        return Err(format!(
            "trace openings count mismatch: cur={} nxt={} expected={n_queries}",
            proof.openings_cur.len(), proof.openings_nxt.len()
        ));
    }

    let cfg = trace_tree_cfg(n0);
    let tag = trace_tree_tag(n0, width, domain_sep);

    for k in 0..n_queries {
        let (pos, c_eval_at_pos) = extract_query_position_and_c_eval(
            &fri_proof, k, n0, m0,
        )?;
        debug_assert_eq!(pos, positions[k]);
        let nxt_pos = (pos + blowup) % n0;

        // 3a. Cell-count + index sanity.
        let cur_op = &proof.openings_cur[k];
        let nxt_op = &proof.openings_nxt[k];
        if cur_op.cells.len() != width || nxt_op.cells.len() != width {
            return Err(format!(
                "query {k}: cells len mismatch (cur={}, nxt={}, expected={width})",
                cur_op.cells.len(), nxt_op.cells.len()
            ));
        }
        if cur_op.merkle.index != pos {
            return Err(format!(
                "query {k}: cur Merkle index {} ≠ FRI position {pos}",
                cur_op.merkle.index
            ));
        }
        if nxt_op.merkle.index != nxt_pos {
            return Err(format!(
                "query {k}: nxt Merkle index {} ≠ expected {nxt_pos}",
                nxt_op.merkle.index
            ));
        }

        // 3b. Verify cell hash matches the committed leaf hash.
        let cur_leaf = compute_leaf_hash(&cfg, pos, &cur_op.cells);
        if cur_leaf != cur_op.merkle.leaf {
            return Err(format!(
                "query {k}: cur cells hash ≠ committed leaf"
            ));
        }
        let nxt_leaf = compute_leaf_hash(&cfg, nxt_pos, &nxt_op.cells);
        if nxt_leaf != nxt_op.merkle.leaf {
            return Err(format!(
                "query {k}: nxt cells hash ≠ committed leaf"
            ));
        }

        // 3c. Verify Merkle paths to trace_root.
        if !MerkleTreeChannel::verify_opening(&cfg, proof.trace_root, &cur_op.merkle, &tag) {
            return Err(format!("query {k}: cur trace Merkle path failed"));
        }
        if !MerkleTreeChannel::verify_opening(&cfg, proof.trace_root, &nxt_op.merkle, &tag) {
            return Err(format!("query {k}: nxt trace Merkle path failed"));
        }

        // 3d. Skip constraint check at the last trace row.
        //
        // The merge functions (`deep_ali_merge_*`) gate constraints to
        // zero at `trace_row == n_trace - 1` because the
        // FRI/LDE wrap-around between row n-1 and row 0 isn't a real
        // AIR transition.
        let trace_row = pos / blowup;
        if trace_row >= n_trace - 1 {
            continue;
        }

        // 3e. Evaluate constraint formula at the queried trace cells
        //     and check `c_eval(x) · Z_H(x) = phi(x)`.
        //
        //     Soundness: at any queried position `x ∈ H_0` (the LDE
        //     domain), `c_eval(x) · Z_H(x) = Σ α_j · Φ_j(trace[x], x)`
        //     iff the constraint composition `phi` vanishes on H — i.e.
        //     all per-row AIR constraints are satisfied on the
        //     trace domain.  Each AIR's `fill_trace` is responsible
        //     for populating padding rows with constraint-satisfying
        //     values (gap #5b — fixed for use_hint 2026-05-09).
        let cvals = eval_per_row_fn(&cur_op.cells, &nxt_op.cells, trace_row);
        if cvals.len() != num_constraints {
            return Err(format!(
                "query {k}: eval_per_row returned {} ≠ {num_constraints} constraints",
                cvals.len()
            ));
        }
        let phi_at_pos: F = (0..num_constraints)
            .map(|j| comb_coeffs[j] * cvals[j])
            .sum();

        let pos_f = lde_omega_pow(pos, n0);
        let z_h = z_h_at(pos_f, n_trace);
        // c_eval_at_pos was extracted at loop top via
        // `extract_query_position_and_c_eval` (FRI or STIR aware).
        let lhs = c_eval_at_pos * Ext::from_fp(z_h);
        let rhs = Ext::from_fp(phi_at_pos);

        if lhs != rhs {
            return Err(format!(
                "query {k} (pos={pos}, row={trace_row}): constraint formula mismatch.\n  \
                 c_eval·Z_H = {lhs:?}\n  phi = {rhs:?}"
            ));
        }
    }

    Ok(())
}
