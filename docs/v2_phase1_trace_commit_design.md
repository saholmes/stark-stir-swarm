# Phase 1: Trace Commit + Per-Query Constraint Check — Design

**Goal:** close the malicious-prover soundness gap (audit doc gap #5)
by binding the FRI's `c_eval` commitment to a specific trace via a
parallel trace Merkle tree + per-query constraint-formula check.

**Soundness:** standard STARK pattern. With `r` FRI queries at rate
`ρ`, soundness ≈ `r · log₂(1/ρ)` bits. At `r=54`, `ρ=1/32`, that's
**270 bits** — comfortably above NIST PQ Level 1 (128 bits) and
sufficient for L3 with `r=79` and L5 with `r=105`.

**Why this is sound without DEEP/eq-1:** at each queried LDE position
`x`, the verifier opens the trace cells at row `x/blowup` and at row
`(x+blowup) mod n_lde` (cur and nxt for `eval_per_row`), evaluates
the constraint formula to get `phi(x)`, and checks
`c_eval(x) · Z_H(x) = phi(x)`. For a malicious prover with an
invalid AIR, `phi(x) ≠ 0` at some `x ∈ H`. The check fails when a
queried position falls at that `x` — happens with probability
`≥ 1 − ρ^r`.

## Components

### 1. New module: `crates/deep_ali/src/sub_air_with_trace.rs` (~250 LoC)

```rust
//! Trace-bound wrapper around prove_one_sub_air / verify_one_sub_air.
//! Adds a parallel trace LDE Merkle commitment and per-query trace
//! openings, with a verifier-side constraint-formula re-evaluation
//! that binds c_eval to the actual trace.

use crate::tower_field::TowerField;
use crate::sextic_ext::SexticExt;
use crate::octic_ext::OcticExt;
use crate::trace_import::lde_trace_columns;
use ark_goldilocks::Goldilocks as F;
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use merkle::{MerkleChannelCfg, MerkleTreeChannel, MerkleOpening, compute_leaf_hash};
use hash::sha3::{Digest, Sha3_256};
use hash::selected::HASH_BYTES;
use sha3::digest::ExtendableOutput;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

/// Pick the appropriate F_ext per active sha3-N feature.
#[cfg(any(feature = "sha3-256", feature = "sha3-384"))]
pub type Ext = SexticExt;
#[cfg(feature = "sha3-512")]
pub type Ext = OcticExt;
#[cfg(not(any(feature = "sha3-256", feature = "sha3-384", feature = "sha3-512")))]
pub type Ext = SexticExt;

/// Augmented proof bundle: FRI proof + trace commitment + per-query
/// trace openings.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SubAirProofWithTrace {
    pub fri_proof_bytes: Vec<u8>,
    pub trace_root: [u8; 32],
    /// One per FRI query: trace cells at queried LDE position (cur).
    pub trace_openings_cur: Vec<MerkleOpening>,
    /// One per FRI query: trace cells at (queried_pos + blowup) % n_lde
    /// (nxt — needed for `eval_per_row(cur, nxt, row)`).
    pub trace_openings_nxt: Vec<MerkleOpening>,
}

/// Trace Merkle tree config: packed leaves with W F-values per row.
fn trace_tree_config(n_lde: usize) -> MerkleChannelCfg {
    let arity = pick_arity_for_layer(n_lde, 16).max(2);
    let depth = merkle_depth(n_lde, arity);
    MerkleChannelCfg::new(vec![arity; depth], 0xAA)  // 0xAA = trace tree tag
}

fn trace_tree_hash_tag(n_lde: usize, width: usize, domain_sep: &[u8]) -> [u8; HASH_BYTES] {
    let mut h = Sha3_256::new();
    Digest::update(&mut h, b"deep_ali/trace_tree");
    Digest::update(&mut h, domain_sep);
    Digest::update(&mut h, &(n_lde as u64).to_le_bytes());
    Digest::update(&mut h, &(width as u64).to_le_bytes());
    let result = h.finalize();
    let mut out = [0u8; HASH_BYTES];
    out.copy_from_slice(result.as_slice());
    out
}

/// Build the trace LDE Merkle tree.  Each leaf at row `i` packs all
/// W column-cells: `[lde[0][i], lde[1][i], …, lde[W-1][i]]`.
fn commit_trace_lde(
    lde: &[Vec<F>],
    domain_sep: &[u8],
) -> ([u8; 32], MerkleTreeChannel) {
    let n_lde = lde[0].len();
    let width = lde.len();
    let cfg = trace_tree_config(n_lde);
    let tag = trace_tree_hash_tag(n_lde, width, domain_sep);
    let mut tree = MerkleTreeChannel::new(cfg, tag);
    for i in 0..n_lde {
        let leaf: Vec<F> = (0..width).map(|c| lde[c][i]).collect();
        tree.push_leaf(&leaf);
    }
    let root = tree.finalize();
    (root, tree)
}

/// Augment pi_hash to bind a sub-AIR's trace_root.
fn augment_pi_hash(
    pi_hash: &[u8; 32],
    trace_root: &[u8; 32],
    domain_sep: &[u8],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    Digest::update(&mut h, b"deep_ali/sub_air/aug_pi_hash");
    Digest::update(&mut h, domain_sep);
    Digest::update(&mut h, pi_hash);
    Digest::update(&mut h, trace_root);
    h.finalize().into()
}

/// LDE domain element at index `i`.  H_0 has size n_lde; the
/// generator is the (n_lde)-th root of unity in Goldilocks.
fn lde_domain_element(i: usize, n_lde: usize) -> F {
    let dom = GeneralEvaluationDomain::<F>::new(n_lde).expect("LDE domain");
    dom.element(i)  // = ω^i
}

/// Z_H(x) = x^T - 1, where T = trace size (n_trace).
fn z_h_at(x: F, n_trace: usize) -> F {
    x.pow(&[n_trace as u64]) - F::one()
}

/// Extract the LDE position at FRI query k (layer-0 position).
fn query_position_at(
    fri_proof: &crate::fri::DeepFriProof<Ext>,
    k: usize,
) -> usize {
    fri_proof.queries[k].per_layer_refs[0].i
}

/// Extract the f_val (= c_eval(x)) at FRI query k (layer-0 payload).
fn query_f_val(
    fri_proof: &crate::fri::DeepFriProof<Ext>,
    k: usize,
) -> Ext {
    fri_proof.queries[k].per_layer_payloads[0].f_val
}

pub fn prove_one_sub_air_with_trace(
    trace: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    c_eval_fn: impl FnOnce(&[Vec<F>], usize, usize) -> Vec<F>,
) -> SubAirProofWithTrace {
    let n0 = n_trace * blowup;
    let lde = lde_trace_columns(trace, n_trace, blowup).expect("LDE");

    // 1. Commit trace LDE.
    let (trace_root, trace_tree) = commit_trace_lde(&lde, domain_sep);

    // 2. Augment pi_hash to bind trace_root.
    let aug_pi_hash = augment_pi_hash(&pi_hash, &trace_root, domain_sep);

    // 3. Compute c_eval and run FRI with aug_pi_hash.
    let c_eval = c_eval_fn(&lde, n_trace, blowup);
    let domain = crate::fri::FriDomain::new_radix2(n0);
    let params = crate::v2_fri_params(n0, aug_pi_hash);  // existing helper
    let fri_proof = crate::fri::deep_fri_prove::<Ext>(c_eval, domain, &params);

    // 4. For each FRI query, open trace at (cur_pos, nxt_pos).
    let mut trace_openings_cur = Vec::with_capacity(fri_proof.queries.len());
    let mut trace_openings_nxt = Vec::with_capacity(fri_proof.queries.len());
    for k in 0..fri_proof.queries.len() {
        let pos = query_position_at(&fri_proof, k);
        let nxt_pos = (pos + blowup) % n0;
        trace_openings_cur.push(trace_tree.open(pos));
        trace_openings_nxt.push(trace_tree.open(nxt_pos));
    }

    // 5. Serialize FRI proof and bundle.
    let fri_proof_bytes = serialize_fri_proof(&fri_proof);

    SubAirProofWithTrace {
        fri_proof_bytes,
        trace_root,
        trace_openings_cur,
        trace_openings_nxt,
    }
}

pub fn verify_one_sub_air_with_trace(
    proof: &SubAirProofWithTrace,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    width: usize,
    num_constraints: usize,
    eval_per_row_fn: impl Fn(&[F], &[F], usize) -> Vec<F>,
) -> Result<(), String> {
    let n0 = n_trace * blowup;
    let aug_pi_hash = augment_pi_hash(&pi_hash, &proof.trace_root, domain_sep);

    // 1. Verify FRI proof against aug_pi_hash.
    let fri_proof = deserialize_fri_proof(&proof.fri_proof_bytes)
        .map_err(|e| format!("FRI proof deserialization: {e}"))?;
    let params = crate::v2_fri_params(n0, aug_pi_hash);
    if !crate::fri::deep_fri_verify::<Ext>(&params, &fri_proof) {
        return Err("FRI verify rejected".into());
    }

    // 2. Recompute combination coeffs (must match prover's derivation).
    let comb_coeffs = crate::comb_coeffs(num_constraints, &aug_pi_hash, domain_sep);
    //                     ^^^^^^^^^^^ make `comb_coeffs` pub(crate) or move to this module.

    // 3. For each FRI query, verify trace openings + check constraint
    //    formula c_eval(x) · Z_H(x) = phi(x).
    let cfg = trace_tree_config(n0);
    let trace_tag = trace_tree_hash_tag(n0, width, domain_sep);

    if proof.trace_openings_cur.len() != fri_proof.queries.len()
        || proof.trace_openings_nxt.len() != fri_proof.queries.len()
    {
        return Err(format!(
            "trace openings count mismatch: got cur={} nxt={} expected={}",
            proof.trace_openings_cur.len(),
            proof.trace_openings_nxt.len(),
            fri_proof.queries.len(),
        ));
    }

    for k in 0..fri_proof.queries.len() {
        let pos = query_position_at(&fri_proof, k);
        let nxt_pos = (pos + blowup) % n0;

        let cur_op = &proof.trace_openings_cur[k];
        let nxt_op = &proof.trace_openings_nxt[k];

        if cur_op.index != pos {
            return Err(format!("query {k} cur opening index {} ≠ expected {pos}",
                cur_op.index));
        }
        if nxt_op.index != nxt_pos {
            return Err(format!("query {k} nxt opening index {} ≠ expected {nxt_pos}",
                nxt_op.index));
        }

        // 3a. Verify Merkle paths for cur and nxt openings.
        if !MerkleTreeChannel::verify_opening(&cfg, proof.trace_root, cur_op, &trace_tag) {
            return Err(format!("query {k} cur trace Merkle verify failed"));
        }
        if !MerkleTreeChannel::verify_opening(&cfg, proof.trace_root, nxt_op, &trace_tag) {
            return Err(format!("query {k} nxt trace Merkle verify failed"));
        }

        // 3b. Extract trace cells from leaf data.
        let cur_cells = leaf_to_trace_cells(cur_op, width)?;
        let nxt_cells = leaf_to_trace_cells(nxt_op, width)?;

        // 3c. Evaluate constraint formula.
        let trace_row = pos / blowup;
        let cvals = eval_per_row_fn(&cur_cells, &nxt_cells, trace_row);
        if cvals.len() != num_constraints {
            return Err(format!("query {k}: eval_per_row returned {} != {} constraints",
                cvals.len(), num_constraints));
        }
        let phi_at_pos: F = (0..num_constraints)
            .map(|j| comb_coeffs[j] * cvals[j])
            .sum();

        // 3d. Compute c_eval(x) · Z_H(x).
        let pos_f = lde_domain_element(pos, n0);
        let z_h_pos = z_h_at(pos_f, n_trace);
        let c_eval_pos = query_f_val(&fri_proof, k);  // Ext-valued
        let lhs = c_eval_pos * Ext::from_fp(z_h_pos);
        let rhs = Ext::from_fp(phi_at_pos);

        if lhs != rhs {
            return Err(format!(
                "query {k} (pos={pos}): constraint formula check failed.\n  \
                 c_eval·Z_H = {lhs:?}\n  phi = {rhs:?}"
            ));
        }
    }

    Ok(())
}

fn leaf_to_trace_cells(op: &MerkleOpening, width: usize) -> Result<Vec<F>, String> {
    if op.leaf_data.len() != width {
        return Err(format!("leaf data length {} != trace width {width}", op.leaf_data.len()));
    }
    Ok(op.leaf_data.clone())
}

// FRI proof (de)serialization helpers — same as orchestration's existing
// `serialize_fri` / `deserialize_fri`.
fn serialize_fri_proof(proof: &crate::fri::DeepFriProof<Ext>) -> Vec<u8> { … }
fn deserialize_fri_proof(bytes: &[u8]) -> Result<crate::fri::DeepFriProof<Ext>, String> { … }
```

### 2. Orchestration changes (`ml_dsa_verify_air_v2_orchestration.rs`) (~150 LoC)

```rust
// Update V2ProofReal to use SubAirProofWithTrace per sub-AIR.
pub struct V2ProofReal {
    pub pi_hash: [u8; 32],
    pub c_tilde_prime: [u8; C_TILDE_BYTES],
    pub fri_v17:        sub_air_with_trace::SubAirProofWithTrace,
    pub fri_intt:       Vec<sub_air_with_trace::SubAirProofWithTrace>,  // K = 4
    pub fri_decompose:  sub_air_with_trace::SubAirProofWithTrace,
    pub fri_use_hint:   sub_air_with_trace::SubAirProofWithTrace,
    pub fri_w1_encode:  sub_air_with_trace::SubAirProofWithTrace,
    pub fri_transcript: sub_air_with_trace::SubAirProofWithTrace,
    pub fri_t_mem:      sub_air_with_trace::SubAirProofWithTrace,
}

// Update prove_v2_real: replace prove_one_sub_air with
// prove_one_sub_air_with_trace at all 7 call sites.
// Pass domain_sep (existing tags: b"v17", b"intt:" + k, etc.).

// Update verify_v2_real: replace verify_one_sub_air with
// verify_one_sub_air_with_trace at all 7 call sites.
// Pass eval_per_row closure for each AIR.
```

### 3. `lib.rs` change

Make `comb_coeffs` accessible from `sub_air_with_trace.rs`. Either
`pub(crate)` it in orchestration, or move it to the new module.

### 4. Tests

The existing `v2_real_round_trip` test should pass with the new
prove/verify path (honest round-trip is unaffected). Add:
- `v2_malicious_trace_rejected`: alter one trace cell post-hoc;
  expect verify to reject.
- `v2_constraint_violation_rejected`: corrupt a single constraint
  output in the trace; expect verify to reject.

## Estimated effort

| Task | LoC | Time |
|------|-----|------|
| sub_air_with_trace module | ~250 | 1.5h |
| Orchestration prove integration (7 sites) | ~80 | 30min |
| Orchestration verify integration (7 sites) | ~80 | 30min |
| Test additions | ~150 | 1h |
| L1/L3/L5 round-trip + debugging | — | 1h |
| **Total** | **~560** | **~4-5h focused** |

## Things to verify before starting (status: PRE-VALIDATED)

1. **`MerkleOpening` struct fields** — VALIDATED.
   `merkle/src/lib.rs:136-140`:
   ```rust
   pub struct MerkleOpening {
       pub leaf: [u8; HASH_BYTES],   // leaf HASH, NOT raw data
       pub path: Vec<Vec<[u8; HASH_BYTES]>>,
       pub index: usize,
   }
   ```
   **Implication**: leaf data must be sent separately alongside the
   opening. The augmented proof needs:
   ```rust
   pub struct TraceOpeningAtQuery {
       pub cells: Vec<F>,             // W F-values at the queried row
       pub merkle: MerkleOpening,     // proof of cells against trace_root
   }
   ```
   Verifier path:
   ```rust
   let expected_leaf = compute_leaf_hash(&cfg, op.merkle.index, &op.cells);
   if expected_leaf != op.merkle.leaf { return Err("leaf hash mismatch"); }
   if !verify_opening(&cfg, trace_root, &op.merkle, &tag) { return Err("path"); }
   ```

2. **`fri_proof.queries[k].per_layer_refs[0].i` is the LDE-domain index.**
   VALIDATED via `fri.rs:1240-1247` and `fri.rs:1462` (f0 = layer 0).

3. **`v2_fri_params` is accessible from `sub_air_with_trace.rs`.**
   Currently private in orchestration. Move to `pub(crate)` OR move into
   the new module (it's only ~12 LoC).

4. **`comb_coeffs` is accessible.** Same — make `pub(crate)`.

5. **FRI proof's f_val at layer-0 = c_eval(x_pos).** VALIDATED via
   `fri.rs:1447, 1462` (`f0 → f0_ext → f_layers_ext[0]`); per-query
   payload `f_val` reads from this.

6. **`compute_leaf_hash(cfg, index, values: &[F])`** — VALIDATED at
   `merkle/src/lib.rs:806-813`. Use this for verifier-side leaf
   reconstruction.

## Phase 2 follow-up (paper-exact eq-1)

After Phase 1 lands and tests pass, Phase 2:
1. Lift `comb_coeffs` to F_ext (Vec<E>).
2. Lift the merge pipeline (phi, ifft, fft, poly_div_zh) to E-valued.
3. Apply DEEP correction at z ∈ F_pe.
4. Add HVZK blinding β·R(X).
5. Optionally lift `deep_fri_prove` to accept Vec<E> initial functions.

Phase 1's trace-commit pattern remains useful as a soundness fallback
even after Phase 2 (the standard STARK pattern is well-trodden).

## Next-session checklist

When starting Phase 1 implementation:
- [ ] Verify the 5 "things to verify" items above with quick greps.
- [ ] Create `sub_air_with_trace.rs` with the helpers + prove fn.
- [ ] Add unit test for `commit_trace_lde` round-trip (single sub-AIR,
      e.g. T-MEM).
- [ ] Add unit test for `prove + verify` round-trip on T-MEM at L1.
- [ ] If T-MEM works, propagate to V17.
- [ ] If V17 works, propagate to remaining 5 sub-AIRs.
- [ ] Run `v2_real_round_trip` at L1, L3, L5 to confirm honest path.
- [ ] Add `v2_malicious_trace_rejected` test to confirm soundness.
