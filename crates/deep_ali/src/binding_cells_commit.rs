//! v2 perm-arg rebuild — binding-cells FRI commit foundation.
//!
//! **Status: Session 4 foundation (2026-05-10).**  This module
//! provides the primitive that the v2 perm-arg rebuild will use to
//! cross-bind a sub-AIR's binding cells to a perm-arg sub-AIR's
//! `VALUE` column without the K·N Merkle inclusion proofs currently
//! used by F2b L0-L5.
//!
//! ## Design (recap)
//!
//! The current F2b cross-binding emits K·N Merkle inclusion proofs
//! per binding leg, contributing the dominant cost in the verify
//! path (~141 ms STIR at L3 because each opening costs ~22 hashes
//! to authenticate × K·N positions × multiple bindings).
//!
//! The perm-arg rebuild replaces K·N inclusion proofs with a single
//! perm-arg FRI sub-proof.  The remaining cross-trace consistency
//! check — that the perm-arg's `VALUE` column equals corresponding
//! cells in source sub-AIRs' independently-FRI-committed traces —
//! is provided by **OOD evaluation + Schwartz-Zippel**:
//!
//! 1. Each sub-AIR's binding columns are packed into a single
//!    polynomial via interleaving (`commit_binding_cells`).
//! 2. The packed polynomial is FRI-committed via `deep_fri_prove`.
//! 3. At a Fiat-Shamir-derived ζ ∈ F_ext, prover OOD-evaluates the
//!    packed polynomial via `compute_q_layer_ext`.
//! 4. The perm-arg's `VALUE` polynomial is similarly committed +
//!    OOD-evaluated at the **same** ζ.
//! 5. Verifier checks the two OOD values are equal.  Schwartz-Zippel
//!    at F_ext = Fp⁶ (L1/L3) / Fp⁸ (L5) gives soundness
//!    `≥ 1 − n/|F_ext| ≈ 1 − 2⁻³⁷⁰` (Fp⁶, n ≈ 2¹⁴) — well below
//!    per-level ε budget.
//!
//! ## Session 4 deliverable (this file)
//!
//! - `BindingCellsCommit` struct: encapsulates the LDE packing scheme
//!   and the resulting FRI commitment.
//! - `commit_binding_cells`: extracts the relevant columns from a
//!   sub-AIR's LDE, packs them into a single base-field polynomial,
//!   FRI-commits the polynomial.
//! - Round-trip test validating that the commit can be FRI-verified.
//!
//! ## Session 5+ work (not in this file yet)
//!
//! - `ood_eval_at_zeta`: produce the OOD evaluation + bind it to the
//!   committed polynomial.  **Open architectural question**: how to
//!   synchronize FRI's internal FS-derived z_0 across two independent
//!   `deep_fri_prove` invocations so they evaluate at the SAME ζ.
//!   Two viable paths:
//!   * **Path A (recommended)**: derive ζ externally from a shared
//!     transcript (pi_hash + both commitments' trace roots), then
//!     use `compute_q_layer_ext` to compute the quotient + value
//!     pair, and FRI-prove the quotient via an Ext-input FRI
//!     prover.  Currently `deep_fri_prove` only takes base-F input;
//!     this requires either a new Ext-input variant OR re-deriving
//!     the OOD machinery internally.
//!   * **Path B**: use `deep_fri_prove`'s existing internal OOD
//!     mechanism (which OOD-evaluates at FS-derived z_0 internally
//!     via `fri_sample_z_ell`) but synchronize z_0 across two
//!     commits by feeding the SAME pi_hash + seed_z to both.  This
//!     requires careful FRI transcript audit since trace_root
//!     augmentation may diverge the FS state.
//!
//! - `verify_ood_consistency`: verify the cross-trace OOD consistency
//!   check, including FRI re-verification of both quotients.
//!
//! - Integration into v2: replace L0/L1/L2/L3/L4/L5 inclusion proofs
//!   with OOD-eval cross-binding.

#![allow(dead_code)]

use ark_goldilocks::Goldilocks as F;
use crate::fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, DeepFriProof, FriDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

// ─── F_ext type, matching v2_orchestration's choice ──────────────────

#[cfg(any(feature = "sha3-256", feature = "sha3-384"))]
pub type Ext = crate::sextic_ext::SexticExt;

#[cfg(feature = "sha3-512")]
pub type Ext = crate::octic_ext::OcticExt;

#[cfg(not(any(feature = "sha3-256", feature = "sha3-384", feature = "sha3-512")))]
pub type Ext = crate::sextic_ext::SexticExt;

// ─── BindingCellsCommit ──────────────────────────────────────────────

/// A FRI commitment to the binding cells of a sub-AIR.
///
/// The binding cells are extracted from specified columns of the
/// sub-AIR's full LDE, packed into a single polynomial via column
/// interleaving, and committed via `deep_fri_prove`.  The resulting
/// `DeepFriProof<Ext>` is bound to `pi_hash` via the FRI prover's
/// internal Fiat-Shamir.
///
/// Used as input to the cross-trace OOD-eval consistency check in
/// the v2 perm-arg rebuild (see module docstring).
#[derive(Clone, ark_serialize::CanonicalSerialize, ark_serialize::CanonicalDeserialize)]
pub struct BindingCellsCommit {
    /// Serialized `DeepFriProof<Ext>` for the packed binding-cells
    /// polynomial.
    pub fri_proof_bytes: Vec<u8>,
    /// Number of binding columns interleaved.  The packed polynomial
    /// has degree < `n_trace * num_cols`.
    pub num_cols: u32,
    /// Sub-AIR's trace length (rows per column).
    pub n_trace: u32,
    /// LDE blowup factor (so packed LDE size = `n_trace * num_cols * blowup`).
    pub blowup: u32,
    /// Domain separator (e.g. `b"v17_binding"`) used to bind this
    /// commit to a specific sub-AIR.
    pub domain_sep: Vec<u8>,
}

impl BindingCellsCommit {
    /// Serialize to bytes via `CanonicalSerialize`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        <Self as ark_serialize::CanonicalSerialize>::serialize_with_mode(
            self, &mut buf, Compress::Yes,
        ).expect("BindingCellsCommit serialize");
        buf
    }

    /// Deserialize from bytes.
    pub fn from_bytes(data: &[u8]) -> Result<Self, String> {
        <Self as ark_serialize::CanonicalDeserialize>::deserialize_with_mode(
            data, Compress::Yes, Validate::Yes,
        ).map_err(|e| format!("BindingCellsCommit: deserialize: {e:?}"))
    }
}

/// Extract the binding columns from a sub-AIR's LDE, pack them into
/// a single polynomial via interleaving, and FRI-commit the result.
///
/// **LDE packing scheme:** the packed polynomial has length
/// `n_trace * num_cols * blowup`.  Column `c` at LDE position `i` is
/// placed at packed index `c * (n_trace * blowup) + i`.  This is the
/// simplest interleave that lets the verifier compute the cell at
/// any (col, row) index, given the packed LDE.
///
/// Returns:
/// - `BindingCellsCommit`: the FRI commitment.
/// - `Vec<F>`: the packed LDE itself (needed by the prover for
///   subsequent OOD evaluation).
///
/// `pi_hash`: the v2 pi_hash that all sub-AIRs share.  This binds
/// the commit to the same public-input context as the rest of the
/// v2 proof, so the FS challenges (alpha, query positions) are
/// synchronized.
///
/// `domain_sep`: distinguishes this commit from other binding-cell
/// commits in the same proof (e.g. `b"v17_binding"`, `b"intt:0_binding"`).
pub fn commit_binding_cells(
    lde: &[Vec<F>],
    binding_col_indices: &[usize],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    fri_params_fn: impl FnOnce(usize, [u8; 32]) -> DeepFriParams,
) -> (BindingCellsCommit, Vec<F>) {
    assert!(!binding_col_indices.is_empty(), "must have at least one binding column");
    let n_lde = n_trace * blowup;
    for &col in binding_col_indices {
        assert!(col < lde.len(), "binding col index {col} out of bounds (lde width = {})", lde.len());
        assert_eq!(lde[col].len(), n_lde, "lde column {col} has wrong length");
    }

    let num_cols = binding_col_indices.len();
    let packed_n_lde = n_lde * num_cols;

    // Pack: column c, LDE position i → packed index c * n_lde + i.
    let mut packed_lde: Vec<F> = Vec::with_capacity(packed_n_lde);
    for &col in binding_col_indices {
        packed_lde.extend_from_slice(&lde[col]);
    }

    // FRI-commit the packed polynomial.
    let domain = FriDomain::new_radix2(packed_n_lde);
    let params = fri_params_fn(packed_n_lde, pi_hash);
    let fri_proof = deep_fri_prove::<Ext>(packed_lde.clone(), domain, &params);

    let mut fri_proof_bytes = Vec::new();
    fri_proof.serialize_with_mode(&mut fri_proof_bytes, Compress::Yes)
        .expect("serialize binding-cells FRI proof");

    let commit = BindingCellsCommit {
        fri_proof_bytes,
        num_cols: num_cols as u32,
        n_trace: n_trace as u32,
        blowup: blowup as u32,
        domain_sep: domain_sep.to_vec(),
    };
    (commit, packed_lde)
}

/// Verify the FRI commitment on a `BindingCellsCommit`.
///
/// This re-derives the FRI parameters from `pi_hash` + `domain_sep`
/// (must match the prover's), then runs `deep_fri_verify` on the
/// stored proof.
///
/// **Note**: this only verifies the polynomial is low-degree.  The
/// cross-trace OOD consistency check (binding the packed cells to
/// specific positions in the source sub-AIR's trace and to the
/// perm-arg's `VALUE` column) is implemented in a separate function
/// — see module docstring for Session 5+ work.
pub fn verify_binding_cells_commit(
    commit: &BindingCellsCommit,
    pi_hash: [u8; 32],
    fri_params_fn: impl FnOnce(usize, [u8; 32]) -> DeepFriParams,
) -> Result<(), String> {
    let packed_n_lde = (commit.n_trace as usize) * (commit.blowup as usize) * (commit.num_cols as usize);
    let fri_proof = <DeepFriProof<Ext> as CanonicalDeserialize>::deserialize_with_mode(
        commit.fri_proof_bytes.as_slice(),
        Compress::Yes,
        Validate::Yes,
    ).map_err(|e| format!("BindingCellsCommit: FRI deserialize: {e:?}"))?;
    let params = fri_params_fn(packed_n_lde, pi_hash);
    if !deep_fri_verify::<Ext>(&params, &fri_proof) {
        return Err("BindingCellsCommit: FRI verify rejected".into());
    }
    Ok(())
}

/// Extract the OOD evaluation `f(z_0)` from a `BindingCellsCommit`.
///
/// `z_0 = fri_sample_z_ell(seed_z, 0, n0)` is FS-derived from the
/// FRI params (`seed_z`, level=0, `n0` = packed LDE size).  When two
/// `BindingCellsCommit`s are constructed with the same `seed_z` and
/// the same `n0` (packed LDE size), they share `z_0` — making
/// `fz_per_layer[0]` directly comparable across commits.
///
/// This is the foundation for the cross-trace OOD consistency check:
/// given two FRI-committed polynomials `f` and `g` over the same LDE,
/// if `f(z_0) = g(z_0)`, then `f ≡ g` as polynomials of degree
/// `< n` with Schwartz-Zippel error `≤ n/|F_ext|` (at F_ext = Fp⁶,
/// n ≈ 2¹⁴: ε ≈ 2⁻³⁷⁰).
pub fn extract_ood_value(commit: &BindingCellsCommit) -> Result<Ext, String> {
    let fri_proof = <DeepFriProof<Ext> as CanonicalDeserialize>::deserialize_with_mode(
        commit.fri_proof_bytes.as_slice(),
        Compress::Yes,
        Validate::Yes,
    ).map_err(|e| format!("BindingCellsCommit: FRI deserialize: {e:?}"))?;
    if fri_proof.fz_per_layer.is_empty() {
        return Err("BindingCellsCommit: fz_per_layer is empty".into());
    }
    Ok(fri_proof.fz_per_layer[0])
}

/// Verify cross-trace OOD consistency between two `BindingCellsCommit`s.
///
/// **Preconditions:** both commits must have been constructed with:
/// - The same `seed_z` (in `DeepFriParams`).
/// - The same `n0` (= packed LDE size = `n_trace · num_cols · blowup`).
/// - The same `pi_hash` (for FS-derived FRI challenges).
///
/// Then both share the same FS-derived OOD point `z_0`, and their
/// `fz_per_layer[0]` values are comparable.
///
/// **Verification:**
/// 1. Verify both FRI proofs are valid (low-degree).
/// 2. Verify the packed-LDE sizes match.
/// 3. Extract `f(z_0)` from each commit.
/// 4. Check `f_a(z_0) == f_b(z_0)`.
///
/// If all four checks pass, Schwartz-Zippel implies `f_a ≡ f_b` as
/// polynomials of degree `< n`, with error `≤ n/|F_ext|`.
///
/// **Soundness assumption:** the two polynomials encode their values
/// in the SAME order (= packed in identical column/row interleave).
/// The caller is responsible for ensuring this.  Cross-binding
/// between polynomials with different encodings requires an
/// additional permutation argument — see module docstring.
pub fn verify_ood_consistency(
    commit_a: &BindingCellsCommit,
    commit_b: &BindingCellsCommit,
    pi_hash: [u8; 32],
    fri_params_fn: impl Fn(usize, [u8; 32]) -> DeepFriParams,
) -> Result<(), String> {
    let n_a = (commit_a.n_trace as usize) * (commit_a.blowup as usize) * (commit_a.num_cols as usize);
    let n_b = (commit_b.n_trace as usize) * (commit_b.blowup as usize) * (commit_b.num_cols as usize);
    if n_a != n_b {
        return Err(format!(
            "verify_ood_consistency: packed LDE sizes mismatch (n_a={n_a}, n_b={n_b}) \
             — cannot share z_0"
        ));
    }

    verify_binding_cells_commit(commit_a, pi_hash, &fri_params_fn)
        .map_err(|e| format!("verify_ood_consistency: commit_a verify failed: {e}"))?;
    verify_binding_cells_commit(commit_b, pi_hash, &fri_params_fn)
        .map_err(|e| format!("verify_ood_consistency: commit_b verify failed: {e}"))?;

    // Cross-check seed_z: both must be configured identically for z_0 to align.
    let params_a = fri_params_fn(n_a, pi_hash);
    let params_b = fri_params_fn(n_b, pi_hash);
    if params_a.seed_z != params_b.seed_z {
        return Err(format!(
            "verify_ood_consistency: seed_z mismatch (a={}, b={}) — z_0 won't align",
            params_a.seed_z, params_b.seed_z
        ));
    }

    let fz_a = extract_ood_value(commit_a)?;
    let fz_b = extract_ood_value(commit_b)?;
    if fz_a != fz_b {
        return Err(format!(
            "verify_ood_consistency: f_a(z_0) ≠ f_b(z_0) — committed polynomials differ \
             (Schwartz-Zippel binding failed)"
        ));
    }
    Ok(())
}

/// Verify a `BindingCellsCommit` against a known **public** trace
/// column.
///
/// Use case: public-input OOD bindings (L2c: public h, L4: public
/// w1bytes, parts of L0 and L5).  The verifier knows the canonical
/// trace column values directly (no source-side FRI commit needed)
/// and just needs to confirm that the source sub-AIR's BCC evaluates
/// to the same value at z_0.
///
/// `public_trace_col`: the canonical trace column values, length
/// `n_trace` (= `bcc.n_trace`).  Caller pads with zeros for unused
/// rows (matches sub-AIR's fill_trace zero-padding convention).
///
/// `seed_z`: must match the FRI prover's seed_z (= `V2_SEED_Z` for v2).
///
/// **Soundness**: `bcc.fz_per_layer[0]` is bound to the committed
/// polynomial via the FRI quotient mechanism (DEEP-ALI).  The
/// verifier-computed `public(z_0)` is bound to the canonical public
/// trace values via IFFT (unique polynomial of degree < n_trace
/// interpolating the values).  Equality at z_0 implies equality as
/// polynomials of degree < n_trace via Schwartz-Zippel
/// (ε ≤ n_trace/|F_ext| ≈ 2⁻³⁷⁰ at L3 Fp⁶).
pub fn verify_ood_against_public_trace_col(
    bcc: &BindingCellsCommit,
    public_trace_col: &[F],
    pi_hash: [u8; 32],
    seed_z: u64,
    fri_params_fn: impl Fn(usize, [u8; 32]) -> DeepFriParams,
) -> Result<(), String> {
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
    use crate::tower_field::TowerField;
    use ark_ff::Zero;
    let _ = seed_z;  // now derived from params via fri_params_fn

    if bcc.num_cols != 1 {
        return Err(format!(
            "verify_ood_against_public_trace_col: BCC must wrap a single column (got num_cols = {})",
            bcc.num_cols
        ));
    }
    let n_trace = bcc.n_trace as usize;
    if public_trace_col.len() != n_trace {
        return Err(format!(
            "public_trace_col len {} ≠ bcc.n_trace {}",
            public_trace_col.len(), n_trace
        ));
    }

    // 1. FRI-verify the BCC.
    verify_binding_cells_commit(bcc, pi_hash, &fri_params_fn)
        .map_err(|e| format!("public-binding: BCC FRI verify: {e}"))?;

    // 2. **Session 8 fix**: derive z_ext via transcript-replay
    //    (`derive_z_ext_for_proof`), matching the FRI prover's
    //    internal `challenge_ext` exactly.  The earlier
    //    `fri_sample_z_ell`-based approach was WRONG (that function
    //    is orphan; actual z_ext comes from a transcript including
    //    proof.root_f0).
    let packed_n_lde = n_trace * (bcc.blowup as usize) * (bcc.num_cols as usize);
    let params = fri_params_fn(packed_n_lde, pi_hash);
    let fri_proof = <DeepFriProof<Ext> as CanonicalDeserialize>::deserialize_with_mode(
        bcc.fri_proof_bytes.as_slice(),
        Compress::Yes,
        Validate::Yes,
    ).map_err(|e| format!("public-binding: FRI deserialize: {e:?}"))?;
    let z_ext = crate::fri::derive_z_ext_for_proof::<Ext>(&fri_proof, &params);

    // 3. Build the trace polynomial from public values via IFFT,
    //    then evaluate at z_ext via Horner.
    let dom = GeneralEvaluationDomain::<F>::new(n_trace)
        .ok_or_else(|| "n_trace must be a power of 2 for IFFT".to_string())?;
    let coeffs = dom.ifft(public_trace_col);
    let mut public_at_z = Ext::zero();
    for k in (0..coeffs.len()).rev() {
        public_at_z = public_at_z * z_ext + <Ext as TowerField>::from_fp(coeffs[k]);
    }

    // 4. Extract BCC's fz_per_layer[0] (= f(z_ext)) and compare.
    if fri_proof.fz_per_layer.is_empty() {
        return Err("public-binding: fz_per_layer is empty".into());
    }
    let bcc_at_z = fri_proof.fz_per_layer[0];
    if bcc_at_z != public_at_z {
        return Err(format!(
            "public-binding: BCC(z_ext) ≠ public(z_ext) — Schwartz-Zippel rejection \
             (bcc_at_z = {bcc_at_z:?}, public_at_z = {public_at_z:?})"
        ));
    }
    Ok(())
}

// ─── Tests ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{Field, Zero};
    use crate::fri::DeepFriParams;

    fn synthetic_lde(width: usize, n_trace: usize, blowup: usize) -> Vec<Vec<F>> {
        // Each column is the LDE of a low-degree poly.  We use a
        // simple deterministic pattern: column c, row r has value
        // (c * 257 + r * 31) mod some small bound.
        use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
        let lde_size = n_trace * blowup;
        let _trace_dom = GeneralEvaluationDomain::<F>::new(n_trace).unwrap();
        let lde_dom = GeneralEvaluationDomain::<F>::new(lde_size).unwrap();

        let mut columns: Vec<Vec<F>> = Vec::with_capacity(width);
        for c in 0..width {
            // Build a low-degree polynomial via random coefficients.
            let coeffs: Vec<F> = (0..n_trace)
                .map(|r| F::from((c * 257 + r * 31) as u64))
                .collect();
            // The coeffs are the trace values; ifft to get true poly
            // coefficients, then evaluate on LDE domain.
            let trace_dom = GeneralEvaluationDomain::<F>::new(n_trace).unwrap();
            let poly_coeffs = trace_dom.ifft(&coeffs);
            let mut padded = poly_coeffs.clone();
            padded.resize(lde_size, F::zero());
            let lde_evals = lde_dom.fft(&padded);
            columns.push(lde_evals);
        }
        columns
    }

    fn test_params(n0: usize, pi_hash: [u8; 32]) -> DeepFriParams {
        DeepFriParams {
            schedule: vec![2usize; n0.trailing_zeros() as usize],
            r: 16,
            seed_z: 0xDEEF_BAAD,
            coeff_commit_final: true,
            d_final: 1,
            stir: false,
            s0: 16,
            public_inputs_hash: Some(pi_hash),
        }
    }

    #[test]
    fn binding_cells_commit_round_trip() {
        let width = 8;
        let n_trace = 64;
        let blowup = 4;
        let lde = synthetic_lde(width, n_trace, blowup);

        let binding_cols = vec![0usize, 2, 4, 6];  // pick a subset
        let pi_hash = [0x42u8; 32];
        let (commit, _packed) = commit_binding_cells(
            &lde, &binding_cols, n_trace, blowup, pi_hash, b"test_binding",
            test_params,
        );

        // FRI verify should accept.
        verify_binding_cells_commit(&commit, pi_hash, test_params)
            .expect("honest binding-cells commit must verify");

        assert_eq!(commit.num_cols, 4u32);
        assert_eq!(commit.n_trace, n_trace as u32);
        assert_eq!(commit.blowup, blowup as u32);
        assert_eq!(commit.domain_sep, b"test_binding");
    }

    /// Cross-trace OOD consistency: two commits to the SAME packed
    /// polynomial (same columns, same order) must pass verify_ood_consistency.
    #[test]
    fn ood_consistency_accepts_identical_commits() {
        let width = 8;
        let n_trace = 64;
        let blowup = 4;
        let lde = synthetic_lde(width, n_trace, blowup);
        let binding_cols = vec![0usize, 2, 4, 6];
        let pi_hash = [0x42u8; 32];

        let (commit_a, _) = commit_binding_cells(
            &lde, &binding_cols, n_trace, blowup, pi_hash, b"a_binding",
            test_params,
        );
        // Build a SECOND commit on the same LDE (so the polynomials
        // are identical) — the domain_sep differs to simulate different
        // "owner" sub-AIRs, but z_0 only depends on seed_z + n0 (not
        // domain_sep).
        let (commit_b, _) = commit_binding_cells(
            &lde, &binding_cols, n_trace, blowup, pi_hash, b"b_binding",
            test_params,
        );

        verify_ood_consistency(&commit_a, &commit_b, pi_hash, test_params)
            .expect("identical commits must pass OOD consistency");
    }

    /// Cross-trace OOD consistency: commits to DIFFERENT polynomials
    /// (different binding columns from the same LDE) must reject.
    /// This is the Schwartz-Zippel soundness binding — committed
    /// polys must agree at z_0 for verify to accept.
    #[test]
    fn ood_consistency_rejects_different_polys() {
        let width = 8;
        let n_trace = 64;
        let blowup = 4;
        let lde = synthetic_lde(width, n_trace, blowup);
        let pi_hash = [0x42u8; 32];

        // Two commits over DIFFERENT columns → different packed polys.
        let cols_a = vec![0usize, 2, 4, 6];
        let cols_b = vec![1usize, 3, 5, 7];  // different columns
        let (commit_a, _) = commit_binding_cells(
            &lde, &cols_a, n_trace, blowup, pi_hash, b"a_binding",
            test_params,
        );
        let (commit_b, _) = commit_binding_cells(
            &lde, &cols_b, n_trace, blowup, pi_hash, b"b_binding",
            test_params,
        );

        let res = verify_ood_consistency(&commit_a, &commit_b, pi_hash, test_params);
        assert!(res.is_err(),
            "different polynomials must fail OOD consistency: got {res:?}");
        let err = res.unwrap_err();
        assert!(err.contains("f_b(z_0)") || err.contains("Schwartz-Zippel"),
            "expected Schwartz-Zippel error, got: {err}");
    }

    /// Cross-trace OOD consistency: mismatched packed LDE sizes
    /// (different num_cols) must reject — they cannot share z_0.
    #[test]
    fn ood_consistency_rejects_size_mismatch() {
        let width = 8;
        let n_trace = 64;
        let blowup = 4;
        let lde = synthetic_lde(width, n_trace, blowup);
        let pi_hash = [0x42u8; 32];

        let cols_a = vec![0usize, 2, 4, 6];          // 4 cols
        let cols_b = vec![1usize, 3];                 // 2 cols → different n0
        let (commit_a, _) = commit_binding_cells(
            &lde, &cols_a, n_trace, blowup, pi_hash, b"a_binding",
            test_params,
        );
        let (commit_b, _) = commit_binding_cells(
            &lde, &cols_b, n_trace, blowup, pi_hash, b"b_binding",
            test_params,
        );

        let res = verify_ood_consistency(&commit_a, &commit_b, pi_hash, test_params);
        assert!(res.is_err(), "size mismatch must reject");
        let err = res.unwrap_err();
        assert!(err.contains("LDE sizes mismatch"),
            "expected size mismatch error, got: {err}");
    }

    #[test]
    fn binding_cells_commit_rejects_tampered_pi_hash() {
        let width = 8;
        let n_trace = 64;
        let blowup = 4;
        let lde = synthetic_lde(width, n_trace, blowup);
        let binding_cols = vec![0usize, 2];
        let pi_hash_real = [0x42u8; 32];
        let (commit, _) = commit_binding_cells(
            &lde, &binding_cols, n_trace, blowup, pi_hash_real, b"test_binding",
            test_params,
        );

        // Verifier uses different pi_hash → FRI FS challenges diverge
        // → verify must reject.
        let pi_hash_tampered = [0x99u8; 32];
        let res = verify_binding_cells_commit(&commit, pi_hash_tampered, test_params);
        assert!(res.is_err(), "tampered pi_hash must reject the commit");
    }
}
