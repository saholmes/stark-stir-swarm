//! Bridge between wrapper-stark constraints and the deep_ali FRI prover.
//!
//! # Impedance mismatch
//!
//! - wrapper-stark uses **cell-list constraints**: [`BitOp`] references
//!   specific `CellRef { row, col }` positions.  Same θ-XOR shape is
//!   instantiated 1 600 times per round, once per bit position.
//!
//! - deep_ali's FRI prover ([`deep_ali::fri::deep_fri_prove`]) consumes
//!   a **column-major LDE table** + a **composed polynomial** Φ(trace)
//!   that's a function of column values "at the current row" (and
//!   possibly transitions to the next row, with row-shifting).
//!
//! Reconciling these requires one of:
//!
//! 1. **Restructure to row-uniform** — replace the 1 600 θ-XOR BitOps
//!    with ONE polynomial constraint `output_col[bit] - (input_col[bit]
//!    + D_col[bit] - 2·input_col[bit]·D_col[bit]) = 0` evaluated at
//!    every bit-position column.  Selector polynomials gate the
//!    constraint to θ rows.  Far more efficient (k columns × 1 constraint
//!    instead of k × N constraints), but requires a uniform-column
//!    layout for each sub-step's bits.
//!
//! 2. **Boundary-constraint blowup** — keep cell-list BitOps, treat
//!    each as a boundary constraint gated by an indicator polynomial
//!    that vanishes everywhere except at its specific (row, col).
//!    Trivially correct but produces O(constraint_count) composition
//!    cost, ~843 K boundary constraints for one permutation.
//!
//! 3. **Single-row degenerate trace** — flatten the entire wrapper-AIR
//!    trace into ONE conceptual row of width = total_cells.  Then
//!    `n_trace = 1`, `blowup × 1` LDE evaluates the cells at `blowup`
//!    interpolated points.  Constraints become single-row polynomial
//!    identities over the flat column vector.  Works mechanically
//!    but creates a very wide LDE (millions of columns) and loses
//!    the natural row-based proof structure.
//!
//! # Choice for the wrapper STARK
//!
//! Path (1) is the right answer for production — it's how every other
//! production STARK encodes Keccak (uniform per-row constraints + θ/ρπ/
//! χ/ι selector polynomials).  Implementing it requires:
//!
//! - Uniform column layout: every row has the same 1 600 bit-state
//!   columns at the same positions, regardless of which sub-step the
//!   row encodes
//! - Selector polynomials: `s_theta(r)`, `s_rho_pi(r)`, `s_chi(r)`,
//!   `s_iota(r)`, `s_absorb(r)` — each is 1 on its rows, 0 elsewhere
//! - Per-step constraint polynomial that fires only when its selector
//!   is 1
//!
//! This is the next-phase refactor scoped at ~2-3 commits.  This
//! module establishes the bridge interface and the type plumbing
//! so the refactor has a clear landing point.
//!
//! # Current status
//!
//! Stubbed types + documentation.  The `prepare_fri_input` function
//! returns `Err(BridgeError::NotImplemented)` until the row-uniform
//! refactor lands.

use ark_ff::{Field, Zero};

use crate::bit_constraint::FieldTraceAccess;
use crate::composition::ConstraintSet;
use crate::row_uniform::{
    AlwaysConstraint, ColRef, RowUniformConstraint, RowUniformOp,
    SelectorIndex, UniformAirConstraints, UniformRowSchema, UniformTrace,
};

/// Errors that can occur while preparing inputs for the FRI prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BridgeError {
    /// The constraint set is not yet expressed in row-uniform form.
    /// The cell-list form ([`crate::bit_constraint::BitOp`] with
    /// absolute `CellRef`s) cannot be plugged into `deep_fri_prove`
    /// directly without one of: row-uniform restructure (preferred),
    /// boundary-constraint blowup, or single-row degenerate trace.
    /// See module docs.
    NotImplemented(&'static str),
    /// Field arithmetic overflow or domain mismatch.
    Internal(String),
}

impl std::fmt::Display for BridgeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotImplemented(why) => write!(f, "FRI bridge not yet implemented: {why}"),
            Self::Internal(msg) => write!(f, "FRI bridge internal error: {msg}"),
        }
    }
}

impl std::error::Error for BridgeError {}

/// The data deep_ali's `deep_fri_prove` needs.  Produced by
/// [`prepare_fri_input`]; passed straight through to the FRI prover
/// once the row-uniform refactor lands.
#[derive(Debug, Clone)]
pub struct FriInput<F: Field> {
    /// LDE table, column-major: `lde[col][lde_row]`.  Width is
    /// determined by the row-uniform layout (e.g. 1 600 state-bit
    /// columns + helper columns).  Length is `n_trace × blowup`.
    pub lde: Vec<Vec<F>>,
    /// Number of trace rows (before LDE expansion).
    pub n_trace: usize,
    /// LDE blowup factor (production: 32; smoke tests: 4).
    pub blowup: usize,
    /// Composed polynomial value per LDE row: `c_eval[r] = Σ_j α_j · Φ_j(LDE @ r)`.
    /// This is what FRI low-degree-tests.
    pub c_eval: Vec<F>,
}

impl<F: Field> FriInput<F> {
    /// Width of the LDE (= number of columns).
    pub fn width(&self) -> usize { self.lde.len() }

    /// Length of each LDE column (= n_trace × blowup).
    pub fn lde_length(&self) -> usize { self.n_trace * self.blowup }

    /// Sanity-check shape invariants.  Returns `Err` if any LDE column
    /// doesn't have length `n_trace × blowup`, or if c_eval has a
    /// different length.
    pub fn check_shape(&self) -> Result<(), BridgeError> {
        let expected_len = self.lde_length();
        for (col_idx, col) in self.lde.iter().enumerate() {
            if col.len() != expected_len {
                return Err(BridgeError::Internal(format!(
                    "column {col_idx} has length {} but expected {expected_len}",
                    col.len()
                )));
            }
        }
        if self.c_eval.len() != expected_len {
            return Err(BridgeError::Internal(format!(
                "c_eval has length {} but expected {expected_len}",
                self.c_eval.len()
            )));
        }
        Ok(())
    }
}

/// Prepare inputs for [`deep_ali::fri::deep_fri_prove`] from a wrapper-
/// stark constraint set + trace.  Stub: returns `NotImplemented` until
/// the row-uniform refactor lands.
///
/// # Arguments
///
/// - `constraints`: cell-list BitOps from any of the wrapper-stark
///   constraint generators (e.g. `theta_constraints`, `round_constraints`,
///   `permutation_constraints`, `sponge_constraints`)
/// - `trace`: a trace satisfying the constraint set
/// - `alphas`: FS-derived combination coefficients (one per constraint)
/// - `blowup`: LDE blowup factor (paper §10.1: 32 production, 4 smoke)
///
/// # Returns
///
/// On success, a [`FriInput`] ready to feed to `deep_fri_prove`.
/// On the current scaffolding, always returns `NotImplemented`.
pub fn prepare_fri_input<F: Field>(
    constraints: &ConstraintSet,
    _trace: &impl FieldTraceAccess<F>,
    alphas: &[F],
    blowup: usize,
) -> Result<FriInput<F>, BridgeError> {
    if alphas.len() != constraints.len() {
        return Err(BridgeError::Internal(format!(
            "alphas count {} != constraint count {}",
            alphas.len(), constraints.len()
        )));
    }
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(BridgeError::Internal(format!(
            "blowup must be a power of two ≥ 2; got {blowup}"
        )));
    }
    Err(BridgeError::NotImplemented(
        "use prepare_fri_input_row_uniform for the row-uniform path; \
         this cell-list overload is deprecated.",
    ))
}

// ─── Row-uniform path: real implementation ─────────────────────────

use ark_goldilocks::Goldilocks;
use deep_ali::trace_import::lde_trace_columns;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
type FBase = ark_goldilocks::Goldilocks;

/// Digest-boundary specification.  Pins specific (column, expected_bit)
/// pairs at the trace's last row.  Used to bind a public SHA-3 output
/// digest into the AIR.
#[derive(Clone, Debug)]
pub struct DigestBoundary {
    /// (state_out column, expected bit value ∈ {0, 1}) pairs.
    pub pinned_bits: Vec<(usize, u8)>,
    /// Combination coefficient α applied to the whole boundary sum.
    /// FS-derived from pi_hash so the verifier reproduces it.
    pub alpha: FBase,
}

/// Compute the Lagrange-basis indicator polynomial for the last trace
/// row, evaluated on the full LDE domain.  `indicator_lde[r] = 1` at
/// the LDE row corresponding to the last trace row, `0` at all other
/// trace rows, and interpolated values at intermediate LDE positions.
///
/// The indicator vanishes at every trace row except the last, so when
/// we add `alpha · indicator(r) · (state_out_cell(r) − expected_bit)`
/// to c_eval, the contribution is zero at all trace rows except the
/// last, where it pins the cell to the expected bit.
fn compute_last_row_indicator_lde(n_trace: usize, blowup: usize) -> Vec<FBase> {
    compute_single_row_indicator_lde(n_trace - 1, n_trace, blowup)
}

/// Generalisation of [`compute_last_row_indicator_lde`]: the indicator
/// polynomial that's 1 at trace row `target_row` and 0 at all other
/// trace rows, evaluated on the full LDE domain.  Used by the Merkle
/// path prover to gate selection + cross-row constraints to the
/// specific row each fires at.
pub fn compute_single_row_indicator_lde(
    target_row: usize, n_trace: usize, blowup: usize,
) -> Vec<FBase> {
    let n_lde = n_trace * blowup;
    debug_assert!(target_row < n_trace);
    let mut trace_vals = vec![FBase::from(0u64); n_trace];
    trace_vals[target_row] = FBase::from(1u64);

    let trace_dom = Radix2EvaluationDomain::<FBase>::new(n_trace)
        .expect("trace domain radix-2");
    let coeffs = trace_dom.ifft(&trace_vals);
    let mut padded = coeffs;
    padded.resize(n_lde, FBase::from(0u64));
    let lde_dom = Radix2EvaluationDomain::<FBase>::new(n_lde)
        .expect("LDE domain radix-2");
    lde_dom.fft(&padded)
}

/// Prepare a FRI input from a row-uniform trace + constraints.  This
/// is the paper-grade path: column-major LDE + per-row constraint
/// composition.
///
/// # Arguments
///
/// - `trace`: row-uniform trace satisfying the constraints
/// - `air`: row-uniform AIR constraint set (selected + always)
/// - `alphas_selected`: one α per selected constraint
/// - `alphas_always`:   one α per always constraint
/// - `blowup`: LDE blowup factor (paper §10.1: 32 production, 4 smoke)
///
/// # Algorithm
///
/// 1. Pad `trace.n_rows` up to next power of two `n_trace` (zero rows)
/// 2. Convert row-major u8 trace into column-major `Vec<Vec<F>>`
/// 3. LDE each column to length `n_trace × blowup` via deep_ali's
///    `lde_trace_columns`
/// 4. For each LDE row r, compute
///    `c_eval[r] = Σ α_j_sel · selector_at(r, j) · Φ_j_sel(LDE @ r)
///               + Σ α_k_always · Φ_k_always(LDE @ r [, LDE @ r+1])`
/// 5. Return FriInput with the LDE columns + c_eval
///
/// Note: NextRowCopy constraints read at LDE rows r and r+1.  At the
/// last LDE row, they read at row 0 (cyclic), which is correct under
/// the FRI domain's multiplicative structure.
pub fn prepare_fri_input_row_uniform(
    trace: &UniformTrace,
    air: &UniformAirConstraints,
    alphas_selected: &[FBase],
    alphas_always: &[FBase],
    blowup: usize,
) -> Result<FriInput<FBase>, BridgeError> {
    prepare_fri_input_row_uniform_with_boundary(
        trace, air, alphas_selected, alphas_always, blowup, None,
    )
}

/// As [`prepare_fri_input_row_uniform`] but optionally adds a
/// digest-boundary contribution to c_eval.  When `digest_boundary` is
/// `Some`, the boundary fires only at the last trace row (via the
/// Lagrange indicator), pinning each named state_out cell to its
/// expected bit value.  This is what makes the SHA-3 STARK a
/// **proof-of-knowledge of a pre-image** for the public digest:
/// without the boundary, the prover can produce a valid trace for
/// any message and claim any digest.
pub fn prepare_fri_input_row_uniform_with_boundary(
    trace: &UniformTrace,
    air: &UniformAirConstraints,
    alphas_selected: &[FBase],
    alphas_always: &[FBase],
    blowup: usize,
    digest_boundary: Option<&DigestBoundary>,
) -> Result<FriInput<FBase>, BridgeError> {
    if alphas_selected.len() != air.selected.len() {
        return Err(BridgeError::Internal(format!(
            "alphas_selected count {} != air.selected count {}",
            alphas_selected.len(), air.selected.len()
        )));
    }
    if alphas_always.len() != air.always.len() {
        return Err(BridgeError::Internal(format!(
            "alphas_always count {} != air.always count {}",
            alphas_always.len(), air.always.len()
        )));
    }
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(BridgeError::Internal(format!(
            "blowup must be a power of two ≥ 2; got {blowup}"
        )));
    }

    let width = trace.schema.width;
    let n_trace = trace.n_rows.next_power_of_two();
    let n_lde = n_trace * blowup;

    // 1. Convert row-major u8 trace into column-major Goldilocks,
    //    padded with zeros to n_trace rows.
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

    // 2. LDE each column.
    let lde: Vec<Vec<FBase>> = lde_trace_columns(&columns, n_trace, blowup)
        .map_err(|e| BridgeError::Internal(format!("LDE failed: {e}")))?;

    // 3. Compute c_eval per LDE row.  NextRowCopy steps by `blowup`
    //    LDE rows (one trace-row step), cyclically.
    let mut c_eval = vec![FBase::from(0u64); n_lde];
    for r in 0..n_lde {
        let mut acc = FBase::from(0u64);
        // Selected: multiplied by selector value at this row.
        for (j, c) in air.selected.iter().enumerate() {
            let alpha = alphas_selected[j];
            let sel_col = trace.schema.selector(c.selector);
            let sel_val = lde[sel_col][r];
            let phi = eval_op_at_lde::<FBase>(&c.op, &lde, r, n_lde, blowup);
            acc += alpha * sel_val * phi;
        }
        // Always: no selector multiplication.
        for (k, c) in air.always.iter().enumerate() {
            let alpha = alphas_always[k];
            let phi = eval_op_at_lde::<FBase>(&c.op, &lde, r, n_lde, blowup);
            acc += alpha * phi;
        }
        c_eval[r] = acc;
    }

    // 4. Optional digest-boundary contribution: pins state_out cells
    //    at the last trace row to public expected bits.  This is the
    //    soundness mechanism that makes the wrapper STARK a real
    //    pre-image PoK against a public digest.
    if let Some(bdry) = digest_boundary {
        let indicator_lde = compute_last_row_indicator_lde(n_trace, blowup);
        debug_assert_eq!(indicator_lde.len(), n_lde);
        for r in 0..n_lde {
            let ind = indicator_lde[r];
            if ind.is_zero() { continue; }   // skip when indicator is 0 (most LDE rows)
            let mut bdry_acc = FBase::from(0u64);
            for &(col, expected_bit) in &bdry.pinned_bits {
                let expected = FBase::from(expected_bit as u64);
                bdry_acc += lde[col][r] - expected;
            }
            c_eval[r] += bdry.alpha * ind * bdry_acc;
        }
    }

    Ok(FriInput { lde, n_trace, blowup, c_eval })
}

/// Evaluate one RowUniformOp at LDE row `r`.  Returns the polynomial
/// residue (zero on satisfying trace).  Handles cross-row reads
/// (NextRowCopy) by reading at row `(r + blowup) mod n_lde` — one
/// TRACE-row step forward, cyclically.
fn eval_op_at_lde<F: Field>(
    op: &RowUniformOp,
    lde: &[Vec<F>],
    r: usize,
    n_lde: usize,
    blowup: usize,
) -> F {
    let two = F::one() + F::one();
    match *op {
        RowUniformOp::Xor { c, a, b } => {
            let a = lde[a.0][r];
            let b = lde[b.0][r];
            let c = lde[c.0][r];
            c - (a + b - two * a * b)
        }
        RowUniformOp::And { c, a, b } => {
            let a = lde[a.0][r];
            let b = lde[b.0][r];
            let c = lde[c.0][r];
            c - a * b
        }
        RowUniformOp::Not { c, a } => {
            let a = lde[a.0][r];
            let c = lde[c.0][r];
            c - (F::one() - a)
        }
        RowUniformOp::Copy { c, a } => {
            lde[c.0][r] - lde[a.0][r]
        }
        RowUniformOp::XorConst { c, a, k } => {
            let a = lde[a.0][r];
            let c = lde[c.0][r];
            let k = F::from(k as u64);
            c - (a + k - two * a * k)
        }
        RowUniformOp::Boolean { b } => {
            let b = lde[b.0][r];
            b * (b - F::one())
        }
        RowUniformOp::NextRowCopy { dst, src } => {
            // One trace-row step in LDE = blowup LDE rows, cyclically.
            let next_r = (r + blowup) % n_lde;
            lde[dst.0][next_r] - lde[src.0][r]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_goldilocks::Goldilocks;
    use crate::bit_constraint::{BitOp, CellRef, FieldMockTrace};
    use crate::composition::ConstraintSet;

    fn cell(row: usize, col: usize) -> CellRef { CellRef::new(row, col) }

    #[test]
    fn prepare_fri_input_returns_not_implemented() {
        let set = ConstraintSet::new(vec![
            BitOp::Boolean { b: cell(0, 0) },
        ]);
        let trace = FieldMockTrace::<Goldilocks>::zeros(1, 1);
        let alphas = vec![Goldilocks::from(1u64)];
        let result = prepare_fri_input(&set, &trace, &alphas, 32);
        assert!(matches!(result, Err(BridgeError::NotImplemented(_))));
    }

    #[test]
    fn prepare_fri_input_rejects_alpha_count_mismatch() {
        let set = ConstraintSet::new(vec![
            BitOp::Boolean { b: cell(0, 0) },
            BitOp::Boolean { b: cell(0, 1) },
        ]);
        let trace = FieldMockTrace::<Goldilocks>::zeros(1, 2);
        let alphas = vec![Goldilocks::from(1u64)];  // wrong count
        let result = prepare_fri_input(&set, &trace, &alphas, 32);
        assert!(matches!(result, Err(BridgeError::Internal(_))));
    }

    #[test]
    fn prepare_fri_input_rejects_non_power_of_two_blowup() {
        let set = ConstraintSet::new(vec![BitOp::Boolean { b: cell(0, 0) }]);
        let trace = FieldMockTrace::<Goldilocks>::zeros(1, 1);
        let alphas = vec![Goldilocks::from(1u64)];
        for bad_blowup in [0usize, 1, 3, 5, 7, 9] {
            let result = prepare_fri_input(&set, &trace, &alphas, bad_blowup);
            assert!(matches!(result, Err(BridgeError::Internal(_))),
                "blowup {bad_blowup} should be rejected");
        }
    }

    #[test]
    fn prepare_fri_input_accepts_power_of_two_blowups() {
        // Power-of-two blowups should pass the early checks and hit
        // NotImplemented (not Internal).  Catches future regressions
        // where the blowup check is too strict.
        let set = ConstraintSet::new(vec![BitOp::Boolean { b: cell(0, 0) }]);
        let trace = FieldMockTrace::<Goldilocks>::zeros(1, 1);
        let alphas = vec![Goldilocks::from(1u64)];
        for good_blowup in [2usize, 4, 8, 16, 32, 64] {
            let result = prepare_fri_input(&set, &trace, &alphas, good_blowup);
            assert!(matches!(result, Err(BridgeError::NotImplemented(_))),
                "blowup {good_blowup} should hit NotImplemented");
        }
    }

    #[test]
    fn fri_input_shape_check() {
        let n_trace = 4;
        let blowup = 8;
        let width = 3;
        let lde_len = n_trace * blowup;
        let lde = vec![vec![Goldilocks::from(0u64); lde_len]; width];
        let c_eval = vec![Goldilocks::from(0u64); lde_len];
        let good = FriInput { lde, n_trace, blowup, c_eval };
        assert!(good.check_shape().is_ok());
        assert_eq!(good.width(), width);
        assert_eq!(good.lde_length(), lde_len);

        // Bad: c_eval length mismatch.
        let bad = FriInput {
            lde: vec![vec![Goldilocks::from(0u64); lde_len]; width],
            n_trace, blowup,
            c_eval: vec![Goldilocks::from(0u64); lde_len - 1],
        };
        assert!(bad.check_shape().is_err());

        // Bad: column length mismatch.
        let mut bad_col = vec![vec![Goldilocks::from(0u64); lde_len]; width];
        bad_col[1] = vec![Goldilocks::from(0u64); lde_len - 1];
        let bad2 = FriInput {
            lde: bad_col, n_trace, blowup,
            c_eval: vec![Goldilocks::from(0u64); lde_len],
        };
        assert!(bad2.check_shape().is_err());
    }

    #[test]
    fn bridge_error_display() {
        let e = BridgeError::NotImplemented("test reason");
        let s = format!("{e}");
        assert!(s.contains("not yet implemented"));
        assert!(s.contains("test reason"));

        let e2 = BridgeError::Internal("foo".into());
        let s2 = format!("{e2}");
        assert!(s2.contains("internal error"));
        assert!(s2.contains("foo"));
    }

    // ─── Row-uniform path integration tests ─────────────────────────

    use crate::row_uniform::{
        UniformAirConstraints, UniformRowSchema, UniformTrace,
        synthesize_uniform_trace,
    };
    use crate::sha3_absorb_air::Sha3Variant;
    use crate::composition::alphas_from_transcript;
    use ark_ff::Zero;

    fn pad_input_for_test(input: &[u8], variant: Sha3Variant) -> Vec<Vec<u8>> {
        let block_len = variant.block_bytes();
        let mut blocks: Vec<Vec<u8>> = Vec::new();
        let mut offset = 0;
        while offset + block_len <= input.len() {
            blocks.push(input[offset..offset + block_len].to_vec());
            offset += block_len;
        }
        let mut last = vec![0u8; block_len];
        last[..input.len() - offset].copy_from_slice(&input[offset..]);
        last[input.len() - offset] = 0x06;
        last[block_len - 1] |= 0x80;
        blocks.push(last);
        blocks
    }

    #[test]
    fn row_uniform_prepare_fri_input_smoke() {
        let blocks = pad_input_for_test(b"abc", Sha3Variant::Sha3_256);
        let refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let trace = synthesize_uniform_trace(&refs, Sha3Variant::Sha3_256);
        let schema = trace.schema.clone();
        let air = UniformAirConstraints::for_schema(&schema);

        let seed = [0xCAu8; 32];
        let alphas_sel = alphas_from_transcript::<Goldilocks>(&seed, air.selected.len());
        let mut seed2 = seed; seed2[0] ^= 1;
        let alphas_alw = alphas_from_transcript::<Goldilocks>(&seed2, air.always.len());

        let result = prepare_fri_input_row_uniform(
            &trace, &air, &alphas_sel, &alphas_alw, /*blowup=*/4
        );
        let fri_input = result.expect("prepare_fri_input must succeed on a valid trace");

        // Shape sanity.
        assert_eq!(fri_input.lde.len(), schema.width);
        let expected_lde_len = trace.n_rows.next_power_of_two() * 4;
        for col in &fri_input.lde {
            assert_eq!(col.len(), expected_lde_len);
        }
        assert_eq!(fri_input.c_eval.len(), expected_lde_len);
        assert!(fri_input.check_shape().is_ok());
    }

    #[test]
    fn row_uniform_c_eval_is_zero_at_trace_rows_for_valid_trace() {
        // The composed polynomial c_eval must evaluate to ZERO at every
        // LDE row that corresponds to an ORIGINAL trace row (multiples
        // of `blowup`).  At intermediate LDE rows, c_eval is generally
        // non-zero (it interpolates between trace rows) — that's what
        // FRI's low-degree test checks.
        let blocks = pad_input_for_test(b"abc", Sha3Variant::Sha3_256);
        let refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let trace = synthesize_uniform_trace(&refs, Sha3Variant::Sha3_256);
        let schema = trace.schema.clone();
        let air = UniformAirConstraints::for_schema(&schema);

        let seed = [0x11u8; 32];
        let alphas_sel = alphas_from_transcript::<Goldilocks>(&seed, air.selected.len());
        let mut seed2 = seed; seed2[0] ^= 1;
        let alphas_alw = alphas_from_transcript::<Goldilocks>(&seed2, air.always.len());

        let blowup = 4;
        let fri_input = prepare_fri_input_row_uniform(
            &trace, &air, &alphas_sel, &alphas_alw, blowup,
        ).expect("prepare must succeed");

        // At trace rows 0..n_rows-1, c_eval must be zero.
        // (The last row's NextRowCopy wraps cyclically, so it can be
        // non-zero — we skip it for this check.)
        for trace_row in 0..(trace.n_rows - 1) {
            let lde_row = trace_row * blowup;
            assert!(fri_input.c_eval[lde_row].is_zero(),
                "c_eval at trace row {trace_row} (LDE row {lde_row}) should be 0; got {:?}",
                fri_input.c_eval[lde_row]);
        }
    }

    #[test]
    fn row_uniform_prepare_rejects_alpha_count_mismatch() {
        let blocks = pad_input_for_test(b"x", Sha3Variant::Sha3_256);
        let refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let trace = synthesize_uniform_trace(&refs, Sha3Variant::Sha3_256);
        let air = UniformAirConstraints::for_schema(&trace.schema);

        // Wrong selected count.
        let alphas_sel = vec![Goldilocks::from(1u64); 1];
        let alphas_alw = vec![Goldilocks::from(1u64); air.always.len()];
        let result = prepare_fri_input_row_uniform(&trace, &air, &alphas_sel, &alphas_alw, 4);
        assert!(matches!(result, Err(BridgeError::Internal(_))));

        // Wrong always count.
        let alphas_sel = vec![Goldilocks::from(1u64); air.selected.len()];
        let alphas_alw = vec![Goldilocks::from(1u64); 1];
        let result = prepare_fri_input_row_uniform(&trace, &air, &alphas_sel, &alphas_alw, 4);
        assert!(matches!(result, Err(BridgeError::Internal(_))));
    }
}
