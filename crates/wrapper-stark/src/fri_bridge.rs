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

use ark_ff::Field;

use crate::bit_constraint::FieldTraceAccess;
use crate::composition::ConstraintSet;

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
        "row-uniform restructure pending: cell-list BitOp constraints need \
         conversion to row-uniform form with selector polynomials before \
         deep_fri_prove can consume them.  See fri_bridge module docs.",
    ))
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
}
