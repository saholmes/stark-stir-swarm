//! Bit-level polynomial constraint primitives for the SHA-3 AIR.
//!
//! # Why a separate module
//!
//! [`crate::sha3_absorb_air::keccak_f1600_bit_level`] computes Keccak
//! at the bit level using ordinary `u8 ∈ {0, 1}` cells.  The AIR has
//! to express the SAME computation as polynomial constraints over a
//! prime field (Goldilocks), so that FRI/STIR can prove the trace
//! satisfies them.  This module defines the constraint primitives
//! that bridge the two representations.
//!
//! # Constraint zoo (paper §3 + standard bit-level AIR practice)
//!
//! Each primitive maps a boolean operation to a polynomial that
//! must vanish on a satisfying trace.  Inputs are boolean cells
//! (booleanity is enforced separately by [`BitOp::Boolean`]).
//!
//! | Operation         | Boolean expression          | Polynomial constraint (must = 0) |
//! |-------------------|-----------------------------|----------------------------------|
//! | XOR  `c = a ⊕ b`  | `c = a + b - 2ab` (mod 2)   | `c - (a + b - 2ab)`              |
//! | AND  `c = a ∧ b`  | `c = a · b`                 | `c - a · b`                      |
//! | NOT  `c = ¬a`     | `c = 1 - a`                 | `c - (1 - a)`                    |
//! | COPY `c = a`      | `c = a`                     | `c - a`                          |
//! | XOR-with-constant | `c = a ⊕ k`  (k ∈ {0,1})    | `c - (a + k - 2ak)` (simplified) |
//! | Booleanity        | `b ∈ {0, 1}`                | `b · (b - 1)`                    |
//!
//! All polynomials are degree ≤ 2 — composition over multiple
//! constraints in a single column requires either intermediate cells
//! or higher-degree composition; we choose intermediate cells (5-input
//! XOR-chains in θ become 4 chained 2-input XORs through 3 helper bits).
//!
//! # Native evaluation
//!
//! Each [`BitOp`] has an `eval` method that reads its referenced cells
//! from a [`TraceAccess`] implementor and returns the polynomial value.
//! On a valid trace this is 0; on an invalid trace it's non-zero.
//! Used by tests + future native pre-FRI sanity check.

/// Identifies a single cell in the wrapper-AIR trace.  Indexed by
/// `(row, col)` in the row-major layout used by
/// [`crate::verifier_air::WrapperTrace`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CellRef {
    pub row: usize,
    pub col: usize,
}

impl CellRef {
    pub const fn new(row: usize, col: usize) -> Self {
        Self { row, col }
    }
}

/// One bit-level polynomial constraint.  The constraint vanishes
/// (evaluates to 0) on a satisfying trace.  Inputs are boolean cells
/// — booleanity itself is enforced by [`BitOp::Boolean`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitOp {
    /// `c = a XOR b` ⇔ `c - (a + b - 2ab) = 0`
    Xor { c: CellRef, a: CellRef, b: CellRef },
    /// `c = a AND b` ⇔ `c - a·b = 0`
    And { c: CellRef, a: CellRef, b: CellRef },
    /// `c = NOT a` ⇔ `c - (1 - a) = 0`
    Not { c: CellRef, a: CellRef },
    /// `c = a` (used for ρ rotation + π permutation: output bit at one
    /// (row, col) reads input bit from a different (row, col) with no
    /// arithmetic).  Constraint: `c - a = 0`.
    Copy { c: CellRef, a: CellRef },
    /// `c = a XOR k` where `k ∈ {0, 1}` is a public/static bit (used
    /// for ι: XOR-with-round-constant).  Simplifies:
    /// - `k = 0`: `c = a`, constraint `c - a`
    /// - `k = 1`: `c = 1 - a`, constraint `c - (1 - a)`
    XorConst { c: CellRef, a: CellRef, k: u8 },
    /// Booleanity: `b ∈ {0, 1}` ⇔ `b·(b - 1) = 0`.  Required on every
    /// cell that participates in a bit-level operation as input or
    /// output.  Degree 2.
    Boolean { b: CellRef },
}

impl BitOp {
    /// Algebraic degree of this constraint when expressed as a
    /// polynomial in the trace cells.  Drives the AIR's `d_c`
    /// (constraint degree) parameter — paper Corollary 1 sets
    /// `D = d_c · T`, so keeping per-constraint degree low matters.
    pub fn degree(&self) -> usize {
        match self {
            Self::Xor { .. }       => 2,  // 2ab term
            Self::And { .. }       => 2,  // a·b term
            Self::Not { .. }       => 1,
            Self::Copy { .. }      => 1,
            Self::XorConst { .. }  => 1,
            Self::Boolean { .. }   => 2,  // b·(b-1) = b² - b
        }
    }
}

/// Read access to wrapper-AIR trace cells.  Implemented by both
/// `WrapperTrace` (for prover-side constraint synthesis) and any
/// test-mock trace structure.  Cell values are u64 here — the
/// real Goldilocks-field evaluator wraps these in field elements
/// for the FRI prover.
pub trait TraceAccess {
    fn get_cell(&self, cell: CellRef) -> u64;
}

/// Trivial mock impl for testing: a fixed-size 2D grid of u64s.
#[derive(Clone, Debug)]
pub struct MockTrace {
    pub width: usize,
    pub rows: Vec<Vec<u64>>,
}

impl MockTrace {
    pub fn zeros(rows: usize, width: usize) -> Self {
        Self { width, rows: vec![vec![0; width]; rows] }
    }
    pub fn set(&mut self, cell: CellRef, val: u64) {
        self.rows[cell.row][cell.col] = val;
    }
}

impl TraceAccess for MockTrace {
    fn get_cell(&self, cell: CellRef) -> u64 {
        self.rows[cell.row][cell.col]
    }
}

impl BitOp {
    /// Evaluate this constraint as a polynomial expression in the
    /// trace cell values.  Returns the polynomial's value; ZERO means
    /// the trace satisfies the constraint, NON-ZERO means it doesn't.
    ///
    /// Operates on signed-integer arithmetic so we can detect negative
    /// residues; in the real Goldilocks-field evaluator these become
    /// field elements.
    pub fn eval(&self, trace: &impl TraceAccess) -> i128 {
        match *self {
            Self::Xor { c, a, b } => {
                let a = trace.get_cell(a) as i128;
                let b = trace.get_cell(b) as i128;
                let c = trace.get_cell(c) as i128;
                c - (a + b - 2 * a * b)
            }
            Self::And { c, a, b } => {
                let a = trace.get_cell(a) as i128;
                let b = trace.get_cell(b) as i128;
                let c = trace.get_cell(c) as i128;
                c - a * b
            }
            Self::Not { c, a } => {
                let a = trace.get_cell(a) as i128;
                let c = trace.get_cell(c) as i128;
                c - (1 - a)
            }
            Self::Copy { c, a } => {
                let a = trace.get_cell(a) as i128;
                let c = trace.get_cell(c) as i128;
                c - a
            }
            Self::XorConst { c, a, k } => {
                let a = trace.get_cell(a) as i128;
                let c = trace.get_cell(c) as i128;
                let k = k as i128;
                c - (a + k - 2 * a * k)
            }
            Self::Boolean { b } => {
                let b = trace.get_cell(b) as i128;
                b * (b - 1)
            }
        }
    }

    /// Returns `true` iff the trace satisfies this constraint
    /// (polynomial evaluation is zero).
    pub fn satisfied_by(&self, trace: &impl TraceAccess) -> bool {
        self.eval(trace) == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cell(row: usize, col: usize) -> CellRef {
        CellRef::new(row, col)
    }

    #[test]
    fn degrees_are_what_we_expect() {
        let r = cell(0, 0);
        assert_eq!(BitOp::Xor { c: r, a: r, b: r }.degree(), 2);
        assert_eq!(BitOp::And { c: r, a: r, b: r }.degree(), 2);
        assert_eq!(BitOp::Not { c: r, a: r }.degree(), 1);
        assert_eq!(BitOp::Copy { c: r, a: r }.degree(), 1);
        assert_eq!(BitOp::XorConst { c: r, a: r, k: 0 }.degree(), 1);
        assert_eq!(BitOp::Boolean { b: r }.degree(), 2);
    }

    #[test]
    fn xor_truth_table() {
        let op = BitOp::Xor {
            c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
        };
        // (a, b, c, satisfied?)
        for &(a, b, c, ok) in &[
            (0u64, 0, 0, true),  (0, 0, 1, false),
            (0, 1, 1, true),  (0, 1, 0, false),
            (1, 0, 1, true),  (1, 0, 0, false),
            (1, 1, 0, true),  (1, 1, 1, false),
        ] {
            let mut t = MockTrace::zeros(1, 3);
            t.set(cell(0, 0), a);
            t.set(cell(0, 1), b);
            t.set(cell(0, 2), c);
            assert_eq!(op.satisfied_by(&t), ok,
                "XOR({a},{b}) should be {} but trace stores {c}", a ^ b);
        }
    }

    #[test]
    fn and_truth_table() {
        let op = BitOp::And {
            c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
        };
        for &(a, b, c, ok) in &[
            (0u64, 0, 0, true),  (0, 0, 1, false),
            (0, 1, 0, true),  (0, 1, 1, false),
            (1, 0, 0, true),  (1, 0, 1, false),
            (1, 1, 1, true),  (1, 1, 0, false),
        ] {
            let mut t = MockTrace::zeros(1, 3);
            t.set(cell(0, 0), a);
            t.set(cell(0, 1), b);
            t.set(cell(0, 2), c);
            assert_eq!(op.satisfied_by(&t), ok);
        }
    }

    #[test]
    fn not_truth_table() {
        let op = BitOp::Not { c: cell(0, 1), a: cell(0, 0) };
        for &(a, c, ok) in &[
            (0u64, 1, true),  (0, 0, false),
            (1, 0, true),  (1, 1, false),
        ] {
            let mut t = MockTrace::zeros(1, 2);
            t.set(cell(0, 0), a);
            t.set(cell(0, 1), c);
            assert_eq!(op.satisfied_by(&t), ok);
        }
    }

    #[test]
    fn copy_truth_table() {
        let op = BitOp::Copy { c: cell(0, 1), a: cell(0, 0) };
        for &(a, c, ok) in &[
            (0u64, 0, true),  (0, 1, false),
            (1, 1, true),  (1, 0, false),
        ] {
            let mut t = MockTrace::zeros(1, 2);
            t.set(cell(0, 0), a);
            t.set(cell(0, 1), c);
            assert_eq!(op.satisfied_by(&t), ok);
        }
    }

    #[test]
    fn xor_const_k0_is_copy() {
        let op = BitOp::XorConst { c: cell(0, 1), a: cell(0, 0), k: 0 };
        for &(a, c, ok) in &[
            (0u64, 0, true), (0, 1, false),
            (1, 1, true),    (1, 0, false),
        ] {
            let mut t = MockTrace::zeros(1, 2);
            t.set(cell(0, 0), a);
            t.set(cell(0, 1), c);
            assert_eq!(op.satisfied_by(&t), ok);
        }
    }

    #[test]
    fn xor_const_k1_is_not() {
        let op = BitOp::XorConst { c: cell(0, 1), a: cell(0, 0), k: 1 };
        for &(a, c, ok) in &[
            (0u64, 1, true), (0, 0, false),
            (1, 0, true),    (1, 1, false),
        ] {
            let mut t = MockTrace::zeros(1, 2);
            t.set(cell(0, 0), a);
            t.set(cell(0, 1), c);
            assert_eq!(op.satisfied_by(&t), ok);
        }
    }

    #[test]
    fn booleanity_truth_table() {
        let op = BitOp::Boolean { b: cell(0, 0) };
        let mut t = MockTrace::zeros(1, 1);
        // Boolean values pass.
        t.set(cell(0, 0), 0);
        assert!(op.satisfied_by(&t));
        t.set(cell(0, 0), 1);
        assert!(op.satisfied_by(&t));
        // Non-boolean values fail with non-zero residue.
        t.set(cell(0, 0), 2);
        assert_eq!(op.eval(&t), 2);  // 2·(2-1) = 2
        t.set(cell(0, 0), 5);
        assert_eq!(op.eval(&t), 20); // 5·(5-1) = 20
    }

    #[test]
    fn xor_with_non_boolean_input_still_evaluates() {
        // The XOR constraint assumes boolean inputs.  If a caller
        // passes 2 as input, the polynomial still evaluates — it's
        // up to the AIR to enforce booleanity separately.  This
        // test pins that contract: the constraint's `eval` does
        // NOT silently accept non-boolean inputs as if they were
        // valid bits.
        let op = BitOp::Xor {
            c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
        };
        let mut t = MockTrace::zeros(1, 3);
        t.set(cell(0, 0), 2);  // non-boolean
        t.set(cell(0, 1), 0);
        t.set(cell(0, 2), 0);
        // 0 - (2 + 0 - 2·2·0) = -2  ≠ 0
        assert_eq!(op.eval(&t), -2);
    }

    #[test]
    fn constraints_are_copy_and_send() {
        // The AIR may need to clone / move constraint lists around
        // (e.g. into per-region buckets).  Pin that BitOp is small
        // and copyable.
        fn assert_copy_send<T: Copy + Send + Sync>() {}
        assert_copy_send::<BitOp>();
        assert_copy_send::<CellRef>();
    }
}
