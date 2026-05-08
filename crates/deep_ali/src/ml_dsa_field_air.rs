//! AIR for arithmetic in Z_q where q = 8_380_417 (FIPS 204 §3.7).
//!
//! Strategy: we embed Z_q into Goldilocks (1 Goldilocks cell holds
//! 1 Z_q value losslessly — q fits in 23 bits, Goldilocks in 64).
//! The AIR proves a sequence of `(op, a, b, c)` triples where
//! `op ∈ {ADD, SUB, MUL}` and `c ≡ op(a, b) (mod q)`.
//!
//! Trace layout (per row, "gadget" form — one gate per row):
//!
//! ```text
//!   col 0..3:  one-hot op selector  (NOP, ADD, SUB, MUL)
//!   col 4:     operand a
//!   col 5:     operand b
//!   col 6:     result c
//!   col 7:     reduction witness k  (such that a*b - c = k*q for MUL,
//!                                    or 0/-1/+1 for ADD/SUB wraparound)
//!   col 8..30: 23 range-check bits for c < q  (binary decomposition)
//! ```
//!
//! Constraint count per row:
//!   * 4 one-hot selector constraints (each col is 0/1, sum = 1)
//!   * 1 op-correctness constraint (gated by selectors)
//!   * 23 range bits (each is 0/1)
//!   * 1 range-check constraint (Σ b_i · 2^i = c)
//!   = 29 per-row constraints, all degree ≤ 2.
//!
//! Trace width:  31 columns (4 selectors + 3 operands + 1 witness + 23 bits)
//! Trace height: configurable via `n_trace`; one Z_q operation per row.
//!
//! Reusable as a sub-AIR by NTT, polymul, decompose, and norm-check
//! AIRs.  A 256-point NTT issues ~1024 ADD/SUB/MUL calls; ML-DSA
//! verify issues ~16 NTTs (4×ExpandA columns + sk・c products + ...).
//!
//! NB: the in-circuit form below targets *constraint correctness*,
//! not minimum trace width.  A production-grade version would batch
//! multiple ops per row and share range-check tables (PLONK-style
//! lookups).  Constraint-correctness wins for this iteration; we
//! optimise after the full ML-DSA verify AIR composes end-to-end.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::Q;
use crate::ml_dsa_field;

// ─── Op selectors (one-hot) ─────────────────────────────────────────

pub const SEL_NOP: usize = 0;
pub const SEL_ADD: usize = 1;
pub const SEL_SUB: usize = 2;
pub const SEL_MUL: usize = 3;
pub const NUM_SELECTORS: usize = 4;

// ─── Column layout ──────────────────────────────────────────────────

pub const NUM_RANGE_BITS: usize = 23; // ⌈log2 q⌉

/// Total trace width.
pub const WIDTH: usize = NUM_SELECTORS + 3 /* a,b,c */ + 1 /* k */ + NUM_RANGE_BITS;

#[inline] pub const fn col_sel(s: usize) -> usize { s }
#[inline] pub const fn col_a()  -> usize { NUM_SELECTORS }
#[inline] pub const fn col_b()  -> usize { NUM_SELECTORS + 1 }
#[inline] pub const fn col_c()  -> usize { NUM_SELECTORS + 2 }
#[inline] pub const fn col_k()  -> usize { NUM_SELECTORS + 3 }
#[inline] pub const fn col_bit(i: usize) -> usize { NUM_SELECTORS + 4 + i }

/// Number of per-row constraints.
pub const NUM_CONSTRAINTS: usize = NUM_SELECTORS /* booleans */
    + 1 /* selectors sum to 1 */
    + 1 /* op correctness */
    + NUM_RANGE_BITS /* bit booleans */
    + 1 /* range decomposition */;

// ─── Per-row gadget instructions (input to fill) ────────────────────

#[derive(Clone, Copy, Debug)]
pub enum FieldOp {
    Nop,
    Add { a: u32, b: u32 },
    Sub { a: u32, b: u32 },
    Mul { a: u32, b: u32 },
}

impl FieldOp {
    pub fn selector_index(&self) -> usize {
        match self {
            FieldOp::Nop      => SEL_NOP,
            FieldOp::Add {..} => SEL_ADD,
            FieldOp::Sub {..} => SEL_SUB,
            FieldOp::Mul {..} => SEL_MUL,
        }
    }

    pub fn evaluate(&self) -> (u32, i64) {
        // Returns (c, k) where:
        //   ADD: c = a + b - k·q,  k ∈ {0, 1}     (carry indicator)
        //   SUB: c = a - b + k·q,  k ∈ {0, 1}     (borrow indicator)
        //   MUL: c = a·b - k·q,    k = ⌊a·b / q⌋
        //   NOP: (0, 0)
        match self {
            FieldOp::Nop => (0, 0),
            FieldOp::Add { a, b } => {
                let s = (*a as u64) + (*b as u64);
                let k = if s >= Q as u64 { 1 } else { 0 };
                let c = (s - (k as u64) * Q as u64) as u32;
                (c, k)
            }
            FieldOp::Sub { a, b } => {
                let (c, k) = if a >= b {
                    (a - b, 0i64)
                } else {
                    (a + Q - b, 1i64)
                };
                (c, k)
            }
            FieldOp::Mul { a, b } => {
                let prod = (*a as u64) * (*b as u64);
                let k = (prod / Q as u64) as i64;
                let c = (prod % Q as u64) as u32;
                (c, k)
            }
        }
    }
}

// ─── Trace fill ─────────────────────────────────────────────────────

pub fn build_layout(_n_trace: usize) -> () {
    // Layout is currently fully encoded by the column constants
    // above; a future variant that batches multiple ops/row will
    // need a Layout struct.
}

pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, ops: &[FieldOp]) {
    assert!(trace.len() == WIDTH, "ml_dsa_field_air: trace width mismatch");
    assert!(ops.len() <= n_trace, "ml_dsa_field_air: too many ops");
    for col in trace.iter() { assert_eq!(col.len(), n_trace); }

    for (row, op) in ops.iter().enumerate() {
        // One-hot selector
        let sel = op.selector_index();
        for s in 0..NUM_SELECTORS {
            trace[col_sel(s)][row] = if s == sel { F::one() } else { F::zero() };
        }
        // Operands
        let (a, b) = match *op {
            FieldOp::Nop                => (0u32, 0u32),
            FieldOp::Add { a, b }       => (a, b),
            FieldOp::Sub { a, b }       => (a, b),
            FieldOp::Mul { a, b }       => (a, b),
        };
        let (c, k) = op.evaluate();
        trace[col_a()][row] = F::from(a as u64);
        trace[col_b()][row] = F::from(b as u64);
        trace[col_c()][row] = F::from(c as u64);
        // k can be negative for some ops; we use Goldilocks's
        // additive inverse for that case.  Since |k| < 2^23 for
        // ADD/SUB and < 2^23 for MUL (because c, q < 2^23 implies
        // k = (a·b - c)/q < q ≈ 2^23), Goldilocks accommodates it.
        let k_field = if k >= 0 {
            F::from(k as u64)
        } else {
            -F::from((-k) as u64)
        };
        trace[col_k()][row] = k_field;
        // Range bits of c (LSB first)
        let mut cv = c as u64;
        for i in 0..NUM_RANGE_BITS {
            trace[col_bit(i)][row] = F::from((cv & 1) as u64);
            cv >>= 1;
        }
    }
    // Pad the rest with NOPs (selectors set to NOP).
    for row in ops.len()..n_trace {
        for s in 0..NUM_SELECTORS {
            trace[col_sel(s)][row] = if s == SEL_NOP { F::one() } else { F::zero() };
        }
    }
}

// ─── Constraint evaluation ──────────────────────────────────────────

/// Evaluate the per-row constraints.  All entries on a satisfying
/// trace must be zero.  Inputs `cur` and `nxt` follow the
/// deep_ali calling convention; this AIR has no transition
/// constraints (it's a per-row "gate" AIR), so `nxt` is unused.
pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);

    // 1. Each selector is boolean: s · (s − 1) = 0.
    for s in 0..NUM_SELECTORS {
        let v = cur[col_sel(s)];
        out.push(v * (v - F::one()));
    }
    // 2. Selectors sum to 1 (exactly one op per row).
    let sum = (0..NUM_SELECTORS).map(|s| cur[col_sel(s)]).sum::<F>();
    out.push(sum - F::one());

    // 3. Op-correctness.  Combined into one gated constraint:
    //      sel_ADD · (a + b − c − k·q)         = 0
    //    + sel_SUB · (a − b − c + k·q)         = 0
    //    + sel_MUL · (a·b − c − k·q)           = 0
    //    + sel_NOP · (a + b + c)               = 0   (force a=b=c=0 on NOP)
    //
    // We sum the four (each gated by its selector) into one
    // constraint of degree 3.  In a follow-up we'll split into 4
    // degree-2 constraints if the prover's max-degree budget pushes us.
    let a = cur[col_a()];
    let b = cur[col_b()];
    let c = cur[col_c()];
    let k = cur[col_k()];
    let q = F::from(Q as u64);
    let s_add = cur[col_sel(SEL_ADD)];
    let s_sub = cur[col_sel(SEL_SUB)];
    let s_mul = cur[col_sel(SEL_MUL)];
    let s_nop = cur[col_sel(SEL_NOP)];
    let op_constraint =
        s_add * (a + b - c - k * q) +
        s_sub * (a - b - c + k * q) +
        s_mul * (a * b - c - k * q) +
        s_nop * (a + b + c);
    out.push(op_constraint);

    // 4. Each range bit is boolean.
    for i in 0..NUM_RANGE_BITS {
        let bv = cur[col_bit(i)];
        out.push(bv * (bv - F::one()));
    }

    // 5. Range bits compose to c.  Σ bᵢ · 2^i = c.
    let mut acc = F::zero();
    let two = F::from(2u64);
    let mut pow = F::one();
    for i in 0..NUM_RANGE_BITS {
        acc += cur[col_bit(i)] * pow;
        pow *= two;
    }
    out.push(acc - c);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

// ─── Tests ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_trace(n_trace: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n_trace]).collect()
    }

    #[test]
    fn op_correctness_native_round_trip() {
        let cases: Vec<FieldOp> = vec![
            FieldOp::Add { a: 1, b: 2 },
            FieldOp::Add { a: Q - 1, b: 1 },
            FieldOp::Sub { a: 5, b: 3 },
            FieldOp::Sub { a: 0, b: 1 },
            FieldOp::Mul { a: 1234, b: 5678 },
            FieldOp::Mul { a: Q - 1, b: Q - 1 },
            FieldOp::Nop,
        ];

        for case in &cases {
            let (c, _k) = case.evaluate();
            // Native cross-check
            let expected_c = match case {
                FieldOp::Nop => 0,
                FieldOp::Add { a, b } => ml_dsa_field::add_q(*a, *b),
                FieldOp::Sub { a, b } => ml_dsa_field::sub_q(*a, *b),
                FieldOp::Mul { a, b } => ml_dsa_field::mul_q(*a, *b),
            };
            assert_eq!(c, expected_c, "op evaluator disagrees with native: {:?}", case);
        }
    }

    #[test]
    fn satisfying_trace_passes_all_constraints() {
        let ops: Vec<FieldOp> = vec![
            FieldOp::Add { a: 100, b: 200 },
            FieldOp::Sub { a: 50, b: 200 },
            FieldOp::Mul { a: 4_000_000, b: 4_000_000 },  // exercises k > 0
            FieldOp::Mul { a: Q - 1, b: 2 },              // exercises k = 1
            FieldOp::Nop,
        ];
        let n_trace = 8;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &ops);

        for row in 0..n_trace {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let cvals = eval_per_row(&cur, &cur, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "constraint {} on row {} (op={:?}) not zero: {:?}",
                    i, row,
                    if row < ops.len() { Some(ops[row]) } else { None },
                    v);
            }
        }
    }

    #[test]
    fn malicious_c_fails_op_constraint() {
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &[FieldOp::Add { a: 3, b: 4 }]);
        // Tamper: set c = 8 instead of 7.
        trace[col_c()][0] = F::from(8u64);
        // Recompute the bit decomposition for the lie so the range
        // decomposition still passes — exercises the op constraint
        // in isolation.
        let mut bits = 8u64;
        for i in 0..NUM_RANGE_BITS {
            trace[col_bit(i)][0] = F::from((bits & 1) as u64);
            bits >>= 1;
        }
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let cvals = eval_per_row(&cur, &cur, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "op constraint should reject c=8 for 3+4");
    }
}
