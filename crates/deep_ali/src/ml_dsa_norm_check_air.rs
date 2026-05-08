//! AIR for the infinity-norm bound check.
//!
//! Witnesses one coefficient per row.  Layout:
//!
//! | column                          | meaning                            |
//! |---------------------------------|------------------------------------|
//! | `c`                             | coefficient in [0, q)              |
//! | `c_sign`                        | 0 if c ≤ q/2, else 1               |
//! | `c_abs`                         | |c'| where c' is the centred residue |
//! | `slack`                         | bound − 1 − c_abs (must be ≥ 0)    |
//! | range bits for c_abs (17 bits)  | binary decomposition                |
//! | range bits for slack (17 bits)  | binary decomposition                |
//!
//! Constraints (per row, all degree ≤ 2):
//!   - c_sign boolean
//!   - c_abs range bits boolean + Σ = c_abs
//!   - slack range bits boolean + Σ = slack
//!   - lift consistency:  c = (1 − c_sign)·c_abs + c_sign·(q − c_abs)
//!   - bound:              slack + c_abs + 1 − bound = 0
//!
//! `bound` is a public input.  For the ML-DSA `‖z‖∞ < γ₁ − β`
//! check, `bound = Z_BOUND = 130 994` (≤ 2^17 = 131 072), so 17
//! range bits are enough on both `c_abs` and `slack`.
//!
//! Constraint count per row ≈ 38, deg ≤ 2.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::Q;
use crate::ml_dsa_norm_check::Z_BOUND;

// |z|_∞ < Z_BOUND = γ_1 − β.
// L1 (γ_1 = 2¹⁷): Z_BOUND ≈ 130994 < 2¹⁷, fits in 17 bits.
// L3 (γ_1 = 2¹⁹): Z_BOUND ≈ 524092 < 2²⁰, needs 20 bits.
// L5 (γ_1 = 2¹⁹): Z_BOUND ≈ 524168 < 2²⁰, also 20 bits.
#[cfg(feature = "mldsa-44")]
const RANGE_BITS: usize = 17;
#[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
const RANGE_BITS: usize = 20;

#[inline] pub const fn col_c() -> usize { 0 }
#[inline] pub const fn col_sign() -> usize { 1 }
#[inline] pub const fn col_abs() -> usize { 2 }
#[inline] pub const fn col_slack() -> usize { 3 }
#[inline] pub const fn col_abs_bit(i: usize) -> usize { 4 + i }
#[inline] pub const fn col_slack_bit(i: usize) -> usize { 4 + RANGE_BITS + i }

pub const WIDTH: usize = 4 + 2 * RANGE_BITS;

pub const NUM_CONSTRAINTS: usize =
    1                           // sign boolean
  + RANGE_BITS + 1              // abs bits + sum
  + RANGE_BITS + 1              // slack bits + sum
  + 1                           // lift consistency
  + 1;                          // bound: slack + abs + 1 = bound

/// Fill the trace for a sequence of coefficients, all checked
/// against the same `bound`.  Coefficients must satisfy
/// `|centred(c)| < bound`; otherwise the trace will be unsatisfiable
/// (a malicious prover can attempt this; the constraints will reject).
pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, coeffs: &[u32], bound: u32) {
    assert_eq!(trace.len(), WIDTH);
    assert!(coeffs.len() <= n_trace);

    for (row, &c) in coeffs.iter().enumerate() {
        debug_assert!(c < Q);
        let (sign, abs_val) = if c > Q / 2 {
            (1u32, Q - c)
        } else {
            (0u32, c)
        };
        // slack = bound - 1 - abs_val (must be ≥ 0 for honest input).
        let slack = (bound as i64 - 1 - abs_val as i64).max(0) as u32;
        trace[col_c()][row]     = F::from(c as u64);
        trace[col_sign()][row]  = F::from(sign as u64);
        trace[col_abs()][row]   = F::from(abs_val as u64);
        trace[col_slack()][row] = F::from(slack as u64);
        for i in 0..RANGE_BITS {
            trace[col_abs_bit(i)][row]   = F::from(((abs_val   >> i) & 1) as u64);
            trace[col_slack_bit(i)][row] = F::from(((slack     >> i) & 1) as u64);
        }
    }
}

pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize, bound: u32) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();
    let two = F::from(2u64);

    let c     = cur[col_c()];
    let sign  = cur[col_sign()];
    let abs_v = cur[col_abs()];
    let slack = cur[col_slack()];

    out.push(sign * (sign - one));

    let mut acc = F::zero();
    let mut pow = F::one();
    for i in 0..RANGE_BITS {
        let bit = cur[col_abs_bit(i)];
        out.push(bit * (bit - one));
        acc += bit * pow;
        pow *= two;
    }
    out.push(acc - abs_v);

    let mut acc = F::zero();
    let mut pow = F::one();
    for i in 0..RANGE_BITS {
        let bit = cur[col_slack_bit(i)];
        out.push(bit * (bit - one));
        acc += bit * pow;
        pow *= two;
    }
    out.push(acc - slack);

    let q = F::from(Q as u64);
    out.push((one - sign) * abs_v + sign * (q - abs_v) - c);

    let bound_f = F::from(bound as u64);
    out.push(slack + abs_v + one - bound_f);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    #[test]
    fn honest_trace_passes() {
        let bound = Z_BOUND;
        let coeffs: Vec<u32> = vec![
            0, 1, 100, bound - 1, Q - 1, Q - bound + 1, Q - 100,
        ];
        let n_trace = coeffs.len().next_power_of_two().max(2);
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &coeffs, bound);
        for row in 0..coeffs.len() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let cvals = eval_per_row(&cur, &cur, row, bound);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "constraint {i} on row {row} (c={}) not zero: {v:?}",
                    coeffs[row]);
            }
        }
    }

    #[test]
    fn out_of_bound_coefficient_breaks() {
        // |centred| = bound exactly should fail (strict inequality).
        let bound = 100u32;
        // c such that centred(c) = bound  → fail.
        let coeffs = [bound];
        let n_trace = 2;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &coeffs, bound);
        // Slack would be saturated to 0 → constraint slack+abs+1 = bound → 0 + 100 + 1 ≠ 100.
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let cvals = eval_per_row(&cur, &cur, 0, bound);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "out-of-bound coefficient must break a constraint");
    }
}
