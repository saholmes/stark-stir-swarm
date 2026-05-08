//! AIR for `w1Encode` (FIPS 204 §3.5 Algorithm 28).
//!
//! Per coefficient (one row per coefficient), proves that the
//! 7-bit decomposition matches the native byte-packed output.
//! The packed bytes are exposed as a public input to the verify
//! AIR; this AIR's job is only to certify that the bit columns
//! correspond to a valid HighBits value.
//!
//! Trace layout per row:
//!
//! | column                      | meaning                          |
//! |-----------------------------|----------------------------------|
//! | `r1`                        | HighBits coefficient in [0, 88)  |
//! | bit columns (7)             | binary decomposition of r1       |
//!
//! Constraints (per row):
//!   - 7 bit booleans
//!   - r1 = Σ bit_i · 2^i
//!   - r1 < NUM_R1_VALUES (currently soft, see decompose-AIR note)
//!
//! The byte-level packing across 256 coefficients is a shape
//! transformation handled at the layout level (column wiring) of
//! the verify AIR — there are no extra constraints beyond the
//! per-coefficient bit checks above.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa_decompose::NUM_R1_VALUES;

const W1_BITS: usize = 7;

#[inline] pub const fn col_r1() -> usize { 0 }
#[inline] pub const fn col_bit(i: usize) -> usize { 1 + i }

pub const WIDTH: usize = 1 + W1_BITS;
pub const NUM_CONSTRAINTS: usize = W1_BITS + 1;

pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, coeffs: &[u32]) {
    assert_eq!(trace.len(), WIDTH);
    assert!(coeffs.len() <= n_trace);
    for (row, &c) in coeffs.iter().enumerate() {
        debug_assert!(c < NUM_R1_VALUES,
            "w1_encode coefficient {c} out of range [0, {NUM_R1_VALUES})");
        trace[col_r1()][row] = F::from(c as u64);
        for i in 0..W1_BITS {
            trace[col_bit(i)][row] = F::from(((c >> i) & 1) as u64);
        }
    }
}

pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();
    let two = F::from(2u64);

    let mut acc = F::zero();
    let mut pow = F::one();
    for i in 0..W1_BITS {
        let bit = cur[col_bit(i)];
        out.push(bit * (bit - one));
        acc += bit * pow;
        pow *= two;
    }
    out.push(acc - cur[col_r1()]);

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
        let coeffs: Vec<u32> = (0..NUM_R1_VALUES).collect();
        let n_trace = coeffs.len().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &coeffs);
        for row in 0..coeffs.len() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let cvals = eval_per_row(&cur, &cur, row);
            for v in cvals { assert!(v.is_zero()); }
        }
    }

    #[test]
    fn malicious_bit_breaks_constraint() {
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &[42u32]);
        // Flip the high bit
        trace[col_bit(W1_BITS - 1)][0] = F::one() - trace[col_bit(W1_BITS - 1)][0];
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let cvals = eval_per_row(&cur, &cur, 0);
        assert!(cvals.iter().any(|v| !v.is_zero()),
            "tampering with a bit must surface as a constraint failure");
    }
}
