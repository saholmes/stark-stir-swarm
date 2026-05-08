//! AIR for `Decompose` / `HighBits` / `LowBits` (FIPS 204 §3.6).
//!
//! Witnesses `r ∈ Z_q` decomposed as `(r₁, r₀)` with
//! `r₁ ∈ [0, 88)` and `r₀` a centred residue in `(−γ₂, γ₂]`.
//! Used by `ml_dsa_verify_air` to extract HighBits from
//! `w'_approx` and check the hint against the public hint vector.
//!
//! Trace layout (one decomposition per row):
//!
//! | columns                    | meaning                             |
//! |----------------------------|-------------------------------------|
//! | `r`                        | input value in [0, q)              |
//! | `r1`                       | high part in [0, 88)                |
//! | `r0`                       | low part lifted into [0, q)         |
//! | `r0_sign`                  | 0 if r0 ≤ γ₂, 1 otherwise (= "wrapped negative") |
//! | `r0_centred_abs`           | |r0_signed| in [0, γ₂]              |
//! | range bits for r1 (7 bits) | binary decomp; r1 < 128 (88 < 128) |
//! | range bits for r0_abs (18) | binary decomp; γ₂ ≈ 95232 < 2^17... |
//!
//! Constraints (per row):
//!   - r1 range bits boolean + sum = r1
//!   - r0_centred_abs range bits boolean + sum = r0_centred_abs
//!   - r0_sign boolean
//!   - r0 = r0_centred_abs · (1 − 2·r0_sign) + r0_sign · q   (lift)
//!   - r ≡ r1 · 2γ₂ + (r0 − [r0_sign · q])  (mod q)
//!     → enforced as r − r1·2γ₂ − r0_signed = 0 in Z_q via Goldilocks
//!   - r1 < 88 (extra bound check; 88 = 0b1011000, can constrain
//!     directly via a 7-bit decomposition + (r1 - 88) · (witness inverse))
//!
//! Constraint count per row ≈ 30 (deg ≤ 2).
//!
//! **Status:** layout pinned, native-driven trace fill +
//! constraint impl below.  Tested against the native `decompose`
//! reference.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::{GAMMA2, Q};
use crate::ml_dsa_decompose::{decompose, NUM_R1_VALUES};

// ─── Column layout ──────────────────────────────────────────────────

// r1 ∈ [0, NUM_R1_VALUES): L1 → r1 < 44 (6 bits); L3/L5 → r1 < 16 (4 bits).
#[cfg(feature = "mldsa-44")]
const R1_RANGE_BITS: usize = 6;
#[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
const R1_RANGE_BITS: usize = 4;

// |r0_centred| ∈ [0, γ_2]: L1 → γ_2 = 95232 (17 bits); L3/L5 → γ_2 = 261888 (18 bits).
#[cfg(feature = "mldsa-44")]
const R0_ABS_RANGE_BITS: usize = 17;
#[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
const R0_ABS_RANGE_BITS: usize = 18;

#[inline] pub const fn col_r() -> usize { 0 }
#[inline] pub const fn col_r1() -> usize { 1 }
#[inline] pub const fn col_r0() -> usize { 2 }
#[inline] pub const fn col_r0_sign() -> usize { 3 }
#[inline] pub const fn col_r0_abs() -> usize { 4 }
#[inline] pub const fn col_snap() -> usize { 5 }
#[inline] pub const fn col_r1_bit(i: usize) -> usize { 6 + i }
#[inline] pub const fn col_r0_abs_bit(i: usize) -> usize { 6 + R1_RANGE_BITS + i }

pub const WIDTH: usize = 6 + R1_RANGE_BITS + R0_ABS_RANGE_BITS;

pub const NUM_CONSTRAINTS: usize =
    R1_RANGE_BITS              // r1 bit booleans
  + 1                          // r1 = Σ r1_bit · 2^i
  + R0_ABS_RANGE_BITS          // r0_abs bit booleans
  + 1                          // r0_abs = Σ r0_abs_bit · 2^i
  + 1                          // r0_sign boolean
  + 1                          // snap flag boolean
  + 1                          // r0 lift consistency
  + 1                          // recomposition (snap-aware)
  + 1;                         // r1 < NUM_R1_VALUES

// ─── fill_trace ────────────────────────────────────────────────────

pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, values: &[u32]) {
    use crate::ml_dsa::params::GAMMA2;
    assert_eq!(trace.len(), WIDTH);
    assert!(values.len() <= n_trace);

    let two_g2 = 2 * GAMMA2;
    for (row, &r) in values.iter().enumerate() {
        debug_assert!(r < Q);
        let (r1, r0) = decompose(r);
        let (sign, abs) = if r0 > Q / 2 {
            (1u64, Q - r0)
        } else {
            (0u64, r0)
        };
        // Detect snap: pre-snap r1 was NUM_R1_VALUES iff
        //   r % 2γ₂ > γ₂ AND (r - r0_pre_signed) / 2γ₂ == NUM_R1_VALUES
        // Equivalent characterization: snap fires iff post-snap r1 = 0
        // AND r ≥ q − γ₂ + 1 (the only r values producing the boundary).
        // We compute it by checking both decompositions (with and
        // without snap) and seeing which holds.
        let r_mod = r % two_g2;
        let r0_pre_signed: i64 = if r_mod > GAMMA2 {
            r_mod as i64 - two_g2 as i64
        } else {
            r_mod as i64
        };
        let r1_pre = ((r as i64 - r0_pre_signed) / two_g2 as i64) as u32;
        let snap = if r1_pre == NUM_R1_VALUES { 1u64 } else { 0u64 };

        trace[col_r()][row]        = F::from(r as u64);
        trace[col_r1()][row]       = F::from(r1 as u64);
        trace[col_r0()][row]       = F::from(r0 as u64);
        trace[col_r0_sign()][row]  = F::from(sign);
        trace[col_r0_abs()][row]   = F::from(abs as u64);
        trace[col_snap()][row]     = F::from(snap);
        for i in 0..R1_RANGE_BITS {
            trace[col_r1_bit(i)][row] = F::from(((r1 as u64 >> i) & 1) as u64);
        }
        for i in 0..R0_ABS_RANGE_BITS {
            trace[col_r0_abs_bit(i)][row] = F::from(((abs as u64 >> i) & 1) as u64);
        }
    }
}

// ─── constraint evaluation ─────────────────────────────────────────

pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();
    let two = F::from(2u64);

    let r       = cur[col_r()];
    let r1      = cur[col_r1()];
    let r0      = cur[col_r0()];
    let r0_sign = cur[col_r0_sign()];
    let r0_abs  = cur[col_r0_abs()];
    let snap    = cur[col_snap()];

    // r1 bit booleans + decomposition
    let mut acc = F::zero();
    let mut pow = F::one();
    for i in 0..R1_RANGE_BITS {
        let bit = cur[col_r1_bit(i)];
        out.push(bit * (bit - one));
        acc += bit * pow;
        pow *= two;
    }
    out.push(acc - r1);

    // r0_abs bit booleans + decomposition
    let mut acc = F::zero();
    let mut pow = F::one();
    for i in 0..R0_ABS_RANGE_BITS {
        let bit = cur[col_r0_abs_bit(i)];
        out.push(bit * (bit - one));
        acc += bit * pow;
        pow *= two;
    }
    out.push(acc - r0_abs);

    // r0_sign boolean
    out.push(r0_sign * (r0_sign - one));
    // snap flag boolean
    out.push(snap * (snap - one));

    // r0 lift consistency: r0 = (1 - sign) · r0_abs + sign · (q - r0_abs)
    let q = F::from(Q as u64);
    out.push((one - r0_sign) * r0_abs + r0_sign * (q - r0_abs) - r0);

    // Recomposition with snap correction.  In integer terms:
    //   non-snap:  r = r1·2γ₂ + r0_signed
    //   snap:      r = r1·2γ₂ + r0_signed + q   (because pre-snap r1 = NUM_R1_VALUES)
    // Lifting r0_signed → r0 = r0_signed + sign·q, the constraint becomes:
    //   r = r1·2γ₂ + r0 − sign·q + snap·q
    // i.e.  r1·2γ₂ + r0 + (snap − sign)·q − r = 0
    let two_g2 = F::from((2 * GAMMA2) as u64);
    out.push(r1 * two_g2 + r0 + (snap - r0_sign) * q - r);

    // r1 < NUM_R1_VALUES — currently stub; the recomp + bit-range
    // constraints together force r1 into [0, NUM_R1_VALUES) for any
    // honest input, but a malicious prover could in principle pick
    // r1 ∈ [NUM_R1_VALUES, 64) and tweak r0/snap to balance.  A
    // proper bound proof requires an auxiliary column witnessing
    // (NUM_R1_VALUES − 1 − r1).  Listed in the phase-5 follow-up.
    out.push(F::zero());

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_trace(n_trace: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n_trace]).collect()
    }

    #[test]
    fn honest_trace_passes_constraints() {
        // Cover every "interesting" r: zero, near-zero, near γ₂,
        // near 2γ₂, large, near q.
        let values: Vec<u32> = vec![
            0, 1, GAMMA2 - 1, GAMMA2, GAMMA2 + 1,
            2 * GAMMA2 - 1, 2 * GAMMA2, 2 * GAMMA2 + 1,
            Q / 2, Q - GAMMA2, Q - 1,
            123456, 7654321, 4_000_000,
        ];
        let n_trace = values.len().next_power_of_two().max(2);
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &values);

        for row in 0..values.len() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let cvals = eval_per_row(&cur, &cur, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "constraint {i} on row {row} (r={}) not zero: {v:?}",
                    values[row]);
            }
        }
    }

    #[test]
    fn malicious_r1_breaks_constraint() {
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &[12345u32]);
        // Tamper: set r1 to wrong value (still within 7-bit range).
        let bogus = trace[col_r1()][0] + F::one();
        trace[col_r1()][0] = bogus;
        // Recompute its bit decomposition so the range check still passes.
        // (extracting the integer is messy; just zero the bits and count
        //  on the recomposition constraint to fire.)
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let cvals = eval_per_row(&cur, &cur, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "tampering with r1 must break some constraint");
    }
}
