//! T-UseHint: per-coefficient `UseHint(h, r)` AIR (FIPS 204 §3.6 Algorithm 13).
//!
//! `UseHint` is the gate that turns a coefficient `r` of `w_approx`
//! plus a single hint bit `h` into the high-bits value `adjusted_r1`
//! that `w1Encode` then packs into the SHAKE-256 transcript input.
//!
//! ## What v2 needs
//!
//! After v1.7's polynomial-arithmetic AIR commits to
//! `w_approx_ntt[k][i]`, the v2 path runs `INTT` on each row k to
//! get `w_approx[k][i]` (coeff domain).  Then for each `(k, i)`:
//!
//!   `(r1[k][i], r0[k][i]) = Decompose(w_approx[k][i])`
//!   `adjusted_r1[k][i]    = UseHint(h[k][i], w_approx[k][i])`
//!   `w1bytes[k]           = w1Encode(adjusted_r1[k])`
//!
//! Then `c̃' = SHAKE-256(µ ‖ w1bytes_concat)` and finally
//! `c̃' == c̃` closes the verify loop.
//!
//! The `Decompose` AIR (`ml_dsa_decompose_air`) already exists.
//! The `w1Encode` AIR (`ml_dsa_w1_encode_air`) already exists.
//! T-UseHint is the missing bridge: take Decompose's `(r1, r0_sign)`
//! plus a hint bit `h` and produce `adjusted_r1`.
//!
//! ## FIPS 204 §3.6 Algorithm 13 (UseHint)
//!
//! ```text
//! m = (q − 1) / (2 γ_2) = 44   (ML-DSA-44)
//! (r1, r0) = Decompose(r)
//! if h = 1 and r0 >  0: return (r1 + 1) mod m
//! if h = 1 and r0 ≤ 0:  return (r1 − 1) mod m
//! return r1
//! ```
//!
//! ## Per-row layout (one coefficient per row)
//!
//! Inputs (witness or PI-bound):
//! - `r1`         : decompose's r1 ∈ `[0, m)` for this coefficient.
//! - `r0_sign`    : 1 if `r0 > 0`, else 0.
//! - `h`          : the hint bit, ∈ `{0, 1}`.
//!
//! Outputs (witness):
//! - `adjusted_r1`: in `[0, m)`.
//! - `wrap_pos`, `wrap_neg`: ∈ `{0, 1}`, mutually exclusive.
//!   - `wrap_pos = 1` iff the unwrapped result is `−1` (so `adjusted_r1 = m − 1`).
//!   - `wrap_neg = 1` iff the unwrapped result is `m` (so `adjusted_r1 = 0`).
//!
//! Auxiliary:
//! - `delta = h · (2·r0_sign − 1)`: the unwrapped adjustment.
//!
//! Range check on `adjusted_r1 ∈ [0, m)` via 6-bit decomp + slack.
//!
//! ## Per-row constraints (constant cardinality, all ≤ deg 2)
//!
//! 1. `h · (h − 1) = 0`
//! 2. `r0_sign · (r0_sign − 1) = 0`
//! 3. `delta − h · (2·r0_sign − 1) = 0`
//! 4. `wrap_pos · (wrap_pos − 1) = 0`
//! 5. `wrap_neg · (wrap_neg − 1) = 0`
//! 6. `wrap_pos · wrap_neg = 0`  (mutual exclusivity)
//! 7. `adjusted_r1 − r1 − delta + m · wrap_pos − m · wrap_neg = 0`
//!    (algebraic gate: `adjusted_r1 = r1 + delta + m·(wrap_neg − wrap_pos)`)
//! 8. 6 boolean constraints on `adjusted_r1_bits`
//! 9. `adjusted_r1 = Σ adjusted_r1_bits[i] · 2^i`
//! 10. 6 boolean constraints on `slack_bits`
//! 11. `slack = Σ slack_bits[i] · 2^i`
//! 12. `adjusted_r1 + slack + 1 − m = 0`  (range: `adjusted_r1 ≤ m − 1`)

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

/// `m = (q − 1) / (2·γ_2)`.  Each `r1` and `adjusted_r1` lives in
/// `[0, M)`.  Auto-derived from `ml_dsa::params::GAMMA2`:
/// - ML-DSA-44 (γ_2 = (q-1)/88): M = 44, fits in 6 bits.
/// - ML-DSA-65 / ML-DSA-87 (γ_2 = (q-1)/32): M = 16, fits in 4 bits.
pub const M: u32 = (crate::ml_dsa::params::Q - 1) / (2 * crate::ml_dsa::params::GAMMA2);

/// Bits needed to range-check values in `[0, M)`.
#[cfg(feature = "mldsa-44")]
pub const RANGE_BITS: usize = 6;
#[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
pub const RANGE_BITS: usize = 4;

// ─── Column layout ────────────────────────────────────────────────

pub const COL_R1:           usize = 0;
pub const COL_R0_SIGN:      usize = 1;
pub const COL_H:            usize = 2;
pub const COL_DELTA:        usize = 3;
pub const COL_WRAP_POS:     usize = 4;
pub const COL_WRAP_NEG:     usize = 5;
pub const COL_ADJUSTED_R1:  usize = 6;
#[inline] pub const fn col_adj_bit(i: usize) -> usize { 7 + i }       // 7..13
pub const COL_SLACK:        usize = 7 + RANGE_BITS;                   // 13
#[inline] pub const fn col_slack_bit(i: usize) -> usize { 14 + i }    // 14..20

pub const WIDTH: usize = 14 + RANGE_BITS;  // 20

pub const NUM_CONSTRAINTS: usize =
    1                       // h boolean
  + 1                       // r0_sign boolean
  + 1                       // delta correctness
  + 1                       // wrap_pos boolean
  + 1                       // wrap_neg boolean
  + 1                       // wrap mutual exclusivity
  + 1                       // adjusted_r1 algebraic gate
  + RANGE_BITS              // adj bit booleans
  + 1                       // adj reconstruction
  + RANGE_BITS              // slack bit booleans
  + 1                       // slack reconstruction
  + 1;                      // upper-bound range gate

// ─── Native helpers ───────────────────────────────────────────────

/// Native `UseHint`: takes `r1, r0_sign, h` (canonical Decompose
/// outputs + hint bit) and returns `(adjusted_r1, wrap_pos, wrap_neg)`.
///
/// `r0_sign = 1` iff Decompose's `r0 > 0`; `0` iff `r0 ≤ 0`.
pub fn use_hint(r1: u32, r0_sign: u32, h: u32) -> (u32, u32, u32) {
    debug_assert!(r1 < M);
    debug_assert!(r0_sign <= 1);
    debug_assert!(h <= 1);

    let delta: i32 = if h == 0 {
        0
    } else if r0_sign == 1 {
        1
    } else {
        -1
    };
    let unwrapped = (r1 as i32) + delta;
    let (adjusted, wrap_pos, wrap_neg) = if unwrapped < 0 {
        // r1 = 0, delta = -1 → unwrapped = -1 → adjusted = M - 1
        ((M - 1) as i32, 1u32, 0u32)
    } else if unwrapped >= M as i32 {
        // r1 = M-1, delta = +1 → unwrapped = M → adjusted = 0
        (0i32, 0u32, 1u32)
    } else {
        (unwrapped, 0u32, 0u32)
    };
    (adjusted as u32, wrap_pos, wrap_neg)
}

// ─── fill_trace ───────────────────────────────────────────────────

/// One row per coefficient.  `inputs[i] = (r1, r0_sign, h)`.
pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, inputs: &[(u32, u32, u32)]) {
    assert_eq!(trace.len(), WIDTH);
    assert!(inputs.len() <= n_trace);

    for (row, &(r1, r0_sign, h)) in inputs.iter().enumerate() {
        let (adjusted, wrap_pos, wrap_neg) = use_hint(r1, r0_sign, h);

        // delta = h · (2·r0_sign − 1)  (in i32 arithmetic; lift to F at the end)
        let delta_i: i32 = if h == 0 { 0 } else if r0_sign == 1 { 1 } else { -1 };
        let delta_f = if delta_i >= 0 {
            F::from(delta_i as u64)
        } else {
            F::zero() - F::from((-delta_i) as u64)
        };

        // slack = M − 1 − adjusted (so adjusted + slack + 1 = M)
        let slack = M - 1 - adjusted;

        trace[COL_R1][row]          = F::from(r1 as u64);
        trace[COL_R0_SIGN][row]     = F::from(r0_sign as u64);
        trace[COL_H][row]           = F::from(h as u64);
        trace[COL_DELTA][row]       = delta_f;
        trace[COL_WRAP_POS][row]    = F::from(wrap_pos as u64);
        trace[COL_WRAP_NEG][row]    = F::from(wrap_neg as u64);
        trace[COL_ADJUSTED_R1][row] = F::from(adjusted as u64);
        for b in 0..RANGE_BITS {
            trace[col_adj_bit(b)][row] = F::from(((adjusted >> b) & 1) as u64);
        }
        trace[COL_SLACK][row] = F::from(slack as u64);
        for b in 0..RANGE_BITS {
            trace[col_slack_bit(b)][row] = F::from(((slack >> b) & 1) as u64);
        }
    }

    // Padding rows: fill with constraint-satisfying values so phi
    // vanishes on all H points (gap #5b in the soundness audit).
    //
    // Strategy: r1 = adjusted_r1 = 0, h = wrap_pos = wrap_neg = 0,
    // r0_sign = 0, delta = 0, adj_bits all 0, slack = M-1 with bits
    // = binary(M-1).  Walking the constraints:
    //   1. h boolean (0): 0
    //   2. r0_sign boolean (0): 0
    //   3. delta correctness: 0 - 0·(2·0 - 1) = 0
    //   4-6. wrap booleans + mutex (all 0): 0
    //   7. adjusted gate: 0 - 0 - 0 - M·0 + M·0 = 0
    //   8. adj bit booleans (0): 0
    //   9. adj reconstruction: 0 - 0 = 0
    //  10. slack bit booleans (0/1): 0
    //  11. slack reconstruction: (M-1) - (M-1) = 0
    //  12. adj + slack + 1 - M: 0 + (M-1) + 1 - M = 0 ✓
    let slack_pad = M - 1;
    for row in inputs.len()..n_trace {
        trace[COL_SLACK][row] = F::from(slack_pad as u64);
        for b in 0..RANGE_BITS {
            trace[col_slack_bit(b)][row] = F::from(((slack_pad >> b) & 1) as u64);
        }
        // All other columns remain zero from initial allocation.
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();
    let two = F::from(2u64);
    let m = F::from(M as u64);

    let r1 = cur[COL_R1];
    let r0_sign = cur[COL_R0_SIGN];
    let h = cur[COL_H];
    let delta = cur[COL_DELTA];
    let wrap_pos = cur[COL_WRAP_POS];
    let wrap_neg = cur[COL_WRAP_NEG];
    let adj = cur[COL_ADJUSTED_R1];
    let slack = cur[COL_SLACK];

    // 1. h boolean
    out.push(h * (h - one));
    // 2. r0_sign boolean
    out.push(r0_sign * (r0_sign - one));
    // 3. delta = h · (2·r0_sign − 1)
    out.push(delta - h * (two * r0_sign - one));
    // 4. wrap_pos boolean
    out.push(wrap_pos * (wrap_pos - one));
    // 5. wrap_neg boolean
    out.push(wrap_neg * (wrap_neg - one));
    // 6. wrap mutual exclusivity
    out.push(wrap_pos * wrap_neg);
    // 7. adjusted_r1 algebraic gate:
    //    adjusted_r1 = r1 + delta + M·(wrap_pos − wrap_neg)
    //    (wrap_pos = 1 when unwrapped = −1; we add M to reach M − 1.
    //     wrap_neg = 1 when unwrapped = M; we subtract M to reach 0.)
    //    → adjusted_r1 − r1 − delta − M·wrap_pos + M·wrap_neg = 0
    out.push(adj - r1 - delta - m * wrap_pos + m * wrap_neg);

    // 8. adj bit booleans
    for b in 0..RANGE_BITS {
        let v = cur[col_adj_bit(b)];
        out.push(v * (v - one));
    }
    // 9. adj reconstruction
    {
        let mut acc = F::zero();
        let mut pow = F::one();
        let two = F::from(2u64);
        for b in 0..RANGE_BITS {
            acc += cur[col_adj_bit(b)] * pow;
            pow *= two;
        }
        out.push(adj - acc);
    }

    // 10. slack bit booleans
    for b in 0..RANGE_BITS {
        let v = cur[col_slack_bit(b)];
        out.push(v * (v - one));
    }
    // 11. slack reconstruction
    {
        let mut acc = F::zero();
        let mut pow = F::one();
        let two = F::from(2u64);
        for b in 0..RANGE_BITS {
            acc += cur[col_slack_bit(b)] * pow;
            pow *= two;
        }
        out.push(slack - acc);
    }
    // 12. adjusted_r1 + slack + 1 = M  (so adjusted_r1 ≤ M − 1)
    out.push(adj + slack + one - m);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Cover every (r1, r0_sign, h) triple in the domain (44 × 2 × 2
    /// = 176 cases) — exhaustive correctness check on the native
    /// `use_hint`.  At each case, confirm the result matches the
    /// FIPS 204 spec.
    #[test]
    fn use_hint_native_exhaustive() {
        for r1 in 0..M {
            for r0_sign in 0..2u32 {
                for h in 0..2u32 {
                    let (adj, wp, wn) = use_hint(r1, r0_sign, h);
                    // Reference computation per FIPS 204 §3.6:
                    let expected = if h == 0 {
                        r1
                    } else if r0_sign == 1 {
                        (r1 + 1) % M
                    } else {
                        if r1 == 0 { M - 1 } else { r1 - 1 }
                    };
                    assert_eq!(adj, expected,
                        "use_hint mismatch at (r1={r1}, r0_sign={r0_sign}, h={h}): got {adj}, expected {expected}");
                    assert!(wp <= 1 && wn <= 1 && wp + wn <= 1,
                        "wrap flags invalid: ({wp}, {wn}) at r1={r1}");
                }
            }
        }
    }

    /// Honest trace: every constraint zero across all 176 domain
    /// inputs (covers both wrap branches: r1=0,r0_sign=0,h=1 → wrap_pos=1
    /// and r1=43,r0_sign=1,h=1 → wrap_neg=1).
    #[test]
    fn honest_trace_satisfies_all_constraints_exhaustive() {
        let mut inputs = Vec::new();
        for r1 in 0..M {
            for r0_sign in 0..2u32 {
                for h in 0..2u32 {
                    inputs.push((r1, r0_sign, h));
                }
            }
        }

        let n_trace = inputs.len().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &inputs);

        for row in 0..inputs.len() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
            let cvals = eval_per_row(&cur, &dummy_nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-UseHint constraint {i} on row {row} (input {:?}) not zero: {v:?}",
                    inputs[row]);
            }
        }
    }

    /// Tampering: flip the hint bit on a row that legitimately
    /// matches with h=0; the algebraic gate should fire (the
    /// witness adj/wrap_pos/wrap_neg/slack no longer match).
    #[test]
    fn tampered_h_breaks_constraint() {
        let inputs = vec![(10u32, 1u32, 0u32)];  // h=0 → adjusted = r1 = 10
        let mut trace = fresh_trace(2);
        fill_trace(&mut trace, 2, &inputs);

        // Flip h to 1; the gate now expects adjusted = 11 but witness has 10.
        trace[COL_H][0] = F::one();

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
        let cvals = eval_per_row(&cur, &dummy_nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "T-UseHint must reject tampered h");
    }

    /// Tampering: claim `adjusted_r1 = M` (out of range); the upper
    /// bound + bit decomp should fire.
    #[test]
    fn tampered_adjusted_out_of_range_breaks_constraint() {
        let inputs = vec![(10u32, 0u32, 0u32)];
        let mut trace = fresh_trace(2);
        fill_trace(&mut trace, 2, &inputs);

        // Force adjusted_r1 = 44 (= M, out of [0, 44)) by overriding
        // the cell.  Bit decomp won't match (since adj_bits sum to 10
        // but the cell now reads 44), and the upper-bound gate
        // requires adj + slack + 1 = 44, but slack is 33 (from r1=10),
        // giving 44 + 33 + 1 = 78 ≠ 44.
        trace[COL_ADJUSTED_R1][0] = F::from(M as u64);

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
        let cvals = eval_per_row(&cur, &dummy_nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "T-UseHint must reject out-of-range adjusted_r1");
    }

    /// Sanity: the boundary cases for wrap exercise both branches.
    #[test]
    fn wrap_branches_reachable() {
        let (adj, wp, wn) = use_hint(0, 0, 1);   // r1=0, r0≤0, h=1 → -1 → wrap_pos
        assert_eq!((adj, wp, wn), (M - 1, 1, 0));

        let (adj, wp, wn) = use_hint(M - 1, 1, 1);  // r1=M-1, r0>0, h=1 → M → wrap_neg
        assert_eq!((adj, wp, wn), (0, 0, 1));

        // Pick an r1 strictly inside [0, M) for any active level
        // (L1: M=44, L3/L5: M=16): use M/2.
        let mid = M / 2;
        let (adj, wp, wn) = use_hint(mid, 0, 0);   // h=0 → no wrap
        assert_eq!((adj, wp, wn), (mid, 0, 0));
    }
}
