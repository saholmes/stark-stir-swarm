//! Top-level ML-DSA-44 verify AIR — **phase 6 v1: pointwise core**.
//!
//! Composes the polynomial-arithmetic core of FIPS 204 §3
//! Algorithm 3 step 5 plus the bound check from step 8.  Treats
//! the Keccak-based steps (1, 2, 3, 4, 7) as native pre-/post-
//! computation: the prover runs ExpandA, computes `μ` and `c`,
//! and commits the NTT-domain matrices and polynomials as public
//! inputs.  The AIR proves only the final pointwise equation
//!
//! ```text
//!   w'_approx_ntt[k][i] = Σ_l Â[k][l][i] · NTT(z)[l][i]
//!                         − NTT(c)[i] · NTT(t1·2^d)[k][i]
//! ```
//!
//! for every k ∈ [0, K) and every i ∈ [0, N), plus
//! `‖z‖∞ < γ₁ − β` over every coefficient of every `z` polynomial.
//!
//! ## Why this v1 is sound for the gate's threat model
//!
//! The point of the designated-verifier gate is "no `sk` ⇒ no
//! valid PoK".  An adversary without `sk` cannot produce a
//! signature `(c̃, z, h)` such that the verify equation holds.
//! This AIR proves the equation holds given (z, h) — which
//! requires solving an MLWE instance the adversary cannot solve
//! without `sk`.  The Keccak-based steps are checked **natively**
//! by the verifier outside the STARK: recompute `c̃'` from `μ ‖
//! w1Encode(w'_1)`, compare to the supplied `c̃`.
//!
//! v2 (full in-circuit FIPS 204 verify) is the goal but requires
//! a chained-AIR memory argument for the NTT plus full Keccak
//! orchestration.  See `docs/ml_dsa_air_plan.md` phase 6
//! continuation for the v2 roadmap.
//!
//! ## Trace layout (v1)
//!
//! One row per polynomial coefficient.  The verify-AIR processes
//! `K · N` coefficients (K = 4, N = 256, so 1024 rows per verify
//! call).  Each row holds:
//!
//! | column band                        | width | meaning                           |
//! |------------------------------------|-------|-----------------------------------|
//! | z_ntt × L                          | 4     | one cell per `z[l][i]` (NTT-dom)  |
//! | a_ntt × L                          | 4     | row of the matrix Â at coeff i    |
//! | t1_d_ntt                           | 1     | t1·2^d at this (k, i)             |
//! | c_ntt                              | 1     | challenge poly NTT-dom at i       |
//! | w_approx_ntt                       | 1     | claimed result                    |
//! | norm-check witness for z[l][i]     | 4·(4+34) = 152 | sign / abs / slack / bits |
//!
//! Per-row constraints:
//!   - L `mul_q` operations (a_ntt[l] · z_ntt[l]) accumulated
//!   - 1 `mul_q` for c_ntt · t1_d_ntt
//!   - 1 final equality: Σ products − c·t1d − w_approx = 0  (mod q)
//!   - L norm-check sub-AIRs (one per z coefficient at this row)
//!
//! Constraint count per row ≈ 1 + 1 + L · NUM_CONSTRAINTS_NORM_CHECK ≈ 155.
//!
//! For phase 6 v1, we land just the polynomial-equation constraint
//! (no norm-check fold-in yet — that lives in `ml_dsa_norm_check_air`
//! and gets composed at the layout level).  The norm-check rows
//! occupy a separate trace region.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::{K, L, N, Q};

/// Total verify-AIR rows for one ML-DSA-44 verify (K outputs × N coeffs).
pub const VERIFY_AIR_ROWS: usize = K * N;

// ─── Trace columns ─────────────────────────────────────────────────

/// `z_ntt[l]` for l ∈ [0, L).
#[inline] pub const fn col_z_ntt(l: usize) -> usize { l }
/// `a_ntt[l]` for l ∈ [0, L) (this row's slice of the matrix Â).
#[inline] pub const fn col_a_ntt(l: usize) -> usize { L + l }
/// t1·2^d in NTT domain at (k, i).
#[inline] pub const fn col_t1d_ntt() -> usize { 2 * L }
/// challenge polynomial NTT domain at i.
#[inline] pub const fn col_c_ntt() -> usize { 2 * L + 1 }
/// claimed result.
#[inline] pub const fn col_w_approx_ntt() -> usize { 2 * L + 2 }

/// Aux witness column for the matrix-vector accumulator.
/// `acc[l]` = Σ_{l'≤l} a_ntt[l']·z_ntt[l']  (mod q).  `acc[L−1]` is
/// the full inner product.
#[inline] pub const fn col_acc(l: usize) -> usize { 2 * L + 3 + l }

/// Aux witness column for `c_ntt · t1d_ntt`.
#[inline] pub const fn col_c_t1d_prod() -> usize { 2 * L + 3 + L }

/// Aux witness columns for the modular reductions associated with
/// the L MULs in the inner product, plus 1 for the c·t1d MUL.
/// Each holds the integer quotient `k` such that `a · b − c = k · q`
/// (analogous to the field-AIR's reduction witness).
#[inline] pub const fn col_acc_red(l: usize) -> usize { 2 * L + 4 + L + l }
#[inline] pub const fn col_c_t1d_red() -> usize { 2 * L + 4 + 2 * L }
#[inline] pub const fn col_final_red() -> usize { 2 * L + 5 + 2 * L }

pub const WIDTH: usize = 2 * L + 6 + 2 * L;

/// Number of constraints per row.  Each MUL contributes one
/// degree-2 constraint; the final equality is one degree-1
/// constraint.
pub const NUM_CONSTRAINTS: usize =
    L           // first L muls (acc[l] − acc[l-1] − a*z + k*q = 0)
  + 1           // c · t1d mul
  + 1;          // final equation: acc[L-1] − c_t1d_prod − w_approx_ntt = 0  (mod q)

// ─── fill_trace ────────────────────────────────────────────────────

/// Fill the verify-AIR trace from the public inputs `(a_ntt,
/// t1d_ntt, c_ntt, w_approx_ntt)` and witness `z_ntt`.  The caller
/// is responsible for populating these from the FIPS 204 §3
/// Algorithm 3 inputs (after running ExpandA, NTT(z), NTT(c),
/// NTT(t1·2^d) natively).
///
/// Layout: row index = `k * N + i`.  Column 0..L holds `z_ntt[l][i]`
/// (the *witness*), columns L..2L hold `a_ntt[k][l][i]` (the row of
/// the matrix), col 2L holds `t1d_ntt[k][i]`, etc.
pub fn fill_trace(
    trace: &mut [Vec<F>],
    n_trace: usize,
    a_ntt:        &[[[u32; N]; L]; K],   // matrix Â
    z_ntt:        &[[u32; N]; L],
    c_ntt:        &[u32; N],
    t1d_ntt:      &[[u32; N]; K],
    w_approx_ntt: &[[u32; N]; K],
) {
    assert_eq!(trace.len(), WIDTH);
    assert!(n_trace >= VERIFY_AIR_ROWS);

    for k in 0..K {
        for i in 0..N {
            let row = k * N + i;

            for l in 0..L {
                trace[col_z_ntt(l)][row] = F::from(z_ntt[l][i] as u64);
                trace[col_a_ntt(l)][row] = F::from(a_ntt[k][l][i] as u64);
            }
            trace[col_t1d_ntt()][row]    = F::from(t1d_ntt[k][i] as u64);
            trace[col_c_ntt()][row]      = F::from(c_ntt[i] as u64);
            trace[col_w_approx_ntt()][row] = F::from(w_approx_ntt[k][i] as u64);

            // Accumulator: acc[l] = Σ_{l'≤l} a_ntt[l']·z_ntt[l']  mod q.
            let mut acc: u64 = 0;
            for l in 0..L {
                let prod_full = (a_ntt[k][l][i] as u64) * (z_ntt[l][i] as u64);
                let new_acc_full = acc + prod_full;
                let acc_red_k = new_acc_full / (Q as u64);
                let new_acc = new_acc_full % (Q as u64);
                trace[col_acc(l)][row]     = F::from(new_acc);
                trace[col_acc_red(l)][row] = F::from(acc_red_k);
                acc = new_acc;
            }
            // c · t1d
            let ct1d_full = (c_ntt[i] as u64) * (t1d_ntt[k][i] as u64);
            let ct1d_red_k = ct1d_full / (Q as u64);
            let ct1d = ct1d_full % (Q as u64);
            trace[col_c_t1d_prod()][row] = F::from(ct1d);
            trace[col_c_t1d_red()][row]  = F::from(ct1d_red_k);

            // Final equation: w_approx = acc - ct1d (mod q).
            // We allow the final constraint to absorb +q if
            // acc < ct1d (single subtraction wrap).
            let final_red_k: u64 = if acc >= ct1d { 0 } else { 1 };
            trace[col_final_red()][row] = F::from(final_red_k);
        }
    }
}

// ─── Constraints ───────────────────────────────────────────────────

pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let q = F::from(Q as u64);

    // Inner-product accumulator: acc[l] = acc[l-1] + a_ntt[l]·z_ntt[l] - acc_red[l] · q
    let mut prev_acc = F::zero();
    for l in 0..L {
        let a = cur[col_a_ntt(l)];
        let z = cur[col_z_ntt(l)];
        let acc = cur[col_acc(l)];
        let red_k = cur[col_acc_red(l)];
        out.push(prev_acc + a * z - red_k * q - acc);
        prev_acc = acc;
    }

    // c · t1d = c_t1d_prod + c_t1d_red · q
    let c   = cur[col_c_ntt()];
    let t1d = cur[col_t1d_ntt()];
    let ct1d_prod = cur[col_c_t1d_prod()];
    let ct1d_red  = cur[col_c_t1d_red()];
    out.push(c * t1d - ct1d_red * q - ct1d_prod);

    // Final: w_approx = acc[L-1] - c_t1d_prod  (mod q), absorbed as
    //   acc[L-1] - c_t1d_prod + final_red · q − w_approx = 0
    let acc_full   = cur[col_acc(L - 1)];
    let w_approx   = cur[col_w_approx_ntt()];
    let final_red  = cur[col_final_red()];
    out.push(acc_full - ct1d_prod + final_red * q - w_approx);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

// ─── Tests ─────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa_field::{add_q, mul_q, sub_q};

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Build a synthetic, internally-consistent set of NTT-domain
    /// public inputs + witness, fill the trace, and verify every
    /// per-row constraint is zero.
    #[test]
    fn honest_pointwise_trace_satisfies_constraints() {
        // Synth: pick small values so the products fit easily.
        let mut a_ntt = [[[0u32; N]; L]; K];
        let mut z_ntt = [[0u32; N]; L];
        let mut c_ntt = [0u32; N];
        let mut t1d_ntt = [[0u32; N]; K];
        for k in 0..K {
            for l in 0..L {
                for i in 0..N {
                    a_ntt[k][l][i] = (1000 + i as u32 * 17 + l as u32 * 31 + k as u32 * 41) % Q;
                }
            }
        }
        for l in 0..L {
            for i in 0..N {
                z_ntt[l][i] = (3 + i as u32 * 7 + l as u32 * 19) % Q;
            }
        }
        for i in 0..N {
            c_ntt[i] = (1 + i as u32 * 23) % Q;
        }
        for k in 0..K {
            for i in 0..N {
                t1d_ntt[k][i] = (5 + i as u32 * 11 + k as u32 * 13) % Q;
            }
        }

        // Compute w_approx_ntt natively from the equation.
        let mut w_approx_ntt = [[0u32; N]; K];
        for k in 0..K {
            for i in 0..N {
                let mut acc: u32 = 0;
                for l in 0..L {
                    let p = mul_q(a_ntt[k][l][i], z_ntt[l][i]);
                    acc = add_q(acc, p);
                }
                let ct1d = mul_q(c_ntt[i], t1d_ntt[k][i]);
                w_approx_ntt[k][i] = sub_q(acc, ct1d);
            }
        }

        let n_trace = VERIFY_AIR_ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &a_ntt, &z_ntt, &c_ntt, &t1d_ntt, &w_approx_ntt);

        for row in 0..VERIFY_AIR_ROWS {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let cvals = eval_per_row(&cur, &cur, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }

    /// Tampering with a single z_ntt witness must break some constraint.
    #[test]
    fn malicious_z_ntt_breaks_constraint() {
        let a_ntt = [[[1u32; N]; L]; K];
        let z_ntt = [[2u32; N]; L];
        let c_ntt = [3u32; N];
        let t1d_ntt = [[4u32; N]; K];

        let mut w_approx_ntt = [[0u32; N]; K];
        for k in 0..K {
            for i in 0..N {
                let mut acc: u32 = 0;
                for l in 0..L {
                    acc = add_q(acc, mul_q(a_ntt[k][l][i], z_ntt[l][i]));
                }
                let ct1d = mul_q(c_ntt[i], t1d_ntt[k][i]);
                w_approx_ntt[k][i] = sub_q(acc, ct1d);
            }
        }

        let n_trace = VERIFY_AIR_ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &a_ntt, &z_ntt, &c_ntt, &t1d_ntt, &w_approx_ntt);

        // Tamper: increment z_ntt at row 0 so the equation no longer holds.
        trace[col_z_ntt(0)][0] += F::one();

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let cvals = eval_per_row(&cur, &cur, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "tampering with z_ntt must break some constraint");
    }
}
