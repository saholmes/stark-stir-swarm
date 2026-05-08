//! ML-DSA-44 verify AIR — **v1.5** (I1 + I3).
//!
//! Extends `ml_dsa_verify_air` (the v1 polynomial-arithmetic core)
//! with an in-circuit norm check on the response polynomial `z`.
//! After v1.5, Layer-1 native `ml_dsa::verify` no longer carries
//! the `‖z‖∞ < γ_1 − β` check; the STARK enforces it.
//!
//! ## Trace layout
//!
//! Two regions, gated by a single boolean selector column:
//!
//! - **Region A** (rows `0 .. K·N` = `0 .. 1024`):
//!   per-coefficient polynomial-arithmetic check, identical to
//!   `ml_dsa_verify_air`.  Selector `sel_eq = 1`.
//!
//! - **Region B** (rows `K·N .. K·N + L·N` = `1024 .. 2048`):
//!   per-coefficient norm-check on `z[l][i]`.  Selector
//!   `sel_eq = 0`.
//!
//! Total trace rows: `K·N + L·N = 2048`.
//!
//! Each row holds the union of v1's columns and the
//! `ml_dsa_norm_check_air` columns plus one selector column.
//!
//! ## Per-row constraints
//!
//! Every row emits the same constraint vector (FRI requires
//! constant cardinality across rows).  Each constraint is gated
//! by `sel_eq` or `(1 − sel_eq)` so it only "fires" in its region.
//!
//! - 6 polynomial-arithmetic constraints (gated by `sel_eq`)
//! - `NUM_CONSTRAINTS_NORM` norm-check constraints (gated by `1 − sel_eq`)
//! - 1 selector boolean (`sel_eq · (sel_eq − 1) = 0`)
//!
//! Total: `6 + NUM_CONSTRAINTS_NORM + 1`.
//!
//! ## Soundness gain over v1
//!
//! v1's `‖z‖∞` check happens in Layer-1 native `ml_dsa::verify`.
//! v1.5 lifts it into the STARK: any signature whose `z` violates
//! the bound produces a trace that fails the norm-check region
//! constraints, so the FRI verifier rejects without needing
//! Layer-1 to look at it.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::{K, L, N, Q};
use crate::ml_dsa_verify_air;
use crate::ml_dsa_norm_check_air;
use crate::ml_dsa_norm_check::Z_BOUND;

// ─── Geometry ──────────────────────────────────────────────────────

/// Region A row count (polynomial-arithmetic core).
pub const N_EQ_ROWS:   usize = K * N;        // 1024
/// Region B row count (norm-check on z).
pub const N_NORM_ROWS: usize = L * N;        // 1024
/// Total trace rows.
pub const VERIFY_AIR_V15_ROWS: usize = N_EQ_ROWS + N_NORM_ROWS;  // 2048

// ─── Column layout ─────────────────────────────────────────────────
//
// Concatenation: [ sel_eq | v1_columns | norm_check_columns ].

pub const COL_SEL_EQ:    usize = 0;
pub const EQ_BASE:       usize = 1;
pub const EQ_WIDTH:      usize = ml_dsa_verify_air::WIDTH;
pub const NORM_BASE:     usize = EQ_BASE + EQ_WIDTH;
pub const NORM_WIDTH:    usize = ml_dsa_norm_check_air::WIDTH;
pub const WIDTH:         usize = 1 + EQ_WIDTH + NORM_WIDTH;

// ─── Constraint count ──────────────────────────────────────────────

pub const NUM_CONSTRAINTS: usize =
    1                                                      // sel_eq boolean
  + ml_dsa_verify_air::NUM_CONSTRAINTS                    // 6
  + ml_dsa_norm_check_air::NUM_CONSTRAINTS;               // 38

// ─── fill_trace ────────────────────────────────────────────────────

/// Populate the v1.5 trace from the AIR's full input set: the v1
/// public inputs (Â, c, t1·2^d, w_approx_ntt) + witness z_ntt, plus
/// the cleartext z (for the norm-check region).
pub fn fill_trace(
    trace: &mut [Vec<F>],
    n_trace: usize,
    a_ntt:        &[[[u32; N]; L]; K],
    z_ntt:        &[[u32; N]; L],
    c_ntt:        &[u32; N],
    t1d_ntt:      &[[u32; N]; K],
    w_approx_ntt: &[[u32; N]; K],
    z_cleartext:  &[[u32; N]; L],
) {
    assert_eq!(trace.len(), WIDTH);
    assert!(n_trace >= VERIFY_AIR_V15_ROWS);

    // ── Region A: polynomial-arithmetic core (rows 0..K*N) ────────
    //
    // Set sel_eq = 1; populate v1 columns via a "virtual" trace
    // slice that reuses ml_dsa_verify_air::fill_trace's logic.
    {
        let mut eq_subtrace: Vec<Vec<F>> = (0..EQ_WIDTH)
            .map(|_| vec![F::zero(); n_trace]).collect();
        ml_dsa_verify_air::fill_trace(
            &mut eq_subtrace, n_trace,
            a_ntt, z_ntt, c_ntt, t1d_ntt, w_approx_ntt,
        );
        for row in 0..N_EQ_ROWS {
            trace[COL_SEL_EQ][row] = F::one();
            for c in 0..EQ_WIDTH {
                trace[EQ_BASE + c][row] = eq_subtrace[c][row];
            }
        }
    }

    // ── Region B: norm-check rows (rows K*N..K*N+L*N) ────────────
    //
    // sel_eq = 0; populate norm-check columns via flattened z.
    {
        let mut z_flat: Vec<u32> = Vec::with_capacity(L * N);
        for l in 0..L {
            for i in 0..N {
                z_flat.push(z_cleartext[l][i]);
            }
        }
        let mut norm_subtrace: Vec<Vec<F>> = (0..NORM_WIDTH)
            .map(|_| vec![F::zero(); n_trace]).collect();
        ml_dsa_norm_check_air::fill_trace(
            &mut norm_subtrace, n_trace, &z_flat, Z_BOUND,
        );
        for r in 0..N_NORM_ROWS {
            let row = N_EQ_ROWS + r;
            trace[COL_SEL_EQ][row] = F::zero();
            for c in 0..NORM_WIDTH {
                trace[NORM_BASE + c][row] = norm_subtrace[c][r];
            }
        }
    }
}

// ─── Constraint evaluation ─────────────────────────────────────────

/// Same-cardinality constraint vector across all rows.  Each
/// constraint is multiplied by its region's selector so that
/// out-of-region rows produce zero contributions automatically.
pub fn eval_per_row(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();
    let sel_eq    = cur[COL_SEL_EQ];
    let sel_norm  = one - sel_eq;

    // 1. Selector boolean.
    out.push(sel_eq * (sel_eq - one));

    // 2. Polynomial-arithmetic constraints — gated by sel_eq.
    let eq_view: Vec<F> = (0..EQ_WIDTH).map(|c| cur[EQ_BASE + c]).collect();
    let nxt_view: Vec<F> = (0..EQ_WIDTH).map(|c| nxt[EQ_BASE + c]).collect();
    for v in ml_dsa_verify_air::eval_per_row(&eq_view, &nxt_view, row) {
        out.push(sel_eq * v);
    }

    // 3. Norm-check constraints — gated by sel_norm.
    let norm_view: Vec<F> = (0..NORM_WIDTH).map(|c| cur[NORM_BASE + c]).collect();
    let norm_nxt: Vec<F> = (0..NORM_WIDTH).map(|c| nxt[NORM_BASE + c]).collect();
    for v in ml_dsa_norm_check_air::eval_per_row(&norm_view, &norm_nxt, row, Z_BOUND) {
        out.push(sel_norm * v);
    }

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

    /// Build (PI, witness, cleartext z) from synthetic data such
    /// that both regions are honest, then assert every per-row
    /// constraint is zero across the entire trace.
    #[test]
    fn honest_v15_trace_satisfies_all_constraints() {
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
        for i in 0..N { c_ntt[i] = (1 + i as u32 * 23) % Q; }
        for k in 0..K {
            for i in 0..N { t1d_ntt[k][i] = (5 + i as u32 * 11 + k as u32 * 13) % Q; }
        }
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
        // Cleartext z values that satisfy the norm bound.  We use
        // small centred residues lifted into [0, q).
        let mut z_cleartext = [[0u32; N]; L];
        for l in 0..L {
            for i in 0..N {
                let signed = (i as i32) % 100 - 50;  // |x| ≤ 50, well within Z_BOUND
                z_cleartext[l][i] = if signed >= 0 { signed as u32 } else { (signed + Q as i32) as u32 };
            }
        }

        let n_trace = VERIFY_AIR_V15_ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(
            &mut trace, n_trace,
            &a_ntt, &z_ntt, &c_ntt, &t1d_ntt, &w_approx_ntt, &z_cleartext,
        );

        for row in 0..VERIFY_AIR_V15_ROWS {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v1.5 constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }

    /// A z-cleartext value that violates the norm bound must
    /// surface as a non-zero constraint in the norm-check region.
    /// Demonstrates the v1.5 cryptographic gain over v1.
    #[test]
    fn malicious_z_norm_violation_breaks_constraint() {
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
                w_approx_ntt[k][i] = sub_q(acc, mul_q(c_ntt[i], t1d_ntt[k][i]));
            }
        }

        // z cleartext: one coefficient violates ‖·‖∞ < Z_BOUND.
        let mut z_cleartext = [[0u32; N]; L];
        // Place a value slightly above the bound at position (0, 0).
        z_cleartext[0][0] = Z_BOUND;  // |centred| = Z_BOUND, exceeds bound (strict <).

        let n_trace = VERIFY_AIR_V15_ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(
            &mut trace, n_trace,
            &a_ntt, &z_ntt, &c_ntt, &t1d_ntt, &w_approx_ntt, &z_cleartext,
        );

        // The first norm-check row covers z[0][0]; check it fails.
        let row = N_EQ_ROWS;
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
        let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
        let cvals = eval_per_row(&cur, &nxt, row);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero,
            "v1.5: an out-of-bound z coefficient must break a norm-check constraint");
    }
}
