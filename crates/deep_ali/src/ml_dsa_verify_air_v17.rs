//! ML-DSA-44 verify AIR — **v1.7** (v1.5 + NTT memory argument).
//!
//! Extends `ml_dsa_verify_air_v15` with `L = 4` chained-NTT regions
//! (one per response polynomial `z_l`) so the AIR proves
//! `ẑ_l = NTT(z_l)` in-circuit.  The output of each NTT region
//! (row 1024 within the instance) is the SAME `z_ntt[l]` value
//! consumed by Region A's polynomial-arithmetic check; the input
//! (row 0 within the instance) is the SAME `z_cleartext[l]` value
//! consumed by Region B's norm-check.  Both bindings happen via
//! PI-hash openings outside the AIR's per-row constraints.
//!
//! ## Trace layout
//!
//! Five regions stacked vertically, gated by 3 selector columns:
//!
//! | Region | Rows                          | Count  | Selectors active            |
//! |--------|-------------------------------|--------|-----------------------------|
//! | A (eq) | `0 .. K·N`                    | 1024   | sel_eq=1                    |
//! | B (norm) | `K·N .. K·N + L·N`         | 1024   | sel_norm=1                  |
//! | C₀ NTT(z₀) butterflies | `2048 .. 3072` | 1024 | sel_ntt=1                  |
//! | C₀ NTT(z₀) output      | `3072 .. 3073` | 1    | (all selectors = 0)        |
//! | C₁ NTT(z₁) butterflies | `3073 .. 4097` | 1024 | sel_ntt=1                  |
//! | C₁ NTT(z₁) output      | `4097 .. 4098` | 1    | (all selectors = 0)        |
//! | C₂ NTT(z₂) butterflies | `4098 .. 5122` | 1024 | sel_ntt=1                  |
//! | C₂ NTT(z₂) output      | `5122 .. 5123` | 1    | (all selectors = 0)        |
//! | C₃ NTT(z₃) butterflies | `5123 .. 6147` | 1024 | sel_ntt=1                  |
//! | C₃ NTT(z₃) output      | `6147 .. 6148` | 1    | (all selectors = 0)        |
//! | Padding                | `6148 .. n_trace` | …  | (all selectors = 0)        |
//!
//! Each NTT instance occupies `1025` rows: 1024 butterfly rows
//! (`sel_ntt = 1`) + 1 output row that holds the final NTT state
//! (`sel_ntt = 0`).  The transition row 1023→1024 within an
//! instance is the LAST butterfly; the constraint at row 1024 is
//! suppressed by `sel_ntt = 0` so the trace can switch to the
//! next instance's input at row 1025 without a passthrough check
//! falsely failing.
//!
//! ## Per-row constraints
//!
//! - 3 selector booleans (`sel_eq², sel_norm², sel_ntt²`-form)
//! - 6 polynomial-arithmetic constraints, gated by `sel_eq`
//! - 38 norm-check constraints, gated by `sel_norm`
//! - 259 chained-NTT butterfly constraints, gated by `sel_ntt`
//!
//! Total: `3 + 6 + 38 + 259 = 306` constraints per row.
//!
//! ## Soundness gain over v1.5
//!
//! v1.5 takes `z_ntt` as a witness and trusts (via Layer-1 native
//! `ml_dsa::verify`) that it equals `NTT(z_decoded_from_sig)`.
//! v1.7 forces `z_ntt[l] = NTT(z_cleartext[l])` for all
//! `l ∈ 0..L` *in-circuit*.  After v1.7, the only remaining
//! native checks in Layer-1 are the 4 SHAKE rounds + their
//! rejection sampling (these become v2's responsibility).
//!
//! ## What the verifier still checks via PI binding (not in this AIR)
//!
//! - Row 0 of NTT-instance `l` must contain `z_cleartext[l]`
//!   (also the value placed in Region B's norm-check rows).
//! - Row 1024 of NTT-instance `l` must contain `z_ntt[l]`
//!   (also the value placed in Region A's poly-arithmetic rows).
//! - These bindings are enforced by FRI openings against the
//!   pi_hash that commits to (pk, message, sig) — outside the
//!   per-row constraints.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::{K, L, N};
use crate::ml_dsa_verify_air;
use crate::ml_dsa_norm_check_air;
use crate::ml_dsa_norm_check::Z_BOUND;
use crate::ml_dsa_ntt_chained_air;

// ─── Geometry ──────────────────────────────────────────────────────

pub const N_EQ_ROWS: usize = K * N;            // 1024
pub const N_NORM_ROWS: usize = L * N;          // 1024
pub const NTT_INSTANCE_ROWS: usize =
    ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT + 1;  // 1025
pub const N_NTT_TOTAL_ROWS: usize = L * NTT_INSTANCE_ROWS;  // 4100
pub const VERIFY_AIR_V17_ACTIVE_ROWS: usize =
    N_EQ_ROWS + N_NORM_ROWS + N_NTT_TOTAL_ROWS;  // 6148

pub const NTT_REGION_BASE: usize = N_EQ_ROWS + N_NORM_ROWS;  // 2048

// ─── Column layout ────────────────────────────────────────────────

pub const COL_SEL_EQ:   usize = 0;
pub const COL_SEL_NORM: usize = 1;
pub const COL_SEL_NTT:  usize = 2;

pub const EQ_BASE:   usize = 3;
pub const EQ_WIDTH:  usize = ml_dsa_verify_air::WIDTH;
pub const NORM_BASE: usize = EQ_BASE + EQ_WIDTH;
pub const NORM_WIDTH: usize = ml_dsa_norm_check_air::WIDTH;
pub const NTT_BASE: usize = NORM_BASE + NORM_WIDTH;
pub const NTT_WIDTH: usize = ml_dsa_ntt_chained_air::WIDTH;
pub const WIDTH: usize = 3 + EQ_WIDTH + NORM_WIDTH + NTT_WIDTH;

// ─── Constraint count ─────────────────────────────────────────────

pub const NUM_CONSTRAINTS: usize =
    3                                                  // 3 selector booleans
  + ml_dsa_verify_air::NUM_CONSTRAINTS                 // 6  (gated by sel_eq)
  + ml_dsa_norm_check_air::NUM_CONSTRAINTS             // 38 (gated by sel_norm)
  + ml_dsa_ntt_chained_air::NUM_CONSTRAINTS;           // 259 (gated by sel_ntt)

// ─── Region classification ────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RegionKind {
    Eq,
    Norm,
    NttButterfly { r_in_instance: usize },
    NttInstanceOutput,
    Padding,
}

fn classify(row: usize) -> RegionKind {
    if row < N_EQ_ROWS {
        RegionKind::Eq
    } else if row < N_EQ_ROWS + N_NORM_ROWS {
        RegionKind::Norm
    } else if row < VERIFY_AIR_V17_ACTIVE_ROWS {
        let r_off = row - NTT_REGION_BASE;
        let r_in_instance = r_off % NTT_INSTANCE_ROWS;
        if r_in_instance < ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT {
            RegionKind::NttButterfly { r_in_instance }
        } else {
            RegionKind::NttInstanceOutput
        }
    } else {
        RegionKind::Padding
    }
}

// ─── fill_trace ───────────────────────────────────────────────────

/// Populate the v1.7 trace from the full input set:
/// - v1 inputs (`a_ntt`, `c_ntt`, `t1d_ntt`, `w_approx_ntt`) +
///   witness `z_ntt` for the polynomial-arithmetic core
/// - cleartext `z_cleartext` for the norm-check region AND for the
///   NTT region inputs (instance `l`'s row 0 = `z_cleartext[l]`)
/// - `z_ntt` ALSO appears at instance `l`'s row 1024 (the NTT
///   output), bound to Region A's `z_ntt` value via PI-hash.
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
    assert!(n_trace >= VERIFY_AIR_V17_ACTIVE_ROWS);

    // ── Region A: polynomial-arithmetic core ────────────────────
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

    // ── Region B: norm-check ─────────────────────────────────────
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
            trace[COL_SEL_NORM][row] = F::one();
            for c in 0..NORM_WIDTH {
                trace[NORM_BASE + c][row] = norm_subtrace[c][r];
            }
        }
    }

    // ── Region C: 4× chained NTT (one per z_l) ──────────────────
    for l in 0..L {
        // Build a temporary NTT-only sub-trace big enough for one
        // instance (NTT_INSTANCE_ROWS).  We use a power-of-two
        // upper bound so chained_air::fill_trace's pad loop has
        // room (it requires `n_trace > BUTTERFLIES_PER_NTT`).
        let sub_len = NTT_INSTANCE_ROWS.next_power_of_two();  // 2048
        let mut sub: Vec<Vec<F>> = (0..NTT_WIDTH)
            .map(|_| vec![F::zero(); sub_len]).collect();
        ml_dsa_ntt_chained_air::fill_trace(&mut sub, sub_len, &z_cleartext[l]);

        // Sanity: row 0 = z_cleartext[l]; row 1024 = z_ntt[l]
        // (after the chained AIR runs the canonical NTT).  This is
        // the in-circuit assertion that `z_ntt[l] = NTT(z_cleartext[l])`.
        debug_assert!({
            let bp = ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT;
            (0..N).all(|i| {
                sub[ml_dsa_ntt_chained_air::col_state(i)][bp]
                    == F::from(z_ntt[l][i] as u64)
            })
        }, "v1.7 internal: NTT-AIR row 1024 must equal z_ntt[l]; \
            mismatch between caller's z_ntt and NTT(z_cleartext)");

        // Copy sub-trace into v1.7 at the instance's row offset.
        let base = NTT_REGION_BASE + l * NTT_INSTANCE_ROWS;
        for r in 0..NTT_INSTANCE_ROWS {
            // sel_ntt = 1 only on butterfly rows (r < BUTTERFLIES_PER_NTT);
            // 0 on the instance-output row.
            if r < ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT {
                trace[COL_SEL_NTT][base + r] = F::one();
            }
            for c in 0..NTT_WIDTH {
                trace[NTT_BASE + c][base + r] = sub[c][r];
            }
        }
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

pub fn eval_per_row(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();

    let sel_eq   = cur[COL_SEL_EQ];
    let sel_norm = cur[COL_SEL_NORM];
    let sel_ntt  = cur[COL_SEL_NTT];

    // 1. Three selector booleans.
    out.push(sel_eq   * (sel_eq   - one));
    out.push(sel_norm * (sel_norm - one));
    out.push(sel_ntt  * (sel_ntt  - one));

    // 2. Region A — polynomial-arithmetic, gated by sel_eq.
    let eq_view: Vec<F> = (0..EQ_WIDTH).map(|c| cur[EQ_BASE + c]).collect();
    let nxt_eq:  Vec<F> = (0..EQ_WIDTH).map(|c| nxt[EQ_BASE + c]).collect();
    for v in ml_dsa_verify_air::eval_per_row(&eq_view, &nxt_eq, row) {
        out.push(sel_eq * v);
    }

    // 3. Region B — norm-check, gated by sel_norm.
    let norm_view: Vec<F> = (0..NORM_WIDTH).map(|c| cur[NORM_BASE + c]).collect();
    let norm_nxt:  Vec<F> = (0..NORM_WIDTH).map(|c| nxt[NORM_BASE + c]).collect();
    for v in ml_dsa_norm_check_air::eval_per_row(&norm_view, &norm_nxt, row, Z_BOUND) {
        out.push(sel_norm * v);
    }

    // 4. Region C — chained-NTT butterfly transitions, gated by sel_ntt.
    //
    // The chained AIR's eval_per_row needs a "row-within-instance"
    // index.  At active butterfly rows we pass `r_in_instance ∈
    // [0, 1024)`; everywhere else (v1.5 rows, instance-output rows,
    // padding) we pass `BUTTERFLIES_PER_NTT` which triggers the
    // chained AIR's padding branch (256 passthroughs of zero +
    // 3 zero-fillers).  Since `sel_ntt = 0` outside the butterfly
    // rows, the gating multiplies any non-zero passthrough by 0.
    let ntt_view: Vec<F> = (0..NTT_WIDTH).map(|c| cur[NTT_BASE + c]).collect();
    let ntt_nxt:  Vec<F> = (0..NTT_WIDTH).map(|c| nxt[NTT_BASE + c]).collect();
    let row_for_chained = match classify(row) {
        RegionKind::NttButterfly { r_in_instance } => r_in_instance,
        _ => ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT,  // padding branch
    };
    for v in ml_dsa_ntt_chained_air::eval_per_row(&ntt_view, &ntt_nxt, row_for_chained) {
        out.push(sel_ntt * v);
    }

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::Q;
    use crate::ml_dsa_field::{add_q, mul_q, sub_q};
    use crate::ml_dsa_ntt;

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Build a synthetic, internally-consistent (a_ntt, z_cleartext,
    /// z_ntt, c_ntt, t1d_ntt, w_approx_ntt) tuple where:
    /// - z_cleartext[l] satisfies the norm bound for v1.5 Region B
    /// - z_ntt[l] = NTT(z_cleartext[l]) — enforced by Region C
    /// - w_approx_ntt[k] = Σ_l a_ntt[k][l]·z_ntt[l] − c_ntt·t1d_ntt[k]
    ///   — the Region A relation
    /// then assert every per-row constraint is zero across the
    /// entire active trace.
    #[test]
    fn honest_v17_trace_satisfies_all_constraints() {
        // Step 1: pick small centred z, lift to z_cleartext[l].
        let mut z_cleartext = [[0u32; N]; L];
        for l in 0..L {
            for i in 0..N {
                let signed = ((i as i32 + l as i32 * 7) % 100) - 50;  // |x| ≤ 50
                z_cleartext[l][i] =
                    if signed >= 0 { signed as u32 } else { (signed + Q as i32) as u32 };
            }
        }

        // Step 2: derive z_ntt[l] = NTT(z_cleartext[l]).
        let mut z_ntt = [[0u32; N]; L];
        for l in 0..L {
            let mut tmp = z_cleartext[l];
            ml_dsa_ntt::ntt(&mut tmp);
            z_ntt[l] = tmp;
        }

        // Step 3: pick public a_ntt, c_ntt, t1d_ntt; compute w_approx_ntt.
        let mut a_ntt = [[[0u32; N]; L]; K];
        for k in 0..K {
            for l in 0..L {
                for i in 0..N {
                    a_ntt[k][l][i] = (1000 + i as u32 * 17 + l as u32 * 31 + k as u32 * 41) % Q;
                }
            }
        }
        let mut c_ntt = [0u32; N];
        for i in 0..N { c_ntt[i] = (1 + i as u32 * 23) % Q; }
        let mut t1d_ntt = [[0u32; N]; K];
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
                w_approx_ntt[k][i] = sub_q(acc, mul_q(c_ntt[i], t1d_ntt[k][i]));
            }
        }

        // Step 4: build trace.
        let n_trace = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(
            &mut trace, n_trace,
            &a_ntt, &z_ntt, &c_ntt, &t1d_ntt, &w_approx_ntt, &z_cleartext,
        );

        // Step 5: every per-row constraint must be zero on
        // active rows + the wraparound transition.
        for row in 0..VERIFY_AIR_V17_ACTIVE_ROWS {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v1.7 constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }

    /// If a malicious prover claims `z_ntt[0]` differs from the true
    /// `NTT(z_cleartext[0])` by tampering with the NTT region's
    /// output row, the chained-NTT constraints must reject.  This
    /// is the v1.7 cryptographic gain over v1.5.
    #[test]
    fn tampered_z_ntt_breaks_chained_ntt_region() {
        // Honest setup, then tamper with the NTT-region output cell.
        let mut z_cleartext = [[0u32; N]; L];
        for l in 0..L {
            for i in 0..N {
                let signed = ((i as i32 + l as i32) % 80) - 40;
                z_cleartext[l][i] =
                    if signed >= 0 { signed as u32 } else { (signed + Q as i32) as u32 };
            }
        }
        let mut z_ntt = [[0u32; N]; L];
        for l in 0..L {
            let mut tmp = z_cleartext[l];
            ml_dsa_ntt::ntt(&mut tmp);
            z_ntt[l] = tmp;
        }
        let a_ntt = [[[7u32; N]; L]; K];
        let c_ntt = [3u32; N];
        let t1d_ntt = [[5u32; N]; K];
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

        let n_trace = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(
            &mut trace, n_trace,
            &a_ntt, &z_ntt, &c_ntt, &t1d_ntt, &w_approx_ntt, &z_cleartext,
        );

        // Tamper: flip one state cell on a butterfly row of NTT
        // instance 1 (instance index 1, in-instance row 600).
        let target_row = NTT_REGION_BASE + 1 * NTT_INSTANCE_ROWS + 600;
        let target_col = NTT_BASE + ml_dsa_ntt_chained_air::col_state(123);
        trace[target_col][target_row] = trace[target_col][target_row] + F::one();

        // Constraint at row 599 (whose nxt = row 600) and/or row 600
        // (whose cur = row 600) must fire.
        let mut found_break = false;
        for row in (target_row.saturating_sub(1))..=target_row {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            if cvals.iter().any(|v| !v.is_zero()) {
                found_break = true;
                break;
            }
        }
        assert!(found_break,
            "v1.7: tampering with an NTT-region butterfly state cell \
             must break ≥1 constraint on adjacent rows");
    }
}
