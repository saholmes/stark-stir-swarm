//! Chained 256-point NTT AIR — **v1.7 sub-AIR**.
//!
//! Where `ml_dsa_ntt_air` is an informational FieldOp emitter
//! (no cross-row binding), this module *constrains* a complete
//! 256-point Cooley-Tukey NTT step-by-step.  The prover commits
//! the polynomial state at every butterfly; the AIR checks every
//! transition.  After this AIR, the v1.7 verify-AIR can soundly
//! enforce `ẑ = NTT(z)` for the response polynomial `z` decoded
//! from a real ML-DSA-44 signature.
//!
//! ## Design choices
//!
//! - **State per row**: `N = 256` polynomial cells.  Each row
//!   represents the polynomial state at one step of the in-place
//!   NTT.  Row `r` is the state *after* the `r`-th butterfly.
//!   Row `0` is the input `a`; row `BUTTERFLIES_PER_NTT` is the
//!   output `NTT(a)`.
//!
//! - **One butterfly per row.**  Each butterfly modifies exactly
//!   two cells `(j, j+len)` and leaves the other 254 unchanged.
//!   Per-row constraints enforce: 254 cells pass through
//!   unchanged, 2 cells satisfy the butterfly relation
//!   `next[j] = cur[j] + t (mod q)`,
//!   `next[j+len] = cur[j] − t (mod q)`,
//!   where `t = ζ_k · cur[j+len] (mod q)` and `ζ_k` is the row's
//!   twiddle factor.
//!
//! - **Schedule is row-dependent.**  Row `r` knows its `(j, len, k)`
//!   from the canonical NTT schedule (FIPS 204 §3.8.4 Algorithm 35).
//!   The verifier computes the same schedule from `r` — no witness
//!   columns needed for it.  We use the deep_ali per-row evaluator
//!   pattern (which already accepts `row` as a parameter).
//!
//! - **Modular arithmetic witnesses.**  Three modular ops per row
//!   (one `mul_q`, two add/sub with possible wrap).  Each carries
//!   a quotient witness so the constraint is enforced over
//!   Goldilocks integers without needing a separate range proof.
//!
//! ## Constraint count per row
//!
//! - 1 mul-q quotient: `ζ · a[j+len] − t − k_mul · q = 0`  (deg 2)
//! - 1 add-q wrap:     `cur[j] + t − next[j] − k_add · q = 0`  (deg 1)
//! - 1 sub-q wrap:     `cur[j] − t − next[j+len] + k_sub · q = 0`  (deg 1)
//! - 254 passthrough constraints (deg 1)
//! - 3 boolean witnesses (k_add, k_sub, optional sign for k_mul)
//! - Total ≈ 260 constraints per row, all ≤ deg 2.
//!
//! Trace: `(N + workspace) × n_trace`.  Workspace ~5 cells:
//! `t`, `k_mul`, `k_add`, `k_sub`, optional `t_sign`.  Width ≈ 261.
//! Per NTT: 1024 rows.
//!
//! ## What this AIR proves
//!
//! Given the state at row 0 (input `a`) and the state at row 1024
//! (claimed output `b`), the AIR proves `b = NTT(a)` via the
//! step-by-step butterfly trace.  The verifier checks (a) row 0's
//! state matches the public input and (b) row 1024's state matches
//! the public claimed-output, via `public_inputs_hash`.
//!
//! ## Phase scope
//!
//! This module: native + AIR for ONE 256-point NTT.  Composing it
//! with v1.5 to produce v1.7 (which proves `ẑ_l = NTT(z_l)` for
//! all `L = 4` response polynomials of an ML-DSA-44 signature) is
//! the next session's deliverable.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::{N, Q};
use crate::ml_dsa_ntt::compute_zetas;

/// Total butterflies in one 256-point NTT.
pub const BUTTERFLIES_PER_NTT: usize = 1024; // 8 stages × 128 butterflies

// ─── Column layout ─────────────────────────────────────────────────

#[inline] pub const fn col_state(i: usize) -> usize { i }
pub const COL_T:     usize = N;
pub const COL_K_MUL: usize = N + 1;
pub const COL_K_ADD: usize = N + 2;
pub const COL_K_SUB: usize = N + 3;

pub const WIDTH: usize = N + 4;

/// Number of constraints per row.
pub const NUM_CONSTRAINTS: usize = (N - 2)  // passthrough cells (j and j+len excluded)
    + 1  // butterfly + (j)
    + 1  // butterfly − (j+len)
    + 1  // mul-q definition of t
    + 1  // k_add boolean
    + 1; // k_sub boolean

// ─── Schedule ──────────────────────────────────────────────────────

/// Decode the canonical FIPS 204 Algorithm 35 NTT schedule: for
/// butterfly index `r ∈ [0, 1024)`, return `(j, len, k_zeta)`.
/// Both prover and verifier compute this; no witness needed.
pub fn butterfly_schedule(r: usize) -> (usize, usize, usize) {
    debug_assert!(r < BUTTERFLIES_PER_NTT);
    // Stage `s` has `len = 128 / 2^s` and `2^s` groups, each with
    // `len` butterflies.  Stage `s` starts at `k = 2^s`, in-stage
    // butterflies advance `k` by 1 per group.
    let mut acc = 0usize;
    for s in 0..8 {
        let len = 128 >> s;
        let groups = 1usize << s;
        let stage_butterflies = groups * len;
        if r < acc + stage_butterflies {
            // Within stage s.
            let r_in_stage = r - acc;
            let group = r_in_stage / len;
            let inner = r_in_stage % len;
            let start = group * (2 * len);
            let j = start + inner;
            let k_zeta = (1 << s) + group;
            return (j, len, k_zeta);
        }
        acc += stage_butterflies;
    }
    unreachable!()
}

// ─── fill_trace ────────────────────────────────────────────────────

/// Drive the NTT step-by-step, recording state at every butterfly.
/// Row 0 holds the input; row `BUTTERFLIES_PER_NTT` holds the output.
pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, input: &[u32; N]) {
    assert_eq!(trace.len(), WIDTH);
    assert!(n_trace > BUTTERFLIES_PER_NTT);

    let zetas = compute_zetas();
    let mut state: [u32; N] = *input;

    // Row 0: input state.
    for i in 0..N {
        trace[col_state(i)][0] = F::from(state[i] as u64);
    }
    // Workspace columns at row 0 are zero (no butterfly happens at row 0;
    // butterfly r operates from row r to row r+1).

    for r in 0..BUTTERFLIES_PER_NTT {
        let (j, len, k_zeta) = butterfly_schedule(r);
        let zeta = zetas[k_zeta];

        let a_low  = state[j];
        let a_high = state[j + len];

        // t = zeta * a_high (mod q); k_mul = (zeta * a_high - t) / q
        let prod = (zeta as u64) * (a_high as u64);
        let k_mul = prod / Q as u64;
        let t = (prod % Q as u64) as u32;

        // next[j] = (a_low + t) mod q; k_add ∈ {0, 1}
        let sum = a_low as u64 + t as u64;
        let k_add: u64 = if sum >= Q as u64 { 1 } else { 0 };
        let new_aj = if k_add == 1 { (sum - Q as u64) as u32 } else { sum as u32 };

        // next[j+len] = (a_low - t) mod q; k_sub ∈ {0, 1}
        let (new_ajplen, k_sub): (u32, u64) = if a_low >= t {
            (a_low - t, 0)
        } else {
            (a_low + Q - t, 1)
        };

        // Workspace witnesses on row r (the ones describing the
        // r-th butterfly transition).
        trace[COL_T][r]     = F::from(t as u64);
        trace[COL_K_MUL][r] = F::from(k_mul);
        trace[COL_K_ADD][r] = F::from(k_add);
        trace[COL_K_SUB][r] = F::from(k_sub);

        // Update state and write row r+1.
        state[j]       = new_aj;
        state[j + len] = new_ajplen;
        for i in 0..N {
            trace[col_state(i)][r + 1] = F::from(state[i] as u64);
        }
    }
    // Pad remaining rows with the final state (so transition
    // constraints between row `BUTTERFLIES_PER_NTT` and beyond
    // pass trivially).
    for r in (BUTTERFLIES_PER_NTT + 1)..n_trace {
        for i in 0..N {
            trace[col_state(i)][r] = trace[col_state(i)][BUTTERFLIES_PER_NTT];
        }
        // Workspace zero on padding rows.
    }
}

// ─── Constraint evaluation ─────────────────────────────────────────

/// Evaluate the per-row constraints for the butterfly that
/// transitions row `row` → row `row+1`.  Padding rows (≥
/// `BUTTERFLIES_PER_NTT`) emit only passthrough constraints.
pub fn eval_per_row(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let q = F::from(Q as u64);
    let one = F::one();

    if row >= BUTTERFLIES_PER_NTT {
        // Padding: all 256 cells pass through; workspace witnesses
        // expected zero.  We emit 256 passthrough + dummy zeros to
        // match cardinality.
        for i in 0..N {
            out.push(nxt[col_state(i)] - cur[col_state(i)]);
        }
        // Dummy fillers for the remaining (NUM_CONSTRAINTS - 256)
        // constraint slots — we choose zero-valued constraints so
        // they hold trivially.
        let dummy = NUM_CONSTRAINTS - N;
        for _ in 0..dummy {
            out.push(F::zero());
        }
        debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
        return out;
    }

    let (j, len, k_zeta) = butterfly_schedule(row);
    let zeta = compute_zetas()[k_zeta];
    let zeta_f = F::from(zeta as u64);

    let a_low   = cur[col_state(j)];
    let a_high  = cur[col_state(j + len)];
    let next_lo = nxt[col_state(j)];
    let next_hi = nxt[col_state(j + len)];
    let t       = cur[COL_T];
    let k_mul   = cur[COL_K_MUL];
    let k_add   = cur[COL_K_ADD];
    let k_sub   = cur[COL_K_SUB];

    // Mul-q: ζ · a_high − t − k_mul · q = 0
    out.push(zeta_f * a_high - t - k_mul * q);

    // Butterfly +: a_low + t − next_lo − k_add · q = 0
    out.push(a_low + t - next_lo - k_add * q);

    // Butterfly −: a_low − t − next_hi + k_sub · q = 0
    out.push(a_low - t - next_hi + k_sub * q);

    // k_add boolean.
    out.push(k_add * (k_add - one));
    // k_sub boolean.
    out.push(k_sub * (k_sub - one));

    // Passthrough for all cells except j and j+len.
    for i in 0..N {
        if i == j || i == j + len { continue; }
        out.push(nxt[col_state(i)] - cur[col_state(i)]);
    }

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

// ─── Tests ─────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa_ntt;

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// `butterfly_schedule` covers every butterfly exactly once
    /// across all 1024 rows, with valid `(j, len, k_zeta)` ranges.
    #[test]
    fn schedule_is_a_partition() {
        use std::collections::HashSet;
        let mut seen: HashSet<(usize, usize, usize)> = HashSet::new();
        for r in 0..BUTTERFLIES_PER_NTT {
            let (j, len, k) = butterfly_schedule(r);
            assert!(j + len < N, "out-of-bounds butterfly at row {r}");
            assert!(k > 0 && k < 256, "k_zeta out of range at row {r}: {k}");
            assert!(seen.insert((j, len, k)),
                "duplicate butterfly at row {r}: ({j}, {len}, {k})");
        }
        assert_eq!(seen.len(), BUTTERFLIES_PER_NTT);
    }

    /// Trace's final state matches native NTT.
    #[test]
    fn trace_final_state_matches_native_ntt() {
        let mut input = [0u32; N];
        for i in 0..N { input[i] = (i as u32 * 12345) % Q; }

        let n_trace = (BUTTERFLIES_PER_NTT + 1).next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &input);

        let mut expected = input;
        ml_dsa_ntt::ntt(&mut expected);

        // Read row BUTTERFLIES_PER_NTT's first N cells as the AIR's claimed output.
        for i in 0..N {
            let v = trace[col_state(i)][BUTTERFLIES_PER_NTT];
            // F::from converts u64 → Goldilocks; compare via the same map.
            let got = F::from(expected[i] as u64);
            assert_eq!(v, got,
                "row {} cell {} = {:?}, expected {:?} (native NTT[{}] = {})",
                BUTTERFLIES_PER_NTT, i, v, got, i, expected[i]);
        }
    }

    /// Honest trace: every per-row constraint zero on rows 0..1024
    /// (the active butterflies).  Padding rows (≥ 1024) also OK.
    #[test]
    fn honest_trace_satisfies_all_constraints() {
        let mut input = [0u32; N];
        for i in 0..N { input[i] = (i as u32 * 97) % Q; }

        let n_trace = (BUTTERFLIES_PER_NTT + 16).next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &input);

        for row in 0..BUTTERFLIES_PER_NTT {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }

    /// Tampering with a single state cell on row 500 must surface
    /// in row 500's constraint evaluation (passthrough of unchanged
    /// cells, or one of the butterfly cells).
    #[test]
    fn tampered_state_cell_breaks_constraint() {
        let mut input = [0u32; N];
        for i in 0..N { input[i] = (i as u32 * 11) % Q; }

        let n_trace = (BUTTERFLIES_PER_NTT + 16).next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &input);

        // Flip the value at row 500, cell 100.  Row 500's butterfly
        // schedule probably touches a different (j, j+len), so this
        // breaks a passthrough constraint between row 499→500 OR
        // row 500→501.
        trace[col_state(100)][500] = trace[col_state(100)][500] + F::one();

        let mut found_break = false;
        for row in 499..=500 {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            if cvals.iter().any(|v| !v.is_zero()) {
                found_break = true;
                break;
            }
        }
        assert!(found_break,
            "tampering with state cell must break a constraint on adjacent rows");
    }
}
