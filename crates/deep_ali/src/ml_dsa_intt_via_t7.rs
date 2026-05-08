//! T-INTT-orchestration: prove `INTT(w_approx_ntt) = w_approx` by
//! running the chained-NTT AIR (`ml_dsa_ntt_chained_air`, our T7
//! brick) in the FORWARD direction with `w_approx` as witness.
//!
//! ## Why this works
//!
//! T7 proves: "given polynomial `P` at row 0 (input) and polynomial
//! `Q` at row 1024 (output), `Q = NTT(P)`."
//!
//! By the existence-and-uniqueness of NTT⁻¹: `Q = NTT(P) ⇔ P =
//! NTT⁻¹(Q)`.  So if the prover supplies `P = w_approx` as a
//! witness AND we publicly commit `Q = w_approx_ntt`, T7 proves
//! both directions simultaneously.  No separate INTT AIR needed —
//! we get inverse-NTT soundness "for free" from the forward NTT.
//!
//! ## Composition pattern in v2
//!
//! For each `k ∈ 0..K`:
//! 1. Place `w_approx[k]` as 256 input bit cells at row 0 of a
//!    T7 instance (witness).
//! 2. Place `w_approx_ntt[k]` as 256 output bit cells at row 1024
//!    of the same instance (PI-hash bound; the verifier independently
//!    knows `w_approx_ntt[k]` from v1.7's polynomial-arithmetic
//!    region).
//! 3. T7's per-row butterfly constraints enforce that row 1024 =
//!    NTT(row 0).
//! 4. Cross-region binding (T-MEM) links `w_approx[k]` cells in
//!    each T7 instance to the per-coefficient Decompose inputs
//!    (`w_approx[k][i]` for `i ∈ 0..N`).
//!
//! ## What this module provides
//!
//! - `prove_intt_via_t7_native(w_approx_ntt) → w_approx`: native
//!   computation of `w_approx = INTT(w_approx_ntt)`, using
//!   `ml_dsa_ntt::ntt_inv`.
//! - `verify_intt_via_t7_native(w_approx, w_approx_ntt) → bool`:
//!   native equivalent of "prove + verify in one call" — checks
//!   `NTT(w_approx) == w_approx_ntt`.  This is what the in-circuit
//!   T7 instance proves.
//! - `fill_t7_for_intt(trace, n_trace, w_approx)`: drive T7's
//!   `fill_trace` with `w_approx` as input.  After running, row
//!   1024's state cells hold `NTT(w_approx) = w_approx_ntt`.
//! - `extract_w_approx_ntt_from_t7_trace(trace) → [u32; N]`:
//!   helper to read `w_approx_ntt` back from T7's row-1024 state.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::N;
use crate::ml_dsa_ntt;
use crate::ml_dsa_ntt_chained_air::{
    self as t7,
    col_state, BUTTERFLIES_PER_NTT, WIDTH as T7_WIDTH,
};

// ─── Native helpers ───────────────────────────────────────────────

/// Native INTT: given the NTT-domain polynomial `w_approx_ntt`,
/// compute the coefficient-domain polynomial `w_approx`.  The
/// in-circuit T7 instance proves that `NTT(w_approx) =
/// w_approx_ntt`, which is equivalent.
pub fn prove_intt_via_t7_native(w_approx_ntt: &[u32; N]) -> [u32; N] {
    let mut w_approx = *w_approx_ntt;
    ml_dsa_ntt::ntt_inv(&mut w_approx);
    w_approx
}

/// Native equivalent of T7's in-circuit verification: run the
/// forward NTT on `w_approx` and check the result equals
/// `w_approx_ntt`.  Returns `true` iff the prover's pair is valid.
pub fn verify_intt_via_t7_native(w_approx: &[u32; N], w_approx_ntt: &[u32; N]) -> bool {
    let mut got = *w_approx;
    ml_dsa_ntt::ntt(&mut got);
    &got[..] == &w_approx_ntt[..]
}

// ─── Trace driver ─────────────────────────────────────────────────

/// Drive T7's `fill_trace` with `w_approx` as input.  After
/// returning, row `BUTTERFLIES_PER_NTT` of the trace holds
/// `NTT(w_approx)`, which the composing AIR binds to the public
/// `w_approx_ntt` via a boundary constraint.
pub fn fill_t7_for_intt(trace: &mut [Vec<F>], n_trace: usize, w_approx: &[u32; N]) {
    assert_eq!(trace.len(), T7_WIDTH);
    t7::fill_trace(trace, n_trace, w_approx);
}

/// Extract `w_approx_ntt` from the T7 trace's row-`BUTTERFLIES_PER_NTT`
/// state cells.  This is the value that the composing AIR's
/// boundary constraint will pin to the PI-hash-bound public value.
pub fn extract_w_approx_ntt_from_t7_trace(trace: &[Vec<F>]) -> [u32; N] {
    let row = BUTTERFLIES_PER_NTT;
    let mut out = [0u32; N];
    for i in 0..N {
        let v = trace[col_state(i)][row];
        // Trace cells hold u32 values lifted into Goldilocks.  For
        // honest traces, the cell value fits in u32; we extract via
        // the canonical-from-bigint route.
        let big = ark_ff::PrimeField::into_bigint(v);
        out[i] = big.0[0] as u32;
    }
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::Q;

    fn fresh_t7_trace(n: usize) -> Vec<Vec<F>> {
        (0..T7_WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Native round-trip: `INTT(NTT(P)) == P` and `NTT(INTT(Q)) == Q`.
    #[test]
    fn native_intt_inverts_ntt() {
        let mut p = [0u32; N];
        for i in 0..N { p[i] = (i as u32 * 12345 + 7) % Q; }

        // p → NTT → q → INTT → should recover p.
        let mut q = p;
        ml_dsa_ntt::ntt(&mut q);
        let p_recovered = prove_intt_via_t7_native(&q);
        assert_eq!(p, p_recovered);

        // q → INTT → p → NTT → should recover q.
        let p_from_q = prove_intt_via_t7_native(&q);
        let mut q_recovered = p_from_q;
        ml_dsa_ntt::ntt(&mut q_recovered);
        assert_eq!(q, q_recovered);
    }

    /// Native verify: an honest (w_approx, w_approx_ntt) pair where
    /// w_approx_ntt = NTT(w_approx) is accepted.
    #[test]
    fn native_verify_accepts_honest_pair() {
        let mut w_approx = [0u32; N];
        for i in 0..N { w_approx[i] = (3 * i as u32 + 11) % Q; }
        let mut w_approx_ntt = w_approx;
        ml_dsa_ntt::ntt(&mut w_approx_ntt);

        assert!(verify_intt_via_t7_native(&w_approx, &w_approx_ntt));
    }

    /// Native verify: a tampered pair (w_approx_ntt with one
    /// coefficient altered) is rejected.
    #[test]
    fn native_verify_rejects_tampered_pair() {
        let mut w_approx = [0u32; N];
        for i in 0..N { w_approx[i] = (5 * i as u32 + 3) % Q; }
        let mut w_approx_ntt = w_approx;
        ml_dsa_ntt::ntt(&mut w_approx_ntt);

        // Tamper.
        w_approx_ntt[42] = (w_approx_ntt[42] + 1) % Q;
        assert!(!verify_intt_via_t7_native(&w_approx, &w_approx_ntt));
    }

    /// **Headline trace round-trip**: drive T7 with `w_approx` →
    /// trace's row-1024 state must equal native `NTT(w_approx)` =
    /// `w_approx_ntt`.  This proves the composing AIR's boundary
    /// constraint at row 1024 will hold for an honest prover.
    #[test]
    fn t7_trace_row_1024_equals_w_approx_ntt() {
        let mut w_approx = [0u32; N];
        for i in 0..N { w_approx[i] = (7 * i as u32 + 23) % Q; }

        let n_trace = (BUTTERFLIES_PER_NTT + 16).next_power_of_two();
        let mut trace = fresh_t7_trace(n_trace);
        fill_t7_for_intt(&mut trace, n_trace, &w_approx);

        let mut expected = w_approx;
        ml_dsa_ntt::ntt(&mut expected);

        let got = extract_w_approx_ntt_from_t7_trace(&trace);
        assert_eq!(&got[..], &expected[..],
            "T7 trace's row {BUTTERFLIES_PER_NTT} state must equal NTT(w_approx)");
    }

    /// Composition with v2: simulate the v2 pattern where
    /// `w_approx_ntt[k]` is supplied as a public input (e.g. from
    /// v1.7's polynomial-arithmetic region) and the prover supplies
    /// `w_approx[k]` as witness.  Exhaustively check K=4 instances.
    #[test]
    fn v2_composition_pattern_for_K_eq_4() {
        use crate::ml_dsa::params::K;

        for k in 0..K {
            // Synthesise w_approx_ntt[k] as something realistic.
            let mut w_approx_ntt = [0u32; N];
            for i in 0..N {
                w_approx_ntt[i] = ((k as u32 * 1001) + (i as u32 * 17) + 5) % Q;
            }
            // Native compute the witness w_approx[k] = INTT(w_approx_ntt[k]).
            let w_approx = prove_intt_via_t7_native(&w_approx_ntt);

            // Drive T7 with the witness, extract row 1024.
            let n_trace = (BUTTERFLIES_PER_NTT + 16).next_power_of_two();
            let mut trace = fresh_t7_trace(n_trace);
            fill_t7_for_intt(&mut trace, n_trace, &w_approx);

            let row_1024 = extract_w_approx_ntt_from_t7_trace(&trace);

            // The boundary constraint that v2 will add at row 1024:
            // row_1024 cells must equal w_approx_ntt[k].
            assert_eq!(&row_1024[..], &w_approx_ntt[..],
                "v2 boundary constraint would hold for k={k}");
        }
    }

    /// Sanity: T7's existing `honest_trace_satisfies_all_constraints`
    /// applies to traces driven by `fill_t7_for_intt` — i.e., the
    /// AIR remains sound when we frame it as "INTT proof".  We
    /// re-run a minimal version here to make the soundness chain
    /// explicit.
    #[test]
    fn t7_constraints_pass_under_intt_framing() {
        let mut w_approx = [0u32; N];
        for i in 0..N { w_approx[i] = (i as u32 * 97) % Q; }

        let n_trace = (BUTTERFLIES_PER_NTT + 16).next_power_of_two();
        let mut trace = fresh_t7_trace(n_trace);
        fill_t7_for_intt(&mut trace, n_trace, &w_approx);

        for row in 0..BUTTERFLIES_PER_NTT {
            let cur: Vec<F> = (0..T7_WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..T7_WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = t7::eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-INTT-via-T7: T7 constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }
}
