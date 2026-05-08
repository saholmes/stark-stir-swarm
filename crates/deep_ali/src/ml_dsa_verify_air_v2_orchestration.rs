//! T9 orchestration: drive the v2 sub-trace fills end-to-end.
//!
//! Companion to `ml_dsa_verify_air_v2_layout` (which froze the
//! row/col dimensions) and the per-sub-AIR fill_traces.  This
//! module ties them together: given a `V2Witness`, produce the
//! 5 sub-traces ready for FRI prove.
//!
//! ## Scope (this session: 3 of 5 sub-AIRs)
//!
//! - ✅ **V17**: v1.7's existing `verify_air_v17::fill_trace`.
//! - ✅ **INTT**: 4× chained NTT (T7) for `w_approx[k] →
//!   w_approx_ntt[k]`.  Witness `w_approx` is supplied by the
//!   prover (it's the inverse-NTT pre-image of the public
//!   `w_approx_ntt`, which v1.7's poly-arithmetic region commits
//!   to).
//! - ✅ **TRANSCRIPT**: T1.5 multi-block absorb of `µ ‖ w1bytes`.
//!   `w1bytes` comes from running `w1Encode` natively here; the
//!   future T_MEM region will bind these bytes to the COEFF
//!   chain's W1Encode output cells.
//!
//! ## Deferred (next push)
//!
//! - ⏭️ **COEFF**: per-coefficient (Decompose + UseHint + W1Encode)
//!   chain.  Currently the witness `w_approx` is consumed natively
//!   to produce `w1bytes` for TRANSCRIPT; the COEFF AIR will lift
//!   that into in-circuit constraints.
//! - ⏭️ **T_MEM**: cross-region permutation argument linking
//!   COEFF outputs to TRANSCRIPT inputs and INTT row-1024 cells.
//!
//! ## End-to-end soundness story (after all 5 sub-AIRs)
//!
//! 1. V17 proves `w_approx_ntt = Σ a_ntt·z_ntt − c_ntt·t1d_ntt`,
//!    plus `‖z‖∞ < γ_1 − β`, plus `ẑ_l = NTT(z_l)`.
//! 2. INTT proves `w_approx_ntt[k] = NTT(w_approx[k])`.
//! 3. COEFF proves each coefficient's `r1, r0, adjusted_r1, w1bytes`.
//! 4. TRANSCRIPT proves `c̃' = SHAKE-256(µ ‖ w1bytes)[0..32]`.
//! 5. T_MEM binds: w_approx (INTT) ↔ Decompose input (COEFF),
//!    UseHint output ↔ W1Encode input, W1Encode bytes ↔ TRANSCRIPT
//!    absorb input.
//! 6. Final boundary `c̃' == c̃` (PI-hash bound to sigDecode's c̃).
//!
//! Together: any deviation from the canonical FIPS 204 §3 Algorithm
//! 3 verify path makes one of these 5 sub-proofs (or the boundary)
//! reject.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600;
use crate::ml_dsa::params::{K, L, N};
use crate::ml_dsa_ntt;
use crate::ml_dsa_ntt_chained_air as t7;
use crate::ml_dsa_verify_air_v17 as v17;
use crate::ml_dsa_verify_air_v2_layout::{intt, transcript, v17 as v17_dim};
use crate::ml_dsa_transcript;

// ─── V2 witness ────────────────────────────────────────────────────

/// Inputs to v2 prove.  Public fields are bound via PI-hash;
/// witness fields are committed in the trace.
pub struct V2Witness {
    // ── Public (pi_hash bound) ──
    pub a_ntt:        Box<[[[u32; N]; L]; K]>,
    pub c_ntt:        Box<[u32; N]>,
    pub t1d_ntt:      Box<[[u32; N]; K]>,
    pub w_approx_ntt: Box<[[u32; N]; K]>,
    pub mu_bytes:     [u8; 64],
    pub w1bytes:      Vec<u8>,            // 768 B for ML-DSA-44
    // ── Witnesses (trace-committed) ──
    pub z_ntt:        Box<[[u32; N]; L]>,
    pub z_cleartext:  Box<[[u32; N]; L]>,
    pub w_approx:     Box<[[u32; N]; K]>,  // = INTT(w_approx_ntt)
}

// ─── V2 sub-traces bundle ─────────────────────────────────────────

pub struct V2SubTraces {
    pub v17:        Vec<Vec<F>>,         // V17 sub-trace
    pub intt:       Vec<Vec<Vec<F>>>,    // 4 INTT sub-traces (one per k)
    pub transcript: Vec<Vec<F>>,         // TRANSCRIPT sub-trace
    pub coeff_decompose: Vec<Vec<F>>,    // COEFF: Decompose sub-trace (K·N rows)
    pub coeff_use_hint:  Vec<Vec<F>>,    // COEFF: UseHint sub-trace (K·N rows)
    pub coeff_w1_encode: Vec<Vec<F>>,    // COEFF: W1Encode sub-trace (K·N rows)
    pub t_mem:           Vec<Vec<F>>,    // T_MEM permutation-argument sub-trace
}

// ─── fill_v2_traces ────────────────────────────────────────────────

/// Build all 3 architecturally-significant v2 sub-traces from the
/// witness.  Returns sub-traces sized to each sub-proof's pow2 row
/// count (per `ml_dsa_verify_air_v2_layout`).
pub fn fill_v2_traces(witness: &V2Witness) -> V2SubTraces {
    // ── V17 (v1.7 verify-AIR) ──
    let mut v17_trace: Vec<Vec<F>> = (0..v17_dim::N_COLS)
        .map(|_| vec![F::zero(); v17_dim::N_ROWS_POW2]).collect();
    v17::fill_trace(
        &mut v17_trace,
        v17_dim::N_ROWS_POW2,
        &witness.a_ntt,
        &witness.z_ntt,
        &witness.c_ntt,
        &witness.t1d_ntt,
        &witness.w_approx_ntt,
        &witness.z_cleartext,
    );

    // ── INTT (4× chained NTT for w_approx[k] → w_approx_ntt[k]) ──
    let mut intt_traces: Vec<Vec<Vec<F>>> = Vec::with_capacity(K);
    let intt_n_trace_per_instance = (t7::BUTTERFLIES_PER_NTT + 16).next_power_of_two();
    for k in 0..K {
        let mut sub: Vec<Vec<F>> = (0..intt::N_COLS)
            .map(|_| vec![F::zero(); intt_n_trace_per_instance]).collect();
        t7::fill_trace(&mut sub, intt_n_trace_per_instance, &witness.w_approx[k]);
        intt_traces.push(sub);
    }

    // ── TRANSCRIPT (T1.5 absorb of µ ‖ w1bytes) ──
    let transcript_layout = ml_dsa_transcript::build_layout(
        &witness.mu_bytes, &witness.w1bytes,
    );
    let transcript_n_trace = transcript::N_ROWS_POW2;
    let mut transcript_trace: Vec<Vec<F>> = (0..transcript::N_COLS)
        .map(|_| vec![F::zero(); transcript_n_trace]).collect();
    crate::ml_dsa_shake_absorb_multi_air::fill_trace(
        &mut transcript_trace, transcript_n_trace, &transcript_layout,
    );

    V2SubTraces { v17: v17_trace, intt: intt_traces, transcript: transcript_trace }
}

// ─── Native witness derivation ────────────────────────────────────

/// Compute `w_approx[k] = INTT(w_approx_ntt[k])` for all k.  This is
/// the witness the prover supplies for the INTT sub-AIR; correctness
/// is enforced in-circuit by T7 running NTT(w_approx) and checking
/// the result equals `w_approx_ntt`.
pub fn derive_w_approx_witness(w_approx_ntt: &[[u32; N]; K]) -> [[u32; N]; K] {
    let mut w_approx = [[0u32; N]; K];
    for k in 0..K {
        w_approx[k] = w_approx_ntt[k];
        ml_dsa_ntt::ntt_inv(&mut w_approx[k]);
    }
    w_approx
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::Q;
    use crate::ml_dsa_field::{add_q, mul_q, sub_q};
    use crate::keccak_f1600::ROUNDS;
    use crate::ml_dsa_shake_absorb_multi_air;

    /// Synthesise a fully-consistent V2 witness for testing.
    fn synthesize_witness() -> V2Witness {
        // Step 1: small centred z, lift to z_cleartext.
        let mut z_cleartext = Box::new([[0u32; N]; L]);
        for l in 0..L {
            for i in 0..N {
                let signed = ((i as i32 + l as i32 * 7) % 100) - 50;
                z_cleartext[l][i] = if signed >= 0 {
                    signed as u32
                } else {
                    (signed + Q as i32) as u32
                };
            }
        }
        // Step 2: z_ntt[l] = NTT(z_cleartext[l]).
        let mut z_ntt = Box::new([[0u32; N]; L]);
        for l in 0..L {
            let mut tmp = z_cleartext[l];
            ml_dsa_ntt::ntt(&mut tmp);
            z_ntt[l] = tmp;
        }
        // Step 3: random a_ntt, c_ntt, t1d_ntt; compute w_approx_ntt.
        let mut a_ntt = Box::new([[[0u32; N]; L]; K]);
        for k in 0..K {
            for l in 0..L {
                for i in 0..N {
                    a_ntt[k][l][i] =
                        (1000 + i as u32 * 17 + l as u32 * 31 + k as u32 * 41) % Q;
                }
            }
        }
        let mut c_ntt = Box::new([0u32; N]);
        for i in 0..N { c_ntt[i] = (1 + i as u32 * 23) % Q; }
        let mut t1d_ntt = Box::new([[0u32; N]; K]);
        for k in 0..K {
            for i in 0..N { t1d_ntt[k][i] = (5 + i as u32 * 11 + k as u32 * 13) % Q; }
        }
        let mut w_approx_ntt = Box::new([[0u32; N]; K]);
        for k in 0..K {
            for i in 0..N {
                let mut acc: u32 = 0;
                for l in 0..L {
                    acc = add_q(acc, mul_q(a_ntt[k][l][i], z_ntt[l][i]));
                }
                w_approx_ntt[k][i] = sub_q(acc, mul_q(c_ntt[i], t1d_ntt[k][i]));
            }
        }
        // Step 4: w_approx[k] = INTT(w_approx_ntt[k]).
        let mut w_approx = Box::new([[0u32; N]; K]);
        let derived = derive_w_approx_witness(&w_approx_ntt);
        for k in 0..K { w_approx[k] = derived[k]; }

        // Step 5: synthetic µ + w1bytes.  For this test we don't need
        // a "correct" w1bytes — TRANSCRIPT just absorbs whatever we
        // give it.  The future COEFF + T_MEM bind w1bytes to UseHint
        // outputs; for now any 768-byte vector validates the
        // TRANSCRIPT sub-trace's internal constraints.
        let mu_bytes = [0x37u8; 64];
        let w1bytes: Vec<u8> = (0u32..768u32).map(|i| (i as u8).wrapping_mul(13)).collect();

        V2Witness {
            a_ntt, c_ntt, t1d_ntt, w_approx_ntt,
            mu_bytes, w1bytes,
            z_ntt, z_cleartext, w_approx,
        }
    }

    /// **Headline orchestration test.**  Drive `fill_v2_traces` end
    /// to end on a synthesised consistent witness; assert each
    /// sub-trace's per-row constraints all hold for the active rows.
    #[test]
    fn fill_v2_traces_end_to_end_orchestration() {
        let w = synthesize_witness();
        let traces = fill_v2_traces(&w);

        // V17 sub-trace: every per-row constraint zero on rows 0..6147.
        let v17_n = traces.v17[0].len();
        for row in 0..v17_dim::N_ROWS_ACTIVE {
            let cur: Vec<F> = (0..v17_dim::N_COLS).map(|c| traces.v17[c][row]).collect();
            let nxt: Vec<F> = (0..v17_dim::N_COLS).map(|c| traces.v17[c][(row + 1) % v17_n]).collect();
            let cvals = v17::eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 V17: constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // INTT sub-traces: each instance's T7 constraints zero.
        for k in 0..K {
            let intt_n = traces.intt[k][0].len();
            for row in 0..t7::BUTTERFLIES_PER_NTT {
                let cur: Vec<F> = (0..intt::N_COLS).map(|c| traces.intt[k][c][row]).collect();
                let nxt: Vec<F> = (0..intt::N_COLS).map(|c| traces.intt[k][c][(row + 1) % intt_n]).collect();
                let cvals = t7::eval_per_row(&cur, &nxt, row);
                for (i, v) in cvals.iter().enumerate() {
                    assert!(v.is_zero(),
                        "v2 INTT[{k}]: constraint {i} on row {row} not zero: {v:?}");
                }
            }
        }

        // INTT row 1024 binding: t7's row-1024 state matches w_approx_ntt[k].
        for k in 0..K {
            let row_1024 = t7::BUTTERFLIES_PER_NTT;
            for i in 0..N {
                let v_cell = traces.intt[k][t7::col_state(i)][row_1024];
                let v_expected = F::from(w.w_approx_ntt[k][i] as u64);
                assert_eq!(v_cell, v_expected,
                    "v2 INTT[{k}]: row 1024 cell {i} mismatch (binding to w_approx_ntt would fail)");
            }
        }

        // TRANSCRIPT sub-trace: every T1.5 per-row constraint zero.
        let transcript_layout = ml_dsa_transcript::build_layout(&w.mu_bytes, &w.w1bytes);
        let transcript_n = traces.transcript[0].len();
        for row in 0..transcript_layout.active_rows() {
            let cur: Vec<F> = (0..transcript::N_COLS).map(|c| traces.transcript[c][row]).collect();
            let nxt: Vec<F> = (0..transcript::N_COLS).map(|c| traces.transcript[c][(row + 1) % transcript_n]).collect();
            let cvals = ml_dsa_shake_absorb_multi_air::eval_per_row(&cur, &nxt, row, &transcript_layout);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 TRANSCRIPT: constraint {i} on row {row} (block {}) not zero: {v:?}",
                    row / ROUNDS);
            }
        }

        // TRANSCRIPT output binding: c̃' extracted from trace matches
        // native compute_c_tilde_prime for the same (µ, w1bytes).
        let c_tilde_prime_from_trace =
            ml_dsa_transcript::extract_c_tilde_prime_from_trace(&traces.transcript, &transcript_layout);
        let c_tilde_prime_native =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        assert_eq!(c_tilde_prime_from_trace, c_tilde_prime_native,
            "v2 TRANSCRIPT: trace c̃' differs from native — binding to sig's c̃ would fail");
    }

    /// Sub-trace dimensions match the v2 layout module's projections.
    #[test]
    fn fill_v2_traces_dimensions_match_layout() {
        let w = synthesize_witness();
        let traces = fill_v2_traces(&w);

        assert_eq!(traces.v17.len(), v17_dim::N_COLS);
        assert_eq!(traces.v17[0].len(), v17_dim::N_ROWS_POW2);

        assert_eq!(traces.intt.len(), K);
        for k in 0..K {
            assert_eq!(traces.intt[k].len(), intt::N_COLS);
            // Each INTT instance's pow2 row count is 2048 here (matches
            // the t7 standalone test pow2; the layout module's
            // 8192-row figure is for the COMBINED 4-instance trace if
            // it were stacked vertically — we use separate sub-traces
            // per instance for cleaner FRI prove).
            assert!(traces.intt[k][0].len() >= t7::BUTTERFLIES_PER_NTT + 1);
        }

        assert_eq!(traces.transcript.len(), transcript::N_COLS);
        assert_eq!(traces.transcript[0].len(), transcript::N_ROWS_POW2);
    }
}
