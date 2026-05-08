//! T3b-lite: **single-element ExpandA integration harness**.
//!
//! Runs T1 absorb + T2 squeeze + T3a chunk traces *side-by-side*
//! for one matrix element `Â[i][j]`, verifies each region's
//! per-row constraints in isolation, and cross-checks the polynomial
//! output against `ml_dsa_codec::expand_a`.
//!
//! ## What this is and isn't
//!
//! **Is:** a scaffolding harness that proves the trace shapes line
//! up correctly when composed.  All three sub-AIRs' constraints
//! pass on the same input, and the bytes read from T2's post-iota
//! cells (the squeeze stream) match the bytes fed into T3a's chunk
//! input cells.
//!
//! **Is not:** a single composite AIR with **in-circuit** byte-
//! alignment constraints linking T2's post-iota cells to T3a's
//! chunk input cells.  That binding is the T3c milestone — it
//! turns the off-chain "native" check below into a per-row
//! constraint emitted by the composite eval_per_row.  T3b-lite
//! validates the layout is right; T3c makes it sound.
//!
//! ## Layout summary (concrete, ML-DSA-44, SHAKE-128 path)
//!
//! - Absorb region:  24 rows × `ROUND_WIDTH` cols = ~276 K cells
//! - Squeeze region: 4 × 24 = 96 rows × `ROUND_WIDTH` cols = ~1.1 M cells
//!   - Total squeeze blocks: 5 (1 from absorb's post-iota + 4 from
//!     successive Keccak-f calls in T2)
//!   - Total bytes available: 5 × 168 = 840 → 280 chunks (well above
//!     the 256.25 expected for accept rate ≈ 99.9 %)
//! - Chunk region: 280 rows × 51 cols (T3a count-AIR width) = ~14 K cells
//!
//! Per ExpandA element: ~1.4 M trace cells.  Per matrix (K·L = 16):
//! ~22 M cells if absorb is shared (only ρ + (i, j) header changes),
//! ~24 M if not.  The compose layer is T3c's job.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600;
use crate::ml_dsa::params::N;
use crate::ml_dsa_rej_chunk_air;
use crate::ml_dsa_rej_count_air;
use crate::ml_dsa_shake_absorb_air::{
    self, build_absorbed_state, SHAKE_128_RATE_BYTES,
};
use crate::ml_dsa_shake_squeeze_air::{
    self, SqueezeLayout,
};

/// Provisioning: number of squeeze blocks (including block 0 = the
/// post-absorb state).  5 blocks × 168 bytes = 840 bytes = 280
/// chunks, comfortably above the 256.25 expected for ML-DSA-44's
/// rejection rate of ~0.000976.
pub const N_SQUEEZE_BLOCKS_TOTAL: usize = 5;

/// Number of additional Keccak-f calls past block 0.
pub const N_F1600_CALLS_SQUEEZE: usize = N_SQUEEZE_BLOCKS_TOTAL - 1;  // 4

/// Number of chunks provisioned in the chunk region.
pub const N_CHUNKS_PROVISION: usize =
    (N_SQUEEZE_BLOCKS_TOTAL * SHAKE_128_RATE_BYTES) / 3;  // 280

/// Build the 34-byte absorb input for ExpandA element `(i, j)`.
/// FIPS 204 §3.4: SHAKE-128(ρ ‖ j ‖ i) (note byte order — j first).
pub fn build_expand_a_input(rho: &[u8; 32], i: u8, j: u8) -> [u8; 34] {
    let mut m = [0u8; 34];
    m[..32].copy_from_slice(rho);
    m[32] = j;
    m[33] = i;
    m
}

/// Result of the side-by-side trace run.
pub struct ExpandAOneTraces {
    /// T1 absorb sub-trace: 24 rows of one Keccak-f.
    pub absorb_trace: Vec<Vec<F>>,
    /// T2 squeeze sub-trace: N_F1600_CALLS_SQUEEZE × 24 rows.
    pub squeeze_trace: Vec<Vec<F>>,
    /// T3a chunk + count sub-trace: N_CHUNKS_PROVISION rows.
    pub chunk_trace: Vec<Vec<F>>,
    /// Squeeze stream extracted natively from absorb post-iota +
    /// squeeze post-iotas; used to verify the chunk inputs were
    /// taken from the right bytes.
    pub squeeze_stream: Vec<u8>,
    /// First 256 accepted u-values = `Â[i][j]` polynomial.
    pub poly: [u32; N],
    /// Index of the row at which the 256th accept happened (so the
    /// composing AIR knows where the polynomial ends).
    pub last_accept_row: usize,
}

/// End-to-end fill: run T1 + T2 + T3a traces for one ExpandA element.
pub fn fill_expand_a_one(rho: &[u8; 32], i: u8, j: u8) -> ExpandAOneTraces {
    let m = build_expand_a_input(rho, i, j);

    // ── T1: single-block absorb ──
    // Pre-permute state = padded M XOR'd into zero.
    let pre_permute = build_absorbed_state(&m, SHAKE_128_RATE_BYTES);
    let absorb_n_trace = 32usize;  // pow-of-2 ≥ 24
    let mut absorb_trace: Vec<Vec<F>> = (0..ml_dsa_shake_absorb_air::WIDTH)
        .map(|_| vec![F::zero(); absorb_n_trace]).collect();
    ml_dsa_shake_absorb_air::fill_trace(
        &mut absorb_trace, absorb_n_trace, &m, SHAKE_128_RATE_BYTES,
    );
    // Post-absorb state — the FULL 25-lane state including
    // capacity lanes (21..25), needed as T2's initial_state since
    // capacity bits are mixed into the next Keccak-f.  Native
    // computation: apply Keccak-f to the pre-permute state.
    // (Equivalent to reading round-23's post-iota cells from
    // absorb_trace; we use the native call for clarity.  The
    // future T3c constraint will bind row-0 of T2 to absorb's
    // round-23 post-iota cell-by-cell.)
    let mut post_absorb_state = pre_permute;
    keccak_f1600::keccak_f(&mut post_absorb_state);

    // ── T2: multi-block squeeze ──
    let squeeze_layout = SqueezeLayout::new(
        post_absorb_state, N_F1600_CALLS_SQUEEZE, SHAKE_128_RATE_BYTES,
    );
    let squeeze_n_trace = squeeze_layout.active_rows().next_power_of_two();
    let mut squeeze_trace: Vec<Vec<F>> = (0..ml_dsa_shake_squeeze_air::WIDTH)
        .map(|_| vec![F::zero(); squeeze_n_trace]).collect();
    ml_dsa_shake_squeeze_air::fill_trace(
        &mut squeeze_trace, squeeze_n_trace, &squeeze_layout,
    );
    // Squeeze stream: block 0 from layout (= post_absorb's rate
    // bytes) + blocks 1..N from squeeze_trace.
    let squeeze_stream = ml_dsa_shake_squeeze_air::extract_full_squeeze_from_trace(
        &squeeze_trace, &squeeze_layout,
    );

    // ── T3a: chunks + count ──
    let chunks: Vec<(u8, u8, u8)> = (0..N_CHUNKS_PROVISION)
        .map(|c| (squeeze_stream[3 * c], squeeze_stream[3 * c + 1], squeeze_stream[3 * c + 2]))
        .collect();
    let chunk_n_trace = N_CHUNKS_PROVISION.next_power_of_two();
    let mut chunk_trace: Vec<Vec<F>> = (0..ml_dsa_rej_count_air::WIDTH)
        .map(|_| vec![F::zero(); chunk_n_trace]).collect();
    ml_dsa_rej_count_air::fill_trace(&mut chunk_trace, chunk_n_trace, &chunks);

    // ── Extract polynomial: first 256 accepted u-values ──
    let mut poly = [0u32; N];
    let mut count = 0;
    let mut last_accept_row = 0;
    for (r, &(b0, b1, b2)) in chunks.iter().enumerate() {
        let (u, accept, _) = ml_dsa_rej_chunk_air::parse_chunk(b0, b1, b2);
        if accept {
            if count < N {
                poly[count] = u;
                last_accept_row = r;
            }
            count += 1;
            if count == N { break; }
        }
    }
    assert!(count >= N,
        "ran out of provisioned chunks before {N} accepts (count={count})");

    ExpandAOneTraces {
        absorb_trace, squeeze_trace, chunk_trace,
        squeeze_stream, poly, last_accept_row,
    }
}

/// Verify each sub-region's per-row constraints in isolation.
/// Returns a list of (region, row, constraint_idx) for any that fail.
pub fn verify_subregion_constraints(traces: &ExpandAOneTraces) -> Vec<(&'static str, usize, usize)> {
    let mut failures = Vec::new();

    // Absorb region: 24 rows of keccak_f1600 round constraints.
    let absorb_n = traces.absorb_trace[0].len();
    for row in 0..keccak_f1600::ROUNDS {
        let cur: Vec<F> = (0..ml_dsa_shake_absorb_air::WIDTH)
            .map(|c| traces.absorb_trace[c][row]).collect();
        let nxt: Vec<F> = (0..ml_dsa_shake_absorb_air::WIDTH)
            .map(|c| traces.absorb_trace[c][(row + 1) % absorb_n]).collect();
        let cvals = ml_dsa_shake_absorb_air::eval_per_row(&cur, &nxt, row);
        for (i, v) in cvals.iter().enumerate() {
            if !v.is_zero() { failures.push(("absorb", row, i)); }
        }
    }

    // Squeeze region: N_F1600_CALLS_SQUEEZE × 24 rows.
    let squeeze_layout = SqueezeLayout::new(
        [0u64; 25], N_F1600_CALLS_SQUEEZE, SHAKE_128_RATE_BYTES,  // initial_state isn't used by eval
    );
    let squeeze_n = traces.squeeze_trace[0].len();
    for row in 0..squeeze_layout.active_rows() {
        let cur: Vec<F> = (0..ml_dsa_shake_squeeze_air::WIDTH)
            .map(|c| traces.squeeze_trace[c][row]).collect();
        let nxt: Vec<F> = (0..ml_dsa_shake_squeeze_air::WIDTH)
            .map(|c| traces.squeeze_trace[c][(row + 1) % squeeze_n]).collect();
        let cvals = ml_dsa_shake_squeeze_air::eval_per_row(&cur, &nxt, row, &squeeze_layout);
        for (i, v) in cvals.iter().enumerate() {
            if !v.is_zero() { failures.push(("squeeze", row, i)); }
        }
    }

    // Chunk region: N_CHUNKS_PROVISION rows of T3a constraints.
    let chunk_n = traces.chunk_trace[0].len();
    for row in 0..(N_CHUNKS_PROVISION - 1) {  // -1 to skip the last (no nxt)
        let cur: Vec<F> = (0..ml_dsa_rej_count_air::WIDTH)
            .map(|c| traces.chunk_trace[c][row]).collect();
        let nxt: Vec<F> = (0..ml_dsa_rej_count_air::WIDTH)
            .map(|c| traces.chunk_trace[c][(row + 1) % chunk_n]).collect();
        let cvals = ml_dsa_rej_count_air::eval_per_row(&cur, &nxt, row);
        for (i, v) in cvals.iter().enumerate() {
            if !v.is_zero() { failures.push(("chunk", row, i)); }
        }
    }

    failures
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::{K, L};
    use crate::ml_dsa_codec;

    /// **Headline integration test.**  For 2 distinct ρ seeds × 2
    /// distinct (i, j) pairs each = 4 element instances:
    /// 1. Run T1 + T2 + T3a traces.
    /// 2. Verify every per-row constraint in every sub-region.
    /// 3. Verify the polynomial output matches `expand_a`.
    /// 4. Verify the chunk inputs are bit-for-bit consistent with
    ///    the squeeze stream extracted from T2's post-iota cells
    ///    (the binding the future T3c will enforce in-circuit).
    #[test]
    fn expand_a_one_full_pipeline_matches_native() {
        for seed_byte in [0x42u8, 0xA5] {
            let rho = [seed_byte; 32];
            let expected_full = ml_dsa_codec::expand_a(&rho);

            for i in 0..2u8 {
                for j in 0..2u8 {
                    let traces = fill_expand_a_one(&rho, i, j);

                    // 1. All sub-region constraints pass.
                    let failures = verify_subregion_constraints(&traces);
                    assert!(failures.is_empty(),
                        "T3b: sub-region constraint failures at ρ=[{seed_byte:#x};32], (i={i}, j={j}): {failures:?}");

                    // 2. Polynomial matches native expand_a.
                    assert_eq!(&traces.poly[..], &expected_full[i as usize][j as usize][..],
                        "T3b: polynomial mismatch at ρ=[{seed_byte:#x};32], (i={i}, j={j})");

                    // 3. (Off-chain) byte-alignment check: chunk inputs
                    //    must equal the corresponding 3 bytes of the
                    //    squeeze stream.  The future T3c constraint
                    //    will assert this in-circuit.
                    for c in 0..N_CHUNKS_PROVISION {
                        let expected_b0 = traces.squeeze_stream[3 * c];
                        let expected_b1 = traces.squeeze_stream[3 * c + 1];
                        let expected_b2 = traces.squeeze_stream[3 * c + 2];
                        let mut got_b0: u8 = 0;
                        let mut got_b1: u8 = 0;
                        let mut got_b2: u8 = 0;
                        for b in 0..8 {
                            if !traces.chunk_trace[ml_dsa_rej_chunk_air::col_input_bit(b)][c]
                                .is_zero() { got_b0 |= 1 << b; }
                            if !traces.chunk_trace[ml_dsa_rej_chunk_air::col_input_bit(8 + b)][c]
                                .is_zero() { got_b1 |= 1 << b; }
                            if !traces.chunk_trace[ml_dsa_rej_chunk_air::col_input_bit(16 + b)][c]
                                .is_zero() { got_b2 |= 1 << b; }
                        }
                        assert_eq!((got_b0, got_b1, got_b2), (expected_b0, expected_b1, expected_b2),
                            "byte-alignment mismatch at chunk {c} (ρ_byte={seed_byte:#x}, i={i}, j={j})");
                    }

                    // 4. Sanity: 256th accept happens within provisioned chunks.
                    assert!(traces.last_accept_row < N_CHUNKS_PROVISION,
                        "T3b: 256th accept row {} ≥ provisioning {N_CHUNKS_PROVISION}",
                        traces.last_accept_row);
                }
            }
        }
    }

    /// All 16 (i, j) pairs of ML-DSA-44's K × L = 4 × 4 matrix
    /// produce the correct polynomial for a fixed ρ.  Tighter
    /// coverage than the 4-pair test above; runs slower so we use
    /// just one seed.
    #[test]
    fn expand_a_one_covers_full_matrix() {
        let rho = [0x37u8; 32];
        let expected_full = ml_dsa_codec::expand_a(&rho);

        for i in 0..(K as u8) {
            for j in 0..(L as u8) {
                let traces = fill_expand_a_one(&rho, i, j);
                assert_eq!(&traces.poly[..], &expected_full[i as usize][j as usize][..],
                    "T3b full-matrix mismatch at (i={i}, j={j})");
            }
        }
    }
}
