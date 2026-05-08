//! T-Transcript: SHAKE-256(µ ‖ w1bytes) → c̃' (FIPS 204 §3 Algorithm 3 step 7).
//!
//! Where v1.7 takes c̃ as a public input and trusts Layer 1's
//! native `ml_dsa::verify` to recompute c̃' and check c̃' == c̃, v2
//! does the recomputation in-circuit.  This module:
//!
//! 1. Provides the **native** transcript computation for cross-checks.
//! 2. Exposes the multi-block-absorb layout for the in-circuit AIR
//!    (composed via `ml_dsa_shake_absorb_multi_air`).
//! 3. Helper: extract c̃' from a T1.5 trace.
//!
//! ## Wire shape (ML-DSA-44 verify path)
//!
//! - **µ**: 64 bytes (= SHAKE-256(tr ‖ M); tr = SHAKE-256(pk); for
//!   verify, µ is supplied as a public input).
//! - **w1bytes**: `K · N · BITS_PER_W1 / 8` bytes, packed by
//!   `w1Encode`.  For ML-DSA-44: γ₂ = (q − 1)/88, so the high-bits
//!   range is `[0, 44)`, packed at 6 bits per coefficient.  Total:
//!   `4 · 256 · 6 / 8 = 768 bytes`.
//! - **c̃'**: first 32 bytes of the SHAKE-256 squeeze output.
//!
//! Total absorb input = 64 + 768 = **832 bytes**.  SHAKE-256 rate =
//! 136 bytes ⇒ ⌈(832 + 1)/136⌉ = **7 blocks** absorbed.  Output
//! fits in block 0 of the squeeze (32 ≤ 136), so **no T2 squeeze
//! work needed**; c̃' is the first 4 lanes of the post-absorb state.
//!
//! ## How v2 binds w1bytes
//!
//! In the composing AIR, w1bytes are produced by `T-W1Encode` (one
//! cell per byte).  The transcript AIR's absorb input bytes are
//! also one cell per byte.  Cross-region equality between these
//! cell sets is enforced by the T-MEM permutation argument (see
//! `permutation_argument.rs`).

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600::{NUM_LANES, ROUNDS};
use crate::keccak_f1600_air::{cols, post_iota_col, LANE_BITS, ROUND_WIDTH, STATE_BITS};
use crate::ml_dsa_shake_absorb_multi_air::{
    self as t15, MultiAbsorbLayout, SHAKE_256_RATE_BYTES,
};

/// Number of c̃' bytes consumed by the verify equality check.
/// FIPS 204 §3 Algorithm 3 step 7 reads the first **32 bytes** of
/// SHAKE-256 output; the comparison `c̃' == c̃` then accepts/rejects.
pub const C_TILDE_PRIME_BYTES: usize = crate::ml_dsa::params::C_TILDE_BYTES;

// ─── Native ───────────────────────────────────────────────────────

/// Native c̃' = SHAKE-256(µ ‖ w1bytes)[0..32].  Uses T1.5's
/// multi-block absorb (which is itself sha3-cross-checked).
pub fn compute_c_tilde_prime_native(mu: &[u8; 64], w1bytes: &[u8]) -> [u8; C_TILDE_PRIME_BYTES] {
    // Concatenate.
    let mut input = Vec::with_capacity(mu.len() + w1bytes.len());
    input.extend_from_slice(mu);
    input.extend_from_slice(w1bytes);

    // Multi-block absorb (T1.5 native helper).
    let layout = MultiAbsorbLayout::new(&input, SHAKE_256_RATE_BYTES);
    let post_absorb = t15::absorb_native(&layout);

    // First 32 bytes of squeeze: lanes 0..4 as LE bytes (= block 0
    // of squeeze = post-absorb's rate-byte prefix; first 32 ≤ rate).
    let mut out = [0u8; C_TILDE_PRIME_BYTES];
    for lane in 0..(C_TILDE_PRIME_BYTES / 8) {
        let lane_bytes = post_absorb[lane].to_le_bytes();
        out[lane * 8..(lane + 1) * 8].copy_from_slice(&lane_bytes);
    }
    out
}

/// Build the absorb layout for a (µ, w1bytes) tuple.  Used by the
/// composing AIR to drive T1.5's `fill_trace`.
pub fn build_layout(mu: &[u8; 64], w1bytes: &[u8]) -> MultiAbsorbLayout {
    let mut input = Vec::with_capacity(mu.len() + w1bytes.len());
    input.extend_from_slice(mu);
    input.extend_from_slice(w1bytes);
    MultiAbsorbLayout::new(&input, SHAKE_256_RATE_BYTES)
}

// ─── Trace extraction ─────────────────────────────────────────────

/// Read c̃' from a T1.5 absorb trace's last block's post-iota cells.
/// `layout` must match the trace; `trace` must be `t15::WIDTH` cols
/// wide and have at least `layout.active_rows()` populated rows.
pub fn extract_c_tilde_prime_from_trace(
    trace: &[Vec<F>],
    layout: &MultiAbsorbLayout,
) -> [u8; C_TILDE_PRIME_BYTES] {
    debug_assert_eq!(trace.len(), t15::WIDTH);
    let last_block = layout.n_blocks - 1;
    let last_row = last_block * ROUNDS + (ROUNDS - 1);
    let mut out = [0u8; C_TILDE_PRIME_BYTES];
    for lane in 0..(C_TILDE_PRIME_BYTES / 8) {
        let mut lane_bytes = [0u8; 8];
        for byte_i in 0..8 {
            let mut byte = 0u8;
            for bit in 0..8 {
                let global_bit = byte_i * 8 + bit;
                let col = post_iota_col(lane % 5, lane / 5, global_bit);
                let v = trace[col][last_row];
                let b = if v.is_zero() { 0 } else { 1 };
                byte |= b << bit;
            }
            lane_bytes[byte_i] = byte;
        }
        out[lane * 8..(lane + 1) * 8].copy_from_slice(&lane_bytes);
    }
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    fn fresh_t15_trace(n: usize) -> Vec<Vec<F>> {
        (0..t15::WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Native c̃' matches `sha3::Shake256(µ ‖ w1bytes)[0..32]` for
    /// realistic ML-DSA-44 wire shapes.
    #[test]
    fn native_matches_sha3_shake256() {
        let mu = [0x42u8; 64];
        let w1 = vec![0xA5u8; 768];  // canonical ML-DSA-44 w1 length

        let ours = compute_c_tilde_prime_native(&mu, &w1);

        let mut hasher = sha3::Shake256::default();
        hasher.update(&mu);
        hasher.update(&w1);
        let mut reader = hasher.finalize_xof();
        let mut theirs = [0u8; C_TILDE_PRIME_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs,
            "T-Transcript native must match sha3::Shake256 first 32 bytes");
    }

    /// Edge case: w1bytes is 0 bytes (only µ in the input).
    /// Important because µ-only input fits in 1 block but the absorb
    /// + 1-byte-of-padding still pushes to 1 full block of f1600.
    #[test]
    fn native_handles_empty_w1() {
        let mu = [0u8; 64];
        let w1 = vec![];
        let ours = compute_c_tilde_prime_native(&mu, &w1);

        let mut hasher = sha3::Shake256::default();
        hasher.update(&mu);
        let mut reader = hasher.finalize_xof();
        let mut theirs = [0u8; C_TILDE_PRIME_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs);
    }

    /// Distinct (µ, w1) inputs yield distinct c̃' (with overwhelming
    /// probability) — sanity check for the verify-equality gate.
    #[test]
    fn distinct_inputs_yield_distinct_outputs() {
        let mu0 = [0x42u8; 64];
        let mut mu1 = mu0; mu1[0] ^= 0xFF;
        let w1 = vec![0xA5u8; 768];

        let c0 = compute_c_tilde_prime_native(&mu0, &w1);
        let c1 = compute_c_tilde_prime_native(&mu1, &w1);
        assert_ne!(c0, c1);

        let mut w1b = w1.clone(); w1b[0] ^= 0xFF;
        let c2 = compute_c_tilde_prime_native(&mu0, &w1b);
        assert_ne!(c0, c2);
    }

    /// Trace round-trip: drive T1.5's fill_trace on the transcript
    /// input + extract c̃' from the trace; must equal the native
    /// computation.
    #[test]
    fn trace_extraction_matches_native() {
        let mu = [0x37u8; 64];
        let w1 = (0u32..768u32).map(|i| (i as u8).wrapping_mul(13)).collect::<Vec<u8>>();

        let layout = build_layout(&mu, &w1);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_t15_trace(n_trace);
        t15::fill_trace(&mut trace, n_trace, &layout);

        let from_trace = extract_c_tilde_prime_from_trace(&trace, &layout);
        let from_native = compute_c_tilde_prime_native(&mu, &w1);
        assert_eq!(from_trace, from_native);
    }

    /// Trace's per-row constraints all hold for an honest transcript
    /// computation.  Closes the AIR-soundness loop: if the prover
    /// supplies a wrong trace, T1.5's existing per-row constraints
    /// would fire.
    #[test]
    fn honest_transcript_trace_satisfies_t15_constraints() {
        let mu = [0xC4u8; 64];
        let w1 = vec![0x69u8; 768];

        let layout = build_layout(&mu, &w1);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_t15_trace(n_trace);
        t15::fill_trace(&mut trace, n_trace, &layout);

        for row in 0..layout.active_rows() {
            let cur: Vec<F> = (0..t15::WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..t15::WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = t15::eval_per_row(&cur, &nxt, row, &layout);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-Transcript: T1.5 constraint {i} on row {row} (block {}) not zero: {v:?}",
                    row / ROUNDS);
            }
        }
    }

    /// Realistic ML-DSA-44 transcript shape: 7 blocks of f1600 absorb.
    #[test]
    fn ml_dsa_44_transcript_shape_sanity() {
        let mu = [0u8; 64];
        let w1 = vec![0u8; 768];
        let layout = build_layout(&mu, &w1);
        // Total absorb input = 832 B + 1 B suffix = 833 → ⌈833/136⌉ = 7 blocks.
        assert_eq!(layout.n_blocks, 7);
        assert_eq!(layout.active_rows(), 7 * ROUNDS);
    }
}
