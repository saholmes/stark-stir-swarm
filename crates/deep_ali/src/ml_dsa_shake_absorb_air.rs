//! T1: **single-block SHAKE absorb AIR** (FIPS 202 §6.2 + §3).
//!
//! First brick of the v2 ML-DSA roadmap.  Proves "I applied Keccak-f
//! to (M padded per FIPS 202 SHAKE-128/SHAKE-256 absorb rules)" for
//! a message `M` of length less than the absorb rate.  Single-block
//! absorb covers the three v2-critical ML-DSA call sites that take
//! short inputs:
//!
//! - **SampleInBall** consumes `c̃` = 32 bytes (FIPS 204 §3.7).
//!   Rate = 136 bytes (SHAKE-256), so 32 < 136 fits.
//! - **ExpandA seeded element** consumes `ρ‖i‖j` = 34 bytes per
//!   matrix element (FIPS 204 §3.4).  Rate = 168 bytes (SHAKE-128),
//!   so 34 < 168 fits.
//! - **µ derivation** for ML-DSA-44 verify path consumes `tr‖M`
//!   where `tr` is 64 bytes; for short messages this can fit one
//!   block of SHAKE-256 (≤ 71 bytes total).  Longer messages need
//!   the multi-block variant (TBD as a follow-up T1.5).
//!
//! Multi-block absorb is the natural extension; deferred to keep
//! T1's contract minimal and auditable.
//!
//! ## Soundness contract
//!
//! This AIR alone does NOT enforce "the row-0 STATE_IN cells equal
//! `pad_shake(M, rate)` for some specific M".  It just proves
//! "Keccak-f applied to `STATE_IN` produces `STATE_OUT`".  The
//! binding to a specific `M` happens by:
//!
//! 1. The composing v2 AIR placing `M`'s bits in dedicated trace
//!    columns and adding equality constraints linking those bits to
//!    the first `M.len() * 8` bits of `STATE_IN`, plus literal
//!    constraints for the suffix/pad pattern.
//! 2. PI-hash binding `M` to the proof transcript so the verifier's
//!    re-derivation matches the prover's.
//!
//! Both paths are out of scope for T1 standalone but are documented
//! here so the boundary is explicit.
//!
//! ## Trace layout
//!
//! Identical to `keccak_f1600_air`: 24 rows of one Keccak-f round
//! each, ROUND_WIDTH columns of bit cells.  T1 is a thin wrapper:
//! `fill_trace` builds the absorbed initial state from `M` (with
//! correct SHAKE padding) and delegates to
//! `keccak_f1600_air::fill_trace`; `eval_per_row` is verbatim
//! `keccak_f1600_air::eval_per_row`.
//!
//! ## Output extraction
//!
//! The first `rate` bytes of SHAKE squeeze are the low `rate` bits
//! of the post-permutation state, read little-endian within each
//! lane.  Helper `extract_first_squeeze` does this from the trace's
//! final-round POST_IOTA cells; `extract_first_squeeze_native`
//! does the same from a `[u64; 25]` state for cross-checks.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600::{self, NUM_LANES, ROUNDS};
use crate::keccak_f1600_air::{
    self, cols, post_iota_col, LANE_BITS, ROUND_WIDTH, STATE_BITS,
};

// ─── Rate parameters (FIPS 202 §6) ─────────────────────────────────

pub const SHAKE_128_RATE_BYTES: usize = 168;  // r = 1344 bits, c = 256
pub const SHAKE_256_RATE_BYTES: usize = 136;  // r = 1088 bits, c = 512

// ─── Re-export shape so callers don't have to also import keccak_f1600_air ──

pub const WIDTH: usize = ROUND_WIDTH;
pub const ROWS: usize = ROUNDS;

// ─── Native helpers ────────────────────────────────────────────────

/// Pad an absorb message `m` per FIPS 202 SHAKE rules, returning
/// the `rate_bytes`-long padded block.  Panics if `m.len() >=
/// rate_bytes` (single-block contract).
pub fn pad_shake(m: &[u8], rate_bytes: usize) -> Vec<u8> {
    assert!(
        m.len() < rate_bytes,
        "single-block SHAKE absorb requires M.len() < rate ({} ≥ {})",
        m.len(), rate_bytes,
    );
    assert!(rate_bytes % 8 == 0, "rate must be a multiple of 8 bytes");
    let mut padded = vec![0u8; rate_bytes];
    padded[..m.len()].copy_from_slice(m);
    // FIPS 202 §6.2 SHAKE suffix: the 4-bit string `1111` followed
    // by pad10*1's leading `1` — 5 bits at offset m.len()*8.  In
    // little-endian bit ordering, that's the byte 0x1F at offset
    // m.len() (no spillover for any sub-rate length).
    padded[m.len()] |= 0x1F;
    // pad10*1 trailing `1`: the very last bit of the rate = bit 7
    // (MSB) of the last byte.  May overlap with the suffix byte if
    // m.len() == rate_bytes - 1; the |= handles that automatically.
    padded[rate_bytes - 1] |= 0x80;
    padded
}

/// Build the 25-lane Keccak state that results from XORing the
/// padded message into a zero starting state (i.e., the state
/// immediately BEFORE the round-0 application of Keccak-f).
pub fn build_absorbed_state(m: &[u8], rate_bytes: usize) -> [u64; NUM_LANES] {
    let padded = pad_shake(m, rate_bytes);
    let mut state = [0u64; NUM_LANES];
    let n_rate_lanes = rate_bytes / 8;
    for i in 0..n_rate_lanes {
        let mut lane = [0u8; 8];
        lane.copy_from_slice(&padded[i * 8..(i + 1) * 8]);
        state[i] = u64::from_le_bytes(lane);
    }
    // Capacity lanes (n_rate_lanes..25) stay zero — initial state
    // was zero and only the rate portion was XOR'd.
    state
}

/// Native cross-check: the first `rate_bytes` of SHAKE squeeze
/// from `m`.  Equivalent to running `sha3::Shake256` (or 128) and
/// reading the first rate bytes of the XOF stream.
pub fn extract_first_squeeze_native(m: &[u8], rate_bytes: usize) -> Vec<u8> {
    let mut state = build_absorbed_state(m, rate_bytes);
    keccak_f1600::keccak_f(&mut state);
    let n_rate_lanes = rate_bytes / 8;
    let mut out = Vec::with_capacity(rate_bytes);
    for i in 0..n_rate_lanes {
        out.extend_from_slice(&state[i].to_le_bytes());
    }
    out
}

/// Read the AIR's claimed post-permutation state (lanes 0..n_rate_lanes
/// only — the squeezable rate portion) from the trace.
pub fn extract_first_squeeze_from_trace(
    trace: &[Vec<F>], rate_bytes: usize,
) -> Vec<u8> {
    let last_round = ROUNDS - 1;
    let n_rate_lanes = rate_bytes / 8;
    let mut out = Vec::with_capacity(rate_bytes);
    for lane in 0..n_rate_lanes {
        let mut lane_bytes = [0u8; 8];
        for byte_i in 0..8 {
            let mut byte = 0u8;
            for bit in 0..8 {
                let global_bit = byte_i * 8 + bit;
                let col = post_iota_col(lane % 5, lane / 5, global_bit);
                let v = trace[col][last_round];
                let b = if v.is_zero() { 0 } else { 1 };
                byte |= b << bit;
            }
            lane_bytes[byte_i] = byte;
        }
        out.extend_from_slice(&lane_bytes);
    }
    out
}

// ─── fill_trace ────────────────────────────────────────────────────

/// Drive the absorb-then-permute path, recording the trace.
pub fn fill_trace(
    trace: &mut [Vec<F>], n_trace: usize, m: &[u8], rate_bytes: usize,
) {
    assert_eq!(trace.len(), WIDTH);
    let initial_state = build_absorbed_state(m, rate_bytes);
    keccak_f1600_air::fill_trace(trace, n_trace, &initial_state);
}

// ─── Constraint evaluation ─────────────────────────────────────────

/// Per-row constraints — passthrough to the underlying
/// keccak_f1600_air round constraints.
pub fn eval_per_row(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    keccak_f1600_air::eval_per_row(cur, nxt, row)
}


// ─── Tests ─────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// FIPS 202 padding sanity: padded `m` has 0x1F at position
    /// `m.len()` and 0x80 at the last position.
    #[test]
    fn pad_shake_is_well_formed_for_short_m() {
        let m = vec![0x42u8; 32];
        let padded = pad_shake(&m, SHAKE_256_RATE_BYTES);
        assert_eq!(padded.len(), SHAKE_256_RATE_BYTES);
        assert_eq!(&padded[..32], &m[..]);
        assert_eq!(padded[32], 0x1F);
        for i in 33..SHAKE_256_RATE_BYTES - 1 {
            assert_eq!(padded[i], 0, "byte {} must be zero", i);
        }
        assert_eq!(padded[SHAKE_256_RATE_BYTES - 1], 0x80);
    }

    /// Edge case: M.len() == rate − 1, so the suffix and pad-trailing
    /// bit collapse into the same byte (0x9F = 0x1F | 0x80).
    #[test]
    fn pad_shake_handles_max_length_input() {
        let m = vec![0u8; SHAKE_256_RATE_BYTES - 1];
        let padded = pad_shake(&m, SHAKE_256_RATE_BYTES);
        assert_eq!(padded.len(), SHAKE_256_RATE_BYTES);
        assert_eq!(padded[SHAKE_256_RATE_BYTES - 1], 0x9F);
    }

    /// Native first-squeeze must match `sha3::Shake256` on the same
    /// input — the AIR's correctness anchor.
    #[test]
    fn native_first_squeeze_matches_sha3_shake256() {
        let m: &[u8] = b"mmiyc/v2/T1/shake-256-vector-test";
        let ours = extract_first_squeeze_native(m, SHAKE_256_RATE_BYTES);

        let mut hasher = sha3::Shake256::default();
        hasher.update(m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; SHAKE_256_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs, "T1 native must match sha3::Shake256");
    }

    /// Same test for SHAKE-128 (ExpandA's primitive).
    #[test]
    fn native_first_squeeze_matches_sha3_shake128() {
        let m: &[u8] = b"mmiyc/v2/T1/shake-128-vector-test-with-some-extra-bytes";
        assert!(m.len() < SHAKE_128_RATE_BYTES);
        let ours = extract_first_squeeze_native(m, SHAKE_128_RATE_BYTES);

        let mut hasher = sha3::Shake128::default();
        hasher.update(m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; SHAKE_128_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs, "T1 native must match sha3::Shake128");
    }

    /// Empty-input vector for SHAKE-256: pad is the entire block,
    /// just the suffix + final-1 with no message bytes.
    #[test]
    fn native_first_squeeze_for_empty_input() {
        let m: &[u8] = b"";
        let ours = extract_first_squeeze_native(m, SHAKE_256_RATE_BYTES);
        let mut hasher = sha3::Shake256::default();
        hasher.update(m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; SHAKE_256_RATE_BYTES];
        reader.read(&mut theirs);
        assert_eq!(ours, theirs);
    }

    /// Honest trace: every keccak_f1600 round constraint is zero on
    /// rows 0..23 of the absorb-then-permute trace.
    #[test]
    fn honest_absorb_trace_satisfies_keccak_constraints() {
        let m: &[u8] = b"mmiyc/v2/T1/honest-trace-test";
        let n_trace = ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, m, SHAKE_256_RATE_BYTES);

        for row in 0..ROUNDS {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T1 keccak constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }

    /// AIR-side first-squeeze must match the native first-squeeze
    /// on the same input.  Closes the AIR-vs-native loop.
    #[test]
    fn trace_first_squeeze_matches_native() {
        let m: &[u8] = b"mmiyc/v2/T1/squeeze-extraction-test";
        let n_trace = ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, m, SHAKE_256_RATE_BYTES);

        let from_trace = extract_first_squeeze_from_trace(&trace, SHAKE_256_RATE_BYTES);
        let from_native = extract_first_squeeze_native(m, SHAKE_256_RATE_BYTES);
        assert_eq!(from_trace, from_native,
            "T1 trace post-iota must match native keccak-f output");
    }

    /// Tampering with one bit on a middle round must surface in the
    /// boolean / chain constraints around that round.
    #[test]
    fn tampered_state_bit_breaks_keccak_constraint() {
        let m: &[u8] = b"mmiyc/v2/T1/tamper-test";
        let n_trace = ROWS.next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, m, SHAKE_256_RATE_BYTES);

        // Flip a state-in bit on round 5.
        let target_row = 5;
        let target_col = cols::STATE_IN_BASE + 100;
        let original = trace[target_col][target_row];
        // Goldilocks XOR-1 = 1 - x for x ∈ {0, 1}.
        trace[target_col][target_row] = F::from(1u64) - original;

        let mut found = false;
        for row in target_row.saturating_sub(1)..=target_row {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            if cvals.iter().any(|v| !v.is_zero()) {
                found = true;
                break;
            }
        }
        assert!(found, "T1 must reject tampered state bits");
    }
}
