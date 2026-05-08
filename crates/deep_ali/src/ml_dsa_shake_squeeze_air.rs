//! T2: **SHAKE squeeze AIR**.
//!
//! Generates additional rate-byte output blocks after a SHAKE
//! absorb has finished.  Where T1/T1.5 prove "I absorbed M and got
//! state S", T2 proves "starting from state S₀, applying Keccak-f
//! repeatedly produced the chain S₁, S₂, …, Sₙ".  Each Sᵢ's
//! rate-byte prefix is one block of XOF output stream.
//!
//! ## Why this is needed
//!
//! ML-DSA-44's SHAKE call sites read more than one rate's worth of
//! output:
//! - **ExpandA** (FIPS 204 §3.4): reads ~768 bytes per matrix
//!   element via SHAKE-128 (rate 168 → ~5 squeeze blocks per
//!   element, K·L = 16 elements → ~80 blocks total).
//! - **SampleInBall** (FIPS 204 §3.7): rejection-samples until
//!   τ = 39 unique positions are picked, typically 1–2 blocks.
//! - **ExpandMask** for `y` (in signing, but ML-DSA-44 verify
//!   doesn't recompute y; v2 doesn't need this case).
//! - **µ derivation / transcript SHAKE-256 (T5)**: typically a
//!   single block.
//!
//! ## Trace layout
//!
//! `n_f1600_calls × 24` active rows.  Each f1600 call sits in its
//! own 24-row sub-trace; consecutive sub-traces are linked by a
//! **passthrough** boundary constraint (no XOR with input — that's
//! T1.5's job).
//!
//! Total output blocks = `n_f1600_calls + 1`.  Block 0 is the
//! initial state S₀'s rate bytes (supplied as a public input by
//! the caller).  Blocks 1..n_f1600_calls come from the trace's
//! post-iota cells of round 23 of each f1600 call.
//!
//! ## Per-row constraints
//!
//! 1. Standard f1600 round constraints (delegated to
//!    `keccak_f1600_air::eval_per_row`).
//! 2. Round-23 cardinality padding (1600 zero-fillers, same trick
//!    as T1.5).
//! 3. Inter-f1600 passthrough chain at row 24·b + 23 for b <
//!    n_f1600_calls − 1: `nxt[STATE_IN][bit] − cur[POST_IOTA][bit]
//!    = 0` for all 1600 bits.
//!
//! ## Boundary at row 0
//!
//! Same convention as T1.5: the row-0 STATE_IN cells are bound to
//! S₀'s bit decomposition via the composing AIR's PI-hash.  No
//! internal constraint here.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600::{self, NUM_LANES, ROUNDS};
use crate::keccak_f1600_air::{
    self, cols, post_iota_col, state_in_col, LANE_BITS, ROUND_WIDTH, STATE_BITS,
};
pub use crate::ml_dsa_shake_absorb_air::{
    SHAKE_128_RATE_BYTES, SHAKE_256_RATE_BYTES,
};

pub const WIDTH: usize = ROUND_WIDTH;

// ─── Layout (public-input descriptor) ─────────────────────────────

#[derive(Clone)]
pub struct SqueezeLayout {
    /// State immediately after absorb (= S₀ = squeeze block 0).
    pub initial_state: [u64; NUM_LANES],
    /// Number of additional Keccak-f calls during squeeze.  Total
    /// output blocks = `n_f1600_calls + 1`.
    pub n_f1600_calls: usize,
    pub rate_bytes: usize,
}

impl SqueezeLayout {
    pub fn new(initial_state: [u64; NUM_LANES], n_f1600_calls: usize, rate_bytes: usize) -> Self {
        assert!(rate_bytes % 8 == 0);
        Self { initial_state, n_f1600_calls, rate_bytes }
    }

    pub fn active_rows(&self) -> usize {
        self.n_f1600_calls * ROUNDS
    }

    pub fn n_output_blocks(&self) -> usize {
        self.n_f1600_calls + 1
    }
}

// ─── Native helpers ───────────────────────────────────────────────

/// Native SHAKE squeeze: produce `n_f1600_calls + 1` rate-byte
/// output blocks starting from `initial_state`.  Block 0 = initial
/// state's rate bytes (no f1600 call).  Block i (i ≥ 1) = state
/// after i applications of Keccak-f.
pub fn squeeze_native(layout: &SqueezeLayout) -> Vec<u8> {
    let mut state = layout.initial_state;
    let n_rate_lanes = layout.rate_bytes / 8;
    let mut out = Vec::with_capacity(layout.rate_bytes * layout.n_output_blocks());

    // Block 0: read initial state's rate bytes (no f1600 yet).
    for i in 0..n_rate_lanes {
        out.extend_from_slice(&state[i].to_le_bytes());
    }
    // Blocks 1..N: each preceded by one Keccak-f application.
    for _ in 0..layout.n_f1600_calls {
        keccak_f1600::keccak_f(&mut state);
        for i in 0..n_rate_lanes {
            out.extend_from_slice(&state[i].to_le_bytes());
        }
    }
    out
}

// ─── fill_trace ───────────────────────────────────────────────────

/// Drive the squeeze chain, recording the trace.  Each block holds
/// 24 rows of one Keccak-f call.  Initial state of block 0 = S₀
/// from layout; initial state of block b ≥ 1 = post-iota of round
/// 23 of block b − 1.
pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, layout: &SqueezeLayout) {
    assert_eq!(trace.len(), WIDTH);
    assert!(n_trace >= layout.active_rows());

    let mut state = layout.initial_state;

    for b in 0..layout.n_f1600_calls {
        let mut sub: Vec<Vec<F>> = (0..ROUND_WIDTH)
            .map(|_| vec![F::zero(); ROUNDS]).collect();
        keccak_f1600_air::fill_trace(&mut sub, ROUNDS, &state);

        let base = b * ROUNDS;
        for r in 0..ROUNDS {
            for c in 0..ROUND_WIDTH {
                trace[c][base + r] = sub[c][r];
            }
        }

        // Read off post_iota of round 23 → next block's state_in.
        for lane in 0..NUM_LANES {
            let mut v: u64 = 0;
            for b_idx in 0..LANE_BITS {
                let bit_val = sub[cols::POST_IOTA_BASE + lane * LANE_BITS + b_idx][ROUNDS - 1];
                let bit: u64 = if bit_val.is_zero() { 0 } else { 1 };
                v |= bit << b_idx;
            }
            state[lane] = v;
        }
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

pub fn eval_per_row(
    cur: &[F],
    nxt: &[F],
    row: usize,
    layout: &SqueezeLayout,
) -> Vec<F> {
    let mut out = Vec::new();
    let active_rows = layout.active_rows();

    if row >= active_rows {
        let max_card = num_constraints();
        for _ in 0..max_card { out.push(F::zero()); }
        return out;
    }

    let in_block_round = row % ROUNDS;
    let block_idx = row / ROUNDS;
    let is_last_round_of_block = in_block_round == ROUNDS - 1;
    let is_last_block = block_idx == layout.n_f1600_calls - 1;

    // 1. Standard f1600 round constraints + in-block chain (rounds 0..22).
    let standard = keccak_f1600_air::eval_per_row(cur, nxt, in_block_round);
    out.extend(standard);
    if in_block_round == ROUNDS - 1 {
        // Pad round 23's missing chain slots with zeros for uniform cardinality.
        for _ in 0..STATE_BITS { out.push(F::zero()); }
    }

    // 2. Inter-f1600 passthrough chain at the last round of every
    //    block except the final one: nxt[STATE_IN] = cur[POST_IOTA].
    if is_last_round_of_block && !is_last_block {
        for c_off in 0..STATE_BITS {
            let pi = cur[cols::POST_IOTA_BASE + c_off];
            let nx = nxt[cols::STATE_IN_BASE + c_off];
            out.push(nx - pi);
        }
    } else {
        for _ in 0..STATE_BITS { out.push(F::zero()); }
    }

    debug_assert_eq!(out.len(), num_constraints());
    out
}

pub fn num_constraints() -> usize {
    use std::sync::OnceLock;
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        let cur = vec![F::zero(); ROUND_WIDTH];
        let nxt = vec![F::zero(); ROUND_WIDTH];
        let standard_full = keccak_f1600_air::eval_per_row(&cur, &nxt, 0).len();
        standard_full + STATE_BITS
    })
}

// ─── Output extraction from trace ─────────────────────────────────

/// Extract block 0 (initial state's rate bytes) from the layout —
/// not from the trace, since block 0 isn't permuted.
pub fn extract_squeeze_block_0(layout: &SqueezeLayout) -> Vec<u8> {
    let n_rate_lanes = layout.rate_bytes / 8;
    let mut out = Vec::with_capacity(layout.rate_bytes);
    for i in 0..n_rate_lanes {
        out.extend_from_slice(&layout.initial_state[i].to_le_bytes());
    }
    out
}

/// Extract block `b ∈ [1, n_output_blocks)` from the trace's
/// post-iota cells of round 23 of f1600 call (b - 1).
pub fn extract_squeeze_block(
    trace: &[Vec<F>], layout: &SqueezeLayout, b: usize,
) -> Vec<u8> {
    assert!(b >= 1 && b <= layout.n_f1600_calls,
        "block 0 lives in the layout; blocks 1..=n_f1600_calls in trace");
    let row = (b - 1) * ROUNDS + (ROUNDS - 1);
    let n_rate_lanes = layout.rate_bytes / 8;
    let mut out = Vec::with_capacity(layout.rate_bytes);
    for lane in 0..n_rate_lanes {
        let mut lane_bytes = [0u8; 8];
        for byte_i in 0..8 {
            let mut byte = 0u8;
            for bit in 0..8 {
                let global_bit = byte_i * 8 + bit;
                let col = post_iota_col(lane % 5, lane / 5, global_bit);
                let v = trace[col][row];
                let bv = if v.is_zero() { 0 } else { 1 };
                byte |= bv << bit;
            }
            lane_bytes[byte_i] = byte;
        }
        out.extend_from_slice(&lane_bytes);
    }
    out
}

/// Concatenate all output blocks (block 0 from layout, blocks
/// 1..n_f1600_calls from trace).  Returned length =
/// `(n_f1600_calls + 1) * rate_bytes`.
pub fn extract_full_squeeze_from_trace(
    trace: &[Vec<F>], layout: &SqueezeLayout,
) -> Vec<u8> {
    let mut out = extract_squeeze_block_0(layout);
    for b in 1..=layout.n_f1600_calls {
        out.extend_from_slice(&extract_squeeze_block(trace, layout, b));
    }
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa_shake_absorb_air;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Compose absorb (T1) + squeeze (T2) natively; cross-check
    /// against sha3::Shake256 for a multi-block read from a short M.
    #[test]
    fn native_absorb_then_squeeze_matches_sha3_shake256() {
        let m: &[u8] = b"mmiyc/v2/T2/squeeze-multi-block-test";

        // Absorb single-block (T1's path).
        let initial = ml_dsa_shake_absorb_air::build_absorbed_state(
            m, SHAKE_256_RATE_BYTES,
        );
        let mut post_absorb = initial;
        keccak_f1600::keccak_f(&mut post_absorb);

        // Squeeze 5 total blocks (block 0 = post_absorb itself, then 4 more).
        let layout = SqueezeLayout::new(post_absorb, 4, SHAKE_256_RATE_BYTES);
        let ours = squeeze_native(&layout);
        assert_eq!(ours.len(), 5 * SHAKE_256_RATE_BYTES);

        let mut hasher = sha3::Shake256::default();
        hasher.update(m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; 5 * SHAKE_256_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs,
            "T2 native multi-block squeeze must match sha3::Shake256");
    }

    /// Same for SHAKE-128 (the ExpandA case).  ρ ‖ index_byte_0 ‖
    /// index_byte_1 = 34 bytes, 5 squeeze blocks ≈ 840 bytes (more
    /// than enough for one matrix element pre-rejection).
    #[test]
    fn native_absorb_then_squeeze_matches_sha3_shake128_expand_a_shape() {
        let mut m = vec![0u8; 34];
        m[..32].copy_from_slice(&[0x42; 32]);  // synthetic ρ
        m[32] = 1;  // i = 1
        m[33] = 0;  // j = 0

        let initial = ml_dsa_shake_absorb_air::build_absorbed_state(
            &m, SHAKE_128_RATE_BYTES,
        );
        let mut post_absorb = initial;
        keccak_f1600::keccak_f(&mut post_absorb);

        let layout = SqueezeLayout::new(post_absorb, 4, SHAKE_128_RATE_BYTES);
        let ours = squeeze_native(&layout);
        assert_eq!(ours.len(), 5 * SHAKE_128_RATE_BYTES);

        let mut hasher = sha3::Shake128::default();
        hasher.update(&m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; 5 * SHAKE_128_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs,
            "T2 native multi-block squeeze must match sha3::Shake128 (ExpandA path)");
    }

    /// Honest trace: every per-row constraint is zero across all
    /// active rows of a multi-f1600 squeeze trace.
    #[test]
    fn honest_squeeze_trace_satisfies_constraints() {
        let m: &[u8] = b"mmiyc/v2/T2/honest-trace";
        let initial = ml_dsa_shake_absorb_air::build_absorbed_state(
            m, SHAKE_256_RATE_BYTES,
        );
        let mut post_absorb = initial;
        keccak_f1600::keccak_f(&mut post_absorb);

        let layout = SqueezeLayout::new(post_absorb, 3, SHAKE_256_RATE_BYTES);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        for row in 0..layout.active_rows() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, &layout);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T2 constraint {i} on row {row} (block {}) not zero: {v:?}",
                    row / ROUNDS);
            }
        }
    }

    /// AIR-side trace produces same squeeze stream as the native
    /// reference.  Closes the AIR-vs-native loop for multi-block
    /// squeeze.
    #[test]
    fn trace_squeeze_matches_native_squeeze() {
        let m: &[u8] = b"mmiyc/v2/T2/trace-vs-native";
        let initial = ml_dsa_shake_absorb_air::build_absorbed_state(
            m, SHAKE_256_RATE_BYTES,
        );
        let mut post_absorb = initial;
        keccak_f1600::keccak_f(&mut post_absorb);

        let layout = SqueezeLayout::new(post_absorb, 4, SHAKE_256_RATE_BYTES);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        let from_trace = extract_full_squeeze_from_trace(&trace, &layout);
        let from_native = squeeze_native(&layout);
        assert_eq!(from_trace, from_native,
            "T2 trace squeeze must match native squeeze");
    }

    /// Combined absorb+squeeze: AIR-side output for `m` should match
    /// `sha3::Shake256` of the same input for an arbitrary read length.
    #[test]
    fn trace_squeeze_matches_sha3_shake256_full_loop() {
        let m: &[u8] = b"mmiyc/v2/T2/full-shake-loop";
        let initial = ml_dsa_shake_absorb_air::build_absorbed_state(
            m, SHAKE_256_RATE_BYTES,
        );
        let mut post_absorb = initial;
        keccak_f1600::keccak_f(&mut post_absorb);

        let layout = SqueezeLayout::new(post_absorb, 6, SHAKE_256_RATE_BYTES);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        let from_trace = extract_full_squeeze_from_trace(&trace, &layout);

        let mut hasher = sha3::Shake256::default();
        hasher.update(m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; 7 * SHAKE_256_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(from_trace, theirs,
            "T2 trace must match sha3::Shake256 for full absorb+squeeze loop");
    }

    /// Tampering with a STATE_IN bit at the start of block 1 must
    /// surface as a non-zero passthrough chain constraint at the
    /// boundary between block 0 and block 1.
    #[test]
    fn tampered_inter_block_chain_breaks_passthrough_constraint() {
        let m: &[u8] = b"mmiyc/v2/T2/tamper-test";
        let initial = ml_dsa_shake_absorb_air::build_absorbed_state(
            m, SHAKE_256_RATE_BYTES,
        );
        let mut post_absorb = initial;
        keccak_f1600::keccak_f(&mut post_absorb);

        let layout = SqueezeLayout::new(post_absorb, 3, SHAKE_256_RATE_BYTES);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        // Flip block 1's STATE_IN bit so it no longer equals
        // post_iota of block 0.
        let target_row = ROUNDS;
        let target_col = state_in_col(0, 0, 0);
        let original = trace[target_col][target_row];
        trace[target_col][target_row] = F::from(1u64) - original;

        // Boundary at row 23 (last round of block 0) references nxt =
        // row 24 (block 1's first round); the passthrough constraint
        // should fire.
        let row = ROUNDS - 1;
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
        let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
        let cvals = eval_per_row(&cur, &nxt, row, &layout);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero,
            "T2 boundary passthrough chain must reject a tampered inter-block state");
    }
}
