//! T1.5: **multi-block SHAKE absorb AIR**.
//!
//! Generalises `ml_dsa_shake_absorb_air` (single-block) to messages
//! of arbitrary length.  The padded input is split into `N` blocks
//! of `rate_bytes` each; the `N` Keccak-f permutations are stacked
//! vertically (one block per 24-row sub-trace), with a chaining
//! boundary constraint linking each block's `post_iota` to the next
//! block's `state_in` via XOR with the new block's padded bytes.
//!
//! ## Trace layout
//!
//! `N · 24` active rows.  Each row has the same column shape as
//! `keccak_f1600_air` (ROUND_WIDTH columns).  No extra columns are
//! needed: the per-block "input mask" is a public-input constant
//! that the verifier reconstructs from `M` and bakes into the
//! row-dependent boundary constraint formula.
//!
//! ## Per-row constraints
//!
//! At every row `r ∈ [0, 24·N)`:
//!
//! 1. **In-block round constraints** (from `keccak_f1600_air`):
//!    boolean, θ, ρ-π, χ, ι.  Same as single-block.
//!
//! 2. **In-block round chain** (rounds 0..22 of each block):
//!    `nxt[STATE_IN][bit] − cur[POST_IOTA][bit] = 0`.
//!
//! 3. **Block-boundary chain** (row `24·b + 23` for each `b ∈
//!    [0, N − 1)`):
//!    `nxt[STATE_IN][bit] − cur[POST_IOTA][bit] − M_BIT(b+1)[bit] +
//!    2·cur[POST_IOTA][bit]·M_BIT(b+1)[bit] = 0`,
//!    i.e. `state_in_{b+1} = post_iota_b ⊕ block_{b+1}_padded`.
//!    For capacity bits, `M_BIT(b+1)[bit] = 0`, reducing to the
//!    standard equality.
//!
//! At row `24·b + 23` of the LAST block (b = N − 1), no transition
//! constraint fires.  Padding rows (≥ 24·N) emit zero-fillers.
//!
//! ## Boundary at row 0
//!
//! `state_in[bit]` at row 0 must equal `(block_0_padded || 0^c)[bit]`.
//! This is enforced by PI-hash binding (the verifier reconstructs
//! `block_0_padded` from `M` and includes the corresponding lane
//! values in the public-input transcript), not by an internal
//! constraint here.  The composition pattern matches v1.7's binding
//! of `z_cleartext` and `z_ntt`.

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

/// Public-input descriptor passed into `eval_per_row` and
/// `fill_trace`.  Carries the message + rate so that boundary
/// constraints can be formed.
#[derive(Clone)]
pub struct MultiAbsorbLayout {
    pub m_bytes: Vec<u8>,
    pub rate_bytes: usize,
    pub n_blocks: usize,
    /// Padded form of M, length `n_blocks * rate_bytes`.
    pub padded: Vec<u8>,
}

impl MultiAbsorbLayout {
    pub fn new(m_bytes: &[u8], rate_bytes: usize) -> Self {
        assert!(rate_bytes % 8 == 0, "rate must be a multiple of 8 bytes");
        // padded length = smallest multiple of rate ≥ m_bytes + 1
        // (the +1 is for the suffix byte 0x1F).  This always leaves
        // room for the trailing 0x80 — which may overlap with the
        // suffix byte if m_bytes ≡ rate − 1 (mod rate), giving 0x9F.
        let padded_total = ((m_bytes.len() + 1 + rate_bytes - 1) / rate_bytes) * rate_bytes;
        let n_blocks = padded_total / rate_bytes;

        let mut padded = vec![0u8; padded_total];
        padded[..m_bytes.len()].copy_from_slice(m_bytes);
        padded[m_bytes.len()] |= 0x1F;
        padded[padded_total - 1] |= 0x80;

        Self { m_bytes: m_bytes.to_vec(), rate_bytes, n_blocks, padded }
    }

    /// Bytes of block `b`'s padded contribution (`rate_bytes` long).
    pub fn block_bytes(&self, b: usize) -> &[u8] {
        let start = b * self.rate_bytes;
        let end = start + self.rate_bytes;
        &self.padded[start..end]
    }

    /// Bit `bit ∈ [0, STATE_BITS)` of block `b`'s padded contribution
    /// XOR'd into the state.  For rate bits, returns the corresponding
    /// bit of the padded block; for capacity bits, returns 0.
    ///
    /// Lane order: bit `i` corresponds to lane `i / 64`, in-lane bit
    /// `i % 64` (LSB-first).
    pub fn mask_bit(&self, b: usize, bit: usize) -> u8 {
        debug_assert!(bit < STATE_BITS);
        let n_rate_bits = self.rate_bytes * 8;
        if bit >= n_rate_bits {
            return 0;
        }
        let block = self.block_bytes(b);
        let byte_in_block = bit / 8;
        let bit_in_byte = bit % 8;
        (block[byte_in_block] >> bit_in_byte) & 1
    }

    /// Total active rows in the trace (one Keccak-f per block).
    pub fn active_rows(&self) -> usize {
        self.n_blocks * ROUNDS
    }
}

// ─── Native helpers ───────────────────────────────────────────────

/// Run multi-block absorb natively, returning the post-permutation
/// state after the last block.
pub fn absorb_native(layout: &MultiAbsorbLayout) -> [u64; NUM_LANES] {
    let mut state = [0u64; NUM_LANES];
    let n_rate_lanes = layout.rate_bytes / 8;
    for b in 0..layout.n_blocks {
        let block = layout.block_bytes(b);
        for i in 0..n_rate_lanes {
            let mut lane = [0u8; 8];
            lane.copy_from_slice(&block[i * 8..(i + 1) * 8]);
            state[i] ^= u64::from_le_bytes(lane);
        }
        keccak_f1600::keccak_f(&mut state);
    }
    state
}

/// Native first-squeeze: the rate-byte prefix of the absorb output.
pub fn extract_first_squeeze_native(layout: &MultiAbsorbLayout) -> Vec<u8> {
    let state = absorb_native(layout);
    let n_rate_lanes = layout.rate_bytes / 8;
    let mut out = Vec::with_capacity(layout.rate_bytes);
    for i in 0..n_rate_lanes {
        out.extend_from_slice(&state[i].to_le_bytes());
    }
    out
}

// ─── fill_trace ───────────────────────────────────────────────────

/// Drive the absorb-then-permute path for `n_blocks` Keccak-f calls,
/// recording the trace.
pub fn fill_trace(
    trace: &mut [Vec<F>],
    n_trace: usize,
    layout: &MultiAbsorbLayout,
) {
    assert_eq!(trace.len(), WIDTH);
    assert!(n_trace >= layout.active_rows());

    let n_rate_lanes = layout.rate_bytes / 8;
    let mut state = [0u64; NUM_LANES];

    for b in 0..layout.n_blocks {
        // XOR block b into the rate portion of state.
        let block = layout.block_bytes(b);
        for i in 0..n_rate_lanes {
            let mut lane = [0u8; 8];
            lane.copy_from_slice(&block[i * 8..(i + 1) * 8]);
            state[i] ^= u64::from_le_bytes(lane);
        }

        // Drive 24 rounds of f1600 into rows 24b..24b+23.  We use a
        // local sub-trace and then translate.  (keccak_f1600_air's
        // fill_trace assumes row 0 is the start of the call; we
        // remap by writing rows 24b+r explicitly.)
        let mut sub: Vec<Vec<F>> = (0..ROUND_WIDTH)
            .map(|_| vec![F::zero(); ROUNDS]).collect();
        keccak_f1600_air::fill_trace(&mut sub, ROUNDS, &state);

        let base = b * ROUNDS;
        for r in 0..ROUNDS {
            for c in 0..ROUND_WIDTH {
                trace[c][base + r] = sub[c][r];
            }
        }

        // Update state_chain to this block's final post_iota.
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

/// Per-row constraints.
///
/// `row` is the global row index in `[0, n_blocks * 24)` (or
/// `>=` for padding rows).  `layout` carries the per-block input
/// mask values that drive the inter-block boundary constraint.
pub fn eval_per_row(
    cur: &[F],
    nxt: &[F],
    row: usize,
    layout: &MultiAbsorbLayout,
) -> Vec<F> {
    let mut out = Vec::new();
    let active_rows = layout.active_rows();

    if row >= active_rows {
        // Padding row: emit no live constraints.  Cardinality is
        // matched by the largest active-row eval (the round-23
        // boundary case below).
        let max_card = num_constraints(layout);
        for _ in 0..max_card { out.push(F::zero()); }
        return out;
    }

    let in_block_round = row % ROUNDS;
    let block_idx = row / ROUNDS;
    let is_last_round_of_block = in_block_round == ROUNDS - 1;
    let is_last_block = block_idx == layout.n_blocks - 1;

    // 1. Standard f1600 round constraints (boolean, θ, ρ-π, χ, ι),
    //    plus the in-block chain for rounds 0..22.  At round 23 the
    //    standard eval omits the chain; pad with STATE_BITS zeros so
    //    every row's "post-standard" length is uniform.
    let standard = keccak_f1600_air::eval_per_row(cur, nxt, in_block_round);
    out.extend(standard);
    if in_block_round == ROUNDS - 1 {
        for _ in 0..STATE_BITS { out.push(F::zero()); }
    }

    // 2. Block-boundary chain at row 24·b + 23 for b < n_blocks - 1:
    //    nxt[STATE_IN][bit] = cur[POST_IOTA][bit] ⊕ M_BIT(b+1)[bit]
    //    For capacity bits: M_BIT(b+1)[bit] = 0, so equality.
    //    XOR(a, b) = a + b − 2ab, so constraint:
    //      nxt[s] − (cur[p] + M − 2 cur[p] M) = 0
    //    where M ∈ {0, 1} is a public-input-derived constant.
    if is_last_round_of_block && !is_last_block {
        let next_block = block_idx + 1;
        for c_off in 0..STATE_BITS {
            let m: u64 = layout.mask_bit(next_block, c_off) as u64;
            let pi = cur[cols::POST_IOTA_BASE + c_off];
            let nx = nxt[cols::STATE_IN_BASE + c_off];
            let m_f = F::from(m);
            let two = F::from(2u64);
            let xor_val = pi + m_f - two * pi * m_f;
            out.push(nx - xor_val);
        }
    } else {
        // Cardinality filler: emit STATE_BITS zero constraints so
        // every row returns the same number of constraints (FRI
        // requires constant-cardinality eval).
        for _ in 0..STATE_BITS {
            out.push(F::zero());
        }
    }

    debug_assert_eq!(out.len(), num_constraints(layout));
    out
}

/// Cardinality of the per-row constraint vector.  Equal to the
/// standard f1600 per-row constraint count + STATE_BITS for the
/// boundary slot (filled with zeros on rows that don't have an
/// inter-block transition).
pub fn num_constraints(_layout: &MultiAbsorbLayout) -> usize {
    keccak_per_row_constraints() + STATE_BITS
}

/// Empirical f1600 per-row constraint count.  `keccak_f1600_air`
/// doesn't expose a `NUM_CONSTRAINTS` constant, but the count is
/// deterministic given the AIR shape; we measure via a probe call.
fn keccak_per_row_constraints() -> usize {
    use std::sync::OnceLock;
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        let cur = vec![F::zero(); ROUND_WIDTH];
        let nxt = vec![F::zero(); ROUND_WIDTH];
        // Probe at row 0 (chain emitted) to get the maximum count.
        keccak_f1600_air::eval_per_row(&cur, &nxt, 0).len()
    })
}

// ─── Squeeze extraction from trace ────────────────────────────────

pub fn extract_first_squeeze_from_trace(
    trace: &[Vec<F>],
    layout: &MultiAbsorbLayout,
) -> Vec<u8> {
    let last_block = layout.n_blocks - 1;
    let last_row = last_block * ROUNDS + (ROUNDS - 1);
    let n_rate_lanes = layout.rate_bytes / 8;
    let mut out = Vec::with_capacity(layout.rate_bytes);
    for lane in 0..n_rate_lanes {
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
        out.extend_from_slice(&lane_bytes);
    }
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Layout sanity: m_bytes < rate ⇒ n_blocks = 1 (subsumes T1).
    #[test]
    fn layout_single_block_for_short_m() {
        let layout = MultiAbsorbLayout::new(&[0x42u8; 32], SHAKE_256_RATE_BYTES);
        assert_eq!(layout.n_blocks, 1);
        assert_eq!(layout.padded.len(), SHAKE_256_RATE_BYTES);
    }

    /// Layout sanity: m_bytes exactly = rate ⇒ n_blocks = 2 (need an
    /// extra padding-only block).
    #[test]
    fn layout_two_blocks_when_m_is_exactly_rate() {
        let m = vec![0u8; SHAKE_256_RATE_BYTES];
        let layout = MultiAbsorbLayout::new(&m, SHAKE_256_RATE_BYTES);
        assert_eq!(layout.n_blocks, 2);
        assert_eq!(layout.padded.len(), 2 * SHAKE_256_RATE_BYTES);
        // First block = pure message; second block = suffix + pad.
        assert_eq!(&layout.padded[..SHAKE_256_RATE_BYTES], &m[..]);
        assert_eq!(layout.padded[SHAKE_256_RATE_BYTES], 0x1F);
        assert_eq!(layout.padded[2 * SHAKE_256_RATE_BYTES - 1], 0x80);
    }

    /// Native multi-block absorb of a 256-byte M against
    /// `sha3::Shake256` (matches the well-tested upstream impl).
    #[test]
    fn native_multi_block_matches_sha3_shake256_256_bytes() {
        let m: Vec<u8> = (0u32..256u32).map(|i| i as u8).collect();
        let layout = MultiAbsorbLayout::new(&m, SHAKE_256_RATE_BYTES);
        assert!(layout.n_blocks >= 2);

        let ours = extract_first_squeeze_native(&layout);

        let mut hasher = sha3::Shake256::default();
        hasher.update(&m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; SHAKE_256_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs, "T1.5 native multi-block must match sha3::Shake256");
    }

    /// Multi-block on SHAKE-128 (ExpandA-style: long inputs not
    /// expected, but the mechanism is the same).  500-byte M.
    #[test]
    fn native_multi_block_matches_sha3_shake128_500_bytes() {
        let m: Vec<u8> = (0u32..500u32).map(|i| (i as u8).wrapping_mul(7)).collect();
        let layout = MultiAbsorbLayout::new(&m, SHAKE_128_RATE_BYTES);
        assert!(layout.n_blocks >= 2);

        let ours = extract_first_squeeze_native(&layout);

        let mut hasher = sha3::Shake128::default();
        hasher.update(&m);
        let mut reader = hasher.finalize_xof();
        let mut theirs = vec![0u8; SHAKE_128_RATE_BYTES];
        reader.read(&mut theirs);

        assert_eq!(ours, theirs, "T1.5 native multi-block must match sha3::Shake128");
    }

    /// Honest trace: every per-row constraint is zero across all
    /// active rows of a multi-block trace.
    #[test]
    fn honest_multi_block_trace_satisfies_constraints() {
        let m: Vec<u8> = (0u32..200u32).map(|i| i as u8).collect();
        let layout = MultiAbsorbLayout::new(&m, SHAKE_256_RATE_BYTES);
        assert_eq!(layout.n_blocks, 2);

        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        for row in 0..layout.active_rows() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, &layout);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T1.5 constraint {i} on row {row} (block {}) not zero: {v:?}",
                    row / ROUNDS);
            }
        }
    }

    /// Final post-iota of the LAST block must match native multi-block
    /// absorb's first-rate-bytes squeeze.
    #[test]
    fn trace_final_squeeze_matches_native() {
        let m: Vec<u8> = (0u32..200u32).map(|i| i as u8).collect();
        let layout = MultiAbsorbLayout::new(&m, SHAKE_256_RATE_BYTES);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        let from_trace = extract_first_squeeze_from_trace(&trace, &layout);
        let from_native = extract_first_squeeze_native(&layout);
        assert_eq!(from_trace, from_native,
            "T1.5 trace post-iota must match native multi-block absorb");
    }

    /// Tampering with the second block's input mask (by flipping a
    /// post_iota bit on the LAST round of block 0) must surface as a
    /// non-zero boundary constraint.
    #[test]
    fn tampered_inter_block_chain_breaks_boundary_constraint() {
        let m: Vec<u8> = (0u32..200u32).map(|i| i as u8).collect();
        let layout = MultiAbsorbLayout::new(&m, SHAKE_256_RATE_BYTES);
        let n_trace = layout.active_rows().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &layout);

        // Flip block 1's STATE_IN bit so it no longer equals
        // post_iota_block_0 ⊕ block_1_mask.
        let target_row = ROUNDS;  // Row 24 = first round of block 1.
        let target_col = state_in_col(0, 0, 0);
        let original = trace[target_col][target_row];
        trace[target_col][target_row] = F::from(1u64) - original;

        // The boundary constraint at row 23 (last round of block 0)
        // references nxt = row 24 = block 1's first round, so it
        // should fire.
        let row = ROUNDS - 1;
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
        let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][(row + 1) % n_trace]).collect();
        let cvals = eval_per_row(&cur, &nxt, row, &layout);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero,
            "T1.5 boundary chain must reject a tampered inter-block state");
    }
}
