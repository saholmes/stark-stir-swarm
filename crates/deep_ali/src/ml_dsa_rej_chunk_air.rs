//! T3 brick: **rejection-sampling chunk AIR**.
//!
//! One row = one 3-byte chunk parse + rejection-sampling decision,
//! per FIPS 204 §3.4 ExpandA's `RejNTTPoly` (and the equivalent
//! step in §3.7 SampleInBall, which uses different bit widths but
//! the same shape).
//!
//! ## What it proves
//!
//! Given three input bytes `b₀ ‖ b₁ ‖ b₂` (24 bits, little-endian
//! within and across bytes — the natural SHAKE-128 squeeze byte
//! ordering), the AIR enforces:
//!
//! 1. Bit decomposition: each of the 24 input cells is a boolean.
//! 2. Mask: `u = b₀ + 2⁸·b₁ + 2¹⁶·(b₂ & 0x7F)`, i.e. the low 23
//!    bits of the chunk concatenated as a little-endian integer.
//!    The top bit of `b₂` is dropped (this is FIPS 204 §3.4
//!    Algorithm 33 line 6).
//! 3. Range gating: `accept ∈ {0, 1}` with `accept = 1 ⇔ u < q`.
//!    Encoded via a single slack witness `s ∈ [0, 2²³)` and the
//!    algebraic constraint
//!       `u = q + s·(1 − 2·accept) − accept`,
//!    which solves to:
//!       - `accept = 1, s = q − 1 − u` when `u ∈ [0, q−1]`
//!       - `accept = 0, s = u − q`     when `u ∈ [q, 2²³−1]`.
//!
//! ## Composition path to full ExpandA / SampleInBall
//!
//! The composing AIR (next session) places one chunk row per
//! 3-byte chunk extracted from the SHAKE squeeze stream (T2's
//! output).  Boundary equality constraints link the chunk's input
//! bytes to specific 8-bit groups of post-iota cells.  A separate
//! "running accept counter" column counts accepts; the polynomial
//! output is built by reading `u` cells whose `accept = 1` flag
//! marks them as the n-th accepted element.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa::params::Q;

// ─── Column layout ────────────────────────────────────────────────

/// Number of low-bits of `u` we range-check / bit-decompose: 23
/// (the masked range, since top bit of b₂ is dropped).
pub const U_BITS: usize = 23;
/// Number of bits in the slack witness for the `< q` proof.
pub const SLACK_BITS: usize = 23;
/// Number of input bytes per chunk.  Hardcoded 3 for ExpandA's
/// `RejNTTPoly`; SampleInBall uses different widths and is a
/// separate AIR.
pub const CHUNK_BYTES: usize = 3;
pub const CHUNK_BITS: usize = CHUNK_BYTES * 8;  // 24

#[inline] pub const fn col_input_bit(b: usize) -> usize { b }                      // 0..24
pub const COL_U:        usize = CHUNK_BITS;                                        // 24
pub const COL_ACCEPT:   usize = CHUNK_BITS + 1;                                    // 25
pub const COL_SLACK:    usize = CHUNK_BITS + 2;                                    // 26
#[inline] pub const fn col_slack_bit(b: usize) -> usize { CHUNK_BITS + 3 + b }     // 27..50

pub const WIDTH: usize = CHUNK_BITS + 3 + SLACK_BITS;  // 24 + 3 + 23 = 50

// ─── Constraint count ─────────────────────────────────────────────

pub const NUM_CONSTRAINTS: usize =
    CHUNK_BITS                  // 24 input boolean
  + 1                           // accept boolean
  + SLACK_BITS                  // slack bit booleans
  + 1                           // slack reconstruction
  + 1                           // u reconstruction (low 23 bits)
  + 1;                          // u = q + s·(1 − 2·accept) − accept

// ─── Native helpers ───────────────────────────────────────────────

/// Native parse + reject decision.  Mirrors FIPS 204 §3.4
/// Algorithm 33 lines 5–6: combine 3 bytes (top bit of byte 2
/// masked) into a 23-bit integer, accept iff `< q`.  Returns
/// `(u, accept, slack)`.
pub fn parse_chunk(b0: u8, b1: u8, b2: u8) -> (u32, bool, u32) {
    let masked_b2 = b2 & 0x7F;
    let u = (b0 as u32) | ((b1 as u32) << 8) | ((masked_b2 as u32) << 16);
    let accept = u < Q;
    let slack = if accept { Q - 1 - u } else { u - Q };
    (u, accept, slack)
}

// ─── fill_trace ───────────────────────────────────────────────────

/// One row per chunk.  `chunks[i] = (b0, b1, b2)` for the i-th
/// 3-byte chunk read from the SHAKE squeeze stream.
pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, chunks: &[(u8, u8, u8)]) {
    assert_eq!(trace.len(), WIDTH);
    assert!(chunks.len() <= n_trace);

    for (row, &(b0, b1, b2)) in chunks.iter().enumerate() {
        // Input bit cells (bytes 0, 1, 2 in order, LSB-first within each byte).
        for i in 0..8 {
            trace[col_input_bit(i)][row]      = F::from(((b0 >> i) & 1) as u64);
            trace[col_input_bit(8 + i)][row]  = F::from(((b1 >> i) & 1) as u64);
            trace[col_input_bit(16 + i)][row] = F::from(((b2 >> i) & 1) as u64);
        }

        let (u, accept, slack) = parse_chunk(b0, b1, b2);
        trace[COL_U][row]      = F::from(u as u64);
        trace[COL_ACCEPT][row] = F::from(accept as u64);
        trace[COL_SLACK][row]  = F::from(slack as u64);
        for b in 0..SLACK_BITS {
            trace[col_slack_bit(b)][row] = F::from(((slack >> b) & 1) as u64);
        }
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

pub fn eval_per_row(cur: &[F], _nxt: &[F], _row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();
    let q = F::from(Q as u64);

    // 1. Input bit booleans (24 of them).
    for b in 0..CHUNK_BITS {
        let v = cur[col_input_bit(b)];
        out.push(v * (v - one));
    }

    // 2. accept boolean.
    let accept = cur[COL_ACCEPT];
    out.push(accept * (accept - one));

    // 3. slack bit booleans (23 of them).
    for b in 0..SLACK_BITS {
        let v = cur[col_slack_bit(b)];
        out.push(v * (v - one));
    }

    // 4. slack reconstruction: slack_value = Σ slack_bit_i · 2^i.
    {
        let mut acc = F::zero();
        let mut pow = F::one();
        let two = F::from(2u64);
        for b in 0..SLACK_BITS {
            acc += cur[col_slack_bit(b)] * pow;
            pow *= two;
        }
        let slack = cur[COL_SLACK];
        out.push(slack - acc);
    }

    // 5. u reconstruction: u = Σ_{b ∈ 0..23} input_bit_b · 2^b.
    //    The 24th bit (top of b₂) is dropped (the FIPS 204 mask).
    {
        let mut acc = F::zero();
        let mut pow = F::one();
        let two = F::from(2u64);
        for b in 0..U_BITS {
            acc += cur[col_input_bit(b)] * pow;
            pow *= two;
        }
        let u = cur[COL_U];
        out.push(u - acc);
    }

    // 6. Range gate: u = q + s·(1 − 2·accept) − accept.
    //    Solves to:
    //      accept = 1 ⇒ u = q − 1 − s ⇒ s = q − 1 − u, range [0, q − 1].
    //      accept = 0 ⇒ u = q + s     ⇒ s = u − q,     range [0, 2²³ − q].
    {
        let u = cur[COL_U];
        let s = cur[COL_SLACK];
        let two = F::from(2u64);
        // u = q + s − 2·s·accept − accept  ⇔  u − q − s + 2·s·accept + accept = 0
        let expr = u - q - s + two * s * accept + accept;
        out.push(expr);
    }

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
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

    /// `parse_chunk` mask + accept logic on hand-picked vectors.
    #[test]
    fn parse_chunk_known_vectors() {
        // u = 0: accept, slack = q − 1.
        let (u, acc, s) = parse_chunk(0, 0, 0);
        assert_eq!((u, acc, s), (0, true, Q - 1));

        // u = q − 1: still accepts; slack = 0.
        let q_m1 = Q - 1;
        let b0 = (q_m1 & 0xFF) as u8;
        let b1 = ((q_m1 >> 8) & 0xFF) as u8;
        let b2 = ((q_m1 >> 16) & 0xFF) as u8;  // top bit clear since q − 1 < 2²³
        let (u, acc, s) = parse_chunk(b0, b1, b2);
        assert_eq!((u, acc, s), (q_m1, true, 0));

        // u = q: rejects; slack = 0.
        let b0 = (Q & 0xFF) as u8;
        let b1 = ((Q >> 8) & 0xFF) as u8;
        let b2 = ((Q >> 16) & 0xFF) as u8;
        let (u, acc, s) = parse_chunk(b0, b1, b2);
        assert_eq!((u, acc, s), (Q, false, 0));

        // Top-bit-set example: 0xFF_FF_FF — high bit of b₂ is masked
        // out, so u = 0x7F_FF_FF.  Since 2²³ − 1 > q, it rejects.
        let (u, acc, s) = parse_chunk(0xFF, 0xFF, 0xFF);
        assert_eq!(u, 0x7F_FF_FF);
        assert_eq!(acc, false);
        assert_eq!(s, 0x7F_FF_FF - Q);
    }

    /// Honest trace satisfies every per-row constraint for a span of
    /// chunks covering both accept and reject paths.  Synthesise
    /// chunks from a SHAKE-128 stream over 0xFF·168 (likely to span
    /// both regimes due to mask + threshold).
    #[test]
    fn honest_trace_satisfies_all_constraints() {
        // Pull bytes from sha3 to get a realistic byte stream with
        // both accept and reject outcomes.
        let mut hasher = sha3::Shake128::default();
        hasher.update(b"mmiyc/v2/T3/honest-trace");
        let mut reader = hasher.finalize_xof();
        let mut bytes = vec![0u8; 600];
        reader.read(&mut bytes);

        let mut chunks: Vec<(u8, u8, u8)> = Vec::new();
        for k in 0..200 {
            chunks.push((bytes[3*k], bytes[3*k + 1], bytes[3*k + 2]));
        }
        // Sanity: at q ≈ 8.38M and 2²³ ≈ 8.39M, accept rate is
        // ~99.9% (1 reject per 1024 chunks on average), so 200
        // chunks may have 0 or 1 rejects.  We assert ≥99 % to catch
        // gross errors; both branches of the algebraic gate are
        // exercised by `both_accept_and_reject_satisfied`.
        let n_accept = chunks.iter()
            .filter(|&&(b0, b1, b2)| parse_chunk(b0, b1, b2).1)
            .count();
        assert!(n_accept * 100 >= chunks.len() * 99,
            "test stream produced {n_accept} accepts in {} chunks; \
             expected ≥99 % accept rate", chunks.len());

        let n_trace = chunks.len().next_power_of_two();
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &chunks);

        for row in 0..chunks.len() {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
            let cvals = eval_per_row(&cur, &dummy_nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T3 constraint {i} on row {row} not zero (chunk {:?}): {v:?}",
                    chunks[row]);
            }
        }
    }

    /// Tampering: flip the accept flag on a row that legitimately
    /// accepts.  The slack value no longer matches the algebraic
    /// constraint, so something must fire.
    #[test]
    fn tampered_accept_flag_breaks_constraint() {
        let chunks = vec![(0u8, 0u8, 0u8)];  // u = 0, accept legitimately.
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &chunks);

        // Force accept = 0 on a row that should accept.  The slack
        // we've written assumes accept = 1; the algebraic gate must
        // surface the mismatch.
        trace[COL_ACCEPT][0] = F::zero();

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
        let cvals = eval_per_row(&cur, &dummy_nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "T3 must reject a tampered accept flag");
    }

    /// Tampering: flip a slack bit on a legitimate accept row —
    /// the slack reconstruction OR the algebraic gate must fail.
    #[test]
    fn tampered_slack_bit_breaks_constraint() {
        let chunks = vec![(0u8, 0u8, 0u8)];
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &chunks);

        let target_col = col_slack_bit(0);
        trace[target_col][0] = F::one() - trace[target_col][0];

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
        let cvals = eval_per_row(&cur, &dummy_nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "T3 must reject a tampered slack bit");
    }

    /// Confirm both accept and reject happy-paths satisfy all
    /// constraints in isolation (covering the algebraic gate's
    /// branch by way of `accept ∈ {0, 1}`).
    #[test]
    fn both_accept_and_reject_satisfied() {
        // accept-path: u = 0.
        let (b0, b1, b2) = (0u8, 0u8, 0u8);
        let mut trace = fresh_trace(4);
        fill_trace(&mut trace, 4, &[(b0, b1, b2)]);
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let dummy_nxt: Vec<F> = (0..WIDTH).map(|_| F::zero()).collect();
        let cvals = eval_per_row(&cur, &dummy_nxt, 0);
        for v in &cvals { assert!(v.is_zero(), "accept-path: {v:?}"); }

        // reject-path: u = q (rejects exactly at the threshold).
        let b0 = (Q & 0xFF) as u8;
        let b1 = ((Q >> 8) & 0xFF) as u8;
        let b2 = ((Q >> 16) & 0xFF) as u8;
        let mut trace = fresh_trace(4);
        fill_trace(&mut trace, 4, &[(b0, b1, b2)]);
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let cvals = eval_per_row(&cur, &dummy_nxt, 0);
        for v in &cvals { assert!(v.is_zero(), "reject-path: {v:?}"); }
    }
}
