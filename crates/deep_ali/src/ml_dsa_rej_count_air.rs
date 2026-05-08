//! T3a brick: **rejection-sampling cumulative-count AIR**.
//!
//! Extends `ml_dsa_rej_chunk_air` (per-chunk accept/reject) with a
//! cumulative-count column.  After processing N chunks, the count
//! column at row N − 1 holds the total number of accepted elements
//! seen so far.  The composing AIR (full ExpandA / SampleInBall)
//! can then identify the row at which the 256th (or τth) accept
//! occurred and bind the polynomial output cells to those rows.
//!
//! ## Trace layout
//!
//! Width = `ml_dsa_rej_chunk_air::WIDTH + 1` (the new `count`
//! column lives at the end).  Each row holds:
//! - All 50 columns of the per-chunk AIR (24 input bits, u, accept,
//!   slack, 23 slack bits).
//! - `count`: cumulative number of accepts in rows `0..=row`.
//!
//! ## Constraints
//!
//! - All 51 per-chunk constraints from `ml_dsa_rej_chunk_air`,
//!   verbatim.
//! - **Boundary** at row 0: `count[0] = accept[0]` (cumulative
//!   count after row 0 equals row 0's accept).
//! - **Transition** at row r ∈ [0, n − 2]:
//!   `count[r + 1] − count[r] − accept[r + 1] = 0`.
//!
//! Total: 51 + 1 boundary + 1 transition = **52 constraints/row**
//! at the boundary, **53 constraints/row** otherwise.  We pad both
//! to 53 with zero-fillers for cardinality uniformity.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::ml_dsa_rej_chunk_air::{
    self,
    COL_ACCEPT as CHUNK_COL_ACCEPT,
    NUM_CONSTRAINTS as CHUNK_NUM_CONSTRAINTS,
    WIDTH as CHUNK_WIDTH,
};

pub const COL_COUNT: usize = CHUNK_WIDTH;            // 50
pub const WIDTH:     usize = CHUNK_WIDTH + 1;        // 51

pub const NUM_CONSTRAINTS: usize =
    CHUNK_NUM_CONSTRAINTS  // 51
  + 1                      // boundary at row 0 (count[0] = accept[0])
  + 1;                     // transition (count[r+1] = count[r] + accept[r+1])

// ─── fill_trace ───────────────────────────────────────────────────

pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, chunks: &[(u8, u8, u8)]) {
    assert_eq!(trace.len(), WIDTH);
    assert!(chunks.len() <= n_trace);

    // Delegate the per-chunk columns (0..CHUNK_WIDTH) to the chunk AIR.
    let mut chunk_sub: Vec<Vec<F>> = (0..CHUNK_WIDTH)
        .map(|_| vec![F::zero(); n_trace]).collect();
    ml_dsa_rej_chunk_air::fill_trace(&mut chunk_sub, n_trace, chunks);
    for c in 0..CHUNK_WIDTH {
        for r in 0..n_trace {
            trace[c][r] = chunk_sub[c][r];
        }
    }

    // Cumulative count column: count[r] = sum_{k=0..=r} accept[k].
    let mut running: u64 = 0;
    for (r, &(b0, b1, b2)) in chunks.iter().enumerate() {
        let (_u, accept, _s) = ml_dsa_rej_chunk_air::parse_chunk(b0, b1, b2);
        if accept { running += 1; }
        trace[COL_COUNT][r] = F::from(running);
    }
    // Padding rows: count stays at the final value (so transition
    // constraint at the boundary nxt = padding sees `accept = 0`
    // and `count_padding = count_final`, satisfying the relation
    // trivially since padding rows have `accept = 0`).
    for r in chunks.len()..n_trace {
        trace[COL_COUNT][r] = F::from(running);
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

pub fn eval_per_row(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);

    // 1. Per-chunk constraints (delegate to chunk AIR).
    let chunk_view: Vec<F> = (0..CHUNK_WIDTH).map(|c| cur[c]).collect();
    let chunk_nxt:  Vec<F> = (0..CHUNK_WIDTH).map(|c| nxt[c]).collect();
    out.extend(ml_dsa_rej_chunk_air::eval_per_row(&chunk_view, &chunk_nxt, row));

    // 2. Boundary at row 0: count[0] = accept[0].
    if row == 0 {
        out.push(cur[COL_COUNT] - cur[CHUNK_COL_ACCEPT]);
    } else {
        out.push(F::zero());
    }

    // 3. Transition: count[r+1] − count[r] − accept[r+1] = 0.
    //    Applied at every row r (cur = row r, nxt = row r+1).
    out.push(nxt[COL_COUNT] - cur[COL_COUNT] - nxt[CHUNK_COL_ACCEPT]);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::{Q, N};
    use crate::ml_dsa_codec;
    use crate::ml_dsa_shake_absorb_air::{
        self, build_absorbed_state, SHAKE_128_RATE_BYTES,
    };
    use crate::ml_dsa_shake_squeeze_air::{
        self, squeeze_native, SqueezeLayout,
    };
    use crate::keccak_f1600;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Pull `n_bytes` of SHAKE-128 XOF output for `m`, using the AIR
    /// primitives' native helpers (build_absorbed_state + squeeze_native).
    /// This is the path the future T3a AIR will compose in-circuit.
    fn shake_128_via_primitives(m: &[u8], n_bytes: usize) -> Vec<u8> {
        // Single-block absorb: m must fit in one rate (covers
        // ExpandA's 34-byte input).
        assert!(m.len() < SHAKE_128_RATE_BYTES);
        let absorbed = build_absorbed_state(m, SHAKE_128_RATE_BYTES);
        let mut post_absorb = absorbed;
        keccak_f1600::keccak_f(&mut post_absorb);

        // Squeeze enough rate-blocks: block 0 = post_absorb itself,
        // each additional f1600 yields another block.
        let n_blocks_total = n_bytes.div_ceil(SHAKE_128_RATE_BYTES);
        let n_extra = n_blocks_total.saturating_sub(1);
        let layout = SqueezeLayout::new(post_absorb, n_extra, SHAKE_128_RATE_BYTES);
        let mut out = squeeze_native(&layout);
        out.truncate(n_bytes);
        out
    }

    /// **End-to-end native cross-check**: T1 absorb + T2 squeeze +
    /// chunk parser produces the same `Â[i][j]` polynomial as
    /// `ml_dsa_codec::expand_a` for several ρ seeds.  Validates the
    /// T1+T2+T3 primitive composition is structurally correct for
    /// ExpandA.
    #[test]
    fn native_t1_t2_t3_chain_matches_expand_a() {
        for seed in 0u64..3 {
            let mut rho = [0u8; 32];
            // Deterministic ρ from the seed for reproducibility.
            let mut hasher = sha3::Shake256::default();
            hasher.update(b"mmiyc/v2/T3a/rho-seed");
            hasher.update(&seed.to_le_bytes());
            let mut reader = hasher.finalize_xof();
            reader.read(&mut rho);

            let expected = ml_dsa_codec::expand_a(&rho);

            for i in 0..2u8 {  // K = 4 in ML-DSA-44; test 2 to keep the test fast.
                for j in 0..2u8 {
                    // Replicate FIPS 204 §3.4 byte order: ρ ‖ j ‖ i.
                    let mut m = [0u8; 34];
                    m[..32].copy_from_slice(&rho);
                    m[32] = j;
                    m[33] = i;

                    // Squeeze enough bytes for safe rejection-sampling.
                    // 8 blocks × 168 bytes = 1344 bytes = 448 chunks ≫ 256.
                    let stream = shake_128_via_primitives(&m, 8 * SHAKE_128_RATE_BYTES);

                    // RejNTTPoly: read 3-byte chunks, accept iff < q.
                    let mut poly = [0u32; N];
                    let mut count = 0;
                    let mut pos = 0;
                    while count < N && pos + 3 <= stream.len() {
                        let (u, accept, _s) = ml_dsa_rej_chunk_air::parse_chunk(
                            stream[pos], stream[pos + 1], stream[pos + 2],
                        );
                        if accept { poly[count] = u; count += 1; }
                        pos += 3;
                    }
                    assert_eq!(count, N,
                        "ran out of bytes before accepting {N} elements (seed={seed}, i={i}, j={j})");

                    assert_eq!(&poly[..], &expected[i as usize][j as usize][..],
                        "T3a primitive composition mismatch at (seed={seed}, i={i}, j={j})");
                }
            }
        }
    }

    /// Honest trace: chunk constraints + count-column constraints
    /// hold over a 280-chunk SHAKE-128 stream (worst-case-safe
    /// provisioning for one ExpandA element).
    #[test]
    fn honest_count_trace_satisfies_all_constraints() {
        let mut hasher = sha3::Shake128::default();
        hasher.update(b"mmiyc/v2/T3a/honest-count");
        let mut reader = hasher.finalize_xof();
        let mut bytes = vec![0u8; 280 * 3];
        reader.read(&mut bytes);

        let chunks: Vec<(u8, u8, u8)> = (0..280)
            .map(|k| (bytes[3*k], bytes[3*k + 1], bytes[3*k + 2]))
            .collect();

        let n_trace = 512;  // pow-of-2 ≥ chunks.len()
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &chunks);

        // Reach 256+ accepts well before row 280 (accept rate ~99.9 %).
        let final_count: u64 = {
            let v = trace[COL_COUNT][chunks.len() - 1];
            // Goldilocks → integer extraction via canonical decomposition:
            // for small values (< 2^20), F::from(n) round-trip preserves.
            // Here we use a trial probe.
            let mut x = 0u64;
            for guess in 0..400u64 {
                if F::from(guess) == v { x = guess; break; }
            }
            x
        };
        assert!(final_count >= 256,
            "T3a: 280 chunks should produce ≥ 256 accepts; got {final_count}");

        for row in 0..(chunks.len() - 1) {  // skip last row (no nxt)
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T3a constraint {i} on row {row} not zero: {v:?}");
            }
        }
    }

    /// Tampering: zero out the count column on a row that should
    /// have a positive count.  The transition constraint must fire.
    #[test]
    fn tampered_count_breaks_transition_constraint() {
        let chunks = vec![(0, 0, 0), (1, 0, 0), (2, 0, 0)];  // 3 trivial accepts
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &chunks);

        // Zero out count[1] — should be 2 (accept[0] + accept[1] = 1 + 1).
        // The transition at row 0→1 (count[1] = count[0] + accept[1]) fires.
        trace[COL_COUNT][1] = F::zero();

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][1]).collect();
        let cvals = eval_per_row(&cur, &nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero,
            "T3a tampered count must break the transition constraint");
    }

    /// Tampering at row 0: change count[0] to differ from accept[0].
    /// The boundary constraint must fire.
    #[test]
    fn tampered_count_at_row_zero_breaks_boundary() {
        let chunks = vec![(0u8, 0u8, 0u8)];  // accept = 1
        let n_trace = 2;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &chunks);

        // accept[0] = 1; mess with count[0] (was 1).
        trace[COL_COUNT][0] = F::from(5u64);

        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][1]).collect();
        let cvals = eval_per_row(&cur, &nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero,
            "T3a tampered count[0] must break the boundary constraint");
    }
}
