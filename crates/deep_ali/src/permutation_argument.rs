//! T-MEM: **multiset-equality permutation argument**.
//!
//! Standard zk-STARK building block for cross-row cell binding:
//! given two sequences of `(address, value)` pairs — a "writes" log
//! and a "reads" log — prove their multisets are equal.  Used to
//! bind cells across non-adjacent rows of a trace, where deep_ali's
//! per-row evaluator (`eval_per_row(cur, nxt, row)`) can't directly
//! reference both endpoints of the binding.
//!
//! ## Use case (T3c motivation)
//!
//! ExpandA's chunk row at index `c` consumes 24 input bits that
//! must equal specific bytes of a SHAKE-128 squeeze stream — bytes
//! that live in an absorb/squeeze sub-trace at a row determined
//! deterministically from `c`.  The two cells (chunk-bit, source-
//! bit) live HUNDREDS of rows apart, far beyond `(cur, nxt)`'s
//! reach.
//!
//! With this primitive:
//! - The *writes* log has one entry per source post-iota bit:
//!   `(addr = encode(squeeze_block, lane, bit_in_lane), value)`.
//! - The *reads* log has one entry per chunk input bit:
//!   `(addr = encode(chunk, byte_in_chunk, bit_in_byte), value)`.
//!
//! If `addr` is computed in both views with the same encoding, and
//! the multisets match, then for every read the corresponding
//! write exists with identical value.  Per-row constraints in the
//! consuming AIRs already enforce that `value` equals the relevant
//! trace cell on each side, completing the binding.
//!
//! ## Argument shape (per Plonky2 / Cairo)
//!
//! Given a Fiat-Shamir challenge `γ ∈ F_ext` (sampled AFTER the
//! AIR commits to its trace), define:
//!   - `term(addr, val) = γ − (addr · α + val)`  (α also F-S'd)
//!   - `read_product   = ∏_{i ∈ reads} term(addr_i, val_i)`
//!   - `write_product  = ∏_{i ∈ writes} term(addr_i, val_i)`
//!
//! By Schwartz-Zippel, `read_product = write_product` with
//! probability ≥ `1 − N/|F_ext|` iff the multisets are equal.  For
//! Goldilocks ≅ 2⁶⁴ and N ≪ 2⁶⁴, the soundness loss is ≤ N/2⁶⁴.
//! For F-extension (Fp³ or Fp⁶), the bound improves correspondingly.
//!
//! ## Trace layout (one entry per row)
//!
//! | Col | Meaning |
//! |-----|---------|
//! | ADDR  | log entry's address |
//! | VALUE | log entry's value |
//! | OP    | 0 if `reads` entry, 1 if `writes` entry |
//! | TERM  | `γ − (addr · α + value)` |
//! | RR    | `term` if OP = 0 else 1 (read factor) |
//! | RW    | `term` if OP = 1 else 0 (write factor) ... wait, see below |
//! | RP    | running read product up to and including this row |
//! | WP    | running write product up to and including this row |
//!
//! RR is the "read multiplier" — `term` for a read row, `1` for a
//! write row.  RW is symmetric.  Then `RP[r] = RP[r-1] · RR[r]` and
//! `WP[r] = WP[r-1] · RW[r]`.  Final boundary: `RP[N-1] = WP[N-1]`.
//!
//! ## Per-row constraints (constant cardinality, all ≤ deg 2)
//!
//! 1. OP boolean: `OP · (OP − 1) = 0`.
//! 2. TERM correctness: `TERM − γ + ADDR · α + VALUE = 0` (deg 1 if α a constant).
//! 3. RR correctness: `RR − ((1 − OP) · TERM + OP · 1) = 0`.
//! 4. RW correctness: `RW − (OP · TERM + (1 − OP) · 1) = 0`.
//! 5. RP boundary at row 0: `RP − RR = 0` (running product after row 0 = RR).
//! 6. WP boundary at row 0: `WP − RW = 0`.
//! 7. RP transition (row r → row r+1): `nxt.RP − cur.RP · nxt.RR = 0`.
//! 8. WP transition: `nxt.WP − cur.WP · nxt.RW = 0`.
//!
//! Total: 8 per-row constraints, padded uniformly across rows.  The
//! final-row constraint `RP[N-1] − WP[N-1] = 0` is a separate boundary
//! enforced by the composing AIR (or via PI-hash binding both products
//! to the same public-input value).

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

// ─── Column layout ────────────────────────────────────────────────

pub const COL_ADDR:  usize = 0;
pub const COL_VALUE: usize = 1;
pub const COL_OP:    usize = 2;
pub const COL_TERM:  usize = 3;
pub const COL_RR:    usize = 4;
pub const COL_RW:    usize = 5;
pub const COL_RP:    usize = 6;
pub const COL_WP:    usize = 7;
pub const WIDTH:     usize = 8;

pub const NUM_CONSTRAINTS: usize = 8;

// ─── Log entry type ───────────────────────────────────────────────

/// One entry in the permutation argument's combined log.
#[derive(Clone, Copy, Debug)]
pub struct LogEntry {
    pub address: F,
    pub value: F,
    /// `false` = read, `true` = write.
    pub is_write: bool,
}

// ─── fill_trace ───────────────────────────────────────────────────

/// Drive the permutation-argument trace.  `entries` is the
/// concatenation of reads and writes in any order; the final
/// running products `RP[N−1]` and `WP[N−1]` will match iff the
/// READ multiset equals the WRITE multiset.
pub fn fill_trace(
    trace: &mut [Vec<F>],
    n_trace: usize,
    entries: &[LogEntry],
    gamma: F,
    alpha: F,
) {
    assert_eq!(trace.len(), WIDTH);
    assert!(entries.len() <= n_trace);

    let one = F::one();
    let mut running_rp = F::one();
    let mut running_wp = F::one();
    for (r, e) in entries.iter().enumerate() {
        let op = if e.is_write { F::one() } else { F::zero() };
        let term = gamma - (e.address * alpha + e.value);
        let rr = if e.is_write { one } else { term };
        let rw = if e.is_write { term } else { one };

        running_rp *= rr;
        running_wp *= rw;

        trace[COL_ADDR][r]  = e.address;
        trace[COL_VALUE][r] = e.value;
        trace[COL_OP][r]    = op;
        trace[COL_TERM][r]  = term;
        trace[COL_RR][r]    = rr;
        trace[COL_RW][r]    = rw;
        trace[COL_RP][r]    = running_rp;
        trace[COL_WP][r]    = running_wp;
    }
    // Padding rows (≥ entries.len()): we need the per-row gates to
    // hold (RR/RW = 1 for product invariance) AND the algebraic
    // gates (TERM = γ − ADDR·α − VALUE; RR = TERM when OP = 0; RW
    // = 1 when OP = 0) to all be consistent.  Set OP = 0,
    // ADDR = 0, VALUE = γ − 1, so TERM = 1, RR = 1, RW = 1.  All
    // gates satisfied; running products carry the final value.
    let pad_value = gamma - one;
    for r in entries.len()..n_trace {
        trace[COL_ADDR][r]  = F::zero();
        trace[COL_VALUE][r] = pad_value;
        trace[COL_OP][r]    = F::zero();
        trace[COL_TERM][r]  = one;
        trace[COL_RR][r]    = one;
        trace[COL_RW][r]    = one;
        trace[COL_RP][r]    = running_rp;
        trace[COL_WP][r]    = running_wp;
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

pub fn eval_per_row(
    cur: &[F], nxt: &[F], row: usize,
    gamma: F, alpha: F,
) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one = F::one();

    let addr  = cur[COL_ADDR];
    let value = cur[COL_VALUE];
    let op    = cur[COL_OP];
    let term  = cur[COL_TERM];
    let rr    = cur[COL_RR];
    let rw    = cur[COL_RW];
    let rp    = cur[COL_RP];
    let wp    = cur[COL_WP];

    // 1. OP boolean.
    out.push(op * (op - one));

    // 2. TERM correctness: TERM = γ − (ADDR · α + VALUE).
    out.push(term - gamma + addr * alpha + value);

    // 3. RR correctness: RR = (1 − OP) · TERM + OP.
    out.push(rr - ((one - op) * term + op));

    // 4. RW correctness: RW = OP · TERM + (1 − OP).
    out.push(rw - (op * term + (one - op)));

    // 5+6. Row 0 boundary OR row r > 0 transition (mutually
    //      exclusive — only one fires per row).  We emit BOTH
    //      slots and zero out the one that doesn't apply.
    if row == 0 {
        out.push(rp - rr);  // RP[0] = RR[0]
        out.push(wp - rw);  // WP[0] = RW[0]
    } else {
        out.push(F::zero());
        out.push(F::zero());
    }

    // 7+8. Transition: nxt.RP = cur.RP · nxt.RR; same for WP.
    //      We always emit the transition; at the last row before
    //      padding, padding's RR/RW = 1 makes it trivial.
    let nxt_rp = nxt[COL_RP];
    let nxt_wp = nxt[COL_WP];
    let nxt_rr = nxt[COL_RR];
    let nxt_rw = nxt[COL_RW];
    out.push(nxt_rp - rp * nxt_rr);
    out.push(nxt_wp - wp * nxt_rw);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

/// Final-row consistency: the boundary constraint that lives in the
/// composing AIR.  Returns the difference `RP[last] − WP[last]`;
/// honest trace ⇒ zero, multiset mismatch ⇒ non-zero with high
/// probability.
pub fn final_consistency(trace: &[Vec<F>], n_active: usize) -> F {
    trace[COL_RP][n_active - 1] - trace[COL_WP][n_active - 1]
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// Honest trace: reads = writes as multisets ⇒ all per-row
    /// constraints zero AND final consistency holds.
    #[test]
    fn honest_matched_multisets_satisfy_constraints() {
        let writes = vec![
            (F::from(10u64), F::from(100u64)),
            (F::from(20u64), F::from(200u64)),
            (F::from(30u64), F::from(300u64)),
        ];
        let reads = vec![
            (F::from(20u64), F::from(200u64)),  // intentionally permuted
            (F::from(10u64), F::from(100u64)),
            (F::from(30u64), F::from(300u64)),
        ];
        let entries: Vec<LogEntry> = writes.iter().map(|&(a, v)| LogEntry { address: a, value: v, is_write: true })
            .chain(reads.iter().map(|&(a, v)| LogEntry { address: a, value: v, is_write: false }))
            .collect();

        let n_trace = 16;
        let mut trace = fresh_trace(n_trace);
        let gamma = F::from(0xDEAD_BEEFu64);
        let alpha = F::from(0xCAFEu64);
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        // All per-row constraints zero.
        for row in 0..(n_trace - 1) {  // skip last (no nxt)
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, gamma, alpha);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-MEM constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // Final boundary: read product = write product.
        assert_eq!(final_consistency(&trace, entries.len()), F::zero(),
            "honest matched multisets must give RP = WP");
    }

    /// Mismatched multisets: a read has no matching write (or vice
    /// versa) ⇒ final consistency is non-zero with overwhelming
    /// probability.
    #[test]
    fn mismatched_multisets_break_final_consistency() {
        let writes = vec![
            LogEntry { address: F::from(10u64), value: F::from(100u64), is_write: true },
            LogEntry { address: F::from(20u64), value: F::from(200u64), is_write: true },
        ];
        // Reads include an address-1 value-300 pair that's not in writes.
        let reads = vec![
            LogEntry { address: F::from(20u64), value: F::from(200u64), is_write: false },
            LogEntry { address: F::from(99u64), value: F::from(300u64), is_write: false },  // bogus
        ];
        let entries: Vec<LogEntry> = writes.iter().chain(reads.iter()).copied().collect();

        let n_trace = 8;
        let mut trace = fresh_trace(n_trace);
        let gamma = F::from(0xDEAD_BEEFu64);
        let alpha = F::from(0xCAFEu64);
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        // Per-row constraints still pass (the per-row work is
        // bookkeeping; the inconsistency is at the boundary).
        for row in 0..(n_trace - 1) {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, gamma, alpha);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-MEM per-row constraint {i} on row {row} should still hold: {v:?}");
            }
        }

        // Final boundary: should be NON-zero (different multisets).
        assert_ne!(final_consistency(&trace, entries.len()), F::zero(),
            "mismatched multisets must give RP ≠ WP");
    }

    /// Tampering: flip a single read's value ⇒ final consistency fires.
    #[test]
    fn tampered_read_value_breaks_final_consistency() {
        let writes = vec![
            LogEntry { address: F::from(7u64),  value: F::from(70u64),  is_write: true },
            LogEntry { address: F::from(13u64), value: F::from(130u64), is_write: true },
        ];
        let reads = vec![
            LogEntry { address: F::from(7u64),  value: F::from(70u64),  is_write: false },
            LogEntry { address: F::from(13u64), value: F::from(130u64), is_write: false },
        ];
        let mut entries: Vec<LogEntry> = writes.iter().chain(reads.iter()).copied().collect();

        // Tamper: change the second read's value.
        entries[3].value = F::from(999u64);

        let n_trace = 8;
        let mut trace = fresh_trace(n_trace);
        let gamma = F::from(0xCAFE_BABEu64);
        let alpha = F::from(0x1234u64);
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        assert_ne!(final_consistency(&trace, entries.len()), F::zero(),
            "tampered read value must break the final consistency");
    }

    /// Cardinality / boundary sanity: an EMPTY log produces RP = WP = 1,
    /// trivially consistent (vacuously matched).
    #[test]
    fn empty_log_is_trivially_consistent() {
        let entries: Vec<LogEntry> = vec![];
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        let gamma = F::from(7u64);
        let alpha = F::from(11u64);
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        // All padding rows; products initialised to 1 stay 1.
        // No "active" rows, so we read RP/WP at row 0 of padding,
        // both should be 1.
        assert_eq!(trace[COL_RP][0], F::one());
        assert_eq!(trace[COL_WP][0], F::one());
    }

    /// Permutation invariance: rearranging reads and writes within
    /// their own multisets doesn't change `RP[N-1]` / `WP[N-1]`.
    #[test]
    fn permutation_within_multisets_preserves_products() {
        let pairs: Vec<(F, F)> = (0..6u64).map(|k| (F::from(k * 11), F::from(k * 13 + 7))).collect();
        let n_trace = 32;
        let gamma = F::from(0xFEEDu64);
        let alpha = F::from(0x4242u64);

        // Order 1: writes first then reads, same order.
        let order1: Vec<LogEntry> = pairs.iter().map(|&(a, v)| LogEntry { address: a, value: v, is_write: true })
            .chain(pairs.iter().map(|&(a, v)| LogEntry { address: a, value: v, is_write: false }))
            .collect();

        // Order 2: interleaved.
        let mut order2: Vec<LogEntry> = Vec::new();
        for (i, &(a, v)) in pairs.iter().enumerate() {
            order2.push(LogEntry { address: a, value: v, is_write: i % 2 == 0 });
        }
        // Add the missing "other-op" copies to balance.
        for (i, &(a, v)) in pairs.iter().enumerate() {
            order2.push(LogEntry { address: a, value: v, is_write: i % 2 != 0 });
        }

        let mut trace1 = fresh_trace(n_trace);
        let mut trace2 = fresh_trace(n_trace);
        fill_trace(&mut trace1, n_trace, &order1, gamma, alpha);
        fill_trace(&mut trace2, n_trace, &order2, gamma, alpha);

        // Both should have RP = WP at the end (matched multisets).
        assert_eq!(final_consistency(&trace1, order1.len()), F::zero());
        assert_eq!(final_consistency(&trace2, order2.len()), F::zero());

        // And the FINAL products are equal across orderings (the
        // multiset is a set of (addr, value) pairs; product is
        // commutative so the value is invariant under order).
        assert_eq!(trace1[COL_RP][order1.len() - 1], trace2[COL_RP][order2.len() - 1]);
        assert_eq!(trace1[COL_WP][order1.len() - 1], trace2[COL_WP][order2.len() - 1]);
    }
}
