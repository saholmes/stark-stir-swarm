//! T-MEM: **multiset-equality permutation argument over F_ext**.
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
//! ## Argument shape (per Plonky2 / Cairo, lifted to F_ext)
//!
//! Given Fiat-Shamir challenges `(γ, α) ∈ F_ext²` (sampled AFTER the
//! AIR commits to its trace via `derive_t_mem_challenges(pi_hash)`):
//!   - `term(addr, val) = γ − (α · addr + val)`  ∈ F_ext  (`addr, val` lifted from F)
//!   - `RP = ∏_{r ∈ reads}  term(addr_r, val_r)`  ∈ F_ext
//!   - `WP = ∏_{w ∈ writes} term(addr_w, val_w)`  ∈ F_ext
//!
//! By Schwartz-Zippel, `RP = WP` with probability ≥ `1 − N/|F_ext|`
//! iff the multisets are equal.  The ε bound:
//!
//! | Level | sha3-N  | F_ext | DEGREE | log\|F_ext\|     | N/\|F_ext\| (N≈2¹⁴) | target  |
//! |-------|---------|-------|--------|----------------|--------------------|---------|
//! | L1    | sha3-256| Fp6   | 6      | 384            | 2⁻³⁷⁰              | 2⁻¹²⁸   |
//! | L3    | sha3-384| Fp6   | 6      | 384            | 2⁻³⁷⁰              | 2⁻¹⁹²   |
//! | L5    | sha3-512| Fp8   | 8      | 512            | 2⁻⁴⁹⁸              | 2⁻²⁵⁶   |
//!
//! All comfortably below the per-level ε budget — the T-MEM term is
//! no longer the dominant ε at any level.  The extension field choice
//! matches the FRI/STIR extension field used elsewhere in the
//! protocol (see paper §soundness).
//!
//! ## Trace encoding
//!
//! Each F_ext element is encoded as `EXT_DEGREE` base-field columns
//! (its coordinates in the tower-extension basis, via
//! `TowerField::{to,from}_fp_components`).  Per-row constraints emit
//! one base-field equation per coefficient of the F_ext-valued
//! constraint, so an "F_ext equation" lands as `EXT_DEGREE` rows in
//! the constraint composition vector.  This keeps `c_eval ∈ F^n` —
//! compatible with the existing FRI prove infrastructure — while
//! preserving F_ext soundness for the multiset-equality check.
//!
//! Layout (4 + 5·EXT_DEGREE columns):
//!
//! | Column          | Type    | Meaning |
//! |-----------------|---------|---------|
//! | ADDR            | F (1)   | log entry's address |
//! | VALUE           | F (1)   | log entry's value |
//! | OP              | F (1)   | 0 = read, 1 = write |
//! | IS_ACTIVE       | F (1)   | 1 = active row, 0 = padding |
//! | TERM (D cells)  | F_ext   | `γ − (α·addr + value)` |
//! | RR   (D cells)  | F_ext   | `term` if read, `1` if write |
//! | RW   (D cells)  | F_ext   | `term` if write, `1` if read |
//! | RP   (D cells)  | F_ext   | running read product |
//! | WP   (D cells)  | F_ext   | running write product |
//!
//! ## Per-row constraints
//!
//! Shared (2 base-field equations):
//!   1. `OP · (OP − 1) = 0`
//!   2. `IS_ACTIVE · (IS_ACTIVE − 1) = 0`
//!
//! F_ext-valued (each yields `EXT_DEGREE` base-field equations):
//!   3. **TERM correctness** (gated by IS_ACTIVE so padding has TERM = 1):
//!      `IS_ACTIVE · (TERM − γ + α·ADDR + VALUE) = 0`  ∈ F_ext
//!   4. `RR − ((1 − OP) · TERM + OP) = 0`  ∈ F_ext
//!   5. `RW − (OP · TERM + (1 − OP)) = 0`  ∈ F_ext
//!   6. Row-0 boundary: `RP − RR = 0`
//!   7. Row-0 boundary: `WP − RW = 0`
//!   8. Transition: `nxt.RP − cur.RP · nxt.RR = 0`  ∈ F_ext
//!   9. Transition: `nxt.WP − cur.WP · nxt.RW = 0`  ∈ F_ext
//!  10. **Final-row boundary** (the actual multiset-equality check):
//!      `(cur.IS_ACTIVE − nxt.IS_ACTIVE) · (RP − WP) = 0`  ∈ F_ext
//!      The selector `cur.IS_ACTIVE − nxt.IS_ACTIVE` is 1 at the
//!      active → padding transition (the last active row) and 0
//!      everywhere else, so this fires exactly once per proof and
//!      forces `RP_F_ext = WP_F_ext` at the last active row.  This
//!      is what makes the perm-arg actually enforce multiset equality
//!      in the proof — without it, the per-row constraints alone
//!      prove only that the running products are correctly accumulated,
//!      not that they meet at the boundary.  Requires `n_trace > entries.len()`
//!      (i.e. at least one padding row) so the selector is well-defined.
//!
//! Total: `2 + 8 · EXT_DEGREE` base-field constraints.  All degree ≤ 2.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One as _, Zero as _};
use ark_goldilocks::Goldilocks as F;

use crate::tower_field::TowerField;

// ─── Extension-field choice (paper-aligned) ───────────────────────

/// Fp⁶ for L1 / L3 (sha3-256 / sha3-384), Fp⁸ for L5 (sha3-512).
/// Matches the FRI/STIR extension field used elsewhere in the
/// protocol so all ε terms are bound by the same |F_ext|.
#[cfg(any(feature = "sha3-256", feature = "sha3-384"))]
pub type ExtField = crate::sextic_ext::SexticExt;

#[cfg(feature = "sha3-512")]
pub type ExtField = crate::octic_ext::OcticExt;

#[cfg(not(any(feature = "sha3-256", feature = "sha3-384", feature = "sha3-512")))]
pub type ExtField = crate::sextic_ext::SexticExt;

/// Total degree of the extension field over Goldilocks.  6 (Fp6) or 8 (Fp8).
pub const EXT_DEGREE: usize = <ExtField as TowerField>::DEGREE;

// ─── Column layout ────────────────────────────────────────────────

pub const COL_ADDR:      usize = 0;
pub const COL_VALUE:     usize = 1;
pub const COL_OP:        usize = 2;
pub const COL_IS_ACTIVE: usize = 3;

const SHARED_COLS: usize = 4;

/// Each F_ext-valued column occupies `EXT_DEGREE` base columns.
/// Order: TERM, RR, RW, RP, WP.
const FE_BASE_TERM: usize = SHARED_COLS;
const FE_BASE_RR:   usize = FE_BASE_TERM + EXT_DEGREE;
const FE_BASE_RW:   usize = FE_BASE_RR   + EXT_DEGREE;
const FE_BASE_RP:   usize = FE_BASE_RW   + EXT_DEGREE;
const FE_BASE_WP:   usize = FE_BASE_RP   + EXT_DEGREE;

pub const WIDTH:           usize = SHARED_COLS + 5 * EXT_DEGREE;
/// 2 shared base equations + 8 F_ext-valued equations (each yielding
/// `EXT_DEGREE` base equations).  The 8th F_ext equation is the
/// final-row boundary `RP_F_ext = WP_F_ext`, the actual multiset-
/// equality check enforced at the active→padding transition.
pub const NUM_CONSTRAINTS: usize = 2 + 8 * EXT_DEGREE;

// ─── Log entry type ───────────────────────────────────────────────

/// One entry in the permutation argument's combined log.
#[derive(Clone, Copy, Debug)]
pub struct LogEntry {
    pub address: F,
    pub value: F,
    /// `false` = read, `true` = write.
    pub is_write: bool,
}

// ─── F_ext ↔ base-field encoding helpers ──────────────────────────

#[inline]
fn write_ext(trace: &mut [Vec<F>], base_col: usize, row: usize, e: ExtField) {
    let comps = e.to_fp_components();
    debug_assert_eq!(comps.len(), EXT_DEGREE);
    for j in 0..EXT_DEGREE {
        trace[base_col + j][row] = comps[j];
    }
}

#[inline]
fn read_ext(cells: &[F], base_col: usize) -> ExtField {
    let slice = &cells[base_col..base_col + EXT_DEGREE];
    ExtField::from_fp_components(slice)
        .expect("any tuple of EXT_DEGREE Goldilocks elements is a valid F_ext encoding")
}

// ─── fill_trace ───────────────────────────────────────────────────

/// Drive the F_ext permutation-argument trace.  `entries` is the
/// concatenation of reads and writes in any order.  At the last
/// active row, `RP_F_ext` and `WP_F_ext` (read directly from the 2·D
/// running-product cells) match iff the read and write multisets
/// are equal — fail probability ≤ N / |F_ext|.
pub fn fill_trace(
    trace: &mut [Vec<F>],
    n_trace: usize,
    entries: &[LogEntry],
    gamma: ExtField,
    alpha: ExtField,
) {
    assert_eq!(trace.len(), WIDTH,
        "trace must have {WIDTH} columns (got {})", trace.len());
    assert!(entries.len() < n_trace,
        "need at least one padding row: got {} entries with {n_trace} trace rows. \
         The final-row boundary constraint requires the selector \
         (cur.IS_ACTIVE − nxt.IS_ACTIVE) to fire at exactly the active→padding \
         transition; with no padding the selector is undefined.",
        entries.len());

    let one_f    = F::one();
    let zero_f   = F::zero();
    let one_ext  = ExtField::one();

    let mut running_rp = ExtField::one();
    let mut running_wp = ExtField::one();

    // Active rows.
    for (r, e) in entries.iter().enumerate() {
        let op_f = if e.is_write { one_f } else { zero_f };
        trace[COL_ADDR     ][r] = e.address;
        trace[COL_VALUE    ][r] = e.value;
        trace[COL_OP       ][r] = op_f;
        trace[COL_IS_ACTIVE][r] = one_f;

        // term = γ - α·addr - value, all lifted to F_ext.
        let addr_ext  = ExtField::from_fp(e.address);
        let value_ext = ExtField::from_fp(e.value);
        let term = gamma - (alpha * addr_ext + value_ext);
        let (rr, rw) = if e.is_write { (one_ext, term) } else { (term, one_ext) };
        running_rp = running_rp * rr;
        running_wp = running_wp * rw;

        write_ext(trace, FE_BASE_TERM, r, term);
        write_ext(trace, FE_BASE_RR,   r, rr);
        write_ext(trace, FE_BASE_RW,   r, rw);
        write_ext(trace, FE_BASE_RP,   r, running_rp);
        write_ext(trace, FE_BASE_WP,   r, running_wp);
    }

    // Padding rows.  IS_ACTIVE = 0 disables TERM correctness; we
    // set TERM = 1 ∈ F_ext, RR = 1, RW = 1 so the running products
    // pass through unchanged (RP_new = RP_old · 1 = RP_old).
    for r in entries.len()..n_trace {
        trace[COL_ADDR     ][r] = zero_f;
        trace[COL_VALUE    ][r] = zero_f;
        trace[COL_OP       ][r] = zero_f;
        trace[COL_IS_ACTIVE][r] = zero_f;

        write_ext(trace, FE_BASE_TERM, r, one_ext);
        write_ext(trace, FE_BASE_RR,   r, one_ext);
        write_ext(trace, FE_BASE_RW,   r, one_ext);
        write_ext(trace, FE_BASE_RP,   r, running_rp);
        write_ext(trace, FE_BASE_WP,   r, running_wp);
    }
}

// ─── Constraint evaluation ────────────────────────────────────────

/// Per-row constraint evaluation.  Returns `Vec<F>` of length
/// `NUM_CONSTRAINTS = 2 + 7·EXT_DEGREE`.  Each F_ext-valued
/// constraint contributes `EXT_DEGREE` base-field equations (one per
/// coefficient of the F_ext element, all of which must be zero for
/// the F_ext element to be zero).
pub fn eval_per_row(
    cur: &[F], nxt: &[F], row: usize,
    gamma: ExtField, alpha: ExtField,
) -> Vec<F> {
    debug_assert_eq!(cur.len(), WIDTH);
    debug_assert_eq!(nxt.len(), WIDTH);

    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);
    let one_f  = F::one();
    let zero_f = F::zero();
    let one_ext  = ExtField::one();
    let zero_ext = ExtField::zero();

    let addr      = cur[COL_ADDR];
    let value     = cur[COL_VALUE];
    let op        = cur[COL_OP];
    let is_active = cur[COL_IS_ACTIVE];

    // Lifted to F_ext for the F_ext-valued algebra below.
    let addr_ext      = ExtField::from_fp(addr);
    let value_ext     = ExtField::from_fp(value);
    let op_ext        = ExtField::from_fp(op);
    let is_active_ext = ExtField::from_fp(is_active);

    let cur_term = read_ext(cur, FE_BASE_TERM);
    let cur_rr   = read_ext(cur, FE_BASE_RR);
    let cur_rw   = read_ext(cur, FE_BASE_RW);
    let cur_rp   = read_ext(cur, FE_BASE_RP);
    let cur_wp   = read_ext(cur, FE_BASE_WP);

    let nxt_rr   = read_ext(nxt, FE_BASE_RR);
    let nxt_rw   = read_ext(nxt, FE_BASE_RW);
    let nxt_rp   = read_ext(nxt, FE_BASE_RP);
    let nxt_wp   = read_ext(nxt, FE_BASE_WP);

    // Helper: append the EXT_DEGREE base-field components of an F_ext element.
    let push_ext = |out: &mut Vec<F>, e: ExtField| {
        let comps = e.to_fp_components();
        debug_assert_eq!(comps.len(), EXT_DEGREE);
        for c in comps { out.push(c); }
    };

    // 1. OP boolean (degree 2 in base F).
    out.push(op * (op - one_f));
    // 2. IS_ACTIVE boolean.
    out.push(is_active * (is_active - one_f));

    // 3. TERM correctness, GATED by IS_ACTIVE (F_ext eqn → D base eqns).
    //    Active: TERM = γ − α·ADDR − VALUE.  Padding (IS_ACTIVE=0):
    //    TERM is unconstrained by this equation; we set it to 1 in
    //    fill_trace so RR=1, RW=1 propagate unchanged through padding.
    let term_check = is_active_ext * (cur_term - gamma + alpha * addr_ext + value_ext);
    push_ext(&mut out, term_check);

    // 4. RR = (1 − OP) · TERM + OP.
    let rr_check = cur_rr - ((one_ext - op_ext) * cur_term + op_ext);
    push_ext(&mut out, rr_check);

    // 5. RW = OP · TERM + (1 − OP).
    let rw_check = cur_rw - (op_ext * cur_term + (one_ext - op_ext));
    push_ext(&mut out, rw_check);

    // 6 + 7. Row-0 boundary: RP = RR and WP = RW.
    if row == 0 {
        push_ext(&mut out, cur_rp - cur_rr);
        push_ext(&mut out, cur_wp - cur_rw);
    } else {
        for _ in 0..(2 * EXT_DEGREE) { out.push(zero_f); }
        let _ = zero_ext; // silence unused-binding warning when row != 0
    }

    // 8. RP transition: nxt.RP − cur.RP · nxt.RR  ∈ F_ext.
    let rp_trans = nxt_rp - cur_rp * nxt_rr;
    push_ext(&mut out, rp_trans);

    // 9. WP transition: nxt.WP − cur.WP · nxt.RW  ∈ F_ext.
    let wp_trans = nxt_wp - cur_wp * nxt_rw;
    push_ext(&mut out, wp_trans);

    // 10. **Final-row boundary** `RP_F_ext = WP_F_ext` at the
    //     active→padding transition.  Selector `s = cur.IS_ACTIVE −
    //     nxt.IS_ACTIVE` is 1 only at the last active row (cur active,
    //     nxt padding), 0 elsewhere — so `s · (RP − WP) = 0` fires
    //     exactly once per proof and enforces multiset equality.
    //     Without this, the per-row constraints prove only that the
    //     running products are correctly accumulated, not that they
    //     match.
    let nxt_is_active = nxt[COL_IS_ACTIVE];
    let selector_ext  = ExtField::from_fp(is_active - nxt_is_active);
    let rp_wp_match   = selector_ext * (cur_rp - cur_wp);
    push_ext(&mut out, rp_wp_match);

    debug_assert_eq!(out.len(), NUM_CONSTRAINTS);
    out
}

/// Final-row consistency: returns `RP[n_active − 1] − WP[n_active − 1]`
/// as a single F_ext element.  Honest trace ⇒ zero.  Multiset
/// mismatch ⇒ non-zero with probability ≥ 1 − N/|F_ext|.
pub fn final_consistency(trace: &[Vec<F>], n_active: usize) -> ExtField {
    let r = n_active - 1;
    let row_cells: Vec<F> = (0..WIDTH).map(|c| trace[c][r]).collect();
    let rp = read_ext(&row_cells, FE_BASE_RP);
    let wp = read_ext(&row_cells, FE_BASE_WP);
    rp - wp
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    fn dummy_challenges() -> (ExtField, ExtField) {
        // Distinct, non-trivial F_ext elements (depend on EXT_DEGREE).
        let g_components: Vec<F> = (0..EXT_DEGREE)
            .map(|j| F::from(0xDEAD_BEEF_0001u64 + 0x1_0000u64 * j as u64))
            .collect();
        let a_components: Vec<F> = (0..EXT_DEGREE)
            .map(|j| F::from(0xCAFE_BABE_0001u64 + 0x1_0000u64 * j as u64))
            .collect();
        let gamma = ExtField::from_fp_components(&g_components).unwrap();
        let alpha = ExtField::from_fp_components(&a_components).unwrap();
        (gamma, alpha)
    }

    /// Honest trace: reads = writes as multisets ⇒ all per-row
    /// constraints zero AND final consistency holds in F_ext.
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
        let entries: Vec<LogEntry> = writes.iter()
            .map(|&(a, v)| LogEntry { address: a, value: v, is_write: true })
            .chain(reads.iter().map(|&(a, v)| LogEntry { address: a, value: v, is_write: false }))
            .collect();

        let n_trace = 16;
        let mut trace = fresh_trace(n_trace);
        let (gamma, alpha) = dummy_challenges();
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        // All per-row constraints zero on every row including padding.
        for row in 0..(n_trace - 1) {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, gamma, alpha);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-MEM constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // Final boundary: F_ext-valued read product = write product.
        assert!(final_consistency(&trace, entries.len()) == ExtField::zero(),
            "honest matched multisets must give RP_F_ext = WP_F_ext");
    }

    /// Mismatched multisets: a read has no matching write ⇒ final
    /// consistency is non-zero with probability ≥ 1 − N/|F_ext|.
    #[test]
    fn mismatched_multisets_break_final_consistency() {
        let writes = vec![
            LogEntry { address: F::from(10u64), value: F::from(100u64), is_write: true },
            LogEntry { address: F::from(20u64), value: F::from(200u64), is_write: true },
        ];
        let reads = vec![
            LogEntry { address: F::from(20u64), value: F::from(200u64), is_write: false },
            LogEntry { address: F::from(99u64), value: F::from(300u64), is_write: false },  // bogus
        ];
        let entries: Vec<LogEntry> = writes.iter().chain(reads.iter()).copied().collect();

        let n_trace = 8;
        let mut trace = fresh_trace(n_trace);
        let (gamma, alpha) = dummy_challenges();
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        // The boundary constraint at the last active row catches the
        // mismatch — exactly one row should produce a non-zero
        // constraint output (the active→padding transition row).
        let last_active = entries.len() - 1;
        let mut boundary_fired = false;
        for row in 0..(n_trace - 1) {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, gamma, alpha);
            // Boundary contributes the final EXT_DEGREE base equations.
            let bdy_slice = &cvals[NUM_CONSTRAINTS - EXT_DEGREE..];
            let bdy_nonzero = bdy_slice.iter().any(|v| !v.is_zero());
            if row == last_active {
                assert!(bdy_nonzero,
                    "boundary constraint at last active row {row} must catch the multiset mismatch");
                boundary_fired = true;
            } else {
                assert!(!bdy_nonzero,
                    "boundary constraint must NOT fire at row {row} (only at last active row {last_active})");
            }
            // Non-boundary constraints hold everywhere (running-product accumulation is correct).
            for (i, v) in cvals[..NUM_CONSTRAINTS - EXT_DEGREE].iter().enumerate() {
                assert!(v.is_zero(),
                    "T-MEM non-boundary constraint {i} on row {row} should hold: {v:?}");
            }
        }
        assert!(boundary_fired, "boundary constraint never fired — selector logic broken");

        assert!(final_consistency(&trace, entries.len()) != ExtField::zero(),
            "mismatched multisets must give RP_F_ext ≠ WP_F_ext");
    }

    /// Tampering: flip a single read's value ⇒ final consistency
    /// fires.
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
        let (gamma, alpha) = dummy_challenges();
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        assert!(final_consistency(&trace, entries.len()) != ExtField::zero(),
            "tampered read value must break the final consistency");
    }

    /// Empty log: products initialised to 1 stay 1 (in F_ext).
    #[test]
    fn empty_log_is_trivially_consistent() {
        let entries: Vec<LogEntry> = vec![];
        let n_trace = 4;
        let mut trace = fresh_trace(n_trace);
        let (gamma, alpha) = dummy_challenges();
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        let row0: Vec<F> = (0..WIDTH).map(|c| trace[c][0]).collect();
        assert_eq!(read_ext(&row0, FE_BASE_RP), ExtField::one());
        assert_eq!(read_ext(&row0, FE_BASE_WP), ExtField::one());
    }

    /// Permutation invariance: rearranging reads/writes within their
    /// own multisets doesn't change `(RP_F_ext, WP_F_ext)`.
    #[test]
    fn permutation_within_multisets_preserves_products() {
        let pairs: Vec<(F, F)> = (0..6u64)
            .map(|k| (F::from(k * 11), F::from(k * 13 + 7))).collect();
        let n_trace = 32;
        let (gamma, alpha) = dummy_challenges();

        let order1: Vec<LogEntry> = pairs.iter()
            .map(|&(a, v)| LogEntry { address: a, value: v, is_write: true })
            .chain(pairs.iter().map(|&(a, v)| LogEntry { address: a, value: v, is_write: false }))
            .collect();

        let mut order2: Vec<LogEntry> = Vec::new();
        for (i, &(a, v)) in pairs.iter().enumerate() {
            order2.push(LogEntry { address: a, value: v, is_write: i % 2 == 0 });
        }
        for (i, &(a, v)) in pairs.iter().enumerate() {
            order2.push(LogEntry { address: a, value: v, is_write: i % 2 != 0 });
        }

        let mut trace1 = fresh_trace(n_trace);
        let mut trace2 = fresh_trace(n_trace);
        fill_trace(&mut trace1, n_trace, &order1, gamma, alpha);
        fill_trace(&mut trace2, n_trace, &order2, gamma, alpha);

        assert!(final_consistency(&trace1, order1.len()) == ExtField::zero());
        assert!(final_consistency(&trace2, order2.len()) == ExtField::zero());

        // Final products equal across orderings (commutative F_ext mult).
        let r1: Vec<F> = (0..WIDTH).map(|c| trace1[c][order1.len() - 1]).collect();
        let r2: Vec<F> = (0..WIDTH).map(|c| trace2[c][order2.len() - 1]).collect();
        assert_eq!(read_ext(&r1, FE_BASE_RP), read_ext(&r2, FE_BASE_RP));
        assert_eq!(read_ext(&r1, FE_BASE_WP), read_ext(&r2, FE_BASE_WP));
    }

    /// Padding correctness: per-row constraints hold across the
    /// active→padding transition (IS_ACTIVE-gated TERM correctness).
    #[test]
    fn padding_rows_satisfy_constraints() {
        let entries = vec![
            LogEntry { address: F::from(1u64), value: F::from(11u64), is_write: true },
            LogEntry { address: F::from(2u64), value: F::from(22u64), is_write: true },
            LogEntry { address: F::from(2u64), value: F::from(22u64), is_write: false },
            LogEntry { address: F::from(1u64), value: F::from(11u64), is_write: false },
        ];
        let n_trace = 32;  // lots of padding
        let mut trace = fresh_trace(n_trace);
        let (gamma, alpha) = dummy_challenges();
        fill_trace(&mut trace, n_trace, &entries, gamma, alpha);

        for row in 0..(n_trace - 1) {
            let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][row + 1]).collect();
            let cvals = eval_per_row(&cur, &nxt, row, gamma, alpha);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "T-MEM constraint {i} on row {row} (active={}) not zero: {v:?}",
                    cur[COL_IS_ACTIVE]);
            }
        }
    }

    /// Sanity: EXT_DEGREE matches the configured F_ext and selected
    /// security level.
    #[test]
    fn ext_degree_matches_level() {
        #[cfg(feature = "sha3-256")]
        assert_eq!(EXT_DEGREE, 6, "L1: SexticExt expected");
        #[cfg(feature = "sha3-384")]
        assert_eq!(EXT_DEGREE, 6, "L3: SexticExt expected");
        #[cfg(feature = "sha3-512")]
        assert_eq!(EXT_DEGREE, 8, "L5: OcticExt expected");
    }
}
