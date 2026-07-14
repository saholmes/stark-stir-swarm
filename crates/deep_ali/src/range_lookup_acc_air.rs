// range_lookup_acc_air.rs — the per-row F_ext accumulator column that
// turns the LogUp range-check (`range_lookup_air`) into a live multi-row
// argument.
//
// This is the protocol-level half of the lookup lever: a running-SUM
// accumulator over F_ext, structurally identical to the running-PRODUCT
// (RP/WP) columns of `permutation_argument.rs`, but summing reciprocals
// instead of multiplying terms.  It realises the identity
//
//     Σ_i 1/(α − a_i)   =   Σ_t m_t/(α − t)                        (★)
//
// as a boundary on a single accumulator: over one multi-row trace,
//
//     TABLE rows  r ∈ [0, 2^S):  val = r (PINNED to the row index, so
//         the table is canonical [0,2^S) by construction), signed
//         multiplicity  smult = −m_r  (m_r = claimed count of table
//         value r among the looked-up values).
//     LOOKUP rows r ∈ [2^S, 2^S+N): val = a_{r−2^S} (a sub-limb from a
//         gadget), smult = +1.
//     PADDING rows: inactive.
//
// Each active row contributes  smult · 1/(α − val)  to a running sum that
// starts at 0 and must return to 0 at the active→padding transition.  A
// value a_i ∉ [0,2^S) has a pole at α = a_i that NO table row can cancel
// (table poles are pinned to [0,2^S)), so the sum is a non-zero rational
// function of α and the boundary fails w.h.p. over a random α ∈ F_ext —
// regardless of how the prover chooses the multiplicities.
//
// SOUNDNESS accounting: α is sampled in F_ext (F_p^6 at L1/L3, F_p^8 at
// L5) AFTER the trace commitment via the same challenge machinery as the
// T-MEM permutation argument; lookup error ≤ (N+2^S)/|F_ext| ≈ 2^-320 at
// L1, so κ_lookup ≫ κ_IT/κ_bind/κ_FS and κ_sys = min(...) is unchanged.
//
// Column layout (base columns):
//   VAL (1) | SMULT (1) | IS_ACTIVE (1) | INV (EXT_DEGREE) | ACC (EXT_DEGREE)
// Constraints (per row):
//   base: table-pin  (row < 2^S ⇒ VAL = row)
//   F_ext: INV correctness | ACC transition | row-0 boundary | final boundary
//   (each F_ext equation = EXT_DEGREE base equations)

#![allow(non_snake_case, dead_code)]

use ark_ff::{Field, One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::permutation_argument::{ExtField, EXT_DEGREE};
use crate::tower_field::TowerField;

// ─── Column layout ─────────────────────────────────────────────────
pub const COL_VAL: usize = 0;
pub const COL_SMULT: usize = 1;
pub const COL_IS_ACTIVE: usize = 2;
const SHARED_COLS: usize = 3;
const FE_INV: usize = SHARED_COLS;
const FE_ACC: usize = FE_INV + EXT_DEGREE;

pub const WIDTH: usize = SHARED_COLS + 2 * EXT_DEGREE;

/// Base constraints per row: 1 (table-pin) + 4 F_ext equations.
pub const NUM_CONSTRAINTS: usize = 1 + 4 * EXT_DEGREE;

// ─── F_ext ↔ base helpers (mirror permutation_argument) ────────────
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
    ExtField::from_fp_components(slice).expect("valid F_ext encoding")
}

/// Honest table multiplicities: count each in-range value; out-of-range
/// values (≥ table_size) are NOT counted (no canonical table slot).
pub fn multiplicities(values: &[u64], table_size: usize) -> Vec<u64> {
    let mut m = vec![0u64; table_size];
    for &v in values {
        if (v as usize) < table_size {
            m[v as usize] += 1;
        }
    }
    m
}

/// Fill the accumulator trace.  `n_trace ≥ table_size + values.len() + 1`
/// (at least one padding row for the active→padding boundary).
pub fn fill_trace(
    trace: &mut [Vec<F>],
    n_trace: usize,
    table_size: usize,
    values: &[u64],
    mult: &[u64],
    alpha: ExtField,
) {
    assert_eq!(trace.len(), WIDTH, "trace must have {WIDTH} columns");
    assert_eq!(mult.len(), table_size);
    let n_active = table_size + values.len();
    assert!(n_active < n_trace, "need ≥1 padding row");

    let mut acc = ExtField::zero(); // exclusive running sum: acc[r] = Σ_{i<r}
    for r in 0..n_trace {
        // acc[r] recorded BEFORE this row's contribution.
        write_ext(trace, FE_ACC, r, acc);

        let (val, smult, active): (F, F, bool) = if r < table_size {
            // Table row: val pinned to r, smult = −m_r.
            (F::from(r as u64), -F::from(mult[r]), true)
        } else if r < n_active {
            let a = values[r - table_size];
            (F::from(a), F::from(1u64), true)
        } else {
            (F::zero(), F::zero(), false)
        };

        trace[COL_VAL][r] = val;
        trace[COL_SMULT][r] = smult;
        trace[COL_IS_ACTIVE][r] = if active { F::one() } else { F::zero() };

        let inv = if active {
            (alpha - ExtField::from_fp(val)).invert().expect("alpha must avoid val")
        } else {
            ExtField::zero()
        };
        write_ext(trace, FE_INV, r, inv);

        // contribution = active · smult · inv ; update exclusive running sum.
        if active {
            acc = acc + ExtField::from_fp(smult) * inv;
        }
    }
}

/// Per-row constraint evaluation (cur = row, nxt = next row).  Returns
/// `NUM_CONSTRAINTS` base-field residuals; all zero on a valid trace.
pub fn eval_per_row(
    cur: &[F],
    nxt: &[F],
    row: usize,
    table_size: usize,
    alpha: ExtField,
) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_CONSTRAINTS);

    let val = cur[COL_VAL];
    let smult = cur[COL_SMULT];
    let is_active = cur[COL_IS_ACTIVE];
    let inv = read_ext(cur, FE_INV);
    let acc_cur = read_ext(cur, FE_ACC);
    let acc_nxt = read_ext(nxt, FE_ACC);
    let active_ext = ExtField::from_fp(is_active);

    // (1) Table pinning (base): row < table_size ⇒ VAL = row.
    if row < table_size {
        out.push(val - F::from(row as u64));
    } else {
        out.push(F::zero());
    }

    // (2) INV correctness (F_ext): is_active · ((α − val)·inv − 1) = 0.
    let inv_resid = active_ext * ((alpha - ExtField::from_fp(val)) * inv - ExtField::one());
    push_ext(&mut out, inv_resid);

    // (3) ACC transition (F_ext): acc_nxt − acc_cur − is_active·smult·inv = 0.
    let contribution = active_ext * ExtField::from_fp(smult) * inv;
    push_ext(&mut out, acc_nxt - acc_cur - contribution);

    // (4) Row-0 boundary (F_ext): acc_cur = 0 at row 0.
    let row0 = if row == 0 { acc_cur } else { ExtField::zero() };
    push_ext(&mut out, row0);

    // (5) Final-sum boundary (F_ext): at the active→padding transition
    //     (selector = is_active_cur − is_active_nxt = 1) the running sum
    //     must be 0.  acc_nxt at that row holds the total.
    let selector = is_active - nxt[COL_IS_ACTIVE];
    let final_resid = ExtField::from_fp(selector) * acc_nxt;
    push_ext(&mut out, final_resid);

    out
}

#[inline]
fn push_ext(out: &mut Vec<F>, e: ExtField) {
    for c in e.to_fp_components() {
        out.push(c);
    }
}

/// Evaluate every row's constraints (nxt = row+1; last row wraps to
/// itself, harmless since the tail is padding) and return the count of
/// non-zero residuals.
pub fn count_violations(
    trace: &[Vec<F>],
    n_trace: usize,
    table_size: usize,
    alpha: ExtField,
) -> usize {
    let mut nz = 0;
    for r in 0..n_trace {
        let cur: Vec<F> = (0..WIDTH).map(|c| trace[c][r]).collect();
        let nr = if r + 1 < n_trace { r + 1 } else { r };
        let nxt: Vec<F> = (0..WIDTH).map(|c| trace[c][nr]).collect();
        nz += eval_per_row(&cur, &nxt, r, table_size, alpha)
            .iter()
            .filter(|v| !v.is_zero())
            .count();
    }
    nz
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn make_trace(n: usize) -> Vec<Vec<F>> {
        (0..WIDTH).map(|_| vec![F::zero(); n]).collect()
    }

    /// A non-degenerate challenge in F_ext (production: FS-derived from
    /// pi_hash after commit).  Built from a small component pattern.
    fn alpha() -> ExtField {
        let comps: Vec<F> = (0..EXT_DEGREE).map(|i| F::from((0x100_0000u64) + 7 * i as u64 + 3)).collect();
        ExtField::from_fp_components(&comps).expect("valid F_ext")
    }

    /// POSITIVE: every looked-up value is in [0, table_size) and the
    /// multiplicities are honest ⇒ the accumulator returns to 0 and every
    /// constraint (including the final boundary) is satisfied.
    #[test]
    fn acc_valid_when_all_in_range() {
        let s = 4;
        let table_size = 1usize << s; // 16
        let values: Vec<u64> = vec![0, 3, 3, 7, 15, 1, 7, 7, 9, 2];
        let mult = multiplicities(&values, table_size);
        let n_trace = table_size + values.len() + 4; // padding
        let a = alpha();

        let mut trace = make_trace(n_trace);
        fill_trace(&mut trace, n_trace, table_size, &values, &mult, a);
        let nz = count_violations(&trace, n_trace, table_size, a);
        assert_eq!(nz, 0, "valid lookup: {nz} constraint residuals non-zero");
    }

    /// NEGATIVE: one value is out of range (= table_size).  It gets a
    /// lookup row but no table row can cancel it ⇒ the final-sum boundary
    /// fails.  The prover's honest multiplicities cannot help.
    #[test]
    fn acc_fails_on_out_of_range() {
        let s = 4;
        let table_size = 1usize << s;
        let mut values: Vec<u64> = vec![0, 3, 7, 1, 9, 2];
        values.push(table_size as u64); // 16 — out of range
        let mult = multiplicities(&values, table_size);
        let n_trace = table_size + values.len() + 4;
        let a = alpha();

        let mut trace = make_trace(n_trace);
        fill_trace(&mut trace, n_trace, table_size, &values, &mult, a);
        let nz = count_violations(&trace, n_trace, table_size, a);
        assert!(nz > 0, "out-of-range value must violate the accumulator boundary");
    }

    /// A cheating prover who inflates a multiplicity to try to zero the
    /// sum still fails: the running sum no longer returns to 0 (the
    /// transition/boundary constraints are over-determined by the honest
    /// contributions).
    #[test]
    fn acc_fails_on_fake_multiplicity() {
        let s = 4;
        let table_size = 1usize << s;
        let values: Vec<u64> = vec![0, 3, 7, 1, 9, 2];
        let mut mult = multiplicities(&values, table_size);
        mult[3] += 1; // claim one extra occurrence of table value 3
        let n_trace = table_size + values.len() + 4;
        let a = alpha();

        let mut trace = make_trace(n_trace);
        fill_trace(&mut trace, n_trace, table_size, &values, &mult, a);
        let nz = count_violations(&trace, n_trace, table_size, a);
        assert!(nz > 0, "inflated multiplicity must break the boundary");
    }

    /// Tampering the accumulator column mid-trace breaks the transition.
    #[test]
    fn acc_tamper_breaks_transition() {
        let s = 4;
        let table_size = 1usize << s;
        let values: Vec<u64> = vec![0, 3, 7, 1, 9, 2, 5, 5];
        let mult = multiplicities(&values, table_size);
        let n_trace = table_size + values.len() + 4;
        let a = alpha();

        let mut trace = make_trace(n_trace);
        fill_trace(&mut trace, n_trace, table_size, &values, &mult, a);
        assert_eq!(count_violations(&trace, n_trace, table_size, a), 0);

        // Bump one component of an interior ACC cell.
        let r = table_size + 2;
        trace[FE_ACC][r] += F::from(1u64);
        assert!(count_violations(&trace, n_trace, table_size, a) > 0,
            "tampered accumulator must fire a constraint");
    }

    /// The table region is pinned: forging a table row's value to cancel
    /// an out-of-range lookup is caught by the table-pin constraint.
    #[test]
    fn acc_table_pin_prevents_forged_table_entry() {
        let s = 4;
        let table_size = 1usize << s;
        let values: Vec<u64> = vec![0, 3, 7];
        let mult = multiplicities(&values, table_size);
        let n_trace = table_size + values.len() + 4;
        let a = alpha();
        let mut trace = make_trace(n_trace);
        fill_trace(&mut trace, n_trace, table_size, &values, &mult, a);
        // Forge table row 5's value to 999 (would create an off-table pole).
        trace[COL_VAL][5] = F::from(999u64);
        let nz = count_violations(&trace, n_trace, table_size, a);
        assert!(nz > 0, "forged table value must trip the table-pin constraint");
    }

    /// Confirm the lookup's F_ext is large enough for the ACTIVE NIST
    /// level: κ_lookup = log2|F_ext| − log2(N + 2^S) ≥ level bits.  The
    /// accumulator inherits ExtField from `permutation_argument` (sextic
    /// at L1/L3, octic at L5), so this is a checked invariant, not a
    /// choice.  Sampling α in the BASE field (63 bits) would fail.
    #[test]
    fn kappa_lookup_satisfies_active_nist_level() {
        // Conservative: Goldilocks p > 2^63, so log2|F_ext| ≥ 63·EXT_DEGREE.
        const GOLDILOCKS_BITS_LB: usize = 63;
        let ext_bits = GOLDILOCKS_BITS_LB * EXT_DEGREE;
        // Generous upper bound on log2(N + 2^S) for a WHOLE ECDSA verify
        // (~2M sub-limbs + the 2^13 table ≈ 2^21; use 2^30 for headroom).
        let n_values_log2 = 30usize;
        let kappa_lookup = ext_bits.saturating_sub(n_values_log2 + 1);

        let (required, level) = if cfg!(feature = "sha3-512") {
            (256usize, "L5/octic")
        } else if cfg!(feature = "sha3-384") {
            (192, "L3/sextic")
        } else {
            (128, "L1/sextic")
        };

        // Base field would be catastrophic — assert we are NOT there.
        assert!(EXT_DEGREE >= 6, "lookup challenge must be in an extension, not Fp");
        assert!(
            kappa_lookup >= required,
            "{level}: kappa_lookup = {kappa_lookup} bits (EXT_DEGREE={EXT_DEGREE}, \
             ext_bits={ext_bits}) must be ≥ {required}",
        );
        // κ_lookup must not be the binding term (it never is here).
        assert!(kappa_lookup > 256, "kappa_lookup {kappa_lookup} unexpectedly small");
    }
}
