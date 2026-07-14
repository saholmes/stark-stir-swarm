// range_lookup_wire_air.rs — wire a gadget's range-checked element into
// the LogUp accumulator's lookup region.
//
// This closes the loop between the two committed halves of the lookup
// lever:
//   * range_lookup_air        — sub-limb decomposition + LogUp identity
//   * range_lookup_acc_air     — the per-row F_ext accumulator column
//
// A gadget range-checks a field element (10 limbs, each LIMB_BITS=26 bits)
// by proving  limb ∈ [0, 2^26).  Under the lookup migration each limb is
// split into  n = ceil(26/S)  S-bit SUB-LIMBS, tied to the limb by a
// LIMB-PACK constraint
//
//     limb − Σ_k sub_k · 2^{k·S} = 0                                 (P)
//
// and each sub-limb is proven ∈ [0, 2^S) by feeding it into the LogUp
// accumulator's lookup region (its `VAL` column), which the accumulator
// range-checks against the pinned table [0, 2^S).
//
// SOUNDNESS of the composite range check.  (P) forces the limb to equal
// the base-2^S recomposition of its sub-limbs; the lookup forces every
// sub-limb < 2^S.  Hence with n=2, S=13:  0 ≤ limb ≤ (2^13−1)(1+2^13) =
// 2^26 − 1, i.e. exactly the [0, 2^26) the 26-bit decomposition proved —
// at 2 sub-limb cells per limb instead of 26 bit cells.  Neither failure
// mode escapes:
//   * an over-large limb honestly decomposed → a sub-limb ≥ 2^S → the
//     accumulator's final-sum boundary fails (no table pole to cancel it);
//   * an over-large limb whose sub-limbs are forced < 2^S → (P) fails.
//
// The two tests below exercise both paths.  The width win is realised
// here: `evidence_cells` = n·NUM_LIMBS sub-limb cells (20) vs the
// bit-decomposition's LIMB_BITS·NUM_LIMBS (260).

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;

use crate::permutation_argument::ExtField;
use crate::range_lookup_acc_air::{self, multiplicities};
use crate::range_lookup_air::{decompose_sublimbs, recompose_sublimbs, sublimbs_per_limb};

/// P-256 / Ed25519 limb geometry.
pub const NUM_LIMBS: usize = 10;
pub const LIMB_BITS: usize = 26;
/// Sub-limb width: 2 sub-limbs of 13 bits cover [0, 2^26) exactly.
pub const SUBLIMB_BITS: usize = 13;

pub const fn sublimbs_per_element() -> usize {
    NUM_LIMBS * sublimbs_per_limb(LIMB_BITS, SUBLIMB_BITS)
}

/// Sub-limb evidence cells per element (the lookup migration) vs the
/// bit-decomposition it replaces.
pub const fn evidence_cells_lookup() -> usize {
    sublimbs_per_element()
}
pub const fn evidence_cells_bitdecomp() -> usize {
    NUM_LIMBS * LIMB_BITS
}

/// Flatten one element's limbs into their S-bit sub-limbs (LSB first per
/// limb).  These become the values placed into the accumulator's lookup
/// region.  `sublimbs` are computed by masking, so this always returns
/// values in [0, 2^S) — the honest prover's decomposition.
pub fn element_sublimbs(limbs: &[u64; NUM_LIMBS]) -> Vec<u64> {
    limbs
        .iter()
        .flat_map(|&l| decompose_sublimbs(l, LIMB_BITS, SUBLIMB_BITS))
        .collect()
}

/// The LIMB-PACK residuals (P), one per limb, as base-field values:
/// `limb − Σ_k sub_k·2^{k·S}`.  Zero on a consistent (limb, sub-limbs)
/// witness.  `sublimbs` is the flattened per-element sub-limb vector
/// (length `sublimbs_per_element`); the prover may supply values that do
/// NOT match the honest masking (that is the adversarial case handled by
/// the tests).
pub fn limb_pack_residuals(limbs: &[u64; NUM_LIMBS], sublimbs: &[u64]) -> Vec<F> {
    let n = sublimbs_per_limb(LIMB_BITS, SUBLIMB_BITS);
    assert_eq!(sublimbs.len(), NUM_LIMBS * n);
    (0..NUM_LIMBS)
        .map(|i| {
            let subs = &sublimbs[i * n..(i + 1) * n];
            let packed = recompose_sublimbs(subs, SUBLIMB_BITS);
            F::from(limbs[i]) - F::from(packed)
        })
        .collect()
}

/// End-to-end check of a batch of range-checked elements under the lookup
/// migration: assemble every element's sub-limbs into one LogUp
/// accumulator over the table [0, 2^S), and return
/// `(limb_pack_violations, accumulator_violations)`.  Both zero ⇒ every
/// element is validly range-checked to [0, 2^26).
///
/// `witness_sublimbs[e]` is element `e`'s supplied sub-limb vector (the
/// prover's witness); pass `element_sublimbs(&limbs)` for the honest case.
pub fn check_batch(
    elements: &[[u64; NUM_LIMBS]],
    witness_sublimbs: &[Vec<u64>],
    alpha: ExtField,
) -> (usize, usize) {
    assert_eq!(elements.len(), witness_sublimbs.len());

    // (P) limb-pack for each element.
    let mut pack_violations = 0usize;
    for (limbs, subs) in elements.iter().zip(witness_sublimbs) {
        pack_violations += limb_pack_residuals(limbs, subs)
            .iter()
            .filter(|v| !v.is_zero())
            .count();
    }

    // Lookup: all sub-limbs across all elements form the lookup value set.
    let values: Vec<u64> = witness_sublimbs.iter().flatten().copied().collect();
    let table_size = 1usize << SUBLIMB_BITS;
    let mult = multiplicities(&values, table_size);
    let n_trace = (table_size + values.len() + 1).next_power_of_two();

    let mut trace: Vec<Vec<F>> =
        (0..range_lookup_acc_air::WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
    range_lookup_acc_air::fill_trace(&mut trace, n_trace, table_size, &values, &mult, alpha);
    let acc_violations = range_lookup_acc_air::count_violations(&trace, n_trace, table_size, alpha);

    (pack_violations, acc_violations)
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation_argument::EXT_DEGREE;
    use crate::tower_field::TowerField;
    use ark_ff::Field;

    fn alpha() -> ExtField {
        let comps: Vec<F> =
            (0..EXT_DEGREE).map(|i| F::from(0x0200_0000u64 + 11 * i as u64 + 5)).collect();
        ExtField::from_fp_components(&comps).expect("valid F_ext")
    }

    /// A few valid tight elements (every limb < 2^26).
    fn valid_elements() -> Vec<[u64; NUM_LIMBS]> {
        vec![
            [0, 1, (1 << 26) - 1, 12345, 0x2AAAAAA, 7, 42, 0, (1 << 25), 999],
            [(1 << 13), (1 << 13) - 1, 1, 2, 3, 4, 5, 6, 7, 8],
        ]
    }

    /// POSITIVE: honest sub-limbs ⇒ both limb-pack and the lookup
    /// accumulator are satisfied — the element is range-checked to
    /// [0, 2^26) with 20 sub-limb cells instead of 260 bit cells.
    #[test]
    fn wire_valid_elements_pass() {
        let els = valid_elements();
        let subs: Vec<Vec<u64>> = els.iter().map(element_sublimbs).collect();
        let (pack, acc) = check_batch(&els, &subs, alpha());
        assert_eq!(pack, 0, "limb-pack must hold for valid elements");
        assert_eq!(acc, 0, "lookup accumulator must hold for valid elements");
    }

    /// NEGATIVE path A: an over-large limb (= 2^26) honestly decomposed.
    /// The honest masking yields a top sub-limb whose recomposition is
    /// < 2^26, so (P) holds but... actually masking of 2^26 gives sub0=0,
    /// sub1=0 (bit 26 is dropped), which packs to 0 ≠ 2^26 ⇒ LIMB-PACK
    /// fires.  To instead exercise the LOOKUP boundary we force the
    /// sub-limbs to pack correctly (sub1 = 2^13) — which is out of range.
    #[test]
    fn wire_out_of_range_limb_via_forced_pack_fails_lookup() {
        let mut els = valid_elements();
        // Make element 0, limb 0 equal to 2^26 (invalid tight limb).
        els[0][0] = 1 << 26;
        let mut subs: Vec<Vec<u64>> = els.iter().map(element_sublimbs).collect();
        // Force limb 0's sub-limbs to pack to 2^26 exactly: sub0=0, sub1=2^13
        // (2^13 is OUT of the table [0,2^13)).  Now (P) holds, lookup fails.
        subs[0][0] = 0; // sub0 of limb 0
        subs[0][1] = 1 << SUBLIMB_BITS; // sub1 of limb 0 = 8192, out of range
        let (pack, acc) = check_batch(&els, &subs, alpha());
        assert_eq!(pack, 0, "forced sub-limbs make limb-pack hold");
        assert!(acc > 0, "out-of-range sub-limb must fail the lookup accumulator");
    }

    /// NEGATIVE path B: the same over-large limb, but sub-limbs kept in
    /// range (honest masking) ⇒ they pack to < 2^26 ≠ the limb ⇒ (P) fires.
    #[test]
    fn wire_out_of_range_limb_via_masking_fails_pack() {
        let mut els = valid_elements();
        els[0][0] = 1 << 26;
        let subs: Vec<Vec<u64>> = els.iter().map(element_sublimbs).collect(); // honest masking
        let (pack, acc) = check_batch(&els, &subs, alpha());
        assert!(pack > 0, "masked sub-limbs cannot pack to an over-large limb ⇒ limb-pack fires");
        // (the lookup itself passes here — all sub-limbs are in range)
        assert_eq!(acc, 0, "in-range sub-limbs satisfy the lookup");
    }

    /// The width win, wired.
    #[test]
    fn wire_cost_report() {
        let bit = evidence_cells_bitdecomp();
        let look = evidence_cells_lookup();
        println!("\n═══ range-check evidence per element, WIRED ═══");
        println!("  bit decomposition : {bit} cells");
        println!("  sub-limb + lookup : {look} cells  ({:.1}× fewer)", bit as f64 / look as f64);
        println!("  (limb-pack ties sub-limbs to the limb; the accumulator");
        println!("   range-checks the sub-limbs against the pinned table [0,2^{SUBLIMB_BITS}))\n");
        assert!(look * 5 < bit);
    }
}
