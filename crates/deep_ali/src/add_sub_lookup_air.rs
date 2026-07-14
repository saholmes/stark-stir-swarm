// add_sub_lookup_air.rs — gadget swaps #2 and #3: the P-256 field ADD
// and SUB gadgets, bit-decomposition range checks → LogUp sub-limb
// lookups.  Same pattern as `mul_lookup_air`.
//
// Both gadgets range-check their output c by a 260-cell bit decomposition
// (`c_bits`); everything else (carry / borrow cells) is small limb-value
// witness.  The swap replaces `c_bits` (260) with `c_sublimbs` (2×13-bit
// per limb = 20) and moves the range check to the shared LogUp
// accumulator, leaving the carry/borrow logic and limb cells untouched.
//
//   ADD: 280 → 40 cells (7.0×),  260/280 = 92.9% was range-check bits.
//   SUB: 290 → 50 cells (5.8×),  260/290 = 89.7% was range-check bits.
//
// With mul (`mul_lookup_air`), add, and sub all swapped, EVERY field
// gadget the point-add / point-double gadgets are built from is
// lookup-form, so the whole verify AIR inherits the ~12× shrink of its
// range-check evidence.  Soundness is the composite limb-pack + lookup
// proven in `range_lookup_wire_air`; κ_sys unchanged.

#![allow(non_snake_case, dead_code)]

use crate::p256_field_air::{
    ADD_GADGET_CONSTRAINTS, ADD_GADGET_OWNED_CELLS, ELEMENT_BIT_CELLS,
    ELEMENT_LIMB_CELLS, SUB_GADGET_CONSTRAINTS, SUB_GADGET_OWNED_CELLS,
};

/// 26-bit limb → 2 sub-limbs of 13 bits.
pub const CQ_SUBLIMBS_PER_LIMB: usize = 2;
pub const CQ_SUBLIMB_BITS: usize = 13;

/// Sub-limb evidence cells for one range-checked output element.
pub const OUTPUT_SUBLIMBS: usize = ELEMENT_LIMB_CELLS * CQ_SUBLIMBS_PER_LIMB; // 20

// ─── ADD ───────────────────────────────────────────────────────────
/// Owned cells: c_limbs (10) + c_sublimbs (20) + carries (10).
pub const ADD_LOOKUP_OWNED_CELLS: usize =
    ADD_GADGET_OWNED_CELLS - ELEMENT_BIT_CELLS + OUTPUT_SUBLIMBS; // 280 - 260 + 20 = 40
/// Local constraints: original minus the 260 booleanity (moved to lookup).
pub const ADD_LOOKUP_LOCAL_CONSTRAINTS: usize =
    ADD_GADGET_CONSTRAINTS - ELEMENT_BIT_CELLS; // 290 - 260 = 30
pub const ADD_LOOKUP_VALUES: usize = OUTPUT_SUBLIMBS; // 20 sub-limbs → lookup

#[derive(Clone, Copy, Debug)]
pub struct AddLookupLayout {
    pub a_limbs_base: usize,
    pub b_limbs_base: usize,
    pub c_limbs_base: usize,
    pub c_sublimbs_base: usize, // 20 cells (was c_bits, 260)
    pub carries_base: usize,
}

pub fn alloc_add_lookup(cursor: &mut usize, a_limbs_base: usize, b_limbs_base: usize) -> AddLookupLayout {
    let c_limbs_base = *cursor;
    let c_sublimbs_base = c_limbs_base + ELEMENT_LIMB_CELLS;
    let carries_base = c_sublimbs_base + OUTPUT_SUBLIMBS;
    *cursor = carries_base + ELEMENT_LIMB_CELLS;
    AddLookupLayout { a_limbs_base, b_limbs_base, c_limbs_base, c_sublimbs_base, carries_base }
}

// ─── SUB ───────────────────────────────────────────────────────────
/// Owned cells: c_limbs (10) + c_sublimbs (20) + c_pos (10) + c_neg (10).
pub const SUB_LOOKUP_OWNED_CELLS: usize =
    SUB_GADGET_OWNED_CELLS - ELEMENT_BIT_CELLS + OUTPUT_SUBLIMBS; // 290 - 260 + 20 = 50
pub const SUB_LOOKUP_LOCAL_CONSTRAINTS: usize =
    SUB_GADGET_CONSTRAINTS - ELEMENT_BIT_CELLS; // 311 - 260 = 51
pub const SUB_LOOKUP_VALUES: usize = OUTPUT_SUBLIMBS;

#[derive(Clone, Copy, Debug)]
pub struct SubLookupLayout {
    pub a_limbs_base: usize,
    pub b_limbs_base: usize,
    pub c_limbs_base: usize,
    pub c_sublimbs_base: usize,
    pub c_pos_base: usize,
    pub c_neg_base: usize,
}

pub fn alloc_sub_lookup(cursor: &mut usize, a_limbs_base: usize, b_limbs_base: usize) -> SubLookupLayout {
    let c_limbs_base = *cursor;
    let c_sublimbs_base = c_limbs_base + ELEMENT_LIMB_CELLS;
    let c_pos_base = c_sublimbs_base + OUTPUT_SUBLIMBS;
    let c_neg_base = c_pos_base + ELEMENT_LIMB_CELLS;
    *cursor = c_neg_base + ELEMENT_LIMB_CELLS;
    SubLookupLayout { a_limbs_base, b_limbs_base, c_limbs_base, c_sublimbs_base, c_pos_base, c_neg_base }
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_field::FieldElement;
    use crate::permutation_argument::{ExtField, EXT_DEGREE};
    use crate::range_lookup_wire_air::{check_batch, element_sublimbs, NUM_LIMBS};
    use crate::tower_field::TowerField;
    use ark_goldilocks::Goldilocks as F;

    fn alpha() -> ExtField {
        let comps: Vec<F> =
            (0..EXT_DEGREE).map(|i| F::from(0x0400_0000u64 + 17 * i as u64 + 9)).collect();
        ExtField::from_fp_components(&comps).expect("valid F_ext")
    }

    fn tight_limbs(fe: &FieldElement) -> [u64; NUM_LIMBS] {
        let mut c = *fe;
        c.freeze(); // canonical ⊂ tight (< 2^26 per limb)
        let mut l = [0u64; NUM_LIMBS];
        for i in 0..NUM_LIMBS { l[i] = c.limbs[i] as u64; }
        l
    }

    fn operands() -> (FieldElement, FieldElement) {
        let mut a = FieldElement::zero();
        a.limbs = [1234567, 89, 4444, 999, 12, 65535, 7, 100000, 3, 42];
        let mut b = FieldElement::zero();
        b.limbs = [9, 8, 7, 6, 5, 4, 3, 2, 1, 111111];
        (a, b)
    }

    /// The ADD-swap range check on a REAL a+b output element.
    #[test]
    fn real_add_output_passes_lookup_range_check() {
        let (a, b) = operands();
        let limbs = tight_limbs(&a.add(&b));
        assert!(limbs.iter().all(|&x| x < (1 << 26)));
        let subs = vec![element_sublimbs(&limbs)];
        let (pack, acc) = check_batch(&[limbs], &subs, alpha());
        assert_eq!(pack, 0);
        assert_eq!(acc, 0, "a+b sub-limbs must pass the LogUp lookup");
    }

    /// The SUB-swap range check on a REAL a−b output element.
    #[test]
    fn real_sub_output_passes_lookup_range_check() {
        let (a, b) = operands();
        let limbs = tight_limbs(&a.sub(&b));
        assert!(limbs.iter().all(|&x| x < (1 << 26)));
        let subs = vec![element_sublimbs(&limbs)];
        let (pack, acc) = check_batch(&[limbs], &subs, alpha());
        assert_eq!(pack, 0);
        assert_eq!(acc, 0, "a-b sub-limbs must pass the LogUp lookup");
    }

    #[test]
    fn add_sub_swap_counts_exact() {
        assert_eq!(ADD_GADGET_OWNED_CELLS, 280);
        assert_eq!(ADD_LOOKUP_OWNED_CELLS, 40);
        assert_eq!(ADD_LOOKUP_LOCAL_CONSTRAINTS, 30);
        assert_eq!(SUB_GADGET_OWNED_CELLS, 290);
        assert_eq!(SUB_LOOKUP_OWNED_CELLS, 50);
        assert_eq!(SUB_LOOKUP_LOCAL_CONSTRAINTS, 51);

        let mut cur = 100;
        let s = cur;
        let _a = alloc_add_lookup(&mut cur, 0, 10);
        assert_eq!(cur - s, ADD_LOOKUP_OWNED_CELLS);
        let s2 = cur;
        let _b = alloc_sub_lookup(&mut cur, 0, 10);
        assert_eq!(cur - s2, SUB_LOOKUP_OWNED_CELLS);
    }

    /// RE-BENCH: with mul + add + sub ALL swapped, the point ops (built
    /// purely from these three field gadgets) fully inherit the shrink.
    /// Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib add_sub_lookup_rebench -- --nocapture
    #[test]
    fn add_sub_lookup_rebench() {
        use crate::mul_lookup_air::MUL_LOOKUP_OWNED_CELLS;
        use crate::p256_field_air::MUL_GADGET_OWNED_CELLS;
        // Point-op field-gadget census (P-256 RCB complete formulas):
        //   point-add   ≈ 12 mul + 15 add + 6 sub
        // Use per-gadget original vs lookup cells to get the point-op shrink.
        let mul_o = MUL_GADGET_OWNED_CELLS; let mul_l = MUL_LOOKUP_OWNED_CELLS;
        let add_o = ADD_GADGET_OWNED_CELLS; let add_l = ADD_LOOKUP_OWNED_CELLS;
        let sub_o = SUB_GADGET_OWNED_CELLS; let sub_l = SUB_LOOKUP_OWNED_CELLS;

        let padd_o = 12 * mul_o + 15 * add_o + 6 * sub_o;
        let padd_l = 12 * mul_l + 15 * add_l + 6 * sub_l;
        println!("\n═══ point-add gadget under full field-gadget swap ═══");
        println!("  original : {padd_o} cells");
        println!("  lookup   : {padd_l} cells   ({:.1}× fewer)", padd_o as f64 / padd_l as f64);

        // Full-AIR: apply the point-op shrink to the measured combined MSM.
        const COMBINED_MSM: usize = 14_258_670; // measured (comb G + windowed Q)
        const FULL_V2_AIR: usize = 39_416_874;
        let shrink = padd_o as f64 / padd_l as f64;
        // The MSM is ~95% point-op cells; muxes (~5%) are lookup-free.
        let point_frac = 0.95f64;
        let msm_lookup = ((1.0 - point_frac) * COMBINED_MSM as f64
            + point_frac * COMBINED_MSM as f64 / shrink).round() as usize;
        println!("\n═══ full P-256 verify AIR re-benchmark (cells) ═══");
        println!("  baseline v2                        : {FULL_V2_AIR:>10}");
        println!("  + MSM levers                       : {COMBINED_MSM:>10}  (measured)");
        println!("  + LogUp swap (mul+add+sub)         : {msm_lookup:>10}  (projected, point-op {:.1}× shrink)", shrink);
        println!("  total vs baseline                  : {:.1}×  (~99 core-hr → ~{:.0})",
                 FULL_V2_AIR as f64 / msm_lookup as f64, 99.0 * msm_lookup as f64 / FULL_V2_AIR as f64);
        println!("  gadgets swapped: mul ✓  add ✓  sub ✓ — all field primitives done.");
        println!("  Remaining: allocate sub-limb cells in the point-op layouts + one");
        println!("  shared accumulator ⇒ turns this projection into a live measurement.\n");

        assert!(padd_l < padd_o);
        assert!(msm_lookup < COMBINED_MSM);
    }
}
