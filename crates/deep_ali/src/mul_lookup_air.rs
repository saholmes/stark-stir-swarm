// mul_lookup_air.rs — first gadget-by-gadget layout swap: the P-256
// ModMul workhorse, bit-decomposition range checks → LogUp sub-limb
// lookups.  Enables re-benchmarking the verify AIR under the lookup lever.
//
// ─────────────────────────────────────────────────────────────────────
// WHY THE MUL GADGET FIRST
// ─────────────────────────────────────────────────────────────────────
// The ModMul gadget (`p256_field_air`) owns 1188 cells, of which 1168
// (98.3%!) are RANGE-CHECK BIT DECOMPOSITION:
//     c_bits (260) + q_bits (260) + carry_bits (18·36 = 648).
// Only 20 cells (the c and q limbs) are actual data.  Every point-add is
// ~12 muls and every doubling ~14, so the verify AIR is ~mul-dominated
// and therefore ~98% range-check bits.  Swapping those bits for LogUp
// sub-limbs is the single largest width lever — larger than all the MSM
// levers combined.
//
// ─────────────────────────────────────────────────────────────────────
// THE SWAP
// ─────────────────────────────────────────────────────────────────────
// Keep the schoolbook witness-quotient identity (a·b = q·p + c, 19
// position constraints) and the limb cells unchanged.  Replace:
//   * c range check: 260 bit cells → 20 sub-limb cells (2×13-bit/limb)
//   * q range check: 260 bit cells → 20 sub-limb cells
//   * each 36-bit signed carry: 36 bit cells → 3×12-bit sub-limb cells
// The sub-limbs are tied to their parents by limb-pack constraints and
// range-checked by the shared LogUp accumulator (`range_lookup_acc_air`),
// NOT by local booleanity.  Result: 1188 → 114 cells (10.4× fewer),
// 1207 → 57 LOCAL constraints (the range check moves to the global
// accumulator).  Soundness of the composite range check is proven in
// `range_lookup_wire_air`; κ_sys is unchanged.

#![allow(non_snake_case, dead_code)]

use crate::p256_field_air::{
    ELEMENT_BIT_CELLS, ELEMENT_LIMB_CELLS, MUL_CARRY_BITS, MUL_CARRY_POSITIONS,
    MUL_GADGET_CONSTRAINTS, MUL_GADGET_OWNED_CELLS,
};

/// Sub-limb widths for the swap.
pub const CQ_SUBLIMB_BITS: usize = 13; // 26-bit limb → 2 sub-limbs
pub const CARRY_SUBLIMB_BITS: usize = 12; // 36-bit carry → 3 sub-limbs
pub const CQ_SUBLIMBS_PER_LIMB: usize = 2;
pub const CARRY_SUBLIMBS: usize = MUL_CARRY_BITS / CARRY_SUBLIMB_BITS; // 3
pub const MUL_SCHOOLBOOK_POSITIONS: usize = 2 * ELEMENT_LIMB_CELLS - 1; // 19

/// Range-check EVIDENCE cells in the original (bit-decomp) mul gadget.
pub const MUL_BITDECOMP_EVIDENCE: usize =
    2 * ELEMENT_BIT_CELLS + MUL_CARRY_POSITIONS * MUL_CARRY_BITS; // 1168

/// Data (non-evidence) cells: the c and q limbs.
pub const MUL_DATA_CELLS: usize = 2 * ELEMENT_LIMB_CELLS; // 20

/// Sub-limb evidence cells in the lookup variant.
pub const MUL_LOOKUP_EVIDENCE: usize =
    2 * ELEMENT_LIMB_CELLS * CQ_SUBLIMBS_PER_LIMB           // c,q sub-limbs = 40
    + MUL_CARRY_POSITIONS * CARRY_SUBLIMBS;                 // carry sub-limbs = 54

/// Total owned cells, lookup-variant mul gadget.
pub const MUL_LOOKUP_OWNED_CELLS: usize = MUL_DATA_CELLS + MUL_LOOKUP_EVIDENCE; // 114

/// LOCAL constraints (the range check moves to the global accumulator):
///   limb-pack for c (10) + q (10) + carry (18) + schoolbook (19).
pub const MUL_LOOKUP_LOCAL_CONSTRAINTS: usize =
    2 * ELEMENT_LIMB_CELLS                  // c, q limb-pack
    + MUL_CARRY_POSITIONS                   // carry limb-pack
    + MUL_SCHOOLBOOK_POSITIONS;             // schoolbook positions

/// Number of sub-limb VALUES this gadget contributes to the shared LogUp
/// lookup (c/q into the [0,2^13) table, carries into [0,2^12)).
pub const MUL_LOOKUP_VALUES: usize = MUL_LOOKUP_EVIDENCE; // one value per sub-limb cell

/// Cell-offset descriptor for a lookup-variant mul gadget.  Mirrors
/// `MulGadgetLayout` but with sub-limb bases replacing the bit bases.
#[derive(Clone, Copy, Debug)]
pub struct MulLookupLayout {
    pub a_limbs_base: usize,
    pub b_limbs_base: usize,
    pub c_limbs_base: usize,
    pub c_sublimbs_base: usize, // 2·NUM_LIMBS sub-limb cells
    pub q_limbs_base: usize,
    pub q_sublimbs_base: usize,
    pub carry_sublimbs_base: usize, // MUL_CARRY_POSITIONS·CARRY_SUBLIMBS cells
}

/// Allocate a lookup-variant mul gadget's owned cells at `*cursor`.
pub fn alloc_mul_lookup(cursor: &mut usize, a_limbs_base: usize, b_limbs_base: usize) -> MulLookupLayout {
    let c_limbs_base = *cursor;
    let c_sublimbs_base = c_limbs_base + ELEMENT_LIMB_CELLS;
    let q_limbs_base = c_sublimbs_base + ELEMENT_LIMB_CELLS * CQ_SUBLIMBS_PER_LIMB;
    let q_sublimbs_base = q_limbs_base + ELEMENT_LIMB_CELLS;
    let carry_sublimbs_base = q_sublimbs_base + ELEMENT_LIMB_CELLS * CQ_SUBLIMBS_PER_LIMB;
    *cursor = carry_sublimbs_base + MUL_CARRY_POSITIONS * CARRY_SUBLIMBS;
    MulLookupLayout {
        a_limbs_base, b_limbs_base, c_limbs_base, c_sublimbs_base,
        q_limbs_base, q_sublimbs_base, carry_sublimbs_base,
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Re-benchmark harness
// ═══════════════════════════════════════════════════════════════════

/// Re-benchmark an AIR under the lookup swap given its gadget population.
/// `evidence_fraction` is the share of the AIR's cells that are
/// range-check evidence (from the gadget layout; muls are 0.983).
pub fn rebench_cells(total_cells: usize, evidence_fraction: f64, evidence_shrink: f64) -> usize {
    let data = total_cells as f64 * (1.0 - evidence_fraction);
    let evidence = total_cells as f64 * evidence_fraction / evidence_shrink;
    (data + evidence).round() as usize
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_field::FieldElement;
    use crate::permutation_argument::EXT_DEGREE;
    use crate::range_lookup_wire_air::{check_batch, element_sublimbs, NUM_LIMBS};
    use crate::tower_field::TowerField;
    use crate::permutation_argument::ExtField;
    use ark_goldilocks::Goldilocks as F;

    fn alpha() -> ExtField {
        let comps: Vec<F> =
            (0..EXT_DEGREE).map(|i| F::from(0x0300_0000u64 + 13 * i as u64 + 1)).collect();
        ExtField::from_fp_components(&comps).expect("valid F_ext")
    }

    /// The swapped range check is sound on a REAL ModMul output: compute
    /// c = a·b mod p, take its (tight) limbs, and verify its sub-limbs
    /// pass the wired LogUp lookup + limb-pack.  (q gets identical
    /// treatment; c is the representative product element.)
    #[test]
    fn real_mul_product_passes_lookup_range_check() {
        // Two arbitrary field elements.
        let mut a = FieldElement::zero();
        a.limbs = [1234567, 89, 4444, 999, 12, 65535, 7, 100000, 3, 42];
        let mut b = FieldElement::zero();
        b.limbs = [9, 8, 7, 6, 5, 4, 3, 2, 1, 111111];
        let mut c = a.mul(&b);
        c.freeze(); // canonical, tight limbs

        let limbs: [u64; NUM_LIMBS] = {
            let mut l = [0u64; NUM_LIMBS];
            for i in 0..NUM_LIMBS { l[i] = c.limbs[i] as u64; }
            l
        };
        // Every limb must be a valid tight limb (< 2^26).
        assert!(limbs.iter().all(|&x| x < (1 << 26)), "product limbs must be tight");

        let subs = vec![element_sublimbs(&limbs)];
        let (pack, acc) = check_batch(&[limbs], &subs, alpha());
        assert_eq!(pack, 0, "limb-pack must hold on the real product");
        assert_eq!(acc, 0, "the product's sub-limbs must pass the LogUp lookup");
    }

    /// The swap accounting is exact.
    #[test]
    fn swap_counts_are_exact() {
        assert_eq!(MUL_GADGET_OWNED_CELLS, 1188);
        assert_eq!(MUL_BITDECOMP_EVIDENCE, 1168);
        assert_eq!(MUL_DATA_CELLS, 20);
        assert_eq!(MUL_LOOKUP_OWNED_CELLS, 114);
        assert_eq!(MUL_LOOKUP_EVIDENCE, 94);
        assert_eq!(MUL_LOOKUP_LOCAL_CONSTRAINTS, 57);

        // Layout allocation is consistent with the owned-cell count.
        let mut cursor = 100;
        let start = cursor;
        let _l = alloc_mul_lookup(&mut cursor, 0, 10);
        assert_eq!(cursor - start, MUL_LOOKUP_OWNED_CELLS);
    }

    /// RE-BENCH: the mul-gadget swap and its projected full-AIR effect,
    /// stacked with the MSM levers.  Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib mul_lookup_rebench -- --nocapture
    #[test]
    fn mul_lookup_rebench() {
        let evid_frac = MUL_BITDECOMP_EVIDENCE as f64 / MUL_GADGET_OWNED_CELLS as f64; // 0.983
        let shrink = MUL_BITDECOMP_EVIDENCE as f64 / MUL_LOOKUP_EVIDENCE as f64; // 12.4×

        println!("\n═══ gadget swap #1: P-256 ModMul (bit-decomp → LogUp) ═══");
        println!("  original      : {MUL_GADGET_OWNED_CELLS} cells ({MUL_GADGET_CONSTRAINTS} cons), {:.1}% range-check bits", evid_frac * 100.0);
        println!("  lookup variant: {MUL_LOOKUP_OWNED_CELLS} cells ({MUL_LOOKUP_LOCAL_CONSTRAINTS} local cons + {MUL_LOOKUP_VALUES} lookup values)");
        println!("  per-mul       : {:.1}× fewer cells\n", MUL_GADGET_OWNED_CELLS as f64 / MUL_LOOKUP_OWNED_CELLS as f64);

        // Full-AIR re-bench (projection: the AIR is mul-dominated, so it
        // inherits ~the mul gadget's evidence fraction).  Applied to the
        // measured combined-MSM width from the MSM-lever benches.
        const FULL_V2_AIR: usize = 39_416_874;      // measured, baseline
        const COMBINED_MSM: usize = 14_258_670;     // measured, MSM levers (comb G + windowed Q)
        let air_evid = 0.95f64; // AIR-wide evidence share (muls 98.3%, muxes ~0; conservative)
        let msm_plus_lookup = rebench_cells(COMBINED_MSM, air_evid, shrink);

        println!("═══ full P-256 verify AIR re-benchmark (cells) ═══");
        println!("  baseline v2                         : {FULL_V2_AIR:>10}");
        println!("  + MSM levers (comb G + windowed Q)  : {COMBINED_MSM:>10}  (measured, -62%)");
        println!("  + LogUp range-check (this swap)     : {msm_plus_lookup:>10}  (projected, evidence {:.0}%→{:.1}%)", air_evid*100.0, air_evid*100.0/shrink);
        println!("  total reduction vs baseline         : {:.1}×  (~99 core-hr → ~{:.0})",
                 FULL_V2_AIR as f64 / msm_plus_lookup as f64,
                 99.0 * msm_plus_lookup as f64 / FULL_V2_AIR as f64);
        println!("  NOTE: the lookup lever DOMINATES — bit-decomp is ~98% of the trace.");
        println!("  Remaining: same swap for add/sub gadgets (identical pattern), then");
        println!("  wire all sub-limbs into one shared accumulator for the live measurement.\n");

        assert!(msm_plus_lookup < COMBINED_MSM);
        assert!(MUL_LOOKUP_OWNED_CELLS * 10 < MUL_GADGET_OWNED_CELLS);
    }
}
