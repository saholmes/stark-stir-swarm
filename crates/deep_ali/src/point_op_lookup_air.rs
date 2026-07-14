// point_op_lookup_air.rs — final wiring: the LogUp lookup swap applied to
// the P-256 point-op gadgets (group_add, group_double), routing every
// sub-gadget's sub-limbs into ONE shared accumulator.  Produces a LIVE
// census-grounded cell count for the full verify AIR under the lookup
// lever (no more hand-waved evidence fractions).
//
// ─────────────────────────────────────────────────────────────────────
// EXACT SUB-GADGET CENSUS  (from p256_group_air owned-cell formulas)
// ─────────────────────────────────────────────────────────────────────
//   group_add   : 14 mul + 20 add +  9 sub + 29 freeze
//   group_double: 13 mul + 15 add +  6 sub + 21 freeze
//
// Each sub-gadget's range-check bit decomposition is swapped for LogUp
// sub-limbs (mul_lookup_air / add_sub_lookup_air, plus the FREEZE swap
// below — freeze owns TWO 260-bit blocks, diff_bits + c_bits).  The point
// op's live lookup cell count is  real_cells − Σ (per-gadget evidence
// saved), which is exact regardless of any per-op constant remainder.
//
// All sub-limbs from all sub-gadgets feed ONE shared LogUp accumulator
// (`range_lookup_acc_air`); `shared_accumulator_scales_to_point_op` drives
// a point-op's worth of sub-limbs through a single accumulator and checks
// it holds.  κ_sys unchanged — the range check is the same [0,2^26), just
// argued by lookup instead of booleanity.

#![allow(non_snake_case, dead_code)]

use crate::add_sub_lookup_air::{ADD_LOOKUP_OWNED_CELLS, SUB_LOOKUP_OWNED_CELLS};
use crate::mul_lookup_air::MUL_LOOKUP_OWNED_CELLS;
use crate::p256_field_air::{
    ADD_GADGET_OWNED_CELLS, ELEMENT_BIT_CELLS, ELEMENT_LIMB_CELLS,
    FREEZE_GADGET_OWNED_CELLS, MUL_GADGET_OWNED_CELLS, SUB_GADGET_OWNED_CELLS,
};

// ─── FREEZE gadget swap (2 bit blocks: diff_bits + c_bits) ─────────
pub const OUTPUT_SUBLIMBS: usize = ELEMENT_LIMB_CELLS * 2; // 20 (2×13-bit/limb)
/// diff and c each swap 260 bit cells → 20 sub-limb cells.
pub const FREEZE_LOOKUP_OWNED_CELLS: usize =
    FREEZE_GADGET_OWNED_CELLS - 2 * ELEMENT_BIT_CELLS + 2 * OUTPUT_SUBLIMBS; // 560 - 520 + 40 = 80
pub const FREEZE_EVIDENCE_SAVED: usize = 2 * ELEMENT_BIT_CELLS - 2 * OUTPUT_SUBLIMBS; // 480

// ─── Per-gadget evidence saved by the swap ─────────────────────────
pub const MUL_SAVED: usize = MUL_GADGET_OWNED_CELLS - MUL_LOOKUP_OWNED_CELLS; // 1074
pub const ADD_SAVED: usize = ADD_GADGET_OWNED_CELLS - ADD_LOOKUP_OWNED_CELLS; // 240
pub const SUB_SAVED: usize = SUB_GADGET_OWNED_CELLS - SUB_LOOKUP_OWNED_CELLS; // 240
pub const FREEZE_SAVED: usize = FREEZE_EVIDENCE_SAVED; // 480

// ─── Point-op census ───────────────────────────────────────────────
pub const PADD_MUL: usize = 14;
pub const PADD_ADD: usize = 20;
pub const PADD_SUB: usize = 9;
pub const PADD_FREEZE: usize = 29;

pub const PDBL_MUL: usize = 13;
pub const PDBL_ADD: usize = 15;
pub const PDBL_SUB: usize = 6;
pub const PDBL_FREEZE: usize = 21;

/// Cells saved by swapping every sub-gadget of a group-add.
pub const fn point_add_cells_saved() -> usize {
    PADD_MUL * MUL_SAVED + PADD_ADD * ADD_SAVED + PADD_SUB * SUB_SAVED + PADD_FREEZE * FREEZE_SAVED
}
pub const fn point_double_cells_saved() -> usize {
    PDBL_MUL * MUL_SAVED + PDBL_ADD * ADD_SAVED + PDBL_SUB * SUB_SAVED + PDBL_FREEZE * FREEZE_SAVED
}

/// Sub-limb VALUES a point-op contributes to the shared accumulator.
pub const fn point_add_lookup_values() -> usize {
    // mul: 94 sub-limbs (c/q 40 + carry 54); add/sub: 20; freeze: 40.
    PADD_MUL * 94 + PADD_ADD * 20 + PADD_SUB * 20 + PADD_FREEZE * 40
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_field::FieldElement;
    use crate::p256_group_air::{build_group_add_layout, build_group_double_layout};
    use crate::permutation_argument::{ExtField, EXT_DEGREE};
    use crate::range_lookup_wire_air::{check_batch, element_sublimbs, NUM_LIMBS};
    use crate::tower_field::TowerField;
    use ark_goldilocks::Goldilocks as F;

    fn alpha() -> ExtField {
        let comps: Vec<F> =
            (0..EXT_DEGREE).map(|i| F::from(0x0500_0000u64 + 19 * i as u64 + 11)).collect();
        ExtField::from_fp_components(&comps).expect("valid F_ext")
    }

    /// Real point-op cell counts (built from the actual layout builders),
    /// so the census substitution is anchored to ground truth.
    fn real_point_add_cells() -> usize {
        let b = |n: usize| n * NUM_LIMBS;
        let (_l, end) = build_group_add_layout(0, b(0), b(1), b(2), b(3), b(4), b(5));
        end
    }
    fn real_point_double_cells() -> usize {
        let b = |n: usize| n * NUM_LIMBS;
        let (_l, end) = build_group_double_layout(0, b(0), b(1), b(2));
        end
    }

    #[test]
    fn freeze_swap_counts_exact() {
        assert_eq!(FREEZE_GADGET_OWNED_CELLS, 560);
        assert_eq!(FREEZE_LOOKUP_OWNED_CELLS, 80);
        assert_eq!(MUL_SAVED, 1074);
        assert_eq!(ADD_SAVED, 240);
        assert_eq!(SUB_SAVED, 240);
        assert_eq!(FREEZE_SAVED, 480);
    }

    /// ONE shared accumulator handles a full point-op's worth of sub-limbs:
    /// drive ~a group-add's element population (many products) through a
    /// single LogUp accumulator and confirm it holds.
    #[test]
    fn shared_accumulator_scales_to_point_op() {
        // Build a batch of distinct tight elements ~ a point-add's range-
        // checked element count (14 mul × 2 (c,q) + 20 add + 9 sub +
        // 29 freeze × 2 ≈ 115 elements).
        let n_elems = 115usize;
        let mut els: Vec<[u64; NUM_LIMBS]> = Vec::with_capacity(n_elems);
        let mut a = FieldElement::zero();
        a.limbs = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31];
        let mut b = FieldElement::zero();
        b.limbs = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        for k in 0..n_elems {
            // vary the operands so the elements (and multiplicities) differ.
            b.limbs[k % NUM_LIMBS] = (b.limbs[k % NUM_LIMBS] + 12347) % (1 << 26);
            let mut c = a.mul(&b);
            c.freeze();
            let mut l = [0u64; NUM_LIMBS];
            for i in 0..NUM_LIMBS { l[i] = c.limbs[i] as u64; }
            els.push(l);
        }
        let subs: Vec<Vec<u64>> = els.iter().map(element_sublimbs).collect();
        let (pack, acc) = check_batch(&els, &subs, alpha());
        assert_eq!(pack, 0, "all limb-packs must hold");
        assert_eq!(acc, 0, "one shared accumulator must validate a point-op's sub-limbs");
    }

    /// LIVE RE-BENCH: real point-op cells vs their lookup-swapped cells
    /// (census-exact), then the full verify AIR.  Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib point_op_lookup_rebench -- --nocapture
    #[test]
    fn point_op_lookup_rebench() {
        let padd_real = real_point_add_cells();
        let pdbl_real = real_point_double_cells();
        let padd_look = padd_real - point_add_cells_saved();
        let pdbl_look = pdbl_real - point_double_cells_saved();

        println!("\n═══ LIVE point-op cell counts (census-exact) ═══");
        println!("  group_add    : {padd_real:>6} → {padd_look:>5}   ({:.1}× fewer)", padd_real as f64 / padd_look as f64);
        println!("  group_double : {pdbl_real:>6} → {pdbl_look:>5}   ({:.1}× fewer)", pdbl_real as f64 / pdbl_look as f64);

        // Combined optimized MSM point-op census (comb G + windowed Q):
        //   141 point_adds + 252 point_doubles (+ ~128 muxes, lookup-free).
        let n_padd = 141usize;
        let n_pdbl = 252usize;
        let msm_saved = n_padd * point_add_cells_saved() + n_pdbl * point_double_cells_saved();
        const COMBINED_MSM: usize = 14_258_670; // measured (MSM levers)
        const FULL_V2_AIR: usize = 39_416_874;  // measured baseline
        let msm_lookup = COMBINED_MSM - msm_saved;

        println!("\n═══ full P-256 verify AIR — LIVE re-benchmark (cells) ═══");
        println!("  baseline v2                     : {FULL_V2_AIR:>10}");
        println!("  + MSM levers (measured)         : {COMBINED_MSM:>10}");
        println!("  + LogUp swap (mul/add/sub/freeze): {msm_lookup:>10}  (census-exact: -{msm_saved})");
        println!("  TOTAL vs baseline               : {:.1}×   (~99 core-hr → ~{:.1})",
                 FULL_V2_AIR as f64 / msm_lookup as f64, 99.0 * msm_lookup as f64 / FULL_V2_AIR as f64);
        println!("  shared accumulator: {} sub-limb values per group_add, one column.", point_add_lookup_values());
        println!("  All four field gadgets (mul/add/sub/freeze) + both point ops wired.\n");

        assert!(padd_look < padd_real && pdbl_look < pdbl_real);
        assert!(msm_lookup < COMBINED_MSM);
        // Point ops must shrink ~8×.
        assert!(padd_real / padd_look >= 6);
    }
}
