// group_op_lookup_prover_air.rs — compose the fillable field-gadget lookup
// provers into fillable group_add / group_double: fill a REAL EC operation,
// confirm its arithmetic, and route EVERY sub-gadget's range-checked output
// sub-limbs through ONE shared LogUp accumulator.
//
// The point-op layouts expose their sub-gadgets as iterable Vecs
// (`muls`, `adds`, `subs`, `freezes_*`), so we:
//   1. build + fill the real group_add/group_double (correct RCB-2016
//      intermediates, via the vetted `fill_group_*_gadget`),
//   2. `eval_group_*_gadget` == 0  → the arithmetic is valid,
//   3. read every sub-gadget's range-checked output(s) — mul: c AND q;
//      add/sub: c; freeze: diff AND c — decompose to 13-bit sub-limbs,
//   4. pool ALL of them into ONE accumulator and confirm it holds.
//
// This is the composition: a whole point-op's range-check load (thousands
// of sub-limbs across ~35–45 sub-gadgets) validated by a single LogUp
// column, the same [0,2^26) guarantee as bit decomposition.  κ_sys
// unchanged.  The live cell counts (group_add 41352→5436, group_double
// 33414→4332) are in `point_op_lookup_air`.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;

use crate::p256_field::{FieldElement, LIMB_BITS, NUM_LIMBS};
use crate::p256_group::{AffinePoint, GENERATOR};
use crate::p256_group_air::{
    build_group_add_layout, build_group_double_layout, eval_group_add_gadget,
    eval_group_double_gadget, fill_group_add_gadget, fill_group_double_gadget,
    GroupAddGadgetLayout, GroupDoubleGadgetLayout,
};
use crate::permutation_argument::ExtField;
use crate::range_lookup_acc_air::{self, multiplicities};
use crate::range_lookup_air::decompose_sublimbs;

const S: usize = 13; // sub-limb bits

fn read_elem(trace: &[Vec<F>], row: usize, base: usize) -> [u64; NUM_LIMBS] {
    use ark_ff::PrimeField;
    let mut l = [0u64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        l[i] = trace[base + i][row].into_bigint().as_ref()[0];
    }
    l
}

fn push_sublimbs(vals: &mut Vec<u64>, limbs: &[u64; NUM_LIMBS]) {
    for &l in limbs.iter() {
        vals.extend(decompose_sublimbs(l, LIMB_BITS as usize, S));
    }
}

/// Every range-checked output element of a filled group_add, flattened to
/// its 13-bit sub-limbs (the accumulator's lookup value set).
fn collect_add_sublimbs(trace: &[Vec<F>], row: usize, layout: &GroupAddGadgetLayout) -> Vec<u64> {
    let mut v = Vec::new();
    for m in &layout.muls {
        push_sublimbs(&mut v, &read_elem(trace, row, m.c_limbs_base));
        push_sublimbs(&mut v, &read_elem(trace, row, m.q_limbs_base));
    }
    for a in &layout.adds {
        push_sublimbs(&mut v, &read_elem(trace, row, a.c_limbs_base));
    }
    for s in &layout.subs {
        push_sublimbs(&mut v, &read_elem(trace, row, s.c_limbs_base));
    }
    for f in layout.freezes_after_adds.iter().chain(layout.freezes_after_subs.iter()) {
        push_sublimbs(&mut v, &read_elem(trace, row, f.diff_limbs_base));
        push_sublimbs(&mut v, &read_elem(trace, row, f.c_limbs_base));
    }
    v
}

fn collect_double_sublimbs(trace: &[Vec<F>], row: usize, layout: &GroupDoubleGadgetLayout) -> Vec<u64> {
    let mut v = Vec::new();
    for m in &layout.muls {
        push_sublimbs(&mut v, &read_elem(trace, row, m.c_limbs_base));
        push_sublimbs(&mut v, &read_elem(trace, row, m.q_limbs_base));
    }
    for a in &layout.adds {
        push_sublimbs(&mut v, &read_elem(trace, row, a.c_limbs_base));
    }
    for s in &layout.subs {
        push_sublimbs(&mut v, &read_elem(trace, row, s.c_limbs_base));
    }
    for f in layout.freezes_after_adds.iter().chain(layout.freezes_after_subs.iter()) {
        push_sublimbs(&mut v, &read_elem(trace, row, f.diff_limbs_base));
        push_sublimbs(&mut v, &read_elem(trace, row, f.c_limbs_base));
    }
    v
}

fn accumulator_holds(vals: &[u64], alpha: ExtField) -> bool {
    if !vals.iter().all(|&x| x < (1u64 << S)) {
        return false;
    }
    let table_size = 1usize << S;
    let mult = multiplicities(vals, table_size);
    let n_trace = (table_size + vals.len() + 1).next_power_of_two();
    let mut acc: Vec<Vec<F>> =
        (0..range_lookup_acc_air::WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
    range_lookup_acc_air::fill_trace(&mut acc, n_trace, table_size, vals, &mult, alpha);
    range_lookup_acc_air::count_violations(&acc, n_trace, table_size, alpha) == 0
}

fn place_proj(trace: &mut [Vec<F>], row: usize, xb: usize, yb: usize, zb: usize, p: &AffinePoint) {
    for i in 0..NUM_LIMBS {
        trace[xb + i][row] = F::from(p.x.limbs[i] as u64);
        trace[yb + i][row] = F::from(p.y.limbs[i] as u64);
    }
    trace[zb][row] = F::from(1u64);
    for i in 1..NUM_LIMBS {
        trace[zb + i][row] = F::zero();
    }
}

fn z_one() -> FieldElement {
    let mut t = FieldElement::zero();
    t.limbs[0] = 1;
    t
}

/// Fill a real group_add of `p1 + p2` and return every sub-gadget's
/// range-checked output sub-limbs (the accumulator's lookup value set),
/// together with whether the RCB arithmetic is valid.
pub fn group_add_sublimbs(p1: &AffinePoint, p2: &AffinePoint) -> (Vec<u64>, bool) {
    let (px, py, pz) = (0, NUM_LIMBS, 2 * NUM_LIMBS);
    let (qx, qy, qz) = (3 * NUM_LIMBS, 4 * NUM_LIMBS, 5 * NUM_LIMBS);
    let (layout, total) = build_group_add_layout(6 * NUM_LIMBS, px, py, pz, qx, qy, qz);
    let mut trace: Vec<Vec<F>> = (0..total).map(|_| vec![F::zero(); 1]).collect();
    place_proj(&mut trace, 0, px, py, pz, p1);
    place_proj(&mut trace, 0, qx, qy, qz, p2);
    let zo = z_one();
    fill_group_add_gadget(&mut trace, 0, &layout, &p1.x, &p1.y, &zo, &p2.x, &p2.y, &zo);
    let row: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
    let arithmetic_ok = eval_group_add_gadget(&row, &layout).iter().all(|v| v.is_zero());
    (collect_add_sublimbs(&trace, 0, &layout), arithmetic_ok)
}

/// Fill a real group_add of `p1 + p2`, confirm its arithmetic, and route
/// all sub-gadget sub-limbs through one accumulator.  Returns
/// `(sublimb_count, arithmetic_ok, accumulator_ok)`.
pub fn fillable_group_add(p1: &AffinePoint, p2: &AffinePoint, alpha: ExtField) -> (usize, bool, bool) {
    let (vals, arithmetic_ok) = group_add_sublimbs(p1, p2);
    let acc_ok = accumulator_holds(&vals, alpha);
    (vals.len(), arithmetic_ok, acc_ok)
}

/// Fill a real group_double of `2·p` and return every sub-gadget's
/// range-checked output sub-limbs, with whether the arithmetic is valid.
pub fn group_double_sublimbs(p: &AffinePoint) -> (Vec<u64>, bool) {
    let (px, py, pz) = (0, NUM_LIMBS, 2 * NUM_LIMBS);
    let (layout, total) = build_group_double_layout(3 * NUM_LIMBS, px, py, pz);
    let mut trace: Vec<Vec<F>> = (0..total).map(|_| vec![F::zero(); 1]).collect();
    place_proj(&mut trace, 0, px, py, pz, p);
    let zo = z_one();
    fill_group_double_gadget(&mut trace, 0, &layout, &p.x, &p.y, &zo);
    let row: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
    let arithmetic_ok = eval_group_double_gadget(&row, &layout).iter().all(|v| v.is_zero());
    (collect_double_sublimbs(&trace, 0, &layout), arithmetic_ok)
}

/// Fill a real group_double of `2·p`; same contract as `fillable_group_add`.
pub fn fillable_group_double(p: &AffinePoint, alpha: ExtField) -> (usize, bool, bool) {
    let (vals, arithmetic_ok) = group_double_sublimbs(p);
    let acc_ok = accumulator_holds(&vals, alpha);
    (vals.len(), arithmetic_ok, acc_ok)
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation_argument::EXT_DEGREE;
    use crate::tower_field::TowerField;

    fn alpha() -> ExtField {
        let c: Vec<F> = (0..EXT_DEGREE).map(|i| F::from(0x0800_0000u64 + 31 * i as u64 + 13)).collect();
        ExtField::from_fp_components(&c).unwrap()
    }

    /// Compose: a real group_add (3G + 5G) fills correctly AND all its
    /// sub-gadget sub-limbs pass one shared accumulator.
    #[test]
    fn fillable_group_add_composes() {
        let g = *GENERATOR;
        let p1 = g.double().add(&g);           // 3G
        let p2 = g.double().double().add(&g);   // 5G
        assert!(!p1.infinity && !p2.infinity);
        let (n, arith, acc) = fillable_group_add(&p1, &p2, alpha());
        assert!(arith, "real group_add arithmetic must be valid");
        assert!(acc, "one accumulator must validate every group_add sub-limb");
        // A group_add is 14 mul(×2) + 20 add + 9 sub + 29 freeze(×2) elements
        // × 20 sub-limbs each ≈ 3000+.
        assert!(n > 2000, "expected a point-op's worth of sub-limbs, got {n}");
        println!("\n  group_add: {n} sub-limbs through ONE accumulator, arithmetic ✓, lookup ✓");
    }

    /// Compose: a real group_double (2·7G).
    #[test]
    fn fillable_group_double_composes() {
        let g = *GENERATOR;
        let p = g.double().double().double().add(&g); // 9G (non-identity)
        assert!(!p.infinity);
        let (n, arith, acc) = fillable_group_double(&p, alpha());
        assert!(arith, "real group_double arithmetic must be valid");
        assert!(acc, "one accumulator must validate every group_double sub-limb");
        assert!(n > 1500, "expected a point-op's worth of sub-limbs, got {n}");
        println!("  group_double: {n} sub-limbs through ONE accumulator, arithmetic ✓, lookup ✓\n");
    }

    /// A whole scalar-mult STEP (double + add) pooled into ONE accumulator
    /// — the shared lookup scales across composed point ops.
    #[test]
    fn shared_accumulator_across_double_and_add() {
        let g = *GENERATOR;
        let acc_pt = g.double().add(&g); // 3G
        // group_double of 3G, then group_add of (6G + G): collect both.
        let (px, py, pz) = (0, NUM_LIMBS, 2 * NUM_LIMBS);
        let (dl, dtot) = build_group_double_layout(3 * NUM_LIMBS, px, py, pz);
        let mut dt: Vec<Vec<F>> = (0..dtot).map(|_| vec![F::zero(); 1]).collect();
        place_proj(&mut dt, 0, px, py, pz, &acc_pt);
        let zo = z_one();
        fill_group_double_gadget(&mut dt, 0, &dl, &acc_pt.x, &acc_pt.y, &zo);
        let mut vals = collect_double_sublimbs(&dt, 0, &dl);

        let six_g = acc_pt.double(); // 6G
        let (ax, ay, az) = (0, NUM_LIMBS, 2 * NUM_LIMBS);
        let (bx, by, bz) = (3 * NUM_LIMBS, 4 * NUM_LIMBS, 5 * NUM_LIMBS);
        let (al, atot) = build_group_add_layout(6 * NUM_LIMBS, ax, ay, az, bx, by, bz);
        let mut at: Vec<Vec<F>> = (0..atot).map(|_| vec![F::zero(); 1]).collect();
        place_proj(&mut at, 0, ax, ay, az, &six_g);
        place_proj(&mut at, 0, bx, by, bz, &g);
        fill_group_add_gadget(&mut at, 0, &al, &six_g.x, &six_g.y, &zo, &g.x, &g.y, &zo);
        vals.extend(collect_add_sublimbs(&at, 0, &al));

        assert!(accumulator_holds(&vals, alpha()),
            "one accumulator must validate a full scalar-mult step ({} sub-limbs)", vals.len());
        println!("  scalar-mult step (double+add): {} sub-limbs through ONE accumulator ✓", vals.len());
    }
}
