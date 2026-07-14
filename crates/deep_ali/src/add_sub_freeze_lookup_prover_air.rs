// add_sub_freeze_lookup_prover_air.rs — fillable lookup variants of the
// ADD, SUB, and FREEZE gadgets, completing the set of P-256 field
// primitives (mul is in `mul_lookup_prover_air`).  Same pattern: reuse
// the vetted original fill for the arithmetic, re-place the output(s) as
// sub-limbs, and emit local constraints = sub-limb-pack + the gadget's
// carry/borrow/mux logic (which uses the limb cells, never the bit cells,
// so it is unchanged).  Sub-limb RANGE is enforced by the shared LogUp
// accumulator.  κ_sys unchanged.
//
//   ADD    local cons: 10 pack + 10 carry-chain + 9 carry-bool + 1  = 30
//   SUB    local cons: 10 pack + 10 diff + 10 pos + 10 neg + 10 mutex + 1 = 51
//   FREEZE local cons: 20 pack (diff+c) + 10 chain + 10 pos + 10 neg
//                      + 10 mutex + 1 + 10 mux                       = 71
//   lookup values: ADD/SUB 20 (c), FREEZE 40 (diff + c), all ∈ [0,2^13).

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::add_sub_lookup_air::{alloc_add_lookup, alloc_sub_lookup, AddLookupLayout, SubLookupLayout};
use crate::p256_field::{FieldElement, LIMB_BITS, NUM_LIMBS, P_LIMBS_TIGHT};
use crate::p256_field_air::{
    fill_add_gadget, fill_freeze_gadget, fill_sub_gadget, AddGadgetLayout,
    ELEMENT_BIT_CELLS, FreezeGadgetLayout, SubGadgetLayout,
};
use crate::range_lookup_air::decompose_sublimbs;

const S: usize = 13; // sub-limb bits
const SPL: usize = 2; // sub-limbs per limb

fn read_i64(trace: &[Vec<F>], row: usize, base: usize, n: usize) -> Vec<i64> {
    use ark_ff::PrimeField;
    (0..n).map(|i| trace[base + i][row].into_bigint().as_ref()[0] as i64).collect()
}

/// Pack constraint residuals for one element:  limb − (sub0 + 2^13·sub1).
fn pack_residuals(cur: &[F], limbs_base: usize, sublimbs_base: usize, out: &mut Vec<F>) {
    let radix = F::from(1u64 << S);
    for i in 0..NUM_LIMBS {
        let packed = cur[sublimbs_base + i * SPL] + radix * cur[sublimbs_base + i * SPL + 1];
        out.push(cur[limbs_base + i] - packed);
    }
}

fn place_element_sublimbs(trace: &mut [Vec<F>], row: usize, limbs: &[i64], limbs_base: usize, sublimbs_base: usize) {
    for i in 0..NUM_LIMBS {
        trace[limbs_base + i][row] = F::from(limbs[i] as u64);
        let subs = decompose_sublimbs(limbs[i] as u64, LIMB_BITS as usize, S);
        for m in 0..SPL {
            trace[sublimbs_base + i * SPL + m][row] = F::from(subs[m]);
        }
    }
}

fn read_sublimb_values(cur: &[F], sublimbs_base: usize, n: usize) -> Vec<u64> {
    use ark_ff::PrimeField;
    (0..n).map(|i| cur[sublimbs_base + i].into_bigint().as_ref()[0]).collect()
}

// ═══════════════════════════════════════════════════════════════════
//  ADD
// ═══════════════════════════════════════════════════════════════════

pub const ADD_LOOKUP_PROVER_CONSTRAINTS: usize = NUM_LIMBS + NUM_LIMBS + (NUM_LIMBS - 1) + 1; // 30

fn scratch_add(a: &FieldElement, b: &FieldElement) -> (Vec<i64>, Vec<i64>) {
    // c limbs + carries via the vetted fill.
    let a0 = 0; let b0 = NUM_LIMBS; let c0 = 2 * NUM_LIMBS;
    let c_bits = c0 + NUM_LIMBS; let carries = c_bits + ELEMENT_BIT_CELLS;
    let total = carries + NUM_LIMBS;
    let lay = AddGadgetLayout { a_limbs_base: a0, b_limbs_base: b0, c_limbs_base: c0, c_bits_base: c_bits, carries_base: carries };
    let mut sc: Vec<Vec<F>> = (0..total).map(|_| vec![F::zero(); 1]).collect();
    fill_add_gadget(&mut sc, 0, &lay, a, b);
    (read_i64(&sc, 0, c0, NUM_LIMBS), read_i64(&sc, 0, carries, NUM_LIMBS))
}

pub fn fill_add_lookup(trace: &mut [Vec<F>], row: usize, layout: &AddLookupLayout, a: &FieldElement, b: &FieldElement) {
    let (c, carries) = scratch_add(a, b);
    for i in 0..NUM_LIMBS {
        trace[layout.a_limbs_base + i][row] = F::from(a.limbs[i] as u64);
        trace[layout.b_limbs_base + i][row] = F::from(b.limbs[i] as u64);
        trace[layout.carries_base + i][row] = F::from(carries[i] as u64);
    }
    place_element_sublimbs(trace, row, &c, layout.c_limbs_base, layout.c_sublimbs_base);
}

pub fn eval_add_lookup(cur: &[F], layout: &AddLookupLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(ADD_LOOKUP_PROVER_CONSTRAINTS);
    pack_residuals(cur, layout.c_limbs_base, layout.c_sublimbs_base, &mut out);
    let radix = F::from(1u64 << LIMB_BITS);
    for k in 0..NUM_LIMBS {
        let carry_in = if k == 0 { F::zero() } else { cur[layout.carries_base + k - 1] };
        out.push(cur[layout.a_limbs_base + k] + cur[layout.b_limbs_base + k] + carry_in
            - cur[layout.c_limbs_base + k] - radix * cur[layout.carries_base + k]);
    }
    for k in 0..NUM_LIMBS - 1 {
        let cy = cur[layout.carries_base + k];
        out.push(cy * (F::one() - cy));
    }
    out.push(cur[layout.carries_base + NUM_LIMBS - 1]);
    out
}

pub fn add_lookup_values(cur: &[F], layout: &AddLookupLayout) -> Vec<u64> {
    read_sublimb_values(cur, layout.c_sublimbs_base, NUM_LIMBS * SPL)
}

// ═══════════════════════════════════════════════════════════════════
//  SUB
// ═══════════════════════════════════════════════════════════════════

pub const SUB_LOOKUP_PROVER_CONSTRAINTS: usize = NUM_LIMBS + 4 * NUM_LIMBS + 1; // 51

fn scratch_sub(a: &FieldElement, b: &FieldElement) -> (Vec<i64>, Vec<i64>, Vec<i64>) {
    let a0 = 0; let b0 = NUM_LIMBS; let c0 = 2 * NUM_LIMBS;
    let c_bits = c0 + NUM_LIMBS; let c_pos = c_bits + ELEMENT_BIT_CELLS; let c_neg = c_pos + NUM_LIMBS;
    let total = c_neg + NUM_LIMBS;
    let lay = SubGadgetLayout { a_limbs_base: a0, b_limbs_base: b0, c_limbs_base: c0, c_bits_base: c_bits, c_pos_base: c_pos, c_neg_base: c_neg };
    let mut sc: Vec<Vec<F>> = (0..total).map(|_| vec![F::zero(); 1]).collect();
    fill_sub_gadget(&mut sc, 0, &lay, a, b);
    (read_i64(&sc, 0, c0, NUM_LIMBS), read_i64(&sc, 0, c_pos, NUM_LIMBS), read_i64(&sc, 0, c_neg, NUM_LIMBS))
}

pub fn fill_sub_lookup(trace: &mut [Vec<F>], row: usize, layout: &SubLookupLayout, a: &FieldElement, b: &FieldElement) {
    let (c, cpos, cneg) = scratch_sub(a, b);
    for i in 0..NUM_LIMBS {
        trace[layout.a_limbs_base + i][row] = F::from(a.limbs[i] as u64);
        trace[layout.b_limbs_base + i][row] = F::from(b.limbs[i] as u64);
        trace[layout.c_pos_base + i][row] = F::from(cpos[i] as u64);
        trace[layout.c_neg_base + i][row] = F::from(cneg[i] as u64);
    }
    place_element_sublimbs(trace, row, &c, layout.c_limbs_base, layout.c_sublimbs_base);
}

pub fn eval_sub_lookup(cur: &[F], layout: &SubLookupLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(SUB_LOOKUP_PROVER_CONSTRAINTS);
    pack_residuals(cur, layout.c_limbs_base, layout.c_sublimbs_base, &mut out);
    let radix = F::from(1u64 << LIMB_BITS);
    let net = |k: usize| cur[layout.c_pos_base + k] - cur[layout.c_neg_base + k];
    for k in 0..NUM_LIMBS {
        let carry_in = if k == 0 { F::zero() } else { net(k - 1) };
        out.push(cur[layout.a_limbs_base + k] + F::from(P_LIMBS_TIGHT[k] as u64)
            - cur[layout.b_limbs_base + k] + carry_in - cur[layout.c_limbs_base + k] - radix * net(k));
    }
    for k in 0..NUM_LIMBS { let cp = cur[layout.c_pos_base + k]; out.push(cp * (F::one() - cp)); }
    for k in 0..NUM_LIMBS { let cn = cur[layout.c_neg_base + k]; out.push(cn * (F::one() - cn)); }
    for k in 0..NUM_LIMBS { out.push(cur[layout.c_pos_base + k] * cur[layout.c_neg_base + k]); }
    out.push(cur[layout.c_pos_base + NUM_LIMBS - 1] + cur[layout.c_neg_base + NUM_LIMBS - 1]);
    out
}

pub fn sub_lookup_values(cur: &[F], layout: &SubLookupLayout) -> Vec<u64> {
    read_sublimb_values(cur, layout.c_sublimbs_base, NUM_LIMBS * SPL)
}

// ═══════════════════════════════════════════════════════════════════
//  FREEZE  (two sub-limb blocks: diff + c)
// ═══════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug)]
pub struct FreezeLookupLayout {
    pub a_limbs_base: usize,
    pub diff_limbs_base: usize,
    pub diff_sublimbs_base: usize,
    pub c_limbs_base: usize,
    pub c_sublimbs_base: usize,
    pub c_pos_base: usize,
    pub c_neg_base: usize,
}

pub const FREEZE_LOOKUP_PROVER_CONSTRAINTS: usize = 2 * NUM_LIMBS + 4 * NUM_LIMBS + 1 + NUM_LIMBS; // 71

pub fn alloc_freeze_lookup(cursor: &mut usize, a_limbs_base: usize) -> FreezeLookupLayout {
    let diff_limbs_base = *cursor;
    let diff_sublimbs_base = diff_limbs_base + NUM_LIMBS;
    let c_limbs_base = diff_sublimbs_base + NUM_LIMBS * SPL;
    let c_sublimbs_base = c_limbs_base + NUM_LIMBS;
    let c_pos_base = c_sublimbs_base + NUM_LIMBS * SPL;
    let c_neg_base = c_pos_base + NUM_LIMBS;
    *cursor = c_neg_base + NUM_LIMBS;
    FreezeLookupLayout { a_limbs_base, diff_limbs_base, diff_sublimbs_base, c_limbs_base, c_sublimbs_base, c_pos_base, c_neg_base }
}

fn scratch_freeze(a: &FieldElement) -> (Vec<i64>, Vec<i64>, Vec<i64>, Vec<i64>) {
    let a0 = 0; let d0 = NUM_LIMBS; let d_bits = d0 + NUM_LIMBS;
    let c0 = d_bits + ELEMENT_BIT_CELLS; let c_bits = c0 + NUM_LIMBS;
    let c_pos = c_bits + ELEMENT_BIT_CELLS; let c_neg = c_pos + NUM_LIMBS;
    let total = c_neg + NUM_LIMBS;
    let lay = FreezeGadgetLayout { a_limbs_base: a0, diff_limbs_base: d0, diff_bits_base: d_bits, c_limbs_base: c0, c_bits_base: c_bits, c_pos_base: c_pos, c_neg_base: c_neg };
    let mut sc: Vec<Vec<F>> = (0..total).map(|_| vec![F::zero(); 1]).collect();
    for i in 0..NUM_LIMBS { sc[a0 + i][0] = F::from(a.limbs[i] as u64); }
    fill_freeze_gadget(&mut sc, 0, &lay, a);
    (read_i64(&sc, 0, d0, NUM_LIMBS), read_i64(&sc, 0, c0, NUM_LIMBS), read_i64(&sc, 0, c_pos, NUM_LIMBS), read_i64(&sc, 0, c_neg, NUM_LIMBS))
}

pub fn fill_freeze_lookup(trace: &mut [Vec<F>], row: usize, layout: &FreezeLookupLayout, a: &FieldElement) {
    let (diff, c, cpos, cneg) = scratch_freeze(a);
    for i in 0..NUM_LIMBS {
        trace[layout.a_limbs_base + i][row] = F::from(a.limbs[i] as u64);
        trace[layout.c_pos_base + i][row] = F::from(cpos[i] as u64);
        trace[layout.c_neg_base + i][row] = F::from(cneg[i] as u64);
    }
    place_element_sublimbs(trace, row, &diff, layout.diff_limbs_base, layout.diff_sublimbs_base);
    place_element_sublimbs(trace, row, &c, layout.c_limbs_base, layout.c_sublimbs_base);
}

pub fn eval_freeze_lookup(cur: &[F], layout: &FreezeLookupLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(FREEZE_LOOKUP_PROVER_CONSTRAINTS);
    pack_residuals(cur, layout.diff_limbs_base, layout.diff_sublimbs_base, &mut out);
    pack_residuals(cur, layout.c_limbs_base, layout.c_sublimbs_base, &mut out);
    let radix = F::from(1u64 << LIMB_BITS);
    let net = |k: usize| cur[layout.c_pos_base + k] - cur[layout.c_neg_base + k];
    for k in 0..NUM_LIMBS {
        let carry_in = if k == 0 { F::zero() } else { net(k - 1) };
        out.push(cur[layout.a_limbs_base + k] - F::from(P_LIMBS_TIGHT[k] as u64)
            - cur[layout.diff_limbs_base + k] + carry_in - radix * net(k));
    }
    for k in 0..NUM_LIMBS { let cp = cur[layout.c_pos_base + k]; out.push(cp * (F::one() - cp)); }
    for k in 0..NUM_LIMBS { let cn = cur[layout.c_neg_base + k]; out.push(cn * (F::one() - cn)); }
    for k in 0..NUM_LIMBS { out.push(cur[layout.c_pos_base + k] * cur[layout.c_neg_base + k]); }
    out.push(cur[layout.c_pos_base + NUM_LIMBS - 1]);
    let c_neg_9 = cur[layout.c_neg_base + NUM_LIMBS - 1];
    for k in 0..NUM_LIMBS {
        out.push(cur[layout.c_limbs_base + k] - cur[layout.diff_limbs_base + k]
            - c_neg_9 * (cur[layout.a_limbs_base + k] - cur[layout.diff_limbs_base + k]));
    }
    out
}

pub fn freeze_lookup_values(cur: &[F], layout: &FreezeLookupLayout) -> Vec<u64> {
    let mut v = read_sublimb_values(cur, layout.diff_sublimbs_base, NUM_LIMBS * SPL);
    v.extend(read_sublimb_values(cur, layout.c_sublimbs_base, NUM_LIMBS * SPL));
    v
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permutation_argument::{ExtField, EXT_DEGREE};
    use crate::range_lookup_acc_air::{self, multiplicities};
    use crate::tower_field::TowerField;

    fn make(w: usize) -> Vec<Vec<F>> { (0..w).map(|_| vec![F::zero(); 1]).collect() }
    fn alpha() -> ExtField {
        let c: Vec<F> = (0..EXT_DEGREE).map(|i| F::from(0x0700_0000u64 + 29 * i as u64 + 7)).collect();
        ExtField::from_fp_components(&c).unwrap()
    }
    fn ops() -> (FieldElement, FieldElement) {
        let mut a = FieldElement::zero(); a.limbs = [1234567, 89, 4444, 999, 12, 65535, 7, 100000, 3, 42];
        let mut b = FieldElement::zero(); b.limbs = [9, 8, 7, 6, 5, 4, 3, 2, 1, 111111];
        (a, b)
    }

    fn accumulator_ok(vals: &[u64]) -> bool {
        assert!(vals.iter().all(|&v| v < (1 << 13)));
        let table_size = 1usize << 13;
        let mult = multiplicities(vals, table_size);
        let n_trace = (table_size + vals.len() + 1).next_power_of_two();
        let mut acc: Vec<Vec<F>> = (0..range_lookup_acc_air::WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
        range_lookup_acc_air::fill_trace(&mut acc, n_trace, table_size, vals, &mult, alpha());
        range_lookup_acc_air::count_violations(&acc, n_trace, table_size, alpha()) == 0
    }

    #[test]
    fn fillable_add_end_to_end() {
        let mut cur = 0; let l0 = alloc_add_lookup(&mut cur, 0, 0);
        let a_base = cur; let b_base = a_base + NUM_LIMBS; let w = b_base + NUM_LIMBS;
        let layout = AddLookupLayout { a_limbs_base: a_base, b_limbs_base: b_base, ..l0 };
        let (a, b) = ops();
        let mut t = make(w);
        fill_add_lookup(&mut t, 0, &layout, &a, &b);
        let row: Vec<F> = (0..w).map(|c| t[c][0]).collect();
        assert_eq!(eval_add_lookup(&row, &layout).len(), ADD_LOOKUP_PROVER_CONSTRAINTS);
        assert_eq!(eval_add_lookup(&row, &layout).iter().filter(|v| !v.is_zero()).count(), 0);
        assert!(accumulator_ok(&add_lookup_values(&row, &layout)));
    }

    #[test]
    fn fillable_sub_end_to_end() {
        let mut cur = 0; let l0 = alloc_sub_lookup(&mut cur, 0, 0);
        let a_base = cur; let b_base = a_base + NUM_LIMBS; let w = b_base + NUM_LIMBS;
        let layout = SubLookupLayout { a_limbs_base: a_base, b_limbs_base: b_base, ..l0 };
        let (a, b) = ops();
        let mut t = make(w);
        fill_sub_lookup(&mut t, 0, &layout, &a, &b);
        let row: Vec<F> = (0..w).map(|c| t[c][0]).collect();
        assert_eq!(eval_sub_lookup(&row, &layout).iter().filter(|v| !v.is_zero()).count(), 0);
        assert!(accumulator_ok(&sub_lookup_values(&row, &layout)));
    }

    #[test]
    fn fillable_freeze_end_to_end() {
        let mut cur = 0; let a_base = cur; cur += NUM_LIMBS;
        let layout = alloc_freeze_lookup(&mut cur, a_base);
        let w = cur;
        // a in [0, 2p): use a+b (native, non-canonical tight input to freeze).
        let (a, b) = ops();
        let a_in = a.add(&b);
        let mut t = make(w);
        fill_freeze_lookup(&mut t, 0, &layout, &a_in);
        let row: Vec<F> = (0..w).map(|c| t[c][0]).collect();
        assert_eq!(eval_freeze_lookup(&row, &layout).len(), FREEZE_LOOKUP_PROVER_CONSTRAINTS);
        assert_eq!(eval_freeze_lookup(&row, &layout).iter().filter(|v| !v.is_zero()).count(), 0);
        assert!(accumulator_ok(&freeze_lookup_values(&row, &layout)));
    }

    /// One shared accumulator across ALL THREE gadget types at once.
    #[test]
    fn shared_accumulator_across_add_sub_freeze() {
        let (a, b) = ops();
        // Build the three gadgets in one trace region and pool their values.
        let mut cur = 0;
        let al0 = alloc_add_lookup(&mut cur, 0, 0); let aa = cur; let ab = aa + NUM_LIMBS; cur = ab + NUM_LIMBS;
        let add_l = AddLookupLayout { a_limbs_base: aa, b_limbs_base: ab, ..al0 };
        let sl0 = alloc_sub_lookup(&mut cur, 0, 0); let sa = cur; let sb = sa + NUM_LIMBS; cur = sb + NUM_LIMBS;
        let sub_l = SubLookupLayout { a_limbs_base: sa, b_limbs_base: sb, ..sl0 };
        let fa = cur; cur += NUM_LIMBS; let frz_l = alloc_freeze_lookup(&mut cur, fa);
        let w = cur;

        let mut t = make(w);
        fill_add_lookup(&mut t, 0, &add_l, &a, &b);
        fill_sub_lookup(&mut t, 0, &sub_l, &a, &b);
        fill_freeze_lookup(&mut t, 0, &frz_l, &a.add(&b));
        let row: Vec<F> = (0..w).map(|c| t[c][0]).collect();

        // All local constraints hold.
        assert_eq!(eval_add_lookup(&row, &add_l).iter().filter(|v| !v.is_zero()).count(), 0);
        assert_eq!(eval_sub_lookup(&row, &sub_l).iter().filter(|v| !v.is_zero()).count(), 0);
        assert_eq!(eval_freeze_lookup(&row, &frz_l).iter().filter(|v| !v.is_zero()).count(), 0);

        // Pool every gadget's sub-limbs into ONE accumulator.
        let mut vals = add_lookup_values(&row, &add_l);
        vals.extend(sub_lookup_values(&row, &sub_l));
        vals.extend(freeze_lookup_values(&row, &frz_l));
        assert!(accumulator_ok(&vals), "one accumulator must validate add+sub+freeze sub-limbs");
    }
}
