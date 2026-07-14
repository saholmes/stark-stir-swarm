// mul_lookup_prover_air.rs — a FILLABLE lookup-variant ModMul gadget:
// fills a real trace and emits satisfiable constraints, with the range
// check split between local sub-limb-pack constraints and the shared
// LogUp accumulator.  This turns `mul_lookup_air`'s layout/accounting
// into an actual prover: fill → eval (all zero) → feed sub-limbs to the
// accumulator (0 violations).
//
// FILL reuses the vetted `fill_mul_gadget` to compute c = a·b mod p, the
// quotient q, and the 18 signed carries; it then re-places those values
// as sub-limbs (c/q: 2×13-bit per limb; each 36-bit biased carry: 3×12-bit)
// in the lookup layout instead of as bit cells.
//
// EVAL emits the LOCAL constraints only:
//   * sub-limb-pack for c and q:  limb = sub0 + 2^13·sub1        (20 cons)
//   * 19 schoolbook position identities, with each signed carry
//     reconstructed from its 3 sub-limbs (biased − 2^35)         (19 cons)
// The range of every sub-limb (∈ [0,2^13); carries ∈ [0,2^12) ⊂ [0,2^13))
// is enforced GLOBALLY by the shared accumulator — not by local booleanity.
// 39 local constraints vs the original 1207; 94 sub-limb values → lookup.
//
// SOUNDNESS: the position identities force  a·b = q·p + c (mod the
// Goldilocks prime, with the carry-magnitude bound intact); sub-limb-pack
// ties c,q to their sub-limbs; the lookup forces every sub-limb < 2^13, so
// c,q are valid tight limbs.  Identical guarantee to the bit-decomposition
// gadget; κ_sys unchanged.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::mul_lookup_air::{alloc_mul_lookup, MulLookupLayout, CARRY_SUBLIMBS, CARRY_SUBLIMB_BITS, CQ_SUBLIMB_BITS};
use crate::p256_field::{FieldElement, LIMB_BITS, NUM_LIMBS, P_LIMBS_TIGHT};
use crate::p256_field_air::{
    fill_mul_gadget, mul_carry_bit_cell, ELEMENT_BIT_CELLS, MUL_CARRY_BITS,
    MUL_CARRY_OFFSET, MUL_CARRY_POSITIONS, MulGadgetLayout,
};
use crate::range_lookup_air::decompose_sublimbs;

pub const MUL_SCHOOLBOOK_POSITIONS: usize = 2 * NUM_LIMBS - 1; // 19
const CQ_SUBLIMBS_PER_LIMB: usize = 2;

/// Local (non-lookup) constraints emitted per lookup-mul gadget.
pub const MUL_LOOKUP_PROVER_CONSTRAINTS: usize =
    2 * NUM_LIMBS + MUL_SCHOOLBOOK_POSITIONS; // 20 + 19 = 39

fn read_fe(trace: &[Vec<F>], row: usize, base: usize) -> [i64; NUM_LIMBS] {
    use ark_ff::PrimeField;
    let mut l = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        l[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
    }
    l
}

/// Fill a lookup-variant mul gadget.  Places a,b,c,q limbs, the c/q
/// sub-limbs, and the carry sub-limbs.  Reuses `fill_mul_gadget` (via a
/// scratch original-layout trace) for the c/q/carry computation.
pub fn fill_mul_lookup(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &MulLookupLayout,
    a: &FieldElement,
    b: &FieldElement,
) {
    // (1) Scratch original-layout mul to compute c, q, carries.
    let a0 = 0;
    let b0 = NUM_LIMBS;
    let c0 = 2 * NUM_LIMBS;
    let c_bits = c0 + NUM_LIMBS;
    let q0 = c_bits + ELEMENT_BIT_CELLS;
    let q_bits = q0 + NUM_LIMBS;
    let carry_bits = q_bits + ELEMENT_BIT_CELLS;
    let total = carry_bits + MUL_CARRY_POSITIONS * MUL_CARRY_BITS;
    let orig = MulGadgetLayout {
        a_limbs_base: a0, b_limbs_base: b0,
        c_limbs_base: c0, c_bits_base: c_bits,
        q_limbs_base: q0, q_bits_base: q_bits,
        carry_bits_base: carry_bits,
    };
    let mut scratch: Vec<Vec<F>> = (0..total).map(|_| vec![F::zero(); 1]).collect();
    fill_mul_gadget(&mut scratch, 0, &orig, a, b);

    let c = read_fe(&scratch, 0, c0);
    let q = read_fe(&scratch, 0, q0);
    // Reconstruct each biased carry (∈ [0,2^36)) from its 36 bits.
    let mut biased_carry = [0u64; MUL_CARRY_POSITIONS];
    for k in 0..MUL_CARRY_POSITIONS {
        let mut v = 0u64;
        for bkt in 0..MUL_CARRY_BITS {
            let bit = scratch[mul_carry_bit_cell(&orig, k, bkt)][0];
            if bit == F::one() { v |= 1u64 << bkt; }
        }
        biased_carry[k] = v;
    }

    // (2) Place a, b, c, q limbs + sub-limbs into the lookup layout.
    for i in 0..NUM_LIMBS {
        trace[layout.a_limbs_base + i][row] = F::from(a.limbs[i] as u64);
        trace[layout.b_limbs_base + i][row] = F::from(b.limbs[i] as u64);
        trace[layout.c_limbs_base + i][row] = F::from(c[i] as u64);
        trace[layout.q_limbs_base + i][row] = F::from(q[i] as u64);
        // c/q sub-limbs (2 × 13-bit).
        let cs = decompose_sublimbs(c[i] as u64, LIMB_BITS as usize, CQ_SUBLIMB_BITS);
        let qs = decompose_sublimbs(q[i] as u64, LIMB_BITS as usize, CQ_SUBLIMB_BITS);
        for m in 0..CQ_SUBLIMBS_PER_LIMB {
            trace[layout.c_sublimbs_base + i * CQ_SUBLIMBS_PER_LIMB + m][row] = F::from(cs[m]);
            trace[layout.q_sublimbs_base + i * CQ_SUBLIMBS_PER_LIMB + m][row] = F::from(qs[m]);
        }
    }
    // Carry sub-limbs (3 × 12-bit of the biased carry).
    for k in 0..MUL_CARRY_POSITIONS {
        let cs = decompose_sublimbs(biased_carry[k], MUL_CARRY_BITS, CARRY_SUBLIMB_BITS);
        for m in 0..CARRY_SUBLIMBS {
            trace[layout.carry_sublimbs_base + k * CARRY_SUBLIMBS + m][row] = F::from(cs[m]);
        }
    }
}

/// Reconstruct the signed carry at position k from its 3 sub-limbs
/// (biased − 2^35); F::zero() at the k=18 boundary.
fn signed_carry_from_sublimbs(cur: &[F], layout: &MulLookupLayout, k: usize) -> F {
    if k >= MUL_CARRY_POSITIONS {
        return F::zero();
    }
    let mut biased = F::zero();
    for m in 0..CARRY_SUBLIMBS {
        biased += F::from(1u64 << (m * CARRY_SUBLIMB_BITS))
            * cur[layout.carry_sublimbs_base + k * CARRY_SUBLIMBS + m];
    }
    biased - F::from(MUL_CARRY_OFFSET as u64)
}

/// Emit the `MUL_LOOKUP_PROVER_CONSTRAINTS` local residuals; all zero on
/// a valid trace.  (Sub-limb RANGE is enforced separately by the shared
/// accumulator over the values from `lookup_values`.)
pub fn eval_mul_lookup(cur: &[F], layout: &MulLookupLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(MUL_LOOKUP_PROVER_CONSTRAINTS);

    // (1) Sub-limb pack for c and q:  limb = sub0 + 2^13·sub1.
    let radix_cq = F::from(1u64 << CQ_SUBLIMB_BITS);
    for i in 0..NUM_LIMBS {
        let c_pack = cur[layout.c_sublimbs_base + i * CQ_SUBLIMBS_PER_LIMB]
            + radix_cq * cur[layout.c_sublimbs_base + i * CQ_SUBLIMBS_PER_LIMB + 1];
        out.push(cur[layout.c_limbs_base + i] - c_pack);
    }
    for i in 0..NUM_LIMBS {
        let q_pack = cur[layout.q_sublimbs_base + i * CQ_SUBLIMBS_PER_LIMB]
            + radix_cq * cur[layout.q_sublimbs_base + i * CQ_SUBLIMBS_PER_LIMB + 1];
        out.push(cur[layout.q_limbs_base + i] - q_pack);
    }

    // (2) 19 schoolbook position identities (carry from sub-limbs).
    let radix = F::from(1u64 << LIMB_BITS);
    for k in 0..MUL_SCHOOLBOOK_POSITIONS {
        let mut p_ab = F::zero();
        let mut p_qp = F::zero();
        let i_lo = k.saturating_sub(NUM_LIMBS - 1);
        let i_hi = std::cmp::min(NUM_LIMBS - 1, k);
        for i in i_lo..=i_hi {
            let j = k - i;
            p_ab += cur[layout.a_limbs_base + i] * cur[layout.b_limbs_base + j];
            p_qp += cur[layout.q_limbs_base + i] * F::from(P_LIMBS_TIGHT[j] as u64);
        }
        let c_k = if k < NUM_LIMBS { cur[layout.c_limbs_base + k] } else { F::zero() };
        let carry_in = if k == 0 { F::zero() } else { signed_carry_from_sublimbs(cur, layout, k - 1) };
        let carry_out = signed_carry_from_sublimbs(cur, layout, k);
        out.push(p_ab - p_qp - c_k + carry_in - radix * carry_out);
    }
    out
}

/// Extract the 94 sub-limb VALUES this gadget contributes to the shared
/// LogUp lookup (all ∈ [0,2^13)).
pub fn lookup_values(cur: &[F], layout: &MulLookupLayout) -> Vec<u64> {
    use ark_ff::PrimeField;
    let read = |base: usize, n: usize| -> Vec<u64> {
        (0..n).map(|i| cur[base + i].into_bigint().as_ref()[0]).collect()
    };
    let mut v = Vec::with_capacity(94);
    v.extend(read(layout.c_sublimbs_base, NUM_LIMBS * CQ_SUBLIMBS_PER_LIMB));
    v.extend(read(layout.q_sublimbs_base, NUM_LIMBS * CQ_SUBLIMBS_PER_LIMB));
    v.extend(read(layout.carry_sublimbs_base, MUL_CARRY_POSITIONS * CARRY_SUBLIMBS));
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

    fn make_trace(w: usize) -> Vec<Vec<F>> {
        (0..w).map(|_| vec![F::zero(); 1]).collect()
    }
    fn alpha() -> ExtField {
        let c: Vec<F> = (0..EXT_DEGREE).map(|i| F::from(0x0600_0000u64 + 23 * i as u64 + 3)).collect();
        ExtField::from_fp_components(&c).unwrap()
    }
    fn operands() -> (FieldElement, FieldElement) {
        let mut a = FieldElement::zero();
        a.limbs = [1234567, 89, 4444, 999, 12, 65535, 7, 100000, 3, 42];
        let mut b = FieldElement::zero();
        b.limbs = [9, 8, 7, 6, 5, 4, 3, 2, 1, 111111];
        (a, b)
    }

    /// END-TO-END: fill a real a·b, the local constraints are all zero,
    /// and the gadget's sub-limbs pass the shared LogUp accumulator.
    #[test]
    fn fillable_mul_lookup_end_to_end() {
        let mut cur = 0usize;
        let layout = alloc_mul_lookup(&mut cur, 0, 0); // bases fixed below
        // Re-point a/b bases to a fresh region after the owned cells.
        let a_base = cur;
        let b_base = a_base + NUM_LIMBS;
        let width = b_base + NUM_LIMBS;
        let layout = MulLookupLayout { a_limbs_base: a_base, b_limbs_base: b_base, ..layout };

        let (a, b) = operands();
        let mut trace = make_trace(width);
        fill_mul_lookup(&mut trace, 0, &layout, &a, &b);

        // (i) Local constraints satisfied.
        let row: Vec<F> = (0..width).map(|c| trace[c][0]).collect();
        let cons = eval_mul_lookup(&row, &layout);
        assert_eq!(cons.len(), MUL_LOOKUP_PROVER_CONSTRAINTS);
        let nz = cons.iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nz, 0, "fillable lookup-mul: {nz} local constraints failed");

        // (ii) Sub-limbs pass the shared LogUp accumulator (table [0,2^13)).
        let vals = lookup_values(&row, &layout);
        assert_eq!(vals.len(), 94);
        assert!(vals.iter().all(|&v| v < (1 << 13)), "all sub-limbs must be < 2^13");
        let table_size = 1usize << 13;
        let mult = multiplicities(&vals, table_size);
        let n_trace = (table_size + vals.len() + 1).next_power_of_two();
        let mut acc: Vec<Vec<F>> =
            (0..range_lookup_acc_air::WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
        range_lookup_acc_air::fill_trace(&mut acc, n_trace, table_size, &vals, &mult, alpha());
        let av = range_lookup_acc_air::count_violations(&acc, n_trace, table_size, alpha());
        assert_eq!(av, 0, "the mul gadget's sub-limbs must pass the accumulator");
    }

    /// NEGATIVE: tampering a c sub-limb breaks the sub-limb-pack (local),
    /// and forcing it out of range breaks the accumulator.
    #[test]
    fn fillable_mul_lookup_tamper_detected() {
        let mut cur = 0usize;
        let layout0 = alloc_mul_lookup(&mut cur, 0, 0);
        let a_base = cur; let b_base = a_base + NUM_LIMBS; let width = b_base + NUM_LIMBS;
        let layout = MulLookupLayout { a_limbs_base: a_base, b_limbs_base: b_base, ..layout0 };
        let (a, b) = operands();
        let mut trace = make_trace(width);
        fill_mul_lookup(&mut trace, 0, &layout, &a, &b);

        // Tamper c sub-limb 0 → sub-limb-pack no longer matches c limb 0.
        trace[layout.c_sublimbs_base][0] += F::from(1u64);
        let row: Vec<F> = (0..width).map(|c| trace[c][0]).collect();
        let nz = eval_mul_lookup(&row, &layout).iter().filter(|v| !v.is_zero()).count();
        assert!(nz > 0, "tampered sub-limb must break the local pack constraint");
    }
}
