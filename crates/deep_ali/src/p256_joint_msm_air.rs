// p256_joint_msm_air.rs — Shamir's-trick joint scalar multiplication for
// ECDSA-P256 verification:  R = u1·G + u2·Q  in ONE shared doubling ladder.
//
// ─────────────────────────────────────────────────────────────────────
// WHY
// ─────────────────────────────────────────────────────────────────────
// The v2 verify AIR computes u1·G and u2·Q as two INDEPENDENT 256-step
// double-and-add chains, then combines them with a final group add:
//
//     u1·G chain :  256 × (1 double + 1 cond-add)      (~19.3M cells)
//     u2·Q chain :  256 × (1 double + 1 cond-add)      (~19.3M cells)
//     final add  :  1 group add                        (~41k cells)
//                   ── 512 doubles + 513 adds total ──
//
// Shamir's trick shares ONE doubling ladder between both scalars.  Each
// step doubles the joint accumulator once, then conditionally adds G and
// conditionally adds Q:
//
//     acc ← 2·acc                       (1 double)
//     acc ← u1_bit ? acc+G : acc        (1 cond-add)
//     acc ← u2_bit ? acc+Q : acc        (1 cond-add)
//
// After 256 MSB-first steps  acc = u1·G + u2·Q  directly — no separate
// final add.  Op count drops from  512 doubles + 513 adds  to
// 256 doubles + 512 adds: the 256 eliminated doublings (each ~33k cells)
// are ~21% of the whole verify AIR, and the final combine add is folded
// in for free.
//
// This reuses the existing complete-formula gadgets verbatim
// (`group_double`, `group_add`, `select`), so the RCB-2016 exception-
// freeness that the paper claims is preserved — nothing about the
// point-arithmetic soundness changes, only how many ops run.
//
// ─────────────────────────────────────────────────────────────────────
// FIXED-BASE EXTENSION (projected, not yet implemented)
// ─────────────────────────────────────────────────────────────────────
// G is a public constant, so u1·G can instead use a fixed-base comb:
// precompute the multiples {2^i·G} (or windowed {d·2^{wi}·G}) off-circuit
// and conditionally add the selected CONSTANT point per window — zero
// doublings for the G half, and with a w-bit window only 256/w adds.
// That needs a constant-point multiplexer gadget (a 2^w-way select over
// fixed points, pinned by row-0 boundary constraints); `project_costs`
// in the bench below quantifies the additional saving over Shamir alone.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::PrimeField;
use ark_goldilocks::Goldilocks as F;

use crate::p256_field::{FieldElement, LIMB_BITS, NUM_LIMBS};
use crate::p256_field_air::{
    eval_select_gadget, fill_select_gadget, SelectGadgetLayout,
    SELECT_GADGET_CONSTRAINTS,
};
use crate::p256_group_air::{
    build_group_add_layout, build_group_double_layout, eval_group_add_gadget,
    eval_group_double_gadget, fill_group_add_gadget, fill_group_double_gadget,
    group_add_gadget_constraints, group_double_gadget_constraints,
    GroupAddGadgetLayout, GroupDoubleGadgetLayout,
};

/// One joint Shamir step:  acc' = 2·acc + u1_bit·G + u2_bit·Q.
#[derive(Clone, Debug)]
pub struct JointMsmStepLayout {
    pub acc_x_base: usize,
    pub acc_y_base: usize,
    pub acc_z_base: usize,
    pub g_x_base: usize,
    pub g_y_base: usize,
    pub g_z_base: usize,
    pub q_x_base: usize,
    pub q_y_base: usize,
    pub q_z_base: usize,
    pub u1_bit_cell: usize,
    pub u2_bit_cell: usize,

    pub double_layout: GroupDoubleGadgetLayout, // 2·acc
    pub add_g_layout: GroupAddGadgetLayout,     // 2·acc + G
    pub sel_g_x: SelectGadgetLayout,            // u1_bit ? (2·acc+G) : 2·acc
    pub sel_g_y: SelectGadgetLayout,
    pub sel_g_z: SelectGadgetLayout,
    pub add_q_layout: GroupAddGadgetLayout,     // sel_g + Q
    pub sel_q_x: SelectGadgetLayout,            // u2_bit ? (sel_g+Q) : sel_g
    pub sel_q_y: SelectGadgetLayout,
    pub sel_q_z: SelectGadgetLayout,
}

fn alloc_select(
    cursor: &mut usize,
    a_limbs_base: usize,
    b_limbs_base: usize,
    sel_cell: usize,
) -> SelectGadgetLayout {
    let bits_per_elem = NUM_LIMBS * (LIMB_BITS as usize);
    let c_limbs_base = *cursor;
    let c_bits_base = c_limbs_base + NUM_LIMBS;
    *cursor = c_bits_base + bits_per_elem;
    SelectGadgetLayout {
        a_limbs_base,
        b_limbs_base,
        c_limbs_base,
        c_bits_base,
        sel_cell,
    }
}

pub fn build_joint_msm_step_layout(
    start: usize,
    acc_x_base: usize,
    acc_y_base: usize,
    acc_z_base: usize,
    g_x_base: usize,
    g_y_base: usize,
    g_z_base: usize,
    q_x_base: usize,
    q_y_base: usize,
    q_z_base: usize,
    u1_bit_cell: usize,
    u2_bit_cell: usize,
) -> (JointMsmStepLayout, usize) {
    let mut cursor = start;

    // 1. double = 2·acc
    let (double_layout, e1) =
        build_group_double_layout(cursor, acc_x_base, acc_y_base, acc_z_base);
    cursor = e1;
    let da_x = double_layout.result_x3_limbs_base;
    let da_y = double_layout.result_y3_limbs_base;
    let da_z = double_layout.result_z3_limbs_base;

    // 2. add_g = double + G
    let (add_g_layout, e2) =
        build_group_add_layout(cursor, da_x, da_y, da_z, g_x_base, g_y_base, g_z_base);
    cursor = e2;
    let ag_x = add_g_layout.result_x3_limbs_base;
    let ag_y = add_g_layout.result_y3_limbs_base;
    let ag_z = add_g_layout.result_z3_limbs_base;

    // 3. sel_g = u1_bit ? add_g : double   (a = add_g, taken when sel=1)
    let sel_g_x = alloc_select(&mut cursor, ag_x, da_x, u1_bit_cell);
    let sel_g_y = alloc_select(&mut cursor, ag_y, da_y, u1_bit_cell);
    let sel_g_z = alloc_select(&mut cursor, ag_z, da_z, u1_bit_cell);
    let sg_x = sel_g_x.c_limbs_base;
    let sg_y = sel_g_y.c_limbs_base;
    let sg_z = sel_g_z.c_limbs_base;

    // 4. add_q = sel_g + Q
    let (add_q_layout, e4) =
        build_group_add_layout(cursor, sg_x, sg_y, sg_z, q_x_base, q_y_base, q_z_base);
    cursor = e4;
    let aq_x = add_q_layout.result_x3_limbs_base;
    let aq_y = add_q_layout.result_y3_limbs_base;
    let aq_z = add_q_layout.result_z3_limbs_base;

    // 5. sel_q = u2_bit ? add_q : sel_g   (the new accumulator)
    let sel_q_x = alloc_select(&mut cursor, aq_x, sg_x, u2_bit_cell);
    let sel_q_y = alloc_select(&mut cursor, aq_y, sg_y, u2_bit_cell);
    let sel_q_z = alloc_select(&mut cursor, aq_z, sg_z, u2_bit_cell);

    (
        JointMsmStepLayout {
            acc_x_base, acc_y_base, acc_z_base,
            g_x_base, g_y_base, g_z_base,
            q_x_base, q_y_base, q_z_base,
            u1_bit_cell, u2_bit_cell,
            double_layout, add_g_layout,
            sel_g_x, sel_g_y, sel_g_z,
            add_q_layout,
            sel_q_x, sel_q_y, sel_q_z,
        },
        cursor,
    )
}

pub fn joint_msm_step_gadget_constraints(layout: &JointMsmStepLayout) -> usize {
    group_double_gadget_constraints(&layout.double_layout)
        + group_add_gadget_constraints(&layout.add_g_layout)
        + group_add_gadget_constraints(&layout.add_q_layout)
        + 6 * SELECT_GADGET_CONSTRAINTS
}

fn read_fe(trace: &[Vec<F>], row: usize, base: usize) -> FieldElement {
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        let v = trace[base + i][row];
        limbs[i] = v.into_bigint().as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

pub fn fill_joint_msm_step_gadget(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &JointMsmStepLayout,
    acc_x: &FieldElement, acc_y: &FieldElement, acc_z: &FieldElement,
    g_x: &FieldElement, g_y: &FieldElement, g_z: &FieldElement,
    q_x: &FieldElement, q_y: &FieldElement, q_z: &FieldElement,
    u1_bit: bool, u2_bit: bool,
) {
    // 1. 2·acc
    fill_group_double_gadget(trace, row, &layout.double_layout, acc_x, acc_y, acc_z);
    let da_x = read_fe(trace, row, layout.double_layout.result_x3_limbs_base);
    let da_y = read_fe(trace, row, layout.double_layout.result_y3_limbs_base);
    let da_z = read_fe(trace, row, layout.double_layout.result_z3_limbs_base);

    // 2. 2·acc + G
    fill_group_add_gadget(trace, row, &layout.add_g_layout, &da_x, &da_y, &da_z, g_x, g_y, g_z);
    let ag_x = read_fe(trace, row, layout.add_g_layout.result_x3_limbs_base);
    let ag_y = read_fe(trace, row, layout.add_g_layout.result_y3_limbs_base);
    let ag_z = read_fe(trace, row, layout.add_g_layout.result_z3_limbs_base);

    // 3. sel_g = u1_bit ? add_g : 2·acc
    fill_select_gadget(trace, row, &layout.sel_g_x, &ag_x, &da_x, u1_bit);
    fill_select_gadget(trace, row, &layout.sel_g_y, &ag_y, &da_y, u1_bit);
    fill_select_gadget(trace, row, &layout.sel_g_z, &ag_z, &da_z, u1_bit);
    let sg_x = read_fe(trace, row, layout.sel_g_x.c_limbs_base);
    let sg_y = read_fe(trace, row, layout.sel_g_y.c_limbs_base);
    let sg_z = read_fe(trace, row, layout.sel_g_z.c_limbs_base);

    // 4. sel_g + Q
    fill_group_add_gadget(trace, row, &layout.add_q_layout, &sg_x, &sg_y, &sg_z, q_x, q_y, q_z);
    let aq_x = read_fe(trace, row, layout.add_q_layout.result_x3_limbs_base);
    let aq_y = read_fe(trace, row, layout.add_q_layout.result_y3_limbs_base);
    let aq_z = read_fe(trace, row, layout.add_q_layout.result_z3_limbs_base);

    // 5. sel_q = u2_bit ? add_q : sel_g   (new accumulator)
    fill_select_gadget(trace, row, &layout.sel_q_x, &aq_x, &sg_x, u2_bit);
    fill_select_gadget(trace, row, &layout.sel_q_y, &aq_y, &sg_y, u2_bit);
    fill_select_gadget(trace, row, &layout.sel_q_z, &aq_z, &sg_z, u2_bit);
}

pub fn eval_joint_msm_step_gadget(cur: &[F], layout: &JointMsmStepLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(joint_msm_step_gadget_constraints(layout));
    out.extend(eval_group_double_gadget(cur, &layout.double_layout));
    out.extend(eval_group_add_gadget(cur, &layout.add_g_layout));
    out.extend(eval_select_gadget(cur, &layout.sel_g_x));
    out.extend(eval_select_gadget(cur, &layout.sel_g_y));
    out.extend(eval_select_gadget(cur, &layout.sel_g_z));
    out.extend(eval_group_add_gadget(cur, &layout.add_q_layout));
    out.extend(eval_select_gadget(cur, &layout.sel_q_x));
    out.extend(eval_select_gadget(cur, &layout.sel_q_y));
    out.extend(eval_select_gadget(cur, &layout.sel_q_z));
    out
}

// ═══════════════════════════════════════════════════════════════════
//  K-STEP JOINT MSM CHAIN
// ═══════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct JointMsmChainLayout {
    pub init_acc_x_base: usize,
    pub init_acc_y_base: usize,
    pub init_acc_z_base: usize,
    pub g_x_base: usize,
    pub g_y_base: usize,
    pub g_z_base: usize,
    pub q_x_base: usize,
    pub q_y_base: usize,
    pub q_z_base: usize,
    pub u1_bit_cells: Vec<usize>,
    pub u2_bit_cells: Vec<usize>,
    pub steps: Vec<JointMsmStepLayout>,
}

/// Build a K-step joint ladder.  `u1_bit_cells` / `u2_bit_cells` must
/// both have length K (MSB-first; index 0 processed first).
pub fn build_joint_msm_chain_layout(
    start: usize,
    init_acc_x_base: usize,
    init_acc_y_base: usize,
    init_acc_z_base: usize,
    g_x_base: usize,
    g_y_base: usize,
    g_z_base: usize,
    q_x_base: usize,
    q_y_base: usize,
    q_z_base: usize,
    u1_bit_cells: Vec<usize>,
    u2_bit_cells: Vec<usize>,
) -> (JointMsmChainLayout, usize) {
    assert_eq!(u1_bit_cells.len(), u2_bit_cells.len());
    let mut cursor = start;
    let mut steps = Vec::with_capacity(u1_bit_cells.len());
    let mut acc_x = init_acc_x_base;
    let mut acc_y = init_acc_y_base;
    let mut acc_z = init_acc_z_base;
    for k in 0..u1_bit_cells.len() {
        let (step, end) = build_joint_msm_step_layout(
            cursor, acc_x, acc_y, acc_z,
            g_x_base, g_y_base, g_z_base, q_x_base, q_y_base, q_z_base,
            u1_bit_cells[k], u2_bit_cells[k],
        );
        cursor = end;
        acc_x = step.sel_q_x.c_limbs_base;
        acc_y = step.sel_q_y.c_limbs_base;
        acc_z = step.sel_q_z.c_limbs_base;
        steps.push(step);
    }
    (
        JointMsmChainLayout {
            init_acc_x_base, init_acc_y_base, init_acc_z_base,
            g_x_base, g_y_base, g_z_base, q_x_base, q_y_base, q_z_base,
            u1_bit_cells, u2_bit_cells, steps,
        },
        cursor,
    )
}

pub fn joint_msm_chain_gadget_constraints(layout: &JointMsmChainLayout) -> usize {
    layout.steps.iter().map(joint_msm_step_gadget_constraints).sum()
}

/// Fill the chain.  `u1_bits`/`u2_bits` length K.  The accumulator input
/// is (init_acc_*); the final accumulator is the last step's sel_q output.
pub fn fill_joint_msm_chain_gadget(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &JointMsmChainLayout,
    init_acc_x: &FieldElement, init_acc_y: &FieldElement, init_acc_z: &FieldElement,
    g_x: &FieldElement, g_y: &FieldElement, g_z: &FieldElement,
    q_x: &FieldElement, q_y: &FieldElement, q_z: &FieldElement,
    u1_bits: &[bool], u2_bits: &[bool],
) {
    assert_eq!(u1_bits.len(), layout.steps.len());
    assert_eq!(u2_bits.len(), layout.steps.len());
    let mut acc_x = *init_acc_x;
    let mut acc_y = *init_acc_y;
    let mut acc_z = *init_acc_z;
    for (k, step) in layout.steps.iter().enumerate() {
        fill_joint_msm_step_gadget(
            trace, row, step, &acc_x, &acc_y, &acc_z,
            g_x, g_y, g_z, q_x, q_y, q_z,
            u1_bits[k], u2_bits[k],
        );
        acc_x = read_fe(trace, row, step.sel_q_x.c_limbs_base);
        acc_y = read_fe(trace, row, step.sel_q_y.c_limbs_base);
        acc_z = read_fe(trace, row, step.sel_q_z.c_limbs_base);
    }
}

pub fn eval_joint_msm_chain_gadget(cur: &[F], layout: &JointMsmChainLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(joint_msm_chain_gadget_constraints(layout));
    for step in &layout.steps {
        out.extend(eval_joint_msm_step_gadget(cur, step));
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Zero;
    use crate::p256_group::{AffinePoint, GENERATOR};

    fn make_trace_row(width: usize) -> Vec<Vec<F>> {
        (0..width).map(|_| vec![F::zero(); 1]).collect()
    }

    fn z_one() -> FieldElement {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    }

    fn place_affine(
        trace: &mut [Vec<F>], x_base: usize, y_base: usize, z_base: usize, p: &AffinePoint,
    ) {
        assert!(!p.infinity);
        for i in 0..NUM_LIMBS {
            trace[x_base + i][0] = F::from(p.x.limbs[i] as u64);
            trace[y_base + i][0] = F::from(p.y.limbs[i] as u64);
        }
        trace[z_base][0] = F::from(1u64);
        for i in 1..NUM_LIMBS {
            trace[z_base + i][0] = F::zero();
        }
    }

    fn canon(fe: &FieldElement) -> FieldElement {
        let mut t = *fe;
        t.freeze();
        t
    }

    /// A layout with acc/G/Q at fixed low bases and the two bit cells,
    /// for a K-step chain.
    fn chain_layout(k: usize) -> (JointMsmChainLayout, usize) {
        let acc_x = 0; let acc_y = NUM_LIMBS; let acc_z = 2 * NUM_LIMBS;
        let g_x = 3 * NUM_LIMBS; let g_y = 4 * NUM_LIMBS; let g_z = 5 * NUM_LIMBS;
        let q_x = 6 * NUM_LIMBS; let q_y = 7 * NUM_LIMBS; let q_z = 8 * NUM_LIMBS;
        let u1_start = 9 * NUM_LIMBS;
        let u2_start = u1_start + k;
        let u1_cells: Vec<usize> = (0..k).map(|i| u1_start + i).collect();
        let u2_cells: Vec<usize> = (0..k).map(|i| u2_start + i).collect();
        let start = u2_start + k;
        build_joint_msm_chain_layout(
            start, acc_x, acc_y, acc_z, g_x, g_y, g_z, q_x, q_y, q_z,
            u1_cells, u2_cells,
        )
    }

    /// Correctness: a K-step joint ladder from a non-identity init acc P0
    /// computes  acc = 2^K·P0 + u1·G + u2·Q  (u1,u2 the K-bit MSB-first
    /// values), verified against the native group ops.  Starting from a
    /// non-identity P0 avoids exercising the point-at-infinity path in
    /// the fill helpers; production init = O relies on the existing
    /// RCB-2016 completeness of the add/double gadgets.
    #[test]
    fn joint_msm_chain_matches_native_k3() {
        let k = 3;
        let (layout, total) = chain_layout(k);
        let mut trace = make_trace_row(total);

        let g = *GENERATOR;
        let q = g.double();               // Q = 2G (any non-identity)
        let p0 = g.double().add(&g);       // init acc P0 = 3G

        // u1 = 0b101 = 5, u2 = 0b011 = 3 (MSB-first bit arrays).
        let u1_bits = [true, false, true];
        let u2_bits = [false, true, true];

        place_affine(&mut trace, layout.init_acc_x_base, layout.init_acc_y_base, layout.init_acc_z_base, &p0);
        place_affine(&mut trace, layout.g_x_base, layout.g_y_base, layout.g_z_base, &g);
        place_affine(&mut trace, layout.q_x_base, layout.q_y_base, layout.q_z_base, &q);
        for (i, &b) in u1_bits.iter().enumerate() { trace[layout.u1_bit_cells[i]][0] = F::from(b as u64); }
        for (i, &b) in u2_bits.iter().enumerate() { trace[layout.u2_bit_cells[i]][0] = F::from(b as u64); }

        fill_joint_msm_chain_gadget(
            &mut trace, 0, &layout,
            &g.double().add(&g).x, &g.double().add(&g).y, &z_one(), // P0 = 3G affine
            &g.x, &g.y, &z_one(),
            &q.x, &q.y, &z_one(),
            &u1_bits, &u2_bits,
        );

        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let nonzero = eval_joint_msm_chain_gadget(&cur, &layout)
            .iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nonzero, 0, "joint MSM K=3: {nonzero} constraints failed");

        // Native expected: 2^3·P0 + 5·G + 3·Q.
        let scal = |n: i64| { let mut s = crate::p256_scalar::ScalarElement::zero(); s.limbs[0] = n; s };
        let eight_p0 = p0.scalar_mul(&scal(8));
        let expected = eight_p0.add(&g.scalar_mul(&scal(5))).add(&q.scalar_mul(&scal(3)));
        assert!(!expected.infinity);
        let mut ex = expected.x; ex.freeze();

        let last = layout.steps.last().unwrap();
        let x = read_fe(&trace, 0, last.sel_q_x.c_limbs_base);
        let z = read_fe(&trace, 0, last.sel_q_z.c_limbs_base);
        // Compare affine: X/Z == expected.x  ⟺  X == expected.x · Z.
        let lhs = canon(&x);
        let rhs = canon(&ex.mul(&z));
        assert!(lhs.ct_eq(&rhs), "joint MSM K=3 affine x mismatch");
    }

    /// COST BENCH: two-separate-chains + final add (v2) vs Shamir joint
    /// ladder, at K=256; plus a fixed-base comb projection.  Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib joint_msm_cost -- --nocapture
    #[test]
    fn joint_msm_cost_k256() {
        use crate::p256_scalar_mul_air::{
            build_scalar_mul_chain_layout, scalar_mul_chain_gadget_constraints,
        };

        let k = 256;
        // Fixed low bases (values irrelevant to cell counts).
        let b = |n: usize| n * NUM_LIMBS;

        // ── v2: two independent chains + one final group add ──
        let u1_cells: Vec<usize> = (0..k).collect();
        let (c1, c1_end) = build_scalar_mul_chain_layout(
            10 * NUM_LIMBS + 2 * k, b(0), b(1), b(2), b(3), b(4), b(5), u1_cells,
        );
        let c1_cells = c1_end - (10 * NUM_LIMBS + 2 * k);
        let (c2, c2_end) = build_scalar_mul_chain_layout(
            c1_end, b(0), b(1), b(2), b(6), b(7), b(8),
            (0..k).map(|i| k + i).collect(),
        );
        let c2_cells = c2_end - c1_end;
        let (fadd, fadd_end) = build_group_add_layout(
            c2_end, c1.steps.last().unwrap().select_x.c_limbs_base,
            c1.steps.last().unwrap().select_y.c_limbs_base,
            c1.steps.last().unwrap().select_z.c_limbs_base,
            c2.steps.last().unwrap().select_x.c_limbs_base,
            c2.steps.last().unwrap().select_y.c_limbs_base,
            c2.steps.last().unwrap().select_z.c_limbs_base,
        );
        let fadd_cells = fadd_end - c2_end;
        let two_chain_cells = c1_cells + c2_cells + fadd_cells;
        let two_chain_cons = scalar_mul_chain_gadget_constraints(&c1)
            + scalar_mul_chain_gadget_constraints(&c2)
            + group_add_gadget_constraints(&fadd);

        // ── Shamir joint ladder ──
        let (jm, jm_end) = chain_layout(k);
        let jm_cells = jm_end - (9 * NUM_LIMBS + 2 * k);
        let jm_cons = joint_msm_chain_gadget_constraints(&jm);

        let cell_save = two_chain_cells - jm_cells;
        let cons_save = two_chain_cons - jm_cons;
        let cell_pct = 100.0 * cell_save as f64 / two_chain_cells as f64;

        // Full v2 AIR width (measured earlier) for context.
        const FULL_V2_AIR_CELLS: usize = 39_416_874;
        let full_pct = 100.0 * cell_save as f64 / FULL_V2_AIR_CELLS as f64;

        // ── Fixed-base comb projection (G half only) ──
        // Shamir keeps 256 G cond-adds inside the shared ladder.  A w-bit
        // fixed-base comb for u1·G removes ALL G doublings (there are none
        // to share once G leaves the ladder) and reduces the G adds to
        // ceil(256/w).  We estimate one cond-add's cell cost from the
        // per-step add gadget and project the additional saving.
        let per_step_cells = jm_cells / k;                // ~one joint step
        // A joint step = 1 double + 2 adds + 6 selects.  Approx a single
        // "add + 3 selects" (one conditional add) as the comb unit:
        let one_double = build_group_double_layout(0, 0, 1, 2).1;
        let one_add = {
            let (_l, e) = build_group_add_layout(0, 0, 1, 2, 3, 4, 5); e
        };
        let sel_cells = per_step_cells
            .saturating_sub(one_double)
            .saturating_sub(2 * one_add) / 6; // cells per select
        let cond_add_cells = one_add + 3 * sel_cells;

        let w = 4usize;
        let comb_g_adds = (256 + w - 1) / w;              // ceil(256/w)
        // Shamir's G contribution ≈ 256 cond-adds; comb ≈ comb_g_adds.
        let comb_g_saving = (256 - comb_g_adds) * cond_add_cells;

        println!("\n═══ ECDSA-P256  u1·G + u2·Q  @ K=256 ═══");
        println!("  scalar-mult portion (cells):");
        println!("    v2 two chains + final add : {two_chain_cells:>10}  ({two_chain_cons} constraints)");
        println!("    Shamir joint ladder       : {jm_cells:>10}  ({jm_cons} constraints)");
        println!("    saved by Shamir           : {cell_save:>10}  ({cell_pct:.1}% of MSM, {full_pct:.1}% of full verify AIR)");
        println!("    (constraints saved        : {cons_save})");
        println!("  fixed-base comb projection (w={w}, G half, ON TOP of Shamir):");
        println!("    est. cells / conditional-add : {cond_add_cells}");
        println!("    G adds  256 → {comb_g_adds}  ⇒ extra ~{comb_g_saving} cells");
        println!("    Shamir + fixed-base G (proj.): {:>10}", jm_cells.saturating_sub(comb_g_saving));
        println!("  (Binius verify ~linear in committed width ⇒ cells ≈ core-hour proxy.)\n");

        assert!(jm_cells < two_chain_cells, "Shamir must reduce MSM width");
        assert!(jm_cons < two_chain_cons, "Shamir must reduce MSM constraints");
    }
}
