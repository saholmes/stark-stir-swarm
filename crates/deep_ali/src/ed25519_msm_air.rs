// ed25519_msm_air.rs — Shamir joint ladder + fixed-base comb ported from
// the P-256 gadgets (`p256_joint_msm_air`, `p256_const_mux_air`) to the
// Ed25519 twisted-Edwards group.
//
// EdDSA verification is itself a two-scalar MSM  R = [S]·B + [k]·(−A)
// with B the FIXED public base point and A the per-signature key, so the
// same three levers apply — and because the mux/ladder gadgets are group-
// agnostic they compose over the existing extended-coordinate (X:Y:Z:T)
// gadgets (`point_double`, `point_add`, `cond_add`) unchanged.  Only the
// arithmetic differs: Edwards addition is COMPLETE (no exception cases)
// and needs no modular inversion, so the port is strictly cheaper than
// P-256 per group op.
//
// This module ports:
//   * SHAMIR JOINT LADDER  — [S]·B + [k]·A in one shared doubling ladder,
//     reusing `point_double` + `cond_add` (the conditional point-add that
//     already bundles a point_add with 4 field selects).
//   * FIXED-BASE COMB      — [S]·B via a 4-coordinate constant-point mux
//     (the P-256 const mux extended with the T coordinate) + `point_add`.
//
// Windowed variable-base [k]·A is the direct transliteration of
// `p256_windowed_q_air` with the var-point mux widened to 4 coordinates;
// omitted here for brevity — identical structure, T-coordinate added.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::{PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::ed25519_field::{FieldElement, NUM_LIMBS};
use crate::ed25519_group::EdwardsPoint;
use crate::ed25519_group_air::{
    cond_add_layout_at, eval_cond_add_gadget, eval_point_add_gadget,
    eval_point_double_gadget, fill_cond_add_gadget, fill_point_add_gadget,
    fill_point_double_gadget, point_add_layout_at, point_double_layout_at,
    CondAddGadgetLayout, PointAddGadgetLayout, PointDoubleGadgetLayout,
    COND_ADD_CONSTRAINTS, POINT_ADD_CONSTRAINTS, POINT_DBL_CONSTRAINTS,
};

fn canon(fe: &FieldElement) -> FieldElement {
    let mut t = *fe;
    t.freeze();
    t
}

fn place_limbs(trace: &mut [Vec<F>], row: usize, base: usize, fe: &FieldElement) {
    let c = canon(fe);
    for i in 0..NUM_LIMBS {
        trace[base + i][row] = F::from(c.limbs[i] as u64);
    }
}

fn read_limbs(trace: &[Vec<F>], row: usize, base: usize) -> FieldElement {
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

fn place_point(
    trace: &mut [Vec<F>], row: usize,
    xb: usize, yb: usize, zb: usize, tb: usize, p: &EdwardsPoint,
) {
    place_limbs(trace, row, xb, &p.X);
    place_limbs(trace, row, yb, &p.Y);
    place_limbs(trace, row, zb, &p.Z);
    place_limbs(trace, row, tb, &p.T);
}

fn read_point(
    trace: &[Vec<F>], row: usize, xb: usize, yb: usize, zb: usize, tb: usize,
) -> EdwardsPoint {
    EdwardsPoint {
        X: read_limbs(trace, row, xb),
        Y: read_limbs(trace, row, yb),
        Z: read_limbs(trace, row, zb),
        T: read_limbs(trace, row, tb),
    }
}

/// Affine equality of two extended points: X1·Z2 == X2·Z1 && Y1·Z2 == Y2·Z1.
pub fn points_equal_affine(p: &EdwardsPoint, q: &EdwardsPoint) -> bool {
    let xz = canon(&p.X.mul(&q.Z));
    let zx = canon(&q.X.mul(&p.Z));
    let yz = canon(&p.Y.mul(&q.Z));
    let zy = canon(&q.Y.mul(&p.Z));
    xz.limbs == zx.limbs && yz.limbs == zy.limbs
}

// ═══════════════════════════════════════════════════════════════════
//  SHAMIR JOINT LADDER  —  [S]·B + [k]·A
// ═══════════════════════════════════════════════════════════════════
//
// Per step:  acc ← 2·acc;  acc ← s_bit ? acc+B : acc;  acc ← a_bit ? acc+A : acc.
// Reuses point_double + two cond_add gadgets (each cond_add owns its bit).

#[derive(Clone, Debug)]
pub struct Ed25519JointStepLayout {
    pub dbl: PointDoubleGadgetLayout,
    pub ca_b: CondAddGadgetLayout, // + s_bit·B
    pub ca_a: CondAddGadgetLayout, // + a_bit·A
}

#[derive(Clone, Debug)]
pub struct Ed25519JointLadderLayout {
    // Initial accumulator + the two base points (input cell bases).
    pub acc_x: usize, pub acc_y: usize, pub acc_z: usize, pub acc_t: usize,
    pub b_x: usize, pub b_y: usize, pub b_z: usize, pub b_t: usize,
    pub a_x: usize, pub a_y: usize, pub a_z: usize, pub a_t: usize,
    pub steps: Vec<Ed25519JointStepLayout>,
}

pub fn build_ed25519_joint_ladder(
    start: usize,
    acc_x: usize, acc_y: usize, acc_z: usize, acc_t: usize,
    b_x: usize, b_y: usize, b_z: usize, b_t: usize,
    a_x: usize, a_y: usize, a_z: usize, a_t: usize,
    k: usize,
) -> (Ed25519JointLadderLayout, usize) {
    let mut cursor = start;
    let mut steps = Vec::with_capacity(k);
    let (mut cx, mut cy, mut cz, mut ct) = (acc_x, acc_y, acc_z, acc_t);
    for _ in 0..k {
        let dbl = point_double_layout_at(cursor, cx, cy, cz);
        cursor = dbl.end;
        let (dx, dy, dz, dt) = (
            dbl.mul_X3.c_limbs_base, dbl.mul_Y3.c_limbs_base,
            dbl.mul_Z3.c_limbs_base, dbl.mul_T3.c_limbs_base,
        );
        let ca_b = cond_add_layout_at(cursor, dx, dy, dz, dt, b_x, b_y, b_z, b_t);
        cursor = ca_b.end;
        let ca_a = cond_add_layout_at(
            cursor, ca_b.out_x, ca_b.out_y, ca_b.out_z, ca_b.out_t, a_x, a_y, a_z, a_t,
        );
        cursor = ca_a.end;
        cx = ca_a.out_x; cy = ca_a.out_y; cz = ca_a.out_z; ct = ca_a.out_t;
        steps.push(Ed25519JointStepLayout { dbl, ca_b, ca_a });
    }
    (
        Ed25519JointLadderLayout {
            acc_x, acc_y, acc_z, acc_t, b_x, b_y, b_z, b_t, a_x, a_y, a_z, a_t, steps,
        },
        cursor,
    )
}

pub fn ed25519_joint_ladder_constraints(layout: &Ed25519JointLadderLayout) -> usize {
    layout.steps.len() * (POINT_DBL_CONSTRAINTS + 2 * COND_ADD_CONSTRAINTS)
}

pub fn ed25519_joint_ladder_result(layout: &Ed25519JointLadderLayout) -> (usize, usize, usize, usize) {
    match layout.steps.last() {
        Some(s) => (s.ca_a.out_x, s.ca_a.out_y, s.ca_a.out_z, s.ca_a.out_t),
        None => (layout.acc_x, layout.acc_y, layout.acc_z, layout.acc_t),
    }
}

pub fn fill_ed25519_joint_ladder(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &Ed25519JointLadderLayout,
    init_acc: &EdwardsPoint,
    b: &EdwardsPoint,
    a: &EdwardsPoint,
    s_bits: &[bool],
    a_bits: &[bool],
) {
    assert_eq!(s_bits.len(), layout.steps.len());
    assert_eq!(a_bits.len(), layout.steps.len());
    // Place the initial accumulator and the two bases into their cells.
    place_point(trace, row, layout.acc_x, layout.acc_y, layout.acc_z, layout.acc_t, init_acc);
    place_point(trace, row, layout.b_x, layout.b_y, layout.b_z, layout.b_t, b);
    place_point(trace, row, layout.a_x, layout.a_y, layout.a_z, layout.a_t, a);

    let mut acc = *init_acc;
    for (kk, step) in layout.steps.iter().enumerate() {
        // 2·acc
        fill_point_double_gadget(trace, row, &step.dbl, &acc);
        let two = read_point(
            trace, row,
            step.dbl.mul_X3.c_limbs_base, step.dbl.mul_Y3.c_limbs_base,
            step.dbl.mul_Z3.c_limbs_base, step.dbl.mul_T3.c_limbs_base,
        );
        // + s_bit·B
        fill_cond_add_gadget(trace, row, &step.ca_b, &two, b, s_bits[kk]);
        let after_b = read_point(
            trace, row, step.ca_b.out_x, step.ca_b.out_y, step.ca_b.out_z, step.ca_b.out_t,
        );
        // + a_bit·A
        fill_cond_add_gadget(trace, row, &step.ca_a, &after_b, a, a_bits[kk]);
        acc = read_point(
            trace, row, step.ca_a.out_x, step.ca_a.out_y, step.ca_a.out_z, step.ca_a.out_t,
        );
    }
}

pub fn eval_ed25519_joint_ladder(cur: &[F], layout: &Ed25519JointLadderLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(ed25519_joint_ladder_constraints(layout));
    for step in &layout.steps {
        out.extend(eval_point_double_gadget(cur, &step.dbl));
        out.extend(eval_cond_add_gadget(cur, &step.ca_b));
        out.extend(eval_cond_add_gadget(cur, &step.ca_a));
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  4-COORDINATE CONSTANT-POINT MUX  +  FIXED-BASE COMB  ([S]·B)
// ═══════════════════════════════════════════════════════════════════

pub type EdPointXYZT = [FieldElement; 4];

#[derive(Clone, Debug)]
pub struct EdConstMuxLayout {
    pub w: usize,
    pub bit_cells: Vec<usize>,
    pub node_cells: Vec<Vec<usize>>,
    pub out_x: usize,
    pub out_y: usize,
    pub out_z: usize,
    pub out_t: usize,
    pub table: Vec<EdPointXYZT>,
}

pub fn build_ed_const_mux(
    start: usize,
    bit_cells: Vec<usize>,
    table: Vec<EdPointXYZT>,
) -> (EdConstMuxLayout, usize) {
    let w = bit_cells.len();
    assert_eq!(table.len(), 1usize << w);
    let mut cursor = start;
    let mut node_cells: Vec<Vec<usize>> = vec![Vec::new(); w + 1];
    for b in 1..=w {
        node_cells[b] = (0..(1usize << b)).map(|_| { let c = cursor; cursor += 1; c }).collect();
    }
    let out_x = cursor; cursor += NUM_LIMBS;
    let out_y = cursor; cursor += NUM_LIMBS;
    let out_z = cursor; cursor += NUM_LIMBS;
    let out_t = cursor; cursor += NUM_LIMBS;
    (EdConstMuxLayout { w, bit_cells, node_cells, out_x, out_y, out_z, out_t, table }, cursor)
}

pub fn ed_const_mux_constraints(layout: &EdConstMuxLayout) -> usize {
    let w = layout.w;
    w + ((1usize << (w + 1)) - 2) + 4 * NUM_LIMBS
}

pub fn fill_ed_const_mux(trace: &mut [Vec<F>], row: usize, layout: &EdConstMuxLayout, digit_bits: &[bool]) {
    let w = layout.w;
    let digit: usize = digit_bits.iter().enumerate().map(|(c, &b)| (b as usize) << c).sum();
    for (c, &b) in digit_bits.iter().enumerate() {
        trace[layout.bit_cells[c]][row] = F::from(b as u64);
    }
    for b in 1..=w {
        let mask = (1usize << b) - 1;
        for p in 0..(1usize << b) {
            let v = if (digit & mask) == p { 1u64 } else { 0 };
            trace[layout.node_cells[b][p]][row] = F::from(v);
        }
    }
    let t = &layout.table[digit];
    for (k, base) in [layout.out_x, layout.out_y, layout.out_z, layout.out_t].iter().enumerate() {
        for i in 0..NUM_LIMBS {
            trace[base + i][row] = F::from(t[k].limbs[i] as u64);
        }
    }
}

pub fn eval_ed_const_mux(cur: &[F], layout: &EdConstMuxLayout) -> Vec<F> {
    let w = layout.w;
    let mut out = Vec::with_capacity(ed_const_mux_constraints(layout));
    for c in 0..w {
        let d = cur[layout.bit_cells[c]];
        out.push(d * (F::from(1u64) - d));
    }
    for b in 1..=w {
        for p in 0..(1usize << b) {
            let node = cur[layout.node_cells[b][p]];
            let parent = if b == 1 { F::from(1u64) } else { cur[layout.node_cells[b - 1][p & ((1usize << (b - 1)) - 1)]] };
            let appended = (p >> (b - 1)) & 1;
            let d = cur[layout.bit_cells[b - 1]];
            let factor = if appended == 1 { d } else { F::from(1u64) - d };
            out.push(node - parent * factor);
        }
    }
    let leaves = &layout.node_cells[w];
    let coord_bases = [layout.out_x, layout.out_y, layout.out_z, layout.out_t];
    for (coord_idx, &base) in coord_bases.iter().enumerate() {
        for i in 0..NUM_LIMBS {
            let mut sum = F::zero();
            for j in 0..(1usize << w) {
                sum += F::from(layout.table[j][coord_idx].limbs[i] as u64) * cur[leaves[j]];
            }
            out.push(cur[base + i] - sum);
        }
    }
    out
}

/// Comb tables T_i[j] = [j · 2^{w·i}] · B for the fixed base B.  Entry
/// j=0 is the identity (0:1:1:0) in extended coords.
pub fn build_ed_comb_tables(w: usize, n_windows: usize) -> Vec<Vec<EdPointXYZT>> {
    use crate::ed25519_group::ED25519_BASEPOINT;
    let mut tables = Vec::with_capacity(n_windows);
    let mut base = *ED25519_BASEPOINT; // 2^{w·i}·B
    let ident = EdwardsPoint::identity();
    for _ in 0..n_windows {
        let mut tbl: Vec<EdPointXYZT> = Vec::with_capacity(1 << w);
        tbl.push([canon(&ident.X), canon(&ident.Y), canon(&ident.Z), canon(&ident.T)]);
        let mut acc = base;
        for j in 1..(1usize << w) {
            if j > 1 { acc = acc.add(&base); }
            tbl.push([canon(&acc.X), canon(&acc.Y), canon(&acc.Z), canon(&acc.T)]);
        }
        tables.push(tbl);
        for _ in 0..w { base = base.double(); }
    }
    tables
}

#[derive(Clone, Debug)]
pub struct EdFixedBaseCombLayout {
    pub w: usize,
    pub muxes: Vec<EdConstMuxLayout>,
    pub adds: Vec<PointAddGadgetLayout>,
}

pub fn build_ed_fixed_base_comb(
    start: usize,
    w: usize,
    window_bit_cells: &[Vec<usize>],
    tables: &[Vec<EdPointXYZT>],
) -> (EdFixedBaseCombLayout, usize) {
    let n = window_bit_cells.len();
    let mut cursor = start;
    let mut muxes = Vec::with_capacity(n);
    let mut adds = Vec::with_capacity(n.saturating_sub(1));

    let (mux0, e0) = build_ed_const_mux(cursor, window_bit_cells[0].clone(), tables[0].clone());
    cursor = e0;
    let (mut ax, mut ay, mut az, mut at) = (mux0.out_x, mux0.out_y, mux0.out_z, mux0.out_t);
    muxes.push(mux0);

    for i in 1..n {
        let (muxi, ei) = build_ed_const_mux(cursor, window_bit_cells[i].clone(), tables[i].clone());
        cursor = ei;
        let add = point_add_layout_at(
            cursor, ax, ay, az, at, muxi.out_x, muxi.out_y, muxi.out_z, muxi.out_t,
        );
        cursor = add.end;
        ax = add.mul_X3.c_limbs_base; ay = add.mul_Y3.c_limbs_base;
        az = add.mul_Z3.c_limbs_base; at = add.mul_T3.c_limbs_base;
        muxes.push(muxi);
        adds.push(add);
    }
    (EdFixedBaseCombLayout { w, muxes, adds }, cursor)
}

pub fn ed_fixed_base_comb_constraints(layout: &EdFixedBaseCombLayout) -> usize {
    layout.muxes.iter().map(ed_const_mux_constraints).sum::<usize>()
        + layout.adds.len() * POINT_ADD_CONSTRAINTS
}

pub fn ed_fixed_base_comb_result(layout: &EdFixedBaseCombLayout) -> (usize, usize, usize, usize) {
    match layout.adds.last() {
        Some(a) => (a.mul_X3.c_limbs_base, a.mul_Y3.c_limbs_base, a.mul_Z3.c_limbs_base, a.mul_T3.c_limbs_base),
        None => { let m = &layout.muxes[0]; (m.out_x, m.out_y, m.out_z, m.out_t) }
    }
}

pub fn fill_ed_fixed_base_comb(
    trace: &mut [Vec<F>], row: usize, layout: &EdFixedBaseCombLayout, window_digit_bits: &[Vec<bool>],
) {
    fill_ed_const_mux(trace, row, &layout.muxes[0], &window_digit_bits[0]);
    let m0 = &layout.muxes[0];
    let mut acc = read_point(trace, row, m0.out_x, m0.out_y, m0.out_z, m0.out_t);
    for i in 1..layout.muxes.len() {
        fill_ed_const_mux(trace, row, &layout.muxes[i], &window_digit_bits[i]);
        let mi = &layout.muxes[i];
        let mp = read_point(trace, row, mi.out_x, mi.out_y, mi.out_z, mi.out_t);
        let add = &layout.adds[i - 1];
        fill_point_add_gadget(trace, row, add, &acc, &mp);
        acc = read_point(
            trace, row, add.mul_X3.c_limbs_base, add.mul_Y3.c_limbs_base,
            add.mul_Z3.c_limbs_base, add.mul_T3.c_limbs_base,
        );
    }
}

pub fn eval_ed_fixed_base_comb(cur: &[F], layout: &EdFixedBaseCombLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(ed_fixed_base_comb_constraints(layout));
    for m in &layout.muxes { out.extend(eval_ed_const_mux(cur, m)); }
    for a in &layout.adds { out.extend(eval_point_add_gadget(cur, a)); }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ed25519_group::ED25519_BASEPOINT;

    fn make_trace_row(width: usize) -> Vec<Vec<F>> {
        (0..width).map(|_| vec![F::zero(); 1]).collect()
    }

    /// Native reference for the joint recurrence (matches the gadget's
    /// double-then-two-conditional-adds semantics exactly).
    fn native_joint(init: &EdwardsPoint, b: &EdwardsPoint, a: &EdwardsPoint, s_bits: &[bool], a_bits: &[bool]) -> EdwardsPoint {
        let mut acc = *init;
        for k in 0..s_bits.len() {
            acc = acc.double();
            if s_bits[k] { acc = acc.add(b); }
            if a_bits[k] { acc = acc.add(a); }
        }
        acc
    }

    #[test]
    fn ed25519_joint_ladder_matches_native_k3() {
        let b = *ED25519_BASEPOINT;
        let a = b.double();                 // A = 2B
        let p0 = b.double().add(&b);         // init = 3B (non-identity)
        let s_bits = [true, false, true];
        let a_bits = [false, true, true];

        let acc_x = 0; let acc_y = 10; let acc_z = 20; let acc_t = 30;
        let b_x = 40; let b_y = 50; let b_z = 60; let b_t = 70;
        let a_x = 80; let a_y = 90; let a_z = 100; let a_t = 110;
        let (layout, total) = build_ed25519_joint_ladder(
            120, acc_x, acc_y, acc_z, acc_t, b_x, b_y, b_z, b_t, a_x, a_y, a_z, a_t, s_bits.len(),
        );
        let mut trace = make_trace_row(total);
        fill_ed25519_joint_ladder(&mut trace, 0, &layout, &p0, &b, &a, &s_bits, &a_bits);

        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let nz = eval_ed25519_joint_ladder(&cur, &layout).iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nz, 0, "ed25519 joint ladder: {nz} constraints failed");

        let (rx, ry, rz, rt) = ed25519_joint_ladder_result(&layout);
        let got = read_point(&trace, 0, rx, ry, rz, rt);
        let want = native_joint(&p0, &b, &a, &s_bits, &a_bits);
        assert!(points_equal_affine(&got, &want), "ed25519 joint ladder ≠ native");
    }

    #[test]
    fn ed_const_mux_selects_every_entry_w3() {
        let w = 3;
        let b = *ED25519_BASEPOINT;
        // Table T[j] = (j+1)·B (all distinct non-identity).
        let mut mult = b;
        let mut table: Vec<EdPointXYZT> = Vec::new();
        for _j in 0..(1 << w) {
            table.push([canon(&mult.X), canon(&mult.Y), canon(&mult.Z), canon(&mult.T)]);
            mult = mult.add(&b);
        }
        for digit in 0..(1usize << w) {
            let (layout, total) = build_ed_const_mux(w, (0..w).collect(), table.clone());
            let mut trace = make_trace_row(total);
            let bits: Vec<bool> = (0..w).map(|c| (digit >> c) & 1 == 1).collect();
            fill_ed_const_mux(&mut trace, 0, &layout, &bits);
            let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
            let nz = eval_ed_const_mux(&cur, &layout).iter().filter(|v| !v.is_zero()).count();
            assert_eq!(nz, 0, "digit {digit}: {nz} mux constraints failed");
            // Output X == table[digit].X.
            let ox = read_limbs(&trace, 0, layout.out_x);
            assert_eq!(ox.limbs, table[digit][0].limbs, "digit {digit}: wrong X");
        }
    }

    #[test]
    fn ed_fixed_base_comb_computes_sb() {
        let w = 4;
        let tables = build_ed_comb_tables(w, 2);
        // digit_0 = 5, digit_1 = 3 ⇒ S = 5 + 16·3 = 53.
        let d0 = 5usize; let d1 = 3usize;
        let wdb: Vec<Vec<bool>> = vec![
            (0..w).map(|c| (d0 >> c) & 1 == 1).collect(),
            (0..w).map(|c| (d1 >> c) & 1 == 1).collect(),
        ];
        let wbc: Vec<Vec<usize>> = vec![(0..w).collect(), (w..2 * w).collect()];
        let (layout, total) = build_ed_fixed_base_comb(2 * w, w, &wbc, &tables);
        let mut trace = make_trace_row(total);
        for (i, cells) in wbc.iter().enumerate() {
            for (c, &cell) in cells.iter().enumerate() {
                trace[cell][0] = F::from(wdb[i][c] as u64);
            }
        }
        fill_ed_fixed_base_comb(&mut trace, 0, &layout, &wdb);
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let nz = eval_ed_fixed_base_comb(&cur, &layout).iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nz, 0, "ed comb: {nz} constraints failed");

        // Native 53·B via the same 2-window recurrence: 5·B + 16·(3·B).
        let b = *ED25519_BASEPOINT;
        let mut five_b = b; for _ in 0..4 { five_b = five_b.add(&b); }
        let mut three_b = b; for _ in 0..2 { three_b = three_b.add(&b); }
        let mut sixteen_three_b = three_b; for _ in 0..4 { sixteen_three_b = sixteen_three_b.double(); }
        let want = five_b.add(&sixteen_three_b);
        let (rx, ry, rz, rt) = ed_fixed_base_comb_result(&layout);
        let got = read_point(&trace, 0, rx, ry, rz, rt);
        assert!(points_equal_affine(&got, &want), "ed comb S·B ≠ native");
    }

    /// COST BENCH: Ed25519 joint ladder + fixed-base comb vs two separate
    /// double-and-add ladders.  Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib ed25519_msm_cost -- --nocapture
    #[test]
    fn ed25519_msm_cost_k256() {
        let k = 256;
        let w = 4;
        let n_win = k / w;

        // One double-and-add ladder step ≈ point_double + cond_add.
        let per_ladder_step = POINT_DBL_CONSTRAINTS + COND_ADD_CONSTRAINTS;
        let two_ladders_cons = 2 * k * per_ladder_step + POINT_ADD_CONSTRAINTS; // + final combine

        // Shamir joint ladder.
        let (joint, _je) = build_ed25519_joint_ladder(
            0, 0, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, k,
        );
        let joint_cons = ed25519_joint_ladder_constraints(&joint);

        // Fixed-base comb ([S]·B).
        let tables = build_ed_comb_tables(w, n_win);
        let wbc: Vec<Vec<usize>> = (0..n_win).map(|i| (i * w..i * w + w).collect()).collect();
        let (comb, _ce) = build_ed_fixed_base_comb(n_win * w, w, &wbc, &tables);
        let comb_cons = ed_fixed_base_comb_constraints(&comb);

        let joint_pct = 100.0 * (two_ladders_cons - joint_cons) as f64 / two_ladders_cons as f64;

        println!("\n═══ Ed25519  [S]·B + [k]·A  @ 256-bit  (constraints) ═══");
        println!("  two separate ladders + combine : {two_ladders_cons:>10}");
        println!("  Shamir joint ladder            : {joint_cons:>10}  (−{joint_pct:.1}%)");
        println!("  fixed-base-B comb ([S]·B, w={w}) : {comb_cons:>10}  ({n_win} muxes + {} adds, 0 doublings)", n_win - 1);
        println!("  (Edwards add is complete + inversion-free ⇒ cheaper per op than P-256.)\n");

        assert!(joint_cons < two_ladders_cons, "Shamir must reduce Ed25519 MSM");
        assert!(comb_cons < k * per_ladder_step, "comb must beat one ladder");
    }
}
