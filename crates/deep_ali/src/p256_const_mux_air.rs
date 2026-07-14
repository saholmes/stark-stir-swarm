// p256_const_mux_air.rs — constant-point multiplexer + fixed-base comb
// for ECDSA-P256 fixed-base scalar multiplication (u1·G).
//
// ─────────────────────────────────────────────────────────────────────
// CONSTANT-POINT MULTIPLEXER
// ─────────────────────────────────────────────────────────────────────
// Given a w-bit digit  d = (d_0,…,d_{w-1})  (d_0 = LSB) and a table of
// 2^w PUBLIC CONSTANT points  T[0..2^w], the gadget outputs T[digit] as
// a projective (x:y:z) point in the trace, to be added to a fixed-base
// comb accumulator.
//
// The table is baked into the constraints as LITERAL constants — there
// is nothing to pin in the trace and no boundary machinery.  Selection
// is a degree-2 one-hot construction:
//
//   * booleanity:  d_c·(1−d_c) = 0                       (w constraints)
//   * monomial tree:  μ[b][p] = μ[b−1][p mod 2^{b−1}] · (bit ? d : 1−d)
//     builds the 2^w one-hot indicators from the bits (degree 2 each,
//     Σ_{b=1}^{w} 2^b = 2^{w+1}−2 constraints)
//   * output:  out.coord.limb[i] = Σ_j μ[w][j] · T[j].coord.limb[i]
//     (degree 1 — μ are cells, T constants; 3·NUM_LIMBS constraints)
//
// SOUNDNESS.  Booleanity forces every d_c ∈ {0,1}; the monomial tree
// then forces μ[w][·] to be exactly one-hot at index = digit; the output
// constraint forces out = T[digit] limb-by-limb.  A malicious prover has
// no freedom beyond choosing the witness bits (the legitimate scalar
// digit); the output is always a genuine table entry, never a forgery.
// Because out.limb[i] is pinned equal to a canonical constant limb
// (< 2^26), the output needs no separate range-check before feeding the
// group-add gadget.  All constraints are degree ≤ 2.
//
// ─────────────────────────────────────────────────────────────────────
// FIXED-BASE COMB
// ─────────────────────────────────────────────────────────────────────
// u1·G = Σ_i T_i[digit_i]  with  T_i[j] = j · 2^{w·i} · G  (public).
// The comb accumulates window by window: acc = T_0[d_0]; then for each
// later window  acc ← acc + T_i[d_i]  (one mux + one group_add).  For a
// 256-bit scalar with w=4 that is 64 muxes + 63 adds and ZERO doublings,
// vs the ladder's 256 doubles + 256 adds for the same u1·G.
//
// Digit-0 note: T_i[0] = O.  This demo/bench uses the mux for arbitrary
// tables (tested over all digits) and drives the comb with non-zero
// window digits; general digit-0 handling (a signed-digit recoding, or a
// verified complete-add against the (0:1:0) table entry) is the one
// remaining integration step and does not change the op-count / width
// numbers the bench reports.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::{PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::p256_field::{FieldElement, NUM_LIMBS};
use crate::p256_group_air::{
    build_group_add_layout, eval_group_add_gadget, fill_group_add_gadget,
    group_add_gadget_constraints, GroupAddGadgetLayout,
};

fn one_fe() -> FieldElement {
    let mut t = FieldElement::zero();
    t.limbs[0] = 1;
    t
}

/// Projective (x:y:z) coordinates of a constant table point.
pub type PointXYZ = [FieldElement; 3];

#[derive(Clone, Debug)]
pub struct ConstPointMuxLayout {
    pub w: usize,
    /// The w digit-bit cells (d_0 = LSB at index 0).  Referenced, not
    /// owned — typically slices of the scalar's bit decomposition.
    pub bit_cells: Vec<usize>,
    /// Monomial tree cells: `node_cells[b]` (b = 1..=w) has 2^b entries;
    /// `node_cells[0]` is empty (the implicit root value 1).
    pub node_cells: Vec<Vec<usize>>,
    pub out_x_base: usize,
    pub out_y_base: usize,
    pub out_z_base: usize,
    /// 2^w public constant points, baked as literals into the output
    /// constraint.  `table[j]` is selected when digit == j.
    pub table: Vec<PointXYZ>,
}

pub fn build_const_point_mux_layout(
    start: usize,
    bit_cells: Vec<usize>,
    table: Vec<PointXYZ>,
) -> (ConstPointMuxLayout, usize) {
    let w = bit_cells.len();
    assert_eq!(table.len(), 1usize << w, "table must have 2^w entries");
    let mut cursor = start;
    let mut node_cells: Vec<Vec<usize>> = vec![Vec::new(); w + 1];
    for b in 1..=w {
        node_cells[b] = (0..(1usize << b))
            .map(|_| {
                let c = cursor;
                cursor += 1;
                c
            })
            .collect();
    }
    let out_x_base = cursor;
    cursor += NUM_LIMBS;
    let out_y_base = cursor;
    cursor += NUM_LIMBS;
    let out_z_base = cursor;
    cursor += NUM_LIMBS;
    (
        ConstPointMuxLayout {
            w,
            bit_cells,
            node_cells,
            out_x_base,
            out_y_base,
            out_z_base,
            table,
        },
        cursor,
    )
}

pub fn const_point_mux_constraints(layout: &ConstPointMuxLayout) -> usize {
    let w = layout.w;
    w                                   // booleanity
        + ((1usize << (w + 1)) - 2)     // Σ_{b=1}^{w} 2^b monomial products
        + 3 * NUM_LIMBS                 // output selection (x,y,z)
}

pub fn fill_const_point_mux(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &ConstPointMuxLayout,
    digit_bits: &[bool],
) {
    let w = layout.w;
    assert_eq!(digit_bits.len(), w);
    let digit: usize = digit_bits
        .iter()
        .enumerate()
        .map(|(c, &b)| (b as usize) << c)
        .sum();

    for (c, &b) in digit_bits.iter().enumerate() {
        trace[layout.bit_cells[c]][row] = F::from(b as u64);
    }
    // Monomial tree: node[b][p] = 1 iff low-b bits of digit == p.
    for b in 1..=w {
        let mask = (1usize << b) - 1;
        for p in 0..(1usize << b) {
            let v = if (digit & mask) == p { 1u64 } else { 0u64 };
            trace[layout.node_cells[b][p]][row] = F::from(v);
        }
    }
    // Output = table[digit].
    let t = &layout.table[digit];
    for i in 0..NUM_LIMBS {
        trace[layout.out_x_base + i][row] = F::from(t[0].limbs[i] as u64);
        trace[layout.out_y_base + i][row] = F::from(t[1].limbs[i] as u64);
        trace[layout.out_z_base + i][row] = F::from(t[2].limbs[i] as u64);
    }
}

pub fn eval_const_point_mux(cur: &[F], layout: &ConstPointMuxLayout) -> Vec<F> {
    let w = layout.w;
    let mut out = Vec::with_capacity(const_point_mux_constraints(layout));

    // (1) Booleanity of the digit bits.
    for c in 0..w {
        let d = cur[layout.bit_cells[c]];
        out.push(d * (F::from(1u64) - d));
    }

    // (2) Monomial tree.
    for b in 1..=w {
        for p in 0..(1usize << b) {
            let node = cur[layout.node_cells[b][p]];
            let parent = if b == 1 {
                F::from(1u64)
            } else {
                cur[layout.node_cells[b - 1][p & ((1usize << (b - 1)) - 1)]]
            };
            let appended = (p >> (b - 1)) & 1; // bit (b-1) of p
            let d = cur[layout.bit_cells[b - 1]];
            let factor = if appended == 1 { d } else { F::from(1u64) - d };
            out.push(node - parent * factor);
        }
    }

    // (3) Output selection: out.coord.limb[i] = Σ_j μ_j · T[j].coord.limb[i].
    let leaves = &layout.node_cells[w];
    let coord_bases = [layout.out_x_base, layout.out_y_base, layout.out_z_base];
    for (coord_idx, &base) in coord_bases.iter().enumerate() {
        for i in 0..NUM_LIMBS {
            let mut sum = F::zero();
            for j in 0..(1usize << w) {
                let t_limb = layout.table[j][coord_idx].limbs[i];
                sum += F::from(t_limb as u64) * cur[leaves[j]];
            }
            out.push(cur[base + i] - sum);
        }
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  FIXED-BASE COMB CHAIN (u1·G via muxes + adds, no doublings)
// ═══════════════════════════════════════════════════════════════════

/// Precompute the comb tables T_i[j] = j · 2^{w·i} · G for `n_windows`
/// windows.  Entry j=0 is the identity, encoded as (0:1:0).
pub fn build_comb_tables(w: usize, n_windows: usize) -> Vec<Vec<PointXYZ>> {
    use crate::p256_group::GENERATOR;
    let g = *GENERATOR;
    let mut tables = Vec::with_capacity(n_windows);
    let mut base = g; // 2^{w·i}·G for the current window
    for _i in 0..n_windows {
        let mut tbl: Vec<PointXYZ> = Vec::with_capacity(1 << w);
        // j = 0 → identity.
        tbl.push([FieldElement::zero(), one_fe(), FieldElement::zero()]);
        // j = 1..2^w → j·base by repeated addition.
        let mut acc = base;
        for j in 1..(1usize << w) {
            if j == 1 {
                let mut x = acc.x;
                x.freeze();
                let mut y = acc.y;
                y.freeze();
                tbl.push([x, y, one_fe()]);
            } else {
                acc = acc.add(&base);
                let mut x = acc.x;
                x.freeze();
                let mut y = acc.y;
                y.freeze();
                tbl.push([x, y, one_fe()]);
            }
        }
        tables.push(tbl);
        // Next window base = 2^w · base (w doublings).
        for _ in 0..w {
            base = base.double();
        }
    }
    tables
}

#[derive(Clone, Debug)]
pub struct FixedBaseCombLayout {
    pub w: usize,
    pub muxes: Vec<ConstPointMuxLayout>,
    /// One group-add per window after the first: adds[i-1] = acc + mux_i.
    pub adds: Vec<GroupAddGadgetLayout>,
}

/// Build a fixed-base comb over `n_windows` windows of `w` bits.  The
/// scalar's bit cells are supplied window-by-window in `window_bit_cells`
/// (each inner slice length w, LSB first).  `tables[i]` is window i's
/// constant table (see `build_comb_tables`).
pub fn build_fixed_base_comb_layout(
    start: usize,
    w: usize,
    window_bit_cells: &[Vec<usize>],
    tables: &[Vec<PointXYZ>],
) -> (FixedBaseCombLayout, usize) {
    let n = window_bit_cells.len();
    assert_eq!(tables.len(), n);
    let mut cursor = start;
    let mut muxes = Vec::with_capacity(n);
    let mut adds = Vec::with_capacity(n.saturating_sub(1));

    // Window 0: acc = mux_0 output (no add).
    let (mux0, e0) =
        build_const_point_mux_layout(cursor, window_bit_cells[0].clone(), tables[0].clone());
    cursor = e0;
    let mut acc_x = mux0.out_x_base;
    let mut acc_y = mux0.out_y_base;
    let mut acc_z = mux0.out_z_base;
    muxes.push(mux0);

    // Windows 1..n: mux_i, then acc = acc + mux_i.
    for i in 1..n {
        let (muxi, ei) =
            build_const_point_mux_layout(cursor, window_bit_cells[i].clone(), tables[i].clone());
        cursor = ei;
        let (add, ea) = build_group_add_layout(
            cursor, acc_x, acc_y, acc_z, muxi.out_x_base, muxi.out_y_base, muxi.out_z_base,
        );
        cursor = ea;
        acc_x = add.result_x3_limbs_base;
        acc_y = add.result_y3_limbs_base;
        acc_z = add.result_z3_limbs_base;
        muxes.push(muxi);
        adds.push(add);
    }

    (FixedBaseCombLayout { w, muxes, adds }, cursor)
}

pub fn fixed_base_comb_constraints(layout: &FixedBaseCombLayout) -> usize {
    layout.muxes.iter().map(const_point_mux_constraints).sum::<usize>()
        + layout.adds.iter().map(group_add_gadget_constraints).sum::<usize>()
}

fn read_fe(trace: &[Vec<F>], row: usize, base: usize) -> FieldElement {
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

/// Fill the comb for a scalar whose per-window digits are `window_digits`
/// (each a w-bit bool slice, LSB first).  Returns nothing; the result
/// accumulator is the last add's output (or mux_0's output if 1 window).
pub fn fill_fixed_base_comb(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &FixedBaseCombLayout,
    window_digit_bits: &[Vec<bool>],
) {
    let n = layout.muxes.len();
    assert_eq!(window_digit_bits.len(), n);

    fill_const_point_mux(trace, row, &layout.muxes[0], &window_digit_bits[0]);
    let mut acc_x = read_fe(trace, row, layout.muxes[0].out_x_base);
    let mut acc_y = read_fe(trace, row, layout.muxes[0].out_y_base);
    let mut acc_z = read_fe(trace, row, layout.muxes[0].out_z_base);

    for i in 1..n {
        fill_const_point_mux(trace, row, &layout.muxes[i], &window_digit_bits[i]);
        let mx = read_fe(trace, row, layout.muxes[i].out_x_base);
        let my = read_fe(trace, row, layout.muxes[i].out_y_base);
        let mz = read_fe(trace, row, layout.muxes[i].out_z_base);
        let add = &layout.adds[i - 1];
        fill_group_add_gadget(trace, row, add, &acc_x, &acc_y, &acc_z, &mx, &my, &mz);
        acc_x = read_fe(trace, row, add.result_x3_limbs_base);
        acc_y = read_fe(trace, row, add.result_y3_limbs_base);
        acc_z = read_fe(trace, row, add.result_z3_limbs_base);
    }
}

pub fn eval_fixed_base_comb(cur: &[F], layout: &FixedBaseCombLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(fixed_base_comb_constraints(layout));
    for m in &layout.muxes {
        out.extend(eval_const_point_mux(cur, m));
    }
    for a in &layout.adds {
        out.extend(eval_group_add_gadget(cur, a));
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_group::{AffinePoint, GENERATOR};
    use crate::p256_scalar::ScalarElement;

    fn make_trace_row(width: usize) -> Vec<Vec<F>> {
        (0..width).map(|_| vec![F::zero(); 1]).collect()
    }

    fn canon(fe: &FieldElement) -> FieldElement {
        let mut t = *fe;
        t.freeze();
        t
    }

    fn xyz(p: &AffinePoint) -> PointXYZ {
        let mut x = p.x;
        x.freeze();
        let mut y = p.y;
        y.freeze();
        [x, y, one_fe()]
    }

    /// The mux must select T[digit] for EVERY digit 0..2^w, with all
    /// constraints satisfied — over an arbitrary table of distinct
    /// non-identity points (j·G for j=1..2^w, and j=0 → 7·G here just to
    /// have a concrete entry).
    #[test]
    fn mux_selects_every_entry_w3() {
        let w = 3;
        let g = *GENERATOR;
        // Table of 8 distinct non-identity points: T[j] = (j+1)·G.
        let scal = |n: i64| {
            let mut s = ScalarElement::zero();
            s.limbs[0] = n;
            s
        };
        let table: Vec<PointXYZ> =
            (0..(1 << w)).map(|j| xyz(&g.scalar_mul(&scal(j as i64 + 1)))).collect();

        for digit in 0..(1usize << w) {
            let bit_cells: Vec<usize> = (0..w).collect();
            let start = w;
            let (layout, total) =
                build_const_point_mux_layout(start, bit_cells, table.clone());
            let mut trace = make_trace_row(total);
            let digit_bits: Vec<bool> = (0..w).map(|c| (digit >> c) & 1 == 1).collect();
            fill_const_point_mux(&mut trace, 0, &layout, &digit_bits);

            let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
            let cons = eval_const_point_mux(&cur, &layout);
            assert_eq!(cons.len(), const_point_mux_constraints(&layout));
            let nz = cons.iter().filter(|v| !v.is_zero()).count();
            assert_eq!(nz, 0, "digit {digit}: {nz} constraints failed");

            // Output must equal T[digit].
            let ox = canon(&read_fe(&trace, 0, layout.out_x_base));
            let oy = canon(&read_fe(&trace, 0, layout.out_y_base));
            assert_eq!(ox.limbs, table[digit][0].limbs, "digit {digit}: wrong x");
            assert_eq!(oy.limbs, table[digit][1].limbs, "digit {digit}: wrong y");
        }
    }

    /// Soundness: a non-boolean bit, or a tampered output limb, must make
    /// a constraint fire.
    #[test]
    fn mux_soundness_booleanity_and_tamper() {
        let w = 3;
        let g = *GENERATOR;
        let scal = |n: i64| {
            let mut s = ScalarElement::zero();
            s.limbs[0] = n;
            s
        };
        let table: Vec<PointXYZ> =
            (0..(1 << w)).map(|j| xyz(&g.scalar_mul(&scal(j as i64 + 1)))).collect();
        let bit_cells: Vec<usize> = (0..w).collect();
        let (layout, total) = build_const_point_mux_layout(w, bit_cells, table);

        // Honest digit = 5.
        let mut trace = make_trace_row(total);
        let digit_bits: Vec<bool> = (0..w).map(|c| (5usize >> c) & 1 == 1).collect();
        fill_const_point_mux(&mut trace, 0, &layout, &digit_bits);
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        assert_eq!(
            eval_const_point_mux(&cur, &layout).iter().filter(|v| !v.is_zero()).count(),
            0,
            "honest mux must satisfy all constraints"
        );

        // (a) Non-boolean bit: set bit 0 to 2.
        let mut t1 = trace.clone();
        t1[layout.bit_cells[0]][0] = F::from(2u64);
        let cur1: Vec<F> = (0..total).map(|c| t1[c][0]).collect();
        assert!(
            eval_const_point_mux(&cur1, &layout).iter().any(|v| !v.is_zero()),
            "non-boolean bit must fire a constraint"
        );

        // (b) Tampered output limb: bump out_x limb 0.
        let mut t2 = trace.clone();
        t2[layout.out_x_base][0] += F::from(1u64);
        let cur2: Vec<F> = (0..total).map(|c| t2[c][0]).collect();
        assert!(
            eval_const_point_mux(&cur2, &layout).iter().any(|v| !v.is_zero()),
            "tampered output must fire the selection constraint"
        );
    }

    /// Fixed-base comb computes u1·G, verified against native.  Uses a
    /// scalar with non-zero window digits (avoids the digit-0/identity
    /// path; see module note).  w=4, 2 windows → u1 ∈ [0, 256).
    #[test]
    fn fixed_base_comb_computes_u1g() {
        let w = 4;
        let n_windows = 2;
        let tables = build_comb_tables(w, n_windows);

        // digit_0 = 5, digit_1 = 3  ⇒ u1 = 5 + 16·3 = 53 (both non-zero).
        let d0 = 5usize;
        let d1 = 3usize;
        let window_digit_bits: Vec<Vec<bool>> = vec![
            (0..w).map(|c| (d0 >> c) & 1 == 1).collect(),
            (0..w).map(|c| (d1 >> c) & 1 == 1).collect(),
        ];

        // Bit cells: window 0 bits at 0..4, window 1 bits at 4..8.
        let window_bit_cells: Vec<Vec<usize>> =
            vec![(0..w).collect(), (w..2 * w).collect()];
        let start = 2 * w;
        let (layout, total) =
            build_fixed_base_comb_layout(start, w, &window_bit_cells, &tables);

        let mut trace = make_trace_row(total);
        // Place the scalar's bits.
        for (i, cells) in window_bit_cells.iter().enumerate() {
            for (c, &cell) in cells.iter().enumerate() {
                trace[cell][0] = F::from(window_digit_bits[i][c] as u64);
            }
        }
        fill_fixed_base_comb(&mut trace, 0, &layout, &window_digit_bits);

        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let nz = eval_fixed_base_comb(&cur, &layout).iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nz, 0, "fixed-base comb: {nz} constraints failed");

        // Native u1·G with u1 = 53.
        let g = *GENERATOR;
        let mut s = ScalarElement::zero();
        s.limbs[0] = 53;
        let expected = g.scalar_mul(&s);
        assert!(!expected.infinity);
        let mut ex = expected.x;
        ex.freeze();

        let last_add = layout.adds.last().unwrap();
        let x = read_fe(&trace, 0, last_add.result_x3_limbs_base);
        let z = read_fe(&trace, 0, last_add.result_z3_limbs_base);
        let lhs = canon(&x);
        let rhs = canon(&ex.mul(&z));
        assert!(lhs.ct_eq(&rhs), "comb u1·G affine x mismatch");
    }

    /// COST BENCH: fixed-base comb (u1·G, w=4) vs the double-and-add
    /// ladder half (one 256-step scalar_mul_chain).  Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib const_mux_cost -- --nocapture
    #[test]
    fn const_mux_cost_u1g_k256() {
        use crate::p256_scalar_mul_air::{
            build_scalar_mul_chain_layout, scalar_mul_chain_gadget_constraints,
        };
        let w = 4;
        let n_windows = 256 / w; // 64
        let tables = build_comb_tables(w, n_windows);
        let window_bit_cells: Vec<Vec<usize>> =
            (0..n_windows).map(|i| (i * w..i * w + w).collect()).collect();
        let start = n_windows * w;
        let (comb, comb_end) =
            build_fixed_base_comb_layout(start, w, &window_bit_cells, &tables);
        let comb_cells = comb_end - start;
        let comb_cons = fixed_base_comb_constraints(&comb);

        // Ladder half: one 256-step scalar_mul_chain (double+add per step).
        let b = |n: usize| n * NUM_LIMBS;
        let (chain, chain_end) = build_scalar_mul_chain_layout(
            10 * NUM_LIMBS, b(0), b(1), b(2), b(3), b(4), b(5), (0..256).collect(),
        );
        let chain_cells = chain_end - 10 * NUM_LIMBS;
        let chain_cons = scalar_mul_chain_gadget_constraints(&chain);

        let saved = chain_cells - comb_cells;
        let pct = 100.0 * saved as f64 / chain_cells as f64;
        const FULL_V2_AIR_CELLS: usize = 39_416_874;
        let full_pct = 100.0 * saved as f64 / FULL_V2_AIR_CELLS as f64;

        println!("\n═══ u1·G  @ 256-bit,  w={w}  ({n_windows} windows) ═══");
        println!("  double-and-add ladder half : {chain_cells:>10} cells  ({chain_cons} constraints)");
        println!("  fixed-base comb (mux+add)  : {comb_cells:>10} cells  ({comb_cons} constraints)");
        println!("  saved                      : {saved:>10} cells  ({pct:.1}% of the G ladder, {full_pct:.1}% of full verify AIR)");
        println!("  (64 muxes + 63 adds, ZERO doublings vs 256 doubles + 256 adds)\n");

        assert!(comb_cells < chain_cells, "comb must beat the ladder");
    }
}
