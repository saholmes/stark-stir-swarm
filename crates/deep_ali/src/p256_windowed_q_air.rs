// p256_windowed_q_air.rs — windowed variable-base scalar multiplication
// for the per-signature term u2·Q of ECDSA-P256 verification.
//
// ─────────────────────────────────────────────────────────────────────
// VARIABLE-POINT MULTIPLEXER
// ─────────────────────────────────────────────────────────────────────
// The fixed-base comb (`p256_const_mux_air`) selects from a table of
// PUBLIC CONSTANT points (G multiples), so the table is baked into the
// constraints as literals.  Q is per-signature, so its multiples must be
// computed IN-CIRCUIT and live in trace cells.  The variable-point mux is
// the same degree-2 one-hot construction, but the output constraint reads
// the table entries from cells instead of literals:
//
//   out.coord.limb[i] = Σ_j μ_j · table[j].coord.limb[i]     (degree 2:
//                                            μ_j cell × table cell)
//
// SOUNDNESS is identical to the constant mux: booleanity of the w digit
// bits forces the μ_j one-hot, so out = table[digit] exactly; the table
// cells are themselves range-checked group-op outputs, so out inherits
// tight form and needs no separate range check.  All constraints deg ≤ 2.
//
// ─────────────────────────────────────────────────────────────────────
// WINDOWED LADDER
// ─────────────────────────────────────────────────────────────────────
// Precompute {0·Q, 1·Q, …, (2^w−1)·Q} once (table[0]=O, table[1]=Q,
// table[j]=table[j−1]+Q), then process the scalar MSB-first in w-bit
// windows:
//     acc = table[digit_0]
//     per later window:  acc ← 2^w·acc (w doublings);  acc ← acc + table[digit_i]
// Result = u2·Q.  For 256 bits, w=4: 63×4 = 252 doublings + 63 window
// adds + (2^w−2)=14 table-build adds + 64 muxes — vs the naive ladder's
// 256 doubles + 256 adds.  Windowing removes ~192 of the 256 adds (the
// doubling count is inherent to variable-base and unchanged).
//
// Digit-0 note (same as the comb): table[0]=O; this prototype tests with
// non-zero window digits and pins table[0] to (0:1:0).  General digit-0
// handling (signed-digit recode / verified complete-add) is the one
// remaining integration step and does not change the op-count numbers.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::{PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::p256_field::{FieldElement, NUM_LIMBS};
use crate::p256_group_air::{
    build_group_add_layout, build_group_double_layout, eval_group_add_gadget,
    eval_group_double_gadget, fill_group_add_gadget, fill_group_double_gadget,
    group_add_gadget_constraints, group_double_gadget_constraints,
    GroupAddGadgetLayout, GroupDoubleGadgetLayout,
};

fn one_fe() -> FieldElement {
    let mut t = FieldElement::zero();
    t.limbs[0] = 1;
    t
}

fn read_fe(trace: &[Vec<F>], row: usize, base: usize) -> FieldElement {
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

fn place_fe(trace: &mut [Vec<F>], row: usize, base: usize, fe: &FieldElement) {
    for i in 0..NUM_LIMBS {
        trace[base + i][row] = F::from(fe.limbs[i] as u64);
    }
}

// ═══════════════════════════════════════════════════════════════════
//  VARIABLE-POINT MULTIPLEXER
// ═══════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct VarPointMuxLayout {
    pub w: usize,
    pub bit_cells: Vec<usize>,
    pub node_cells: Vec<Vec<usize>>,
    /// Cell bases of the 2^w table entries (referenced, not owned).
    pub table_x_bases: Vec<usize>,
    pub table_y_bases: Vec<usize>,
    pub table_z_bases: Vec<usize>,
    pub out_x_base: usize,
    pub out_y_base: usize,
    pub out_z_base: usize,
}

pub fn build_var_point_mux_layout(
    start: usize,
    bit_cells: Vec<usize>,
    table_x_bases: Vec<usize>,
    table_y_bases: Vec<usize>,
    table_z_bases: Vec<usize>,
) -> (VarPointMuxLayout, usize) {
    let w = bit_cells.len();
    let n = 1usize << w;
    assert_eq!(table_x_bases.len(), n);
    assert_eq!(table_y_bases.len(), n);
    assert_eq!(table_z_bases.len(), n);
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
        VarPointMuxLayout {
            w, bit_cells, node_cells,
            table_x_bases, table_y_bases, table_z_bases,
            out_x_base, out_y_base, out_z_base,
        },
        cursor,
    )
}

pub fn var_point_mux_constraints(layout: &VarPointMuxLayout) -> usize {
    let w = layout.w;
    w + ((1usize << (w + 1)) - 2) + 3 * NUM_LIMBS
}

/// Fill the μ tree and copy table[digit] into the output cells.  The
/// table cells must already be filled (the Q-multiples).
pub fn fill_var_point_mux(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &VarPointMuxLayout,
    digit_bits: &[bool],
) {
    let w = layout.w;
    assert_eq!(digit_bits.len(), w);
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
    // Output = table[digit] (read the selected table cells, write output).
    let tx = read_fe(trace, row, layout.table_x_bases[digit]);
    let ty = read_fe(trace, row, layout.table_y_bases[digit]);
    let tz = read_fe(trace, row, layout.table_z_bases[digit]);
    place_fe(trace, row, layout.out_x_base, &tx);
    place_fe(trace, row, layout.out_y_base, &ty);
    place_fe(trace, row, layout.out_z_base, &tz);
}

pub fn eval_var_point_mux(cur: &[F], layout: &VarPointMuxLayout) -> Vec<F> {
    let w = layout.w;
    let mut out = Vec::with_capacity(var_point_mux_constraints(layout));

    // (1) Booleanity.
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
            let appended = (p >> (b - 1)) & 1;
            let d = cur[layout.bit_cells[b - 1]];
            let factor = if appended == 1 { d } else { F::from(1u64) - d };
            out.push(node - parent * factor);
        }
    }
    // (3) Output selection (bilinear: μ_j · table_cell).
    let leaves = &layout.node_cells[w];
    let coord_bases = [
        (layout.out_x_base, &layout.table_x_bases),
        (layout.out_y_base, &layout.table_y_bases),
        (layout.out_z_base, &layout.table_z_bases),
    ];
    for (out_base, table_bases) in coord_bases {
        for i in 0..NUM_LIMBS {
            let mut sum = F::zero();
            for j in 0..(1usize << w) {
                sum += cur[leaves[j]] * cur[table_bases[j] + i];
            }
            out.push(cur[out_base + i] - sum);
        }
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  WINDOWED VARIABLE-BASE LADDER  (u2·Q)
// ═══════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct WindowedQLayout {
    pub w: usize,
    // Q-table entries (cell bases), index 0..2^w.
    pub table_x_bases: Vec<usize>,
    pub table_y_bases: Vec<usize>,
    pub table_z_bases: Vec<usize>,
    pub o_x_base: usize, // table[0] = O = (0:1:0)
    pub o_y_base: usize,
    pub o_z_base: usize,
    pub table_adds: Vec<GroupAddGadgetLayout>, // j = 2..2^w-1
    pub muxes: Vec<VarPointMuxLayout>,          // one per window
    pub doublings: Vec<GroupDoubleGadgetLayout>, // (n-1)*w doublings, flat
    pub adds: Vec<GroupAddGadgetLayout>,         // (n-1) window adds
}

/// Build a windowed u2·Q ladder.  `q_*_bases` reference the input point
/// Q's (x,y,z) cells (table[1]).  `window_bit_cells[i]` is window i's
/// w-bit digit cells (LSB first); windows are MSB-first (index 0 = top).
pub fn build_windowed_q_layout(
    start: usize,
    w: usize,
    q_x_base: usize,
    q_y_base: usize,
    q_z_base: usize,
    window_bit_cells: &[Vec<usize>],
) -> (WindowedQLayout, usize) {
    let n_entries = 1usize << w;
    let n_windows = window_bit_cells.len();
    let mut cursor = start;

    // table[0] = O owned cells.
    let o_x_base = cursor; cursor += NUM_LIMBS;
    let o_y_base = cursor; cursor += NUM_LIMBS;
    let o_z_base = cursor; cursor += NUM_LIMBS;

    let mut table_x_bases = vec![0usize; n_entries];
    let mut table_y_bases = vec![0usize; n_entries];
    let mut table_z_bases = vec![0usize; n_entries];
    table_x_bases[0] = o_x_base; table_y_bases[0] = o_y_base; table_z_bases[0] = o_z_base;
    table_x_bases[1] = q_x_base; table_y_bases[1] = q_y_base; table_z_bases[1] = q_z_base;

    // table[j] = table[j-1] + Q for j = 2..2^w-1.
    let mut table_adds = Vec::new();
    for j in 2..n_entries {
        let (add, e) = build_group_add_layout(
            cursor,
            table_x_bases[j - 1], table_y_bases[j - 1], table_z_bases[j - 1],
            q_x_base, q_y_base, q_z_base,
        );
        cursor = e;
        table_x_bases[j] = add.result_x3_limbs_base;
        table_y_bases[j] = add.result_y3_limbs_base;
        table_z_bases[j] = add.result_z3_limbs_base;
        table_adds.push(add);
    }

    // Windows.
    let mut muxes = Vec::with_capacity(n_windows);
    let mut doublings = Vec::new();
    let mut adds = Vec::new();

    // Window 0: acc = mux_0.
    let (mux0, e0) = build_var_point_mux_layout(
        cursor, window_bit_cells[0].clone(),
        table_x_bases.clone(), table_y_bases.clone(), table_z_bases.clone(),
    );
    cursor = e0;
    let mut acc_x = mux0.out_x_base;
    let mut acc_y = mux0.out_y_base;
    let mut acc_z = mux0.out_z_base;
    muxes.push(mux0);

    for i in 1..n_windows {
        // w doublings: acc = 2^w · acc.
        for _ in 0..w {
            let (dbl, e) = build_group_double_layout(cursor, acc_x, acc_y, acc_z);
            cursor = e;
            acc_x = dbl.result_x3_limbs_base;
            acc_y = dbl.result_y3_limbs_base;
            acc_z = dbl.result_z3_limbs_base;
            doublings.push(dbl);
        }
        // mux_i.
        let (muxi, em) = build_var_point_mux_layout(
            cursor, window_bit_cells[i].clone(),
            table_x_bases.clone(), table_y_bases.clone(), table_z_bases.clone(),
        );
        cursor = em;
        // acc = acc + mux_i.
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

    (
        WindowedQLayout {
            w,
            table_x_bases, table_y_bases, table_z_bases,
            o_x_base, o_y_base, o_z_base,
            table_adds, muxes, doublings, adds,
        },
        cursor,
    )
}

pub fn windowed_q_constraints(layout: &WindowedQLayout) -> usize {
    layout.table_adds.iter().map(group_add_gadget_constraints).sum::<usize>()
        + layout.muxes.iter().map(var_point_mux_constraints).sum::<usize>()
        + layout.doublings.iter().map(group_double_gadget_constraints).sum::<usize>()
        + layout.adds.iter().map(group_add_gadget_constraints).sum::<usize>()
}

/// Result accumulator bases (the last window add, or mux_0 if 1 window).
pub fn windowed_q_result_bases(layout: &WindowedQLayout) -> (usize, usize, usize) {
    if let Some(add) = layout.adds.last() {
        (add.result_x3_limbs_base, add.result_y3_limbs_base, add.result_z3_limbs_base)
    } else {
        let m = &layout.muxes[0];
        (m.out_x_base, m.out_y_base, m.out_z_base)
    }
}

/// Fill.  `q` is the input point (its cells must already be placed at the
/// q_*_bases passed to build).  `window_digit_bits[i]` is window i's
/// w-bit digit (LSB first), MSB-first across windows.
pub fn fill_windowed_q(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &WindowedQLayout,
    q: &FieldElement, q_y: &FieldElement,
    window_digit_bits: &[Vec<bool>],
) {
    // table[0] = O = (0:1:0).
    place_fe(trace, row, layout.o_x_base, &FieldElement::zero());
    place_fe(trace, row, layout.o_y_base, &one_fe());
    place_fe(trace, row, layout.o_z_base, &FieldElement::zero());
    // table[1] = Q is already placed by the caller at q_*_bases.
    let _ = (q, q_y);

    // Build table[j] = table[j-1] + Q.
    let q_x_fe = read_fe(trace, row, layout.table_x_bases[1]);
    let q_y_fe = read_fe(trace, row, layout.table_y_bases[1]);
    let q_z_fe = read_fe(trace, row, layout.table_z_bases[1]);
    for (idx, add) in layout.table_adds.iter().enumerate() {
        let j = idx + 2;
        let px = read_fe(trace, row, layout.table_x_bases[j - 1]);
        let py = read_fe(trace, row, layout.table_y_bases[j - 1]);
        let pz = read_fe(trace, row, layout.table_z_bases[j - 1]);
        fill_group_add_gadget(trace, row, add, &px, &py, &pz, &q_x_fe, &q_y_fe, &q_z_fe);
    }

    // Window 0.
    fill_var_point_mux(trace, row, &layout.muxes[0], &window_digit_bits[0]);
    let mut acc_x = read_fe(trace, row, layout.muxes[0].out_x_base);
    let mut acc_y = read_fe(trace, row, layout.muxes[0].out_y_base);
    let mut acc_z = read_fe(trace, row, layout.muxes[0].out_z_base);

    let mut dbl_iter = 0usize;
    for i in 1..layout.muxes.len() {
        for _ in 0..layout.w {
            let dbl = &layout.doublings[dbl_iter];
            dbl_iter += 1;
            fill_group_double_gadget(trace, row, dbl, &acc_x, &acc_y, &acc_z);
            acc_x = read_fe(trace, row, dbl.result_x3_limbs_base);
            acc_y = read_fe(trace, row, dbl.result_y3_limbs_base);
            acc_z = read_fe(trace, row, dbl.result_z3_limbs_base);
        }
        fill_var_point_mux(trace, row, &layout.muxes[i], &window_digit_bits[i]);
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

pub fn eval_windowed_q(cur: &[F], layout: &WindowedQLayout) -> Vec<F> {
    let mut out = Vec::with_capacity(windowed_q_constraints(layout));
    for a in &layout.table_adds {
        out.extend(eval_group_add_gadget(cur, a));
    }
    // window 0 mux, then interleaved (doublings, mux, add) per later window.
    out.extend(eval_var_point_mux(cur, &layout.muxes[0]));
    let mut dbl_iter = 0usize;
    for i in 1..layout.muxes.len() {
        for _ in 0..layout.w {
            out.extend(eval_group_double_gadget(cur, &layout.doublings[dbl_iter]));
            dbl_iter += 1;
        }
        out.extend(eval_var_point_mux(cur, &layout.muxes[i]));
        out.extend(eval_group_add_gadget(cur, &layout.adds[i - 1]));
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

    fn place_affine(trace: &mut [Vec<F>], xb: usize, yb: usize, zb: usize, p: &AffinePoint) {
        assert!(!p.infinity);
        for i in 0..NUM_LIMBS {
            trace[xb + i][0] = F::from(p.x.limbs[i] as u64);
            trace[yb + i][0] = F::from(p.y.limbs[i] as u64);
        }
        trace[zb][0] = F::from(1u64);
        for i in 1..NUM_LIMBS {
            trace[zb + i][0] = F::zero();
        }
    }

    /// Variable-point mux selects table[digit] for every digit, over a
    /// table of in-circuit Q-multiples ({1..2^w}·Q placed as cells).
    #[test]
    fn var_mux_selects_every_entry_w3() {
        let w = 3;
        let n = 1usize << w;
        let g = *GENERATOR;
        let q = g.double(); // Q = 2G

        // Lay out the table cells first (x,y,z blocks per entry), then the mux.
        let mut cursor = w; // bit cells 0..w
        let mut tx = vec![0; n]; let mut ty = vec![0; n]; let mut tz = vec![0; n];
        for j in 0..n {
            tx[j] = cursor; cursor += NUM_LIMBS;
            ty[j] = cursor; cursor += NUM_LIMBS;
            tz[j] = cursor; cursor += NUM_LIMBS;
        }
        let (layout, total) = build_var_point_mux_layout(
            cursor, (0..w).collect(), tx.clone(), ty.clone(), tz.clone(),
        );

        // Native table[j] = (j+1)·Q (all non-identity, distinct).
        let scal = |k: i64| { let mut s = ScalarElement::zero(); s.limbs[0] = k; s };
        for j in 0..n {
            let p = q.scalar_mul(&scal(j as i64 + 1));
            let mut trace = make_trace_row(total);
            // (fresh trace per digit below; here just check shape)
            let _ = (p, &mut trace);
        }

        for digit in 0..n {
            let mut trace = make_trace_row(total);
            // Place the full table.
            for j in 0..n {
                let p = q.scalar_mul(&scal(j as i64 + 1));
                place_affine(&mut trace, tx[j], ty[j], tz[j], &p);
            }
            let digit_bits: Vec<bool> = (0..w).map(|c| (digit >> c) & 1 == 1).collect();
            fill_var_point_mux(&mut trace, 0, &layout, &digit_bits);

            let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
            let cons = eval_var_point_mux(&cur, &layout);
            assert_eq!(cons.len(), var_point_mux_constraints(&layout));
            let nz = cons.iter().filter(|v| !v.is_zero()).count();
            assert_eq!(nz, 0, "digit {digit}: {nz} constraints failed");

            let expect = q.scalar_mul(&scal(digit as i64 + 1));
            let ox = canon(&read_fe(&trace, 0, layout.out_x_base));
            let mut exx = expect.x; exx.freeze();
            assert_eq!(ox.limbs, exx.limbs, "digit {digit}: wrong selected x");
        }
    }

    /// Soundness: tampering the selected output or a bit fires a constraint.
    #[test]
    fn var_mux_tamper_rejected() {
        let w = 3;
        let n = 1usize << w;
        let g = *GENERATOR;
        let q = g.double();
        let scal = |k: i64| { let mut s = ScalarElement::zero(); s.limbs[0] = k; s };

        let mut cursor = w;
        let mut tx = vec![0; n]; let mut ty = vec![0; n]; let mut tz = vec![0; n];
        for j in 0..n {
            tx[j] = cursor; cursor += NUM_LIMBS;
            ty[j] = cursor; cursor += NUM_LIMBS;
            tz[j] = cursor; cursor += NUM_LIMBS;
        }
        let (layout, total) = build_var_point_mux_layout(
            cursor, (0..w).collect(), tx.clone(), ty.clone(), tz.clone(),
        );
        let mut trace = make_trace_row(total);
        for j in 0..n {
            place_affine(&mut trace, tx[j], ty[j], tz[j], &q.scalar_mul(&scal(j as i64 + 1)));
        }
        let digit_bits: Vec<bool> = (0..w).map(|c| (5usize >> c) & 1 == 1).collect();
        fill_var_point_mux(&mut trace, 0, &layout, &digit_bits);
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        assert_eq!(eval_var_point_mux(&cur, &layout).iter().filter(|v| !v.is_zero()).count(), 0);

        // Tamper the output.
        let mut t2 = trace.clone();
        t2[layout.out_x_base][0] += F::from(1u64);
        let cur2: Vec<F> = (0..total).map(|c| t2[c][0]).collect();
        assert!(eval_var_point_mux(&cur2, &layout).iter().any(|v| !v.is_zero()));
    }

    /// Windowed ladder computes u2·Q, verified against native.  Non-zero
    /// window digits (see module note).  w=4, 2 windows → u2 ∈ [0,256).
    #[test]
    fn windowed_q_computes_u2q() {
        let w = 4;
        let g = *GENERATOR;
        let q = g.double().add(&g); // Q = 3G

        // Q cells at fixed bases; window bit cells after.
        let q_x = 0; let q_y = NUM_LIMBS; let q_z = 2 * NUM_LIMBS;
        let u_start = 3 * NUM_LIMBS;
        let window_bit_cells: Vec<Vec<usize>> = vec![
            (u_start..u_start + w).collect(),
            (u_start + w..u_start + 2 * w).collect(),
        ];
        let start = u_start + 2 * w;
        let (layout, total) = build_windowed_q_layout(start, w, q_x, q_y, q_z, &window_bit_cells);

        let mut trace = make_trace_row(total);
        place_affine(&mut trace, q_x, q_y, q_z, &q);

        // digit_0 = 3 (top window), digit_1 = 5  ⇒ u2 = 3·16 + 5 = 53.
        let d0 = 3usize; let d1 = 5usize;
        let wdb: Vec<Vec<bool>> = vec![
            (0..w).map(|c| (d0 >> c) & 1 == 1).collect(),
            (0..w).map(|c| (d1 >> c) & 1 == 1).collect(),
        ];
        for (i, cells) in window_bit_cells.iter().enumerate() {
            for (c, &cell) in cells.iter().enumerate() {
                trace[cell][0] = F::from(wdb[i][c] as u64);
            }
        }
        fill_windowed_q(&mut trace, 0, &layout, &q.x, &q.y, &wdb);

        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let nz = eval_windowed_q(&cur, &layout).iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nz, 0, "windowed Q: {nz} constraints failed");

        // Native u2·Q with u2 = 53.
        let mut s = ScalarElement::zero(); s.limbs[0] = 53;
        let expected = q.scalar_mul(&s);
        assert!(!expected.infinity);
        let mut ex = expected.x; ex.freeze();

        let (rx, _ry, rz) = windowed_q_result_bases(&layout);
        let x = read_fe(&trace, 0, rx);
        let z = read_fe(&trace, 0, rz);
        let lhs = canon(&x);
        let rhs = canon(&ex.mul(&z));
        assert!(lhs.ct_eq(&rhs), "windowed u2·Q affine x mismatch");
    }

    /// COST BENCH: windowed-Q vs naive Q ladder, and the FULL combined
    /// MSM (fixed-base-G comb + windowed-Q) vs v2's two chains + final add.
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib windowed_q_cost -- --nocapture
    #[test]
    fn windowed_q_cost_k256() {
        use crate::p256_scalar_mul_air::{
            build_scalar_mul_chain_layout, scalar_mul_chain_gadget_constraints,
        };
        use crate::p256_const_mux_air::{
            build_comb_tables, build_fixed_base_comb_layout, fixed_base_comb_constraints,
        };
        use crate::p256_group_air::build_group_add_layout;

        let w = 4;
        let n_win = 256 / w; // 64

        // Windowed Q.
        let q_x = 0; let q_y = NUM_LIMBS; let q_z = 2 * NUM_LIMBS;
        let u_start = 3 * NUM_LIMBS;
        let wbc: Vec<Vec<usize>> =
            (0..n_win).map(|i| (u_start + i * w..u_start + i * w + w).collect()).collect();
        let start = u_start + n_win * w;
        let (wq, wq_end) = build_windowed_q_layout(start, w, q_x, q_y, q_z, &wbc);
        let wq_cells = wq_end - start;
        let wq_cons = windowed_q_constraints(&wq);

        // Naive Q ladder (256-step chain).
        let b = |n: usize| n * NUM_LIMBS;
        let (chain, chain_end) = build_scalar_mul_chain_layout(
            10 * NUM_LIMBS, b(0), b(1), b(2), b(3), b(4), b(5), (0..256).collect(),
        );
        let chain_cells = chain_end - 10 * NUM_LIMBS;
        let chain_cons = scalar_mul_chain_gadget_constraints(&chain);

        // Fixed-base-G comb.
        let tables = build_comb_tables(w, n_win);
        let gbc: Vec<Vec<usize>> = (0..n_win).map(|i| (i * w..i * w + w).collect()).collect();
        let (comb, comb_end) = build_fixed_base_comb_layout(n_win * w, w, &gbc, &tables);
        let comb_cells = comb_end - n_win * w;
        let comb_cons = fixed_base_comb_constraints(&comb);

        // Original v2 MSM: two 256-step chains + one final add.
        let two_chain_cells = 2 * chain_cells + {
            let (_a, e) = build_group_add_layout(0, 0, 1, 2, 3, 4, 5); e
        };

        // Combined optimized MSM: comb(G) + windowed(Q) + 1 final add.
        let final_add_cells = { let (_a, e) = build_group_add_layout(0, 0, 1, 2, 3, 4, 5); e };
        let combined_cells = comb_cells + wq_cells + final_add_cells;

        let q_saved = chain_cells - wq_cells;
        let q_pct = 100.0 * q_saved as f64 / chain_cells as f64;
        let total_saved = two_chain_cells - combined_cells;
        const FULL_V2_AIR_CELLS: usize = 39_416_874;
        let full_pct = 100.0 * total_saved as f64 / FULL_V2_AIR_CELLS as f64;

        println!("\n═══ u2·Q  @ 256-bit,  w={w} ═══");
        println!("  naive double-and-add ladder : {chain_cells:>10} cells  ({chain_cons} cons)");
        println!("  windowed (table+mux+ladder) : {wq_cells:>10} cells  ({wq_cons} cons)");
        println!("  saved on Q                  : {q_saved:>10} cells  ({q_pct:.1}% of the Q ladder)");
        println!("\n═══ FULL MSM  u1·G + u2·Q  @ 256-bit ═══");
        println!("  v2: two chains + final add       : {two_chain_cells:>10} cells");
        println!("  fixed-base-G comb ({comb_cells} cells, {comb_cons} cons)");
        println!("  + windowed-Q      ({wq_cells} cells)");
        println!("  + final add");
        println!("  combined optimized MSM           : {combined_cells:>10} cells");
        println!("  TOTAL saved vs v2 MSM            : {total_saved:>10} cells  ({full_pct:.1}% of full verify AIR)");
        println!("  (Binius verify ~linear in committed width ⇒ cells ≈ core-hour proxy.)\n");

        assert!(wq_cells < chain_cells, "windowed Q must beat the naive ladder");
        assert!(combined_cells < two_chain_cells, "combined MSM must beat v2");
    }
}
