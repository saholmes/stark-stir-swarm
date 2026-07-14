// p256_ecdsa_air_v2_wi.rs — witnessed-inverse variant of the v2 ECDSA-P256 verify AIR.
//
// Self-contained drop-in alternative to `p256_ecdsa_air_v2` that replaces
// STEP 4 — the projective→affine conversion — only.  Everything else
// (the two scalar-mul chains, the final group add, the X_aff·1 mod n
// reduction and the equality check) is identical, cell-for-cell.
//
// ─────────────────────────────────────────────────────────────────────
// WHAT CHANGES
// ─────────────────────────────────────────────────────────────────────
// v2 computes  Z3⁻¹ = Z3^(p−2) mod p  with a 256-step Fp Fermat chain
// (`p256_fp_fermat_air`): ~677k cells / ~690k constraints, plus 256
// row-0 boundary constraints pinning the (p−2) exponent bits.
//
// This module instead uses a WITNESSED modular inverse:
//
//   * the prover supplies `z3_inv` as a range-checked witness element
//     (270 cells / 270 constraints — one `eval_element_range_check`),
//   * one Fp mul gadget computes  c = Z3 · z3_inv  (mod p)
//     (1188 cells / 1207 constraints — one `mul_gadget`),
//   * a row-0 boundary pins c to the CANONICAL 1 (limbs [1,0,…,0])
//     (NUM_LIMBS = 10 boundary constraints).
//
// Step-4 cost drops from ~677k cells to ~1458 cells — a ~460× reduction
// on the inversion, with the rest of the AIR untouched.
//
// ─────────────────────────────────────────────────────────────────────
// SOUNDNESS (equivalent to the Fermat chain, no relaxation)
// ─────────────────────────────────────────────────────────────────────
// The integer identity enforced by the mul gadget is  Z3·z3_inv = q·p + c.
// Pinning c to the canonical 1 forces  Z3·z3_inv − q·p = 1  exactly, hence
// Z3·z3_inv ≡ 1 (mod p).  This has a solution iff Z3 ≠ 0 — i.e. iff the
// result point R = u₁·G + u₂·Q is not the identity, which is exactly the
// FIPS 186-4 §6.4.2 step-6 precondition the Fermat path also relied on
// (Z3 = 0 ⇒ Z3^(p−2) = 0 ⇒ affine x = 0 ⇒ x mod n = 0 ≠ r).  Given a
// solution, z3_inv is pinned to the unique residue Z3⁻¹ (mod p), so the
// downstream  X_aff = X3·z3_inv (mod p)  is the true affine x.  A prover
// may supply any representative of Z3⁻¹ (the range check is the loose
// tight form [0,2²⁶⁰)); every such representative is ≡ Z3⁻¹ (mod p) and
// yields the same X_aff (mod p), so the freedom is harmless.
//
// The `== 1` check is a ROW-0 BOUNDARY (not a row-uniform constraint):
// on the padded (all-zero) rows a row-uniform `c − 1` would evaluate to
// −1 ≠ 0 and reject a valid proof.  This mirrors v2's (p−2)-bit boundary
// gating exactly.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;

use crate::p256_field::{FieldElement, LIMB_BITS, NUM_LIMBS};
use crate::p256_field_air::{
    eval_mul_gadget, fill_mul_gadget,
    MulGadgetLayout, ELEMENT_BIT_CELLS, ELEMENT_CONSTRAINTS,
    MUL_CARRY_BITS, MUL_CARRY_POSITIONS, MUL_GADGET_CONSTRAINTS,
};
use crate::p256_group_air::{
    build_group_add_layout, eval_group_add_gadget, fill_group_add_gadget,
    group_add_gadget_constraints, GroupAddGadgetLayout,
};
use crate::p256_scalar::ScalarElement;
use crate::p256_scalar_air::{
    eval_scalar_eq_gadget, eval_scalar_mul_gadget, fill_scalar_mul_gadget,
    ScalarEqGadgetLayout, ScalarMulGadgetLayout, SCALAR_EQ_GADGET_CONSTRAINTS,
    SCALAR_MUL_GADGET_CONSTRAINTS,
};
use crate::p256_scalar_mul_air::{
    build_scalar_mul_chain_layout, eval_scalar_mul_chain_gadget,
    fill_scalar_mul_chain_gadget, scalar_mul_chain_gadget_constraints,
    ScalarMulChainGadgetLayout,
};

#[derive(Clone, Debug)]
pub struct EcdsaVerifyV2WiLayout {
    // ─── Steps 1-3 (identical to v2) ────────────────────────────────
    pub g_x_base: usize,
    pub g_y_base: usize,
    pub g_z_base: usize,
    pub q_x_base: usize,
    pub q_y_base: usize,
    pub q_z_base: usize,
    pub u1_bit_cells: Vec<usize>,
    pub u2_bit_cells: Vec<usize>,
    pub u1_g_chain: ScalarMulChainGadgetLayout,
    pub u2_q_chain: ScalarMulChainGadgetLayout,
    pub final_add: GroupAddGadgetLayout,

    // ─── Step 4 (WITNESSED INVERSE — replaces the Fermat chain) ──────
    /// Witnessed z3_inv: limb cells + LSB-first range-check bit cells at
    /// split bases (matching the mul gadget's element convention, since
    /// `z3_inv_limbs_base` is fed as the mul gadgets' `b` input).
    pub z3_inv_limbs_base: usize,
    pub z3_inv_bits_base: usize,
    /// Fp mul gadget computing  c = Z3 · z3_inv (mod p).  Its `c` output
    /// is pinned to the canonical 1 by the row-0 boundary constraints.
    pub z3_inv_mul: MulGadgetLayout,

    // ─── Step 5: X_aff = X3 · z3_inv (reads the witness, not Fermat) ─
    pub x_affine_mul: MulGadgetLayout,

    // ─── Steps 6-7 (identical to v2) ────────────────────────────────
    pub scalar_one_base: usize,
    pub r_x_mod_n_layout: ScalarMulGadgetLayout,
    pub r_input_base: usize,
    pub r_eq_layout: ScalarEqGadgetLayout,
}

/// Allocate a mul-gadget's owned cells starting at `*cursor`.
fn alloc_mul_layout(
    cursor: &mut usize,
    a_limbs_base: usize,
    b_limbs_base: usize,
) -> MulGadgetLayout {
    let c_limbs_base = *cursor;
    let c_bits_base = c_limbs_base + NUM_LIMBS;
    let q_limbs_base = c_bits_base + ELEMENT_BIT_CELLS;
    let q_bits_base = q_limbs_base + NUM_LIMBS;
    let carry_bits_base = q_bits_base + ELEMENT_BIT_CELLS;
    *cursor = carry_bits_base + MUL_CARRY_POSITIONS * MUL_CARRY_BITS;
    MulGadgetLayout {
        a_limbs_base,
        b_limbs_base,
        c_limbs_base,
        c_bits_base,
        q_limbs_base,
        q_bits_base,
        carry_bits_base,
    }
}

/// Build the witnessed-inverse v2 layout.  K is the bit-length of
/// u_1 / u_2 (K=256 for full real ECDSA signatures).
pub fn build_ecdsa_verify_v2_wi_layout(
    start: usize,
    g_x_base: usize,
    g_y_base: usize,
    g_z_base: usize,
    q_x_base: usize,
    q_y_base: usize,
    q_z_base: usize,
    k: usize,
) -> (EcdsaVerifyV2WiLayout, usize) {
    let mut cursor = start;

    // ─── Bit cells for u_1 and u_2 ─────────────────────────────────
    let u1_bit_cells: Vec<usize> = (0..k).map(|i| cursor + i).collect();
    cursor += k;
    let u2_bit_cells: Vec<usize> = (0..k).map(|i| cursor + i).collect();
    cursor += k;

    // ─── u_1 · G chain ─────────────────────────────────────────────
    let (u1_g_chain, end1) = build_scalar_mul_chain_layout(
        cursor, g_x_base, g_y_base, g_z_base, g_x_base, g_y_base, g_z_base,
        u1_bit_cells.clone(),
    );
    cursor = end1;

    // ─── u_2 · Q chain ─────────────────────────────────────────────
    let (u2_q_chain, end2) = build_scalar_mul_chain_layout(
        cursor, q_x_base, q_y_base, q_z_base, q_x_base, q_y_base, q_z_base,
        u2_bit_cells.clone(),
    );
    cursor = end2;

    // ─── Final point addition: R = u_1·G + u_2·Q ───────────────────
    let u1g_x = u1_g_chain.steps.last().unwrap().select_x.c_limbs_base;
    let u1g_y = u1_g_chain.steps.last().unwrap().select_y.c_limbs_base;
    let u1g_z = u1_g_chain.steps.last().unwrap().select_z.c_limbs_base;
    let u2q_x = u2_q_chain.steps.last().unwrap().select_x.c_limbs_base;
    let u2q_y = u2_q_chain.steps.last().unwrap().select_y.c_limbs_base;
    let u2q_z = u2_q_chain.steps.last().unwrap().select_z.c_limbs_base;

    let (final_add, end3) = build_group_add_layout(
        cursor, u1g_x, u1g_y, u1g_z, u2q_x, u2q_y, u2q_z,
    );
    cursor = end3;

    // ─── STEP 4 (WI): witnessed z3_inv + one mul enforcing Z3·z3_inv≡1
    let z3_inv_limbs_base = cursor;
    cursor += NUM_LIMBS;
    let z3_inv_bits_base = cursor;
    cursor += ELEMENT_BIT_CELLS;
    let z3_inv_mul = alloc_mul_layout(
        &mut cursor, final_add.result_z3_limbs_base, z3_inv_limbs_base,
    );

    // ─── STEP 5: X_aff = X3 · z3_inv via mul_gadget ────────────────
    let x_affine_mul = alloc_mul_layout(
        &mut cursor, final_add.result_x3_limbs_base, z3_inv_limbs_base,
    );

    // ─── Step 6: scalar_one + X_aff mod n ──────────────────────────
    let scalar_one_base = cursor;
    cursor += NUM_LIMBS;
    let bits_per_elem = NUM_LIMBS * (LIMB_BITS as usize);
    let r_x_mod_n_c_limbs = cursor;
    let r_x_mod_n_c_bits = r_x_mod_n_c_limbs + NUM_LIMBS;
    let r_x_mod_n_q_limbs = r_x_mod_n_c_bits + bits_per_elem;
    let r_x_mod_n_q_bits = r_x_mod_n_q_limbs + NUM_LIMBS;
    let r_x_mod_n_carry_bits = r_x_mod_n_q_bits + bits_per_elem;
    cursor = r_x_mod_n_carry_bits + MUL_CARRY_POSITIONS * MUL_CARRY_BITS;
    let r_x_mod_n_layout = ScalarMulGadgetLayout {
        a_limbs_base: x_affine_mul.c_limbs_base, // input is X_aff
        b_limbs_base: scalar_one_base,
        c_limbs_base: r_x_mod_n_c_limbs,
        c_bits_base: r_x_mod_n_c_bits,
        q_limbs_base: r_x_mod_n_q_limbs,
        q_bits_base: r_x_mod_n_q_bits,
        carry_bits_base: r_x_mod_n_carry_bits,
    };

    // ─── Step 7: r_input + equality check ──────────────────────────
    let r_input_base = cursor;
    cursor += NUM_LIMBS;
    let r_eq_layout = ScalarEqGadgetLayout {
        a_limbs_base: r_x_mod_n_c_limbs,
        b_limbs_base: r_input_base,
    };

    (
        EcdsaVerifyV2WiLayout {
            g_x_base, g_y_base, g_z_base,
            q_x_base, q_y_base, q_z_base,
            u1_bit_cells, u2_bit_cells,
            u1_g_chain, u2_q_chain, final_add,
            z3_inv_limbs_base, z3_inv_bits_base, z3_inv_mul,
            x_affine_mul,
            scalar_one_base, r_x_mod_n_layout, r_input_base, r_eq_layout,
        },
        cursor,
    )
}

/// Row-uniform constraint count (holds at every LDE row).
pub fn ecdsa_verify_v2_wi_row_uniform_constraints(
    layout: &EcdsaVerifyV2WiLayout,
) -> usize {
    scalar_mul_chain_gadget_constraints(&layout.u1_g_chain)
        + scalar_mul_chain_gadget_constraints(&layout.u2_q_chain)
        + group_add_gadget_constraints(&layout.final_add)
        + ELEMENT_CONSTRAINTS          // z3_inv range check
        + MUL_GADGET_CONSTRAINTS       // Z3 · z3_inv
        + MUL_GADGET_CONSTRAINTS       // X3 · z3_inv
        + SCALAR_MUL_GADGET_CONSTRAINTS
        + SCALAR_EQ_GADGET_CONSTRAINTS
}

/// Row-0 boundary constraints: pin  c = Z3·z3_inv  to the canonical 1.
/// (Replaces v2's 256 (p−2)-bit boundary constraints with NUM_LIMBS.)
pub const ECDSA_V2_WI_ROW0_BOUNDARY_CONSTRAINTS: usize = NUM_LIMBS;

pub fn ecdsa_verify_v2_wi_row0_boundary_constraints() -> usize {
    ECDSA_V2_WI_ROW0_BOUNDARY_CONSTRAINTS
}

pub fn ecdsa_verify_v2_wi_constraints(layout: &EcdsaVerifyV2WiLayout) -> usize {
    ecdsa_verify_v2_wi_row_uniform_constraints(layout)
        + ecdsa_verify_v2_wi_row0_boundary_constraints()
}

fn read_fe_from(trace: &[Vec<F>], row: usize, base: usize) -> FieldElement {
    use ark_ff::PrimeField;
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        let v = trace[base + i][row];
        let bi = v.into_bigint();
        limbs[i] = bi.as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

fn place_proj(
    trace: &mut [Vec<F>],
    row: usize,
    x_base: usize, y_base: usize, z_base: usize,
    x: &FieldElement, y: &FieldElement, z: &FieldElement,
) {
    for i in 0..NUM_LIMBS {
        trace[x_base + i][row] = F::from(x.limbs[i] as u64);
        trace[y_base + i][row] = F::from(y.limbs[i] as u64);
        trace[z_base + i][row] = F::from(z.limbs[i] as u64);
    }
}

/// Fill a witnessed element's limbs + LSB-first bit decomposition at
/// split bases (same convention as the mul gadget's `place_element_split`).
fn place_element_split_local(
    trace: &mut [Vec<F>],
    row: usize,
    limbs_base: usize,
    bits_base: usize,
    fe: &FieldElement,
) {
    for i in 0..NUM_LIMBS {
        let limb = fe.limbs[i];
        trace[limbs_base + i][row] = F::from(limb as u64);
        for b in 0..LIMB_BITS as usize {
            let bit = (limb >> b) & 1;
            trace[bits_base + i * (LIMB_BITS as usize) + b][row] = F::from(bit as u64);
        }
    }
}

/// Range-check (booleanity + limb-pack = `ELEMENT_CONSTRAINTS`) for a
/// split-base element — identical to the mul gadget's internal input
/// range check, so the witnessed z3_inv is pinned to tight form.
fn eval_element_range_check_split(cur: &[F], limbs_base: usize, bits_base: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(ELEMENT_CONSTRAINTS);
    // Booleanity (260).
    for i in 0..NUM_LIMBS {
        for b in 0..LIMB_BITS as usize {
            let cell = cur[bits_base + i * (LIMB_BITS as usize) + b];
            out.push(cell * (F::from(1u64) - cell));
        }
    }
    // Limb pack (10).
    for i in 0..NUM_LIMBS {
        let mut s = F::zero();
        for b in 0..LIMB_BITS as usize {
            s += F::from(1u64 << b) * cur[bits_base + i * (LIMB_BITS as usize) + b];
        }
        out.push(cur[limbs_base + i] - s);
    }
    out
}

/// Fill the WI layout for a real ECDSA verify witness.  Same signature
/// as `fill_ecdsa_verify_v2`; the only behavioural difference is step 4.
pub fn fill_ecdsa_verify_v2_wi(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &EcdsaVerifyV2WiLayout,
    g_x: &FieldElement, g_y: &FieldElement,
    q_x: &FieldElement, q_y: &FieldElement,
    u1_bits: &[bool], u2_bits: &[bool],
    r: &ScalarElement,
) {
    let z_one = {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    };

    // ─── Steps 1-3: u_1·G + u_2·Q → R projective ───────────────────
    place_proj(trace, row, layout.g_x_base, layout.g_y_base, layout.g_z_base, g_x, g_y, &z_one);
    place_proj(trace, row, layout.q_x_base, layout.q_y_base, layout.q_z_base, q_x, q_y, &z_one);

    for (i, &bit) in u1_bits.iter().enumerate() {
        trace[layout.u1_bit_cells[i]][row] = F::from(bit as u64);
    }
    for (i, &bit) in u2_bits.iter().enumerate() {
        trace[layout.u2_bit_cells[i]][row] = F::from(bit as u64);
    }

    fill_scalar_mul_chain_gadget(
        trace, row, &layout.u1_g_chain, g_x, g_y, &z_one, g_x, g_y, &z_one, u1_bits,
    );
    fill_scalar_mul_chain_gadget(
        trace, row, &layout.u2_q_chain, q_x, q_y, &z_one, q_x, q_y, &z_one, u2_bits,
    );

    let u1g = layout.u1_g_chain.steps.last().unwrap();
    let u2q = layout.u2_q_chain.steps.last().unwrap();
    let r1_x = read_fe_from(trace, row, u1g.select_x.c_limbs_base);
    let r1_y = read_fe_from(trace, row, u1g.select_y.c_limbs_base);
    let r1_z = read_fe_from(trace, row, u1g.select_z.c_limbs_base);
    let r2_x = read_fe_from(trace, row, u2q.select_x.c_limbs_base);
    let r2_y = read_fe_from(trace, row, u2q.select_y.c_limbs_base);
    let r2_z = read_fe_from(trace, row, u2q.select_z.c_limbs_base);

    fill_group_add_gadget(
        trace, row, &layout.final_add,
        &r1_x, &r1_y, &r1_z, &r2_x, &r2_y, &r2_z,
    );

    // ─── STEP 4 (WI): witness z3_inv, prove Z3·z3_inv ≡ 1 ──────────
    let r_z = read_fe_from(trace, row, layout.final_add.result_z3_limbs_base);
    // Canonicalise Z3 before inverting (the group-add output is tight
    // but may be non-canonical, in [0,2p)).
    let mut z3_canon = r_z;
    z3_canon.freeze();
    let z3_inv = z3_canon.invert(); // canonical Z3⁻¹ (mod p), < p
    place_element_split_local(
        trace, row, layout.z3_inv_limbs_base, layout.z3_inv_bits_base, &z3_inv,
    );
    // c = Z3 · z3_inv (mod p) = canonical 1 (fill_mul_gadget freezes c).
    fill_mul_gadget(trace, row, &layout.z3_inv_mul, &r_z, &z3_inv);

    // ─── STEP 5: X_aff = X3 · z3_inv via Fp mul_gadget ────────────
    let r_x = read_fe_from(trace, row, layout.final_add.result_x3_limbs_base);
    fill_mul_gadget(trace, row, &layout.x_affine_mul, &r_x, &z3_inv);

    // ─── Step 6: X_aff mod n via scalar_mul gadget (b = 1) ────────
    trace[layout.scalar_one_base][row] = F::from(1u64);
    for i in 1..NUM_LIMBS {
        trace[layout.scalar_one_base + i][row] = F::zero();
    }
    let x_aff_fe = read_fe_from(trace, row, layout.x_affine_mul.c_limbs_base);
    let x_aff_se = ScalarElement { limbs: x_aff_fe.limbs };
    let one_se = ScalarElement::one();
    fill_scalar_mul_gadget(
        trace, row, &layout.r_x_mod_n_layout, &x_aff_se, &one_se,
    );

    // ─── Step 7: r_input for the equality check ───────────────────
    let mut r_canonical = *r;
    r_canonical.freeze();
    for i in 0..NUM_LIMBS {
        trace[layout.r_input_base + i][row] = F::from(r_canonical.limbs[i] as u64);
    }
}

/// Emit ROW-UNIFORM constraints (the gadget composition).
pub fn eval_ecdsa_verify_v2_wi_row_uniform(
    cur: &[F],
    layout: &EcdsaVerifyV2WiLayout,
) -> Vec<F> {
    let mut out =
        Vec::with_capacity(ecdsa_verify_v2_wi_row_uniform_constraints(layout));
    out.extend(eval_scalar_mul_chain_gadget(cur, &layout.u1_g_chain));
    out.extend(eval_scalar_mul_chain_gadget(cur, &layout.u2_q_chain));
    out.extend(eval_group_add_gadget(cur, &layout.final_add));
    out.extend(eval_element_range_check_split(
        cur, layout.z3_inv_limbs_base, layout.z3_inv_bits_base,
    ));
    out.extend(eval_mul_gadget(cur, &layout.z3_inv_mul));
    out.extend(eval_mul_gadget(cur, &layout.x_affine_mul));
    out.extend(eval_scalar_mul_gadget(cur, &layout.r_x_mod_n_layout));
    out.extend(eval_scalar_eq_gadget(cur, &layout.r_eq_layout));
    out
}

/// Emit ROW-0 BOUNDARY constraints: pin  c = Z3·z3_inv  to canonical 1.
pub fn eval_ecdsa_verify_v2_wi_row0_boundary(
    cur: &[F],
    layout: &EcdsaVerifyV2WiLayout,
) -> Vec<F> {
    let mut out = Vec::with_capacity(NUM_LIMBS);
    for i in 0..NUM_LIMBS {
        let expected = if i == 0 { F::from(1u64) } else { F::zero() };
        out.push(cur[layout.z3_inv_mul.c_limbs_base + i] - expected);
    }
    out
}

/// Emit ALL constraints (row-uniform followed by row-0 boundary).
pub fn eval_ecdsa_verify_v2_wi(
    cur: &[F],
    layout: &EcdsaVerifyV2WiLayout,
) -> Vec<F> {
    let mut out = eval_ecdsa_verify_v2_wi_row_uniform(cur, layout);
    out.extend(eval_ecdsa_verify_v2_wi_row0_boundary(cur, layout));
    out
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_group::GENERATOR;

    fn make_trace_row(width: usize) -> Vec<Vec<F>> {
        (0..width).map(|_| vec![F::zero(); 1]).collect()
    }

    /// Constraint-count / eval-length agreement.
    #[test]
    fn wi_constraint_count_matches_eval_length() {
        let g_x = 0; let g_y = NUM_LIMBS; let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) =
            build_ecdsa_verify_v2_wi_layout(start, g_x, g_y, g_z, q_x, q_y, q_z, 2);
        let trace = make_trace_row(total);
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let cons = eval_ecdsa_verify_v2_wi(&cur, &layout);
        assert_eq!(cons.len(), ecdsa_verify_v2_wi_constraints(&layout));
    }

    /// End-to-end constraint satisfaction at K=2, cross-checked against
    /// the existing (correct) v2 Fermat path: on identical inputs the
    /// witnessed-inverse AIR must (a) satisfy all its constraints and
    /// (b) produce the SAME affine x as the Fermat AIR.  Same affine x
    /// ⟹ the witnessed inverse computed Z3⁻¹ correctly.  This verifies
    /// the new path against the shipped reference without depending on
    /// the scalar-mul chain's internal bit semantics.
    #[test]
    fn wi_k2_matches_v2_fermat_affine_x() {
        use crate::p256_ecdsa_air_v2::{
            build_ecdsa_verify_v2_layout, fill_ecdsa_verify_v2,
        };
        let g_x = 0; let g_y = NUM_LIMBS; let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;

        let g = *GENERATOR;
        let q_point = g.double();
        let u1_bits = [true, true];
        let u2_bits = [true, false];
        let zero_scalar = ScalarElement::zero();

        // ── Reference: v2 Fermat path ──
        let (v2_layout, v2_total) =
            build_ecdsa_verify_v2_layout(start, g_x, g_y, g_z, q_x, q_y, q_z, 2);
        let mut v2_trace = make_trace_row(v2_total);
        fill_ecdsa_verify_v2(
            &mut v2_trace, 0, &v2_layout,
            &g.x, &g.y, &q_point.x, &q_point.y,
            &u1_bits, &u2_bits, &zero_scalar,
        );
        let mut v2_affine_x =
            read_fe_from(&v2_trace, 0, v2_layout.x_affine_mul.c_limbs_base);
        v2_affine_x.freeze();

        // ── New: witnessed-inverse path ──
        let (wi_layout, wi_total) =
            build_ecdsa_verify_v2_wi_layout(start, g_x, g_y, g_z, q_x, q_y, q_z, 2);
        let mut wi_trace = make_trace_row(wi_total);
        fill_ecdsa_verify_v2_wi(
            &mut wi_trace, 0, &wi_layout,
            &g.x, &g.y, &q_point.x, &q_point.y,
            &u1_bits, &u2_bits, &zero_scalar,
        );
        // Close the equality gadget self-consistently (as v2's own test does).
        let r_x_mod_n_fe =
            read_fe_from(&wi_trace, 0, wi_layout.r_x_mod_n_layout.c_limbs_base);
        for i in 0..NUM_LIMBS {
            wi_trace[wi_layout.r_input_base + i][0] = F::from(r_x_mod_n_fe.limbs[i] as u64);
        }

        let cur: Vec<F> = (0..wi_total).map(|c| wi_trace[c][0]).collect();
        let nonzero = eval_ecdsa_verify_v2_wi(&cur, &wi_layout)
            .iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nonzero, 0, "WI K=2: {nonzero} constraints failed");

        let mut wi_affine_x =
            read_fe_from(&wi_trace, 0, wi_layout.x_affine_mul.c_limbs_base);
        wi_affine_x.freeze();

        assert_eq!(
            wi_affine_x.limbs, v2_affine_x.limbs,
            "witnessed-inverse affine x ≠ Fermat affine x (WI={:?}, Fermat={:?})",
            wi_affine_x.limbs, v2_affine_x.limbs,
        );
    }

    /// NEGATIVE soundness: corrupting the witnessed z3_inv (so it is no
    /// longer Z3⁻¹) must break the `Z3·z3_inv == 1` boundary and/or the
    /// mul identity — the proof is rejected.  This is the witnessed-
    /// inverse analogue of v2's `row0_boundary_catches_flipped_bit`.
    #[test]
    fn wi_tampered_inverse_is_rejected() {
        let g_x = 0; let g_y = NUM_LIMBS; let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) =
            build_ecdsa_verify_v2_wi_layout(start, g_x, g_y, g_z, q_x, q_y, q_z, 2);

        let mut trace = make_trace_row(total);
        let g = *GENERATOR;
        let q_point = g.double();
        fill_ecdsa_verify_v2_wi(
            &mut trace, 0, &layout,
            &g.x, &g.y, &q_point.x, &q_point.y,
            &[true, true], &[true, false], &ScalarElement::zero(),
        );
        // Close the equality gadget self-consistently so this is a fully
        // honest witness (copy computed R.x mod n into r_input).
        let r_x_mod_n_fe =
            read_fe_from(&trace, 0, layout.r_x_mod_n_layout.c_limbs_base);
        for i in 0..NUM_LIMBS {
            trace[layout.r_input_base + i][0] = F::from(r_x_mod_n_fe.limbs[i] as u64);
        }

        // Honest witness satisfies everything.
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        assert_eq!(
            eval_ecdsa_verify_v2_wi(&cur, &layout).iter().filter(|v| !v.is_zero()).count(),
            0,
            "honest WI witness must satisfy all constraints",
        );

        // Tamper: bump the low limb of z3_inv by 1 (now ≠ Z3⁻¹).  The
        // mul gadget's stale c-cells no longer equal Z3·z3_inv, so the
        // schoolbook/boundary constraints fire.
        let cell = layout.z3_inv_limbs_base; // limb 0 of the witness element
        trace[cell][0] += F::from(1u64);
        let cur_bad: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let nonzero = eval_ecdsa_verify_v2_wi(&cur_bad, &layout)
            .iter().filter(|v| !v.is_zero()).count();
        assert!(
            nonzero > 0,
            "tampering the witnessed inverse must make ≥1 constraint fire",
        );
    }

    /// COST BENCH (not a pass/fail assertion beyond the reduction sign):
    /// prints the K=256 trace-width and constraint-count of the v2
    /// Fermat path vs the witnessed-inverse path, and the delta.  Run:
    ///   cargo test --release -p deep_ali wi_vs_fermat_cost -- --nocapture
    #[test]
    fn wi_vs_fermat_cost_k256() {
        use crate::p256_ecdsa_air_v2::{
            build_ecdsa_verify_v2_layout, ecdsa_verify_v2_constraints,
        };
        let g_x = 0; let g_y = NUM_LIMBS; let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let k = 256;

        let (fermat_layout, fermat_cells) =
            build_ecdsa_verify_v2_layout(start, g_x, g_y, g_z, q_x, q_y, q_z, k);
        let fermat_cons = ecdsa_verify_v2_constraints(&fermat_layout);

        let (wi_layout, wi_cells) =
            build_ecdsa_verify_v2_wi_layout(start, g_x, g_y, g_z, q_x, q_y, q_z, k);
        let wi_cons = ecdsa_verify_v2_wi_constraints(&wi_layout);

        let cell_saving = fermat_cells - wi_cells;
        let cons_saving = fermat_cons - wi_cons;
        let cell_pct = 100.0 * cell_saving as f64 / fermat_cells as f64;
        let cons_pct = 100.0 * cons_saving as f64 / fermat_cons as f64;

        println!("\n═══ ECDSA-P256 verify AIR @ K=256: Fermat vs witnessed-inverse ═══");
        println!("  trace width (cells):");
        println!("    v2 Fermat Z3^(p-2)   : {fermat_cells:>10}");
        println!("    witnessed inverse    : {wi_cells:>10}");
        println!("    saved                : {cell_saving:>10}  ({cell_pct:.1}% of total)");
        println!("  constraints:");
        println!("    v2 Fermat            : {fermat_cons:>10}");
        println!("    witnessed inverse    : {wi_cons:>10}");
        println!("    saved                : {cons_saving:>10}  ({cons_pct:.1}% of total)");
        println!("  (prover/verifier cost in Binius is ~linear in committed width,");
        println!("   so the cell-count delta is the first-order core-hour proxy.)\n");

        assert!(wi_cells < fermat_cells, "WI must reduce trace width");
        assert!(wi_cons < fermat_cons, "WI must reduce constraint count");
    }
}
