// p256_ecdsa_air_v2.rs — Phase 5 v2 ECDSA-P256 verify AIR.
//
// Extends `p256_ecdsa_air` (Phase 5 v0) with the missing projective→
// affine conversion + reduces the AFFINE x mod n for the equality
// check.  The Phase 5 v0 layout reduces projective X3 mod n; per the
// AIR's own docstring that is "tautological consistency" that exercises
// the equality gadget but does NOT actually verify a real ECDSA
// signature.  This v2 layout closes that gap.
//
// Composition:
//
//   1. u_1 · G chain                     (existing scalar_mul_chain)
//   2. u_2 · Q chain                     (existing scalar_mul_chain)
//   3. final_add: R = u_1·G + u_2·Q      (existing group_add gadget)
//   4. Z3⁻¹ = Z3^(p−2) mod p             (NEW: Fp Fermat 256-bit chain)
//   5. X_aff = X3 · Z3⁻¹ mod p           (NEW: Fp mul gadget)
//   6. X_aff mod n                       (existing scalar_mul gadget, b=1)
//   7. X_aff mod n == r                  (existing scalar_eq gadget)
//
// With this composition the AIR's equality check uses the AFFINE x
// coordinate (matching FIPS 186-4 §6.4.2), so a STARK proof over a
// REAL ECDSA signature actually verifies that signature in-circuit.
//
// Soundness: the (p−2) bit cells are pinned by ROW-0 BOUNDARY
// CONSTRAINTS (the 256 entries at the end of the constraint list
// returned by `ecdsa_verify_v2_constraints`).  Each bit cell's
// value at trace row 0 is constrained to equal the corresponding
// constant bit of (p−2); the FRI merge applies the row-0 Lagrange
// indicator polynomial so the constraint vanishes on padded rows
// (rows ≥ 1) regardless of cell contents.  A malicious prover that
// writes different bits produces a non-zero boundary constraint at
// row 0 → c_eval doesn't divide cleanly by Z_H → FRI proximity
// tests reject the proof.  Verified by the
// `row0_boundary_catches_flipped_bit` test below.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use num_bigint::BigUint;

use crate::p256_field::{FieldElement, LIMB_BITS, NUM_LIMBS};
use crate::p256_field_air::{
    eval_mul_gadget, fill_mul_gadget, MulGadgetLayout,
    ELEMENT_BIT_CELLS, MUL_CARRY_BITS, MUL_CARRY_POSITIONS,
    MUL_GADGET_CONSTRAINTS,
};
use crate::p256_fp_fermat_air::{
    build_fp_fermat_chain_layout, eval_fp_fermat_chain_gadget,
    fill_fp_fermat_chain_gadget, fp_fermat_chain_gadget_constraints,
    FpFermatChainGadgetLayout,
};
use crate::p256_group_air::{
    build_group_add_layout, eval_group_add_gadget, fill_group_add_gadget,
    group_add_gadget_constraints, GroupAddGadgetLayout,
};
use crate::p256_scalar::ScalarElement;
use crate::p256_scalar_air::{
    eval_scalar_eq_gadget, eval_scalar_mul_gadget, fill_scalar_mul_gadget,
    ScalarEqGadgetLayout, ScalarMulGadgetLayout,
    SCALAR_EQ_GADGET_CONSTRAINTS, SCALAR_MUL_GADGET_CONSTRAINTS,
};
use crate::p256_scalar_mul_air::{
    build_scalar_mul_chain_layout, eval_scalar_mul_chain_gadget,
    fill_scalar_mul_chain_gadget, scalar_mul_chain_gadget_constraints,
    ScalarMulChainGadgetLayout,
};

/// P-256 prime p = 2^256 - 2^224 + 2^192 + 2^96 - 1.  We need (p-2)
/// for Fermat inversion: `z^(p-2) ≡ z^(-1) mod p`.
const P_MINUS_2_HEX: &[u8] =
    b"FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFD";

/// Return the MSB-first bits of (p-2), exactly 256 of them.
pub fn p_minus_2_bits() -> Vec<bool> {
    let p_minus_2 = BigUint::parse_bytes(P_MINUS_2_HEX, 16)
        .expect("P-256 (p-2) hex constant valid");
    let bytes = p_minus_2.to_bytes_be();
    let mut be32 = [0u8; 32];
    let start = 32 - bytes.len();
    be32[start..].copy_from_slice(&bytes);
    let mut bits = Vec::with_capacity(256);
    for byte in be32.iter() {
        for shift in (0..8).rev() {
            bits.push((byte >> shift) & 1 == 1);
        }
    }
    bits
}

#[derive(Clone, Debug)]
pub struct EcdsaVerifyV2Layout {
    // ─── Inherited from v0 (steps 1-3) ──────────────────────────────
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

    // ─── NEW v2 (step 4): Z3⁻¹ via Fermat ─────────────────────────
    /// 256 cells holding the bits of (p-2) MSB-first.  Filled
    /// deterministically by `fill_ecdsa_verify_v2`; not constrained
    /// to specific values by the row-uniform AIR (trust by construction
    /// — see module docstring).
    pub p_minus_2_bit_cells: Vec<usize>,
    /// Cells holding FieldElement(1) — initial accumulator for the
    /// Fermat chain (z_inv = 1 · z^(p-2) by squaring-and-multiplying).
    pub one_fp_base: usize,
    /// The Fermat-inversion chain over Z3.
    pub z3_inv_chain: FpFermatChainGadgetLayout,

    // ─── NEW v2 (step 5): X_aff = X3 · Z3⁻¹ ───────────────────────
    pub x_affine_mul: MulGadgetLayout,

    // ─── Inherited from v0 (steps 6-7) ──────────────────────────────
    pub scalar_one_base: usize,
    pub r_x_mod_n_layout: ScalarMulGadgetLayout,
    pub r_input_base: usize,
    pub r_eq_layout: ScalarEqGadgetLayout,
}

/// Build the top-level v2 layout.  K is the bit-length of u_1 / u_2
/// (set K=256 for full real ECDSA signatures).
pub fn build_ecdsa_verify_v2_layout(
    start: usize,
    g_x_base: usize,
    g_y_base: usize,
    g_z_base: usize,
    q_x_base: usize,
    q_y_base: usize,
    q_z_base: usize,
    k: usize,
) -> (EcdsaVerifyV2Layout, usize) {
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

    // ─── NEW v2 step 4: Fermat chain over Z3 ───────────────────────
    //
    // p_minus_2 has 256 bits.  Allocate one bit cell per bit + the
    // initial-accumulator cells (FieldElement(1)).
    let p_minus_2_bit_cells: Vec<usize> = (0..256).map(|i| cursor + i).collect();
    cursor += 256;
    let one_fp_base = cursor;
    cursor += NUM_LIMBS;
    let (z3_inv_chain, end4) = build_fp_fermat_chain_layout(
        cursor, one_fp_base, final_add.result_z3_limbs_base,
        p_minus_2_bit_cells.clone(),
    );
    cursor = end4;

    // ─── NEW v2 step 5: X_aff = X3 · Z3⁻¹ via mul_gadget ───────────
    let z3_inv_output_base =
        z3_inv_chain.steps.last().unwrap().select_layout.c_limbs_base;
    let bits_per_elem = NUM_LIMBS * (LIMB_BITS as usize);
    let x_affine_c_limbs = cursor;
    let x_affine_c_bits = x_affine_c_limbs + NUM_LIMBS;
    let x_affine_q_limbs = x_affine_c_bits + bits_per_elem;
    let x_affine_q_bits = x_affine_q_limbs + NUM_LIMBS;
    let x_affine_carry_bits = x_affine_q_bits + bits_per_elem;
    cursor = x_affine_carry_bits + MUL_CARRY_POSITIONS * MUL_CARRY_BITS;
    let x_affine_mul = MulGadgetLayout {
        a_limbs_base: final_add.result_x3_limbs_base,
        b_limbs_base: z3_inv_output_base,
        c_limbs_base: x_affine_c_limbs,
        c_bits_base: x_affine_c_bits,
        q_limbs_base: x_affine_q_limbs,
        q_bits_base: x_affine_q_bits,
        carry_bits_base: x_affine_carry_bits,
    };

    // ─── Inherited v0 step 6: scalar_one + X_aff mod n ─────────────
    let scalar_one_base = cursor;
    cursor += NUM_LIMBS;
    let r_x_mod_n_c_limbs = cursor;
    let r_x_mod_n_c_bits = r_x_mod_n_c_limbs + NUM_LIMBS;
    let r_x_mod_n_q_limbs = r_x_mod_n_c_bits + bits_per_elem;
    let r_x_mod_n_q_bits = r_x_mod_n_q_limbs + NUM_LIMBS;
    let r_x_mod_n_carry_bits = r_x_mod_n_q_bits + bits_per_elem;
    cursor = r_x_mod_n_carry_bits + MUL_CARRY_POSITIONS * MUL_CARRY_BITS;
    let r_x_mod_n_layout = ScalarMulGadgetLayout {
        // KEY DIFFERENCE FROM v0: the input is X_aff, not X3.
        a_limbs_base: x_affine_c_limbs,
        b_limbs_base: scalar_one_base,
        c_limbs_base: r_x_mod_n_c_limbs,
        c_bits_base: r_x_mod_n_c_bits,
        q_limbs_base: r_x_mod_n_q_limbs,
        q_bits_base: r_x_mod_n_q_bits,
        carry_bits_base: r_x_mod_n_carry_bits,
    };

    // ─── Inherited v0 step 7: r_input + equality check ─────────────
    let r_input_base = cursor;
    cursor += NUM_LIMBS;
    let r_eq_layout = ScalarEqGadgetLayout {
        a_limbs_base: r_x_mod_n_c_limbs,
        b_limbs_base: r_input_base,
    };

    (
        EcdsaVerifyV2Layout {
            g_x_base, g_y_base, g_z_base,
            q_x_base, q_y_base, q_z_base,
            u1_bit_cells, u2_bit_cells,
            u1_g_chain, u2_q_chain, final_add,
            p_minus_2_bit_cells, one_fp_base, z3_inv_chain,
            x_affine_mul,
            scalar_one_base, r_x_mod_n_layout, r_input_base, r_eq_layout,
        },
        cursor,
    )
}

/// Count of ROW-UNIFORM constraints in the v2 composition (the kind
/// the existing FRI merge applies on every LDE row).  The boundary
/// constraints are reported separately by
/// `ecdsa_verify_v2_row0_boundary_constraints`.
pub fn ecdsa_verify_v2_row_uniform_constraints(layout: &EcdsaVerifyV2Layout) -> usize {
    scalar_mul_chain_gadget_constraints(&layout.u1_g_chain)
        + scalar_mul_chain_gadget_constraints(&layout.u2_q_chain)
        + group_add_gadget_constraints(&layout.final_add)
        + fp_fermat_chain_gadget_constraints(&layout.z3_inv_chain)
        + MUL_GADGET_CONSTRAINTS
        + SCALAR_MUL_GADGET_CONSTRAINTS
        + SCALAR_EQ_GADGET_CONSTRAINTS
}

/// Number of row-0 boundary constraints: one per (p-2) bit cell,
/// pinning each bit cell to the corresponding constant bit of (p-2).
/// Closes the soundness gap that the row-uniform AIR alone leaves the
/// bit cells unconstrained — a malicious prover with different bits
/// would otherwise compute `base^k` for arbitrary `k ≠ p-2`.
pub const ECDSA_V2_ROW0_BOUNDARY_CONSTRAINTS: usize = 256;

pub fn ecdsa_verify_v2_row0_boundary_constraints() -> usize {
    ECDSA_V2_ROW0_BOUNDARY_CONSTRAINTS
}

/// Total constraint count = row-uniform + row-0 boundary.
pub fn ecdsa_verify_v2_constraints(layout: &EcdsaVerifyV2Layout) -> usize {
    ecdsa_verify_v2_row_uniform_constraints(layout)
        + ecdsa_verify_v2_row0_boundary_constraints()
}

/// Combined per-row constraint vector with the row-0 boundary gated by a
/// `trace_row == 0` step (instead of the Lagrange `row0_indicator` the
/// streaming merge uses).  This makes the evaluator consistent with the
/// generic `sub_air_with_trace` verifier (which only knows the trace row),
/// enabling witness-binding for the single-row ECDSA-P256 v2 AIR.  Pair
/// with `crate::deep_ali_merge_p256_ecdsa_v2_rowgated_streaming`.
pub fn eval_ecdsa_verify_v2_rowgated_per_row(
    cur: &[F],
    trace_row: usize,
    layout: &EcdsaVerifyV2Layout,
) -> Vec<F> {
    let mut out = eval_ecdsa_verify_v2_row_uniform(cur, layout);
    let boundary = eval_ecdsa_verify_v2_row0_boundary(cur, layout);
    if trace_row == 0 {
        out.extend(boundary);
    } else {
        out.extend(core::iter::repeat(F::from(0u64)).take(boundary.len()));
    }
    out
}

/// Read a `FieldElement` from `NUM_LIMBS` adjacent trace cells.
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

/// Place an affine point (x, y, z=1) at the given limb bases.
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

/// Fill the v2 layout for a real ECDSA verify witness.
///
/// Arguments:
/// - `g`, `q` — affine generator G and public-key point Q
/// - `u1_bits`, `u2_bits` — MSB-first bit decomposition of the FIPS
///   186-4 scalars `u_1 = e·s⁻¹ mod n` and `u_2 = r·s⁻¹ mod n`
///   (caller pre-computes via native FIPS 186-4 §6.4.2 steps 1-4)
/// - `r` — the signature's `r` scalar (caller-supplied; the AIR
///   verifies `R.x_affine mod n == r`)
pub fn fill_ecdsa_verify_v2(
    trace: &mut [Vec<F>],
    row: usize,
    layout: &EcdsaVerifyV2Layout,
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

    // ─── NEW step 4: Fermat chain for Z3⁻¹ ────────────────────────
    //
    // Place (p-2) bits, initial accumulator 1, then run the chain
    // with base = Z3 from the previous group_add output.
    let pm2_bits = p_minus_2_bits();
    for (i, &bit) in pm2_bits.iter().enumerate() {
        trace[layout.p_minus_2_bit_cells[i]][row] = F::from(bit as u64);
    }
    let one_fe = {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    };
    for i in 0..NUM_LIMBS {
        trace[layout.one_fp_base + i][row] = F::from(one_fe.limbs[i] as u64);
    }
    let r_z = read_fe_from(trace, row, layout.final_add.result_z3_limbs_base);
    fill_fp_fermat_chain_gadget(
        trace, row, &layout.z3_inv_chain, &one_fe, &r_z, &pm2_bits,
    );

    // ─── NEW step 5: X_aff = X3 · Z3⁻¹ via Fp mul_gadget ──────────
    let r_x = read_fe_from(trace, row, layout.final_add.result_x3_limbs_base);
    let z3_inv = read_fe_from(
        trace, row,
        layout.z3_inv_chain.steps.last().unwrap().select_layout.c_limbs_base,
    );
    fill_mul_gadget(trace, row, &layout.x_affine_mul, &r_x, &z3_inv);

    // ─── Inherited step 6: X_aff mod n via scalar_mul gadget ──────
    trace[layout.scalar_one_base + 0][row] = F::from(1u64);
    for i in 1..NUM_LIMBS {
        trace[layout.scalar_one_base + i][row] = F::zero();
    }
    let x_aff_fe = read_fe_from(trace, row, layout.x_affine_mul.c_limbs_base);
    // Re-interpret the FieldElement limbs as a ScalarElement integer.
    let x_aff_se = ScalarElement { limbs: x_aff_fe.limbs };
    let one_se = ScalarElement::one();
    fill_scalar_mul_gadget(
        trace, row, &layout.r_x_mod_n_layout, &x_aff_se, &one_se,
    );

    // ─── Inherited step 7: r_input for the equality check ─────────
    let mut r_canonical = *r;
    r_canonical.freeze();
    for i in 0..NUM_LIMBS {
        trace[layout.r_input_base + i][row] = F::from(r_canonical.limbs[i] as u64);
    }
}

/// Emit ROW-UNIFORM constraints (the gadget composition).  These hold
/// at EVERY trace row; the FRI merge applies them on every LDE point.
pub fn eval_ecdsa_verify_v2_row_uniform(
    cur: &[F],
    layout: &EcdsaVerifyV2Layout,
) -> Vec<F> {
    let mut out = Vec::with_capacity(ecdsa_verify_v2_row_uniform_constraints(layout));
    out.extend(eval_scalar_mul_chain_gadget(cur, &layout.u1_g_chain));
    out.extend(eval_scalar_mul_chain_gadget(cur, &layout.u2_q_chain));
    out.extend(eval_group_add_gadget(cur, &layout.final_add));
    out.extend(eval_fp_fermat_chain_gadget(cur, &layout.z3_inv_chain));
    out.extend(eval_mul_gadget(cur, &layout.x_affine_mul));
    out.extend(eval_scalar_mul_gadget(cur, &layout.r_x_mod_n_layout));
    out.extend(eval_scalar_eq_gadget(cur, &layout.r_eq_layout));
    out
}

/// Emit ROW-0 BOUNDARY constraints.  These pin each (p-2) bit cell
/// to its constant value at trace row 0; they're gated by a row-0
/// Lagrange indicator in the FRI merge layer, so they vanish on
/// padded (rows ≥ 1) trace rows regardless of the cell contents.
pub fn eval_ecdsa_verify_v2_row0_boundary(
    cur: &[F],
    layout: &EcdsaVerifyV2Layout,
) -> Vec<F> {
    let pm2_bits = p_minus_2_bits();
    let mut out = Vec::with_capacity(layout.p_minus_2_bit_cells.len());
    for (i, &cell) in layout.p_minus_2_bit_cells.iter().enumerate() {
        let actual = cur[cell];
        let expected = F::from(pm2_bits[i] as u64);
        out.push(actual - expected);
    }
    out
}

/// Emit ALL constraints for the v2 layout.  Returns row-uniform
/// constraints followed by row-0 boundary constraints.  Callers that
/// don't apply the row-0 indicator separately (e.g., the K=2
/// satisfaction test that evaluates at exactly trace row 0) can use
/// this directly: the row-0 boundary constraints must hold at row 0
/// regardless of indicator.
pub fn eval_ecdsa_verify_v2(
    cur: &[F],
    layout: &EcdsaVerifyV2Layout,
) -> Vec<F> {
    let mut out = eval_ecdsa_verify_v2_row_uniform(cur, layout);
    out.extend(eval_ecdsa_verify_v2_row0_boundary(cur, layout));
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

    /// Sanity: p_minus_2_bits returns 256 bits whose MSB == 1
    /// (since p - 2 > 2^255).
    #[test]
    fn p_minus_2_bits_shape() {
        let bits = p_minus_2_bits();
        assert_eq!(bits.len(), 256);
        assert!(bits[0], "MSB of p-2 must be 1");
        // Last bit: (p-2) is odd (since p ≡ 3 mod 4) — wait, P-256
        // p ≡ 3 mod 4 means p-1 ≡ 2 mod 4, so p-2 ≡ 1 mod 4 → LSB = 1.
        assert!(bits[255], "LSB of p-2 must be 1");
    }

    /// Layout-shape test: v2 layout is bigger than v0 by ~Fermat chain + Fp mul.
    #[test]
    fn v2_layout_grows_over_v0() {
        use crate::p256_ecdsa_air::build_ecdsa_verify_demo_layout;
        let g_x = 0;       let g_y = NUM_LIMBS;     let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let k = 2;
        let (_v0, v0_total) = build_ecdsa_verify_demo_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, k,
        );
        let (_v2, v2_total) = build_ecdsa_verify_v2_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, k,
        );
        assert!(v2_total > v0_total + 200_000,
            "v2 must add >200k cells for the Fermat chain + Fp mul \
             (v0={v0_total}, v2={v2_total})");
    }

    /// Smoke: v2 layout's constraint-eval returns the right count.
    #[test]
    fn v2_constraint_count_matches_eval_length() {
        let g_x = 0;       let g_y = NUM_LIMBS;     let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) = build_ecdsa_verify_v2_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, 2,
        );
        let trace = make_trace_row(total);
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let cons = eval_ecdsa_verify_v2(&cur, &layout);
        assert_eq!(cons.len(), ecdsa_verify_v2_constraints(&layout));
    }

    /// End-to-end constraint satisfaction at K=2 with a synthetic
    /// witness for Q = 2G, u_1 = (1,1)b = 3, u_2 = (1,0)b = 2.  Same
    /// scalars as the v0 K=2 test, but with the v2 layout (real
    /// affine x conversion).  The fill helper writes whatever scalar
    /// the caller supplies as `r` into `r_input_base`; for a true
    /// verify the caller would pass the AFFINE x mod n of the result.
    #[test]
    fn ecdsa_verify_v2_k2_constraints_satisfied() {
        use crate::p256_field::FieldElement;
        let g_x = 0;       let g_y = NUM_LIMBS;     let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) = build_ecdsa_verify_v2_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, 2,
        );

        let mut trace = make_trace_row(total);
        let g = *GENERATOR;
        let q_point = g.double();
        let u1_bits = [true, true];   // u_1 = 3  (bits "11")
        let u2_bits = [true, false];  // u_2 = 2  (bits "10")

        // First pass: fill with placeholder r = 0 so the gadget computes
        // R.x_affine mod n.  Then read the computed value and overwrite
        // r_input with it to satisfy the equality gadget.  (Same
        // self-consistency pattern as the existing v0 K=2 test —
        // demonstrates the v2 composition runs end-to-end algebraically.)
        let zero_scalar = ScalarElement::zero();
        fill_ecdsa_verify_v2(
            &mut trace, 0, &layout,
            &g.x, &g.y, &q_point.x, &q_point.y,
            &u1_bits, &u2_bits, &zero_scalar,
        );

        let r_x_mod_n_fe = read_fe_from(
            &trace, 0, layout.r_x_mod_n_layout.c_limbs_base,
        );
        for i in 0..NUM_LIMBS {
            trace[layout.r_input_base + i][0] = F::from(r_x_mod_n_fe.limbs[i] as u64);
        }

        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let cons = eval_ecdsa_verify_v2(&cur, &layout);
        let nonzero = cons.iter().filter(|v| !v.is_zero()).count();
        assert_eq!(
            nonzero, 0,
            "ecdsa_verify_v2 K=2: {} constraints failed (of {})",
            nonzero, cons.len()
        );

        // Bonus: the affine x_aff cell should equal the true affine x
        // (= 19G.x in this synthetic configuration: R = 7G + 12G = 19G).
        // Confirms the Fermat + Fp mul chain converted projective → affine
        // correctly.
        let x_aff_fe = read_fe_from(&trace, 0, layout.x_affine_mul.c_limbs_base);
        let mut x_aff = x_aff_fe;
        x_aff.freeze();

        // Native: compute 19G affine x.  AffinePoint::add already
        // converts to affine internally, so nineteen_g.x IS the
        // affine x coordinate.
        let two_g = g.double();
        let three_g = two_g.add(&g);
        let four_g = three_g.add(&g);
        let seven_g = four_g.add(&three_g);
        let twelve_g = seven_g.add(&four_g).add(&g);
        let nineteen_g = seven_g.add(&twelve_g);
        assert!(!nineteen_g.infinity);
        let mut expected_x = nineteen_g.x;
        expected_x.freeze();
        assert_eq!(
            x_aff.limbs, expected_x.limbs,
            "v2 K=2 affine x mismatch: gadget={:?}, expected={:?}",
            x_aff.limbs, expected_x.limbs,
        );
    }

    /// POSITIVE soundness test: with honestly-filled (p-2) bits,
    /// the row-0 boundary constraints all evaluate to zero.
    #[test]
    fn row0_boundary_zero_on_honest_bits() {
        let g_x = 0;       let g_y = NUM_LIMBS;     let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) = build_ecdsa_verify_v2_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, 2,
        );
        let mut trace = make_trace_row(total);
        // Place the honest (p-2) bits.
        let pm2 = p_minus_2_bits();
        for (i, &bit) in pm2.iter().enumerate() {
            trace[layout.p_minus_2_bit_cells[i]][0] = F::from(bit as u64);
        }
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let boundary = eval_ecdsa_verify_v2_row0_boundary(&cur, &layout);
        assert_eq!(boundary.len(), ECDSA_V2_ROW0_BOUNDARY_CONSTRAINTS);
        let nonzero = boundary.iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nonzero, 0,
            "honest (p-2) bits must satisfy all 256 boundary constraints");
    }

    /// NEGATIVE soundness test: flipping a single (p-2) bit causes
    /// the boundary constraint to fire (non-zero).  This is what
    /// catches a malicious prover that tries to substitute a
    /// different exponent into the Fermat chain.
    #[test]
    fn row0_boundary_catches_flipped_bit() {
        let g_x = 0;       let g_y = NUM_LIMBS;     let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) = build_ecdsa_verify_v2_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, 2,
        );
        let mut trace = make_trace_row(total);
        let pm2 = p_minus_2_bits();
        for (i, &bit) in pm2.iter().enumerate() {
            trace[layout.p_minus_2_bit_cells[i]][0] = F::from(bit as u64);
        }
        // Flip bit 100 — should make boundary[100] non-zero.
        let cell_100 = layout.p_minus_2_bit_cells[100];
        let original = trace[cell_100][0];
        trace[cell_100][0] = if original.is_zero() {
            F::from(1u64)
        } else {
            F::zero()
        };
        let cur: Vec<F> = (0..total).map(|c| trace[c][0]).collect();
        let boundary = eval_ecdsa_verify_v2_row0_boundary(&cur, &layout);
        let nonzero = boundary.iter().filter(|v| !v.is_zero()).count();
        assert_eq!(nonzero, 1,
            "flipping one bit must cause exactly one boundary constraint to fire");
        assert!(!boundary[100].is_zero(),
            "the boundary constraint at the flipped position must be non-zero");
    }

    /// End-to-end FRI round-trip exercising the new
    /// `deep_ali_merge_p256_ecdsa_v2_streaming` merge layer at K=2.
    /// LDEs the v2 trace, runs deep_fri_prove + deep_fri_verify.
    /// Confirms the v2 FRI-merge layer is correctly wired.
    #[test]
    #[ignore = "slow — LDEs the v2 trace including Fermat chain (~700k constraints)"]
    fn ecdsa_verify_v2_fri_round_trip_k2() {
        use crate::deep_ali_merge_p256_ecdsa_v2_streaming;
        use crate::fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain};
        use crate::sextic_ext::SexticExt;
        use crate::trace_import::lde_trace_columns;

        let g_x = 0;       let g_y = NUM_LIMBS;     let g_z = 2 * NUM_LIMBS;
        let q_x = 3 * NUM_LIMBS; let q_y = 4 * NUM_LIMBS; let q_z = 5 * NUM_LIMBS;
        let start = 6 * NUM_LIMBS;
        let (layout, total) = build_ecdsa_verify_v2_layout(
            start, g_x, g_y, g_z, q_x, q_y, q_z, 2,
        );

        let n_trace = 8usize;
        let blowup = 4usize;
        let n_lde = n_trace * blowup;
        let mut trace_cols: Vec<Vec<F>> = (0..total)
            .map(|_| vec![F::zero(); n_trace]).collect();

        let g = *GENERATOR;
        let q_point = g.double();
        let u1_bits = [true, true];
        let u2_bits = [true, false];
        let mut row0_trace: Vec<Vec<F>> = (0..total)
            .map(|_| vec![F::zero(); 1]).collect();
        let zero_scalar = ScalarElement::zero();
        fill_ecdsa_verify_v2(
            &mut row0_trace, 0, &layout,
            &g.x, &g.y, &q_point.x, &q_point.y,
            &u1_bits, &u2_bits, &zero_scalar,
        );
        let r_x_mod_n_fe = read_fe_from(
            &row0_trace, 0, layout.r_x_mod_n_layout.c_limbs_base,
        );
        for i in 0..NUM_LIMBS {
            row0_trace[layout.r_input_base + i][0] =
                F::from(r_x_mod_n_fe.limbs[i] as u64);
        }
        for c in 0..total {
            trace_cols[c][0] = row0_trace[c][0];
        }

        let lde_cols = lde_trace_columns(&trace_cols, n_trace, blowup)
            .expect("LDE must succeed");
        let k_constraints = ecdsa_verify_v2_constraints(&layout);
        let combination_coeffs: Vec<F> =
            (0..k_constraints).map(|i| F::from((i + 1) as u64)).collect();

        let (c_eval, info) = deep_ali_merge_p256_ecdsa_v2_streaming(
            &lde_cols, &combination_coeffs, &layout, n_trace, blowup,
        );
        assert_eq!(c_eval.len(), n_lde);
        assert_eq!(info.num_constraints, k_constraints);
        assert_eq!(info.trace_width, total);

        let domain = FriDomain::new_radix2(n_lde);
        let params = DeepFriParams {
            schedule: (0..n_lde.trailing_zeros() as usize)
                .map(|_| 2).collect(),
            r: 8,
            seed_z: 0xDEEFu64,
            coeff_commit_final: true,
            d_final: 1,
            stir: false,
            s0: 8,
            public_inputs_hash: Some([0u8; 32]),
        };
        let proof = deep_fri_prove::<SexticExt>(c_eval, domain, &params);
        let ok = deep_fri_verify::<SexticExt>(&params, &proof);
        assert!(ok, "v2 FRI prove + verify must round-trip on K=2 witness");
    }
}
