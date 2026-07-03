// p256_ecdsa_verify_multirow_air.rs — END-TO-END witness-binding
// multi-row P256 ECDSA *verification* AIR.
//
// Extends the narrow multi-row double-scalar-mult kernel
// (`p256_ecdsa_double_multirow_air`) with a small TAIL that finishes a
// full ECDSA-P256 verify in-circuit:
//
//   rows 0..K-1   : the two scalar-mult chains (one step/row)
//                   A = u1·G, B = u2·Q, with the projective outputs
//                   bound to the `r_a_proj` / `r_b_proj` columns at the
//                   last chain row (K-1).
//   row  K        : the TAIL —
//                     1. R = R_a + R_b              (group_add gadget)
//                     2. r_plus_n = r + n  (mod p)  (add + freeze)
//                     3. r·R.Z and (r+n)·R.Z        (two mul gadgets)
//                     4. selected = sel ? (r+n)·R.Z : r·R.Z   (select)
//                     5. R.X == selected            (10-limb equality)
//                     6. n column == n constant     (10-limb bind)
//   rows K+1..    : padding (all constraints zeroed).
//
// The cross-multiply (step 4/5) is the inverse-free affine-x check:
// the affine x-coordinate x1 = R.X · R.Z^{-1} ∈ [0,p) satisfies
// `x1 mod n == r`  iff  `x1 ∈ {r, r+n}`  iff
// `R.X ≡ r·R.Z (mod p)`  OR  `R.X ≡ (r+n)·R.Z (mod p)`.
// A boolean selector `sel` (inside the select gadget) picks the branch.
// This avoids the ~677k-cell Fermat inverse that would OOM.
//
// SOUNDNESS CHAIN: the scalar-mult chains bind R_a, R_b to the witness
// (u1/u2 bits, G, Q) via the kernel's transition constraints; the
// r_proj columns are constant (column-constancy) so the value bound to
// the chain output at row K-1 is exactly what the tail's group_add
// consumes at row K; r_plus_n is bound to r+n; and the final equality
// ties the projective R.X to the signature's r.  Tampering r (or any
// witness cell) makes some gadget constraint fire → FRI rejects.

#![allow(non_snake_case, non_upper_case_globals, dead_code)]

use ark_ff::{PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::p256_ecdsa_double_multirow_air::{
    build_ecdsa_double_multirow_layout, ecdsa_double_multirow_local_constraints,
    fill_ecdsa_double_multirow, EcdsaDoubleMultirowLayout,
};
use crate::p256_field::{FieldElement, NUM_LIMBS};
use crate::p256_field_air::{
    eval_add_gadget, eval_freeze_gadget, eval_mul_gadget, eval_select_gadget,
    fill_add_gadget, fill_freeze_gadget, fill_mul_gadget, fill_select_gadget,
    AddGadgetLayout, FreezeGadgetLayout, MulGadgetLayout, SelectGadgetLayout,
    ADD_GADGET_CONSTRAINTS, ELEMENT_BIT_CELLS, FREEZE_GADGET_CONSTRAINTS,
    MUL_GADGET_CONSTRAINTS, SELECT_GADGET_CONSTRAINTS,
};
use crate::p256_group_air::{
    alloc_add_layout, alloc_freeze_layout, alloc_mul_layout, build_group_add_layout,
    eval_group_add_gadget, fill_group_add_gadget, group_add_gadget_constraints,
    GroupAddGadgetLayout,
};
use crate::p256_scalar::N_LIMBS_TIGHT;
use crate::p256_scalar_mul_air::fill_scalar_mul_step_gadget;

// ── per-row constraint-slot counts of the kernel sub-blocks ──
const DSM_BOUNDARY: usize = 6 * NUM_LIMBS; // r_proj boundary at row K-1
const DSM_ACC_TRANSITION: usize = 2 * 3 * NUM_LIMBS; // acc[r+1]=select[r]
const DSM_RPROJ_CONSTANCY: usize = 6 * NUM_LIMBS; // r_proj column-constancy

// ── PUBLIC-INPUT BINDING (pin trace public cells to public values) ──
const PUB_BIT_PINS: usize = 2; // u1-bit, u2-bit (per chain row)
const PUB_BASE_PINS: usize = 4 * NUM_LIMBS; // Gx, Gy, Qx, Qy (per chain row)
const PUB_R_PIN: usize = NUM_LIMBS; // signature r at the tail row
/// Total public-input boundary slots emitted every row.
pub const PUBLIC_INPUT_PINS: usize = PUB_BIT_PINS + PUB_BASE_PINS + PUB_R_PIN;

/// The ACTUAL public signature data the verifier knows independently of
/// the prover.  Pinned into the trace's public cells via boundary
/// constraints (and hashed into `pi_hash` at the bench level), so the
/// proof binds to *this specific* (signature, key, message), not merely
/// an internally-consistent witness.
///
/// Field-element limbs are stored exactly as the fill places them
/// (`F::from(limb as u64)` over the tight limbs), so the pins are
/// bit-exact equalities.
#[derive(Clone, Debug)]
pub struct EcdsaVerifyPublicInputs {
    /// u1 = e·s⁻¹ mod n, MSB-first, as field 0/1 (length K).
    pub u1_bits: Vec<F>,
    /// u2 = r·s⁻¹ mod n, MSB-first, as field 0/1 (length K).
    pub u2_bits: Vec<F>,
    pub gx: [F; NUM_LIMBS],
    pub gy: [F; NUM_LIMBS],
    pub qx: [F; NUM_LIMBS],
    pub qy: [F; NUM_LIMBS],
    /// Signature r as a mod-p field element (limbs).
    pub r: [F; NUM_LIMBS],
}

impl EcdsaVerifyPublicInputs {
    pub fn new(
        u1_bits: &[bool],
        u2_bits: &[bool],
        gx: &FieldElement,
        gy: &FieldElement,
        qx: &FieldElement,
        qy: &FieldElement,
        r: &FieldElement,
    ) -> Self {
        let limbs = |fe: &FieldElement| {
            let mut a = [F::zero(); NUM_LIMBS];
            for i in 0..NUM_LIMBS {
                a[i] = F::from(fe.limbs[i] as u64);
            }
            a
        };
        Self {
            u1_bits: u1_bits.iter().map(|&b| F::from(b as u64)).collect(),
            u2_bits: u2_bits.iter().map(|&b| F::from(b as u64)).collect(),
            gx: limbs(gx),
            gy: limbs(gy),
            qx: limbs(qx),
            qy: limbs(qy),
            r: limbs(r),
        }
    }
}

/// END-TO-END multi-row ECDSA-verify layout.
#[derive(Clone, Debug)]
pub struct EcdsaVerifyMultirowLayout {
    /// The reused double-scalar-mult kernel (chains A,B + r_proj cols).
    pub dsm: EcdsaDoubleMultirowLayout,
    /// R = R_a + R_b over the (constant) r_a_proj / r_b_proj columns.
    pub group_add: GroupAddGadgetLayout,
    /// Public column: signature `r` (as a mod-p field element, 10 limbs).
    pub r_base: usize,
    /// Public column: curve order `n` (10 limbs, bound to the constant).
    pub n_const_base: usize,
    /// r + n (integer, < 2p).
    pub add_rn: AddGadgetLayout,
    /// canonical (r + n) mod p.
    pub freeze_rn: FreezeGadgetLayout,
    /// r · R.Z (mod p).
    pub mul_r: MulGadgetLayout,
    /// (r+n) · R.Z (mod p).
    pub mul_rn: MulGadgetLayout,
    /// selected = sel ? mul_rn : mul_r.
    pub select: SelectGadgetLayout,
    /// Number of scalar-mult steps (= number of MSB bits, e.g. 256).
    pub k_steps: usize,
    pub width: usize,
}

pub fn build_ecdsa_verify_multirow_layout(
    start: usize,
    k_steps: usize,
) -> (EcdsaVerifyMultirowLayout, usize) {
    let (dsm, dsm_end) = build_ecdsa_double_multirow_layout(start);
    let mut cursor = dsm_end;

    // R = R_a + R_b over the constant r_proj columns.
    let (group_add, ga_end) = build_group_add_layout(
        cursor,
        dsm.r_a_proj_x_base,
        dsm.r_a_proj_y_base,
        dsm.r_a_proj_z_base,
        dsm.r_b_proj_x_base,
        dsm.r_b_proj_y_base,
        dsm.r_b_proj_z_base,
    );
    cursor = ga_end;

    // Public columns: r and n (limbs only — gadget inputs need no bits).
    let r_base = cursor;
    cursor += NUM_LIMBS;
    let n_const_base = cursor;
    cursor += NUM_LIMBS;

    // r_plus_n = freeze(r + n).
    let add_rn = alloc_add_layout(&mut cursor, r_base, n_const_base);
    let freeze_rn = alloc_freeze_layout(&mut cursor, add_rn.c_limbs_base);
    let r_plus_n_base = freeze_rn.c_limbs_base;

    // Cross-multiply muls against R.Z.
    let z3 = group_add.result_z3_limbs_base;
    let mul_r = alloc_mul_layout(&mut cursor, r_base, z3);
    let mul_rn = alloc_mul_layout(&mut cursor, r_plus_n_base, z3);

    // select: sel ? mul_rn : mul_r.
    let sel_cell = cursor;
    cursor += 1;
    let sel_c_limbs = cursor;
    cursor += NUM_LIMBS;
    let sel_c_bits = cursor;
    cursor += ELEMENT_BIT_CELLS;
    let select = SelectGadgetLayout {
        a_limbs_base: mul_rn.c_limbs_base,
        b_limbs_base: mul_r.c_limbs_base,
        c_limbs_base: sel_c_limbs,
        c_bits_base: sel_c_bits,
        sel_cell,
    };

    let layout = EcdsaVerifyMultirowLayout {
        dsm,
        group_add,
        r_base,
        n_const_base,
        add_rn,
        freeze_rn,
        mul_r,
        mul_rn,
        select,
        k_steps,
        width: cursor,
    };
    (layout, cursor)
}

/// Number of tail (row-K) constraint slots.
pub fn ecdsa_verify_tail_constraints(layout: &EcdsaVerifyMultirowLayout) -> usize {
    group_add_gadget_constraints(&layout.group_add)
        + ADD_GADGET_CONSTRAINTS
        + FREEZE_GADGET_CONSTRAINTS
        + 2 * MUL_GADGET_CONSTRAINTS
        + SELECT_GADGET_CONSTRAINTS
        + NUM_LIMBS // R.X == selected
        + NUM_LIMBS // n column == n constant
}

pub fn ecdsa_verify_multirow_constraints(layout: &EcdsaVerifyMultirowLayout) -> usize {
    ecdsa_double_multirow_local_constraints(&layout.dsm)
        + DSM_BOUNDARY
        + DSM_ACC_TRANSITION
        + DSM_RPROJ_CONSTANCY
        + ecdsa_verify_tail_constraints(layout)
        + PUBLIC_INPUT_PINS
}

#[inline]
fn read_fe_row(trace: &[Vec<F>], base: usize, row: usize) -> FieldElement {
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        let bi = trace[base + i][row].into_bigint();
        limbs[i] = bi.as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

#[inline]
fn place_limbs(trace: &mut [Vec<F>], base: usize, row: usize, fe: &FieldElement) {
    for i in 0..NUM_LIMBS {
        trace[base + i][row] = F::from(fe.limbs[i] as u64);
    }
}

/// `n` (curve order) as a tight-form mod-p FieldElement.
pub fn order_n_field() -> FieldElement {
    FieldElement { limbs: *N_LIMBS_TIGHT }
}

/// Fill the full verify trace.
///
/// `n_trace >= k_steps + 1` (power of two).  The kernel runs `k_steps`
/// scalar-mult steps on rows `0..k_steps`; the tail is filled at row
/// `k_steps`.  Two-pass: the caller first fills with placeholder r_proj
/// to capture the chain outputs at row `k_steps-1`, then refills with
/// the captured projective outputs.  This function performs BOTH passes
/// internally and additionally fills the tail.
///
/// `r_scalar_fe` is the signature `r` reduced into a mod-p FieldElement.
#[allow(clippy::too_many_arguments)]
pub fn fill_ecdsa_verify_multirow(
    trace: &mut [Vec<F>],
    layout: &EcdsaVerifyMultirowLayout,
    n_trace: usize,
    a_initial: (&FieldElement, &FieldElement, &FieldElement),
    a_base: (&FieldElement, &FieldElement, &FieldElement),
    a_bits: &[bool],
    b_initial: (&FieldElement, &FieldElement, &FieldElement),
    b_base: (&FieldElement, &FieldElement, &FieldElement),
    b_bits: &[bool],
    r_scalar_fe: &FieldElement,
) {
    let k = layout.k_steps;
    assert!(n_trace.is_power_of_two());
    assert!(n_trace >= k + 1, "need a tail row at index k_steps");
    assert_eq!(a_bits.len(), k);
    assert_eq!(b_bits.len(), k);

    let zfe = FieldElement::zero();

    // ── Pass 1: r_proj = 0 to capture chain outputs at row k-1. ──
    fill_ecdsa_double_multirow(
        trace, &layout.dsm, n_trace, k, k,
        a_initial.0, a_initial.1, a_initial.2,
        a_base.0, a_base.1, a_base.2, a_bits,
        b_initial.0, b_initial.1, b_initial.2,
        b_base.0, b_base.1, b_base.2, b_bits,
        &zfe, &zfe, &zfe, &zfe, &zfe, &zfe,
    );

    let last = k - 1;
    let r_a_x = read_fe_row(trace, layout.dsm.step_a.select_x.c_limbs_base, last);
    let r_a_y = read_fe_row(trace, layout.dsm.step_a.select_y.c_limbs_base, last);
    let r_a_z = read_fe_row(trace, layout.dsm.step_a.select_z.c_limbs_base, last);
    let r_b_x = read_fe_row(trace, layout.dsm.step_b.select_x.c_limbs_base, last);
    let r_b_y = read_fe_row(trace, layout.dsm.step_b.select_y.c_limbs_base, last);
    let r_b_z = read_fe_row(trace, layout.dsm.step_b.select_z.c_limbs_base, last);

    // ── Pass 2: refill kernel with the captured r_proj values. ──
    fill_ecdsa_double_multirow(
        trace, &layout.dsm, n_trace, k, k,
        a_initial.0, a_initial.1, a_initial.2,
        a_base.0, a_base.1, a_base.2, a_bits,
        b_initial.0, b_initial.1, b_initial.2,
        b_base.0, b_base.1, b_base.2, b_bits,
        &r_a_x, &r_a_y, &r_a_z, &r_b_x, &r_b_y, &r_b_z,
    );

    // ── Tail at row k. ──
    let row = k;
    let n_fe = order_n_field();

    // R = R_a + R_b.
    fill_group_add_gadget(
        trace, row, &layout.group_add,
        &r_a_x, &r_a_y, &r_a_z, &r_b_x, &r_b_y, &r_b_z,
    );
    let r_x3 = read_fe_row(trace, layout.group_add.result_x3_limbs_base, row);
    let r_z3 = read_fe_row(trace, layout.group_add.result_z3_limbs_base, row);

    // Affine x1 = R.X · R.Z^{-1}; choose sel.
    let mut x1 = r_x3.mul(&r_z3.invert());
    x1.freeze();
    let mut r_can = *r_scalar_fe;
    r_can.freeze();
    let mut rn_native = r_scalar_fe.add(&n_fe);
    rn_native.freeze();
    let sel = if x1.ct_eq(&rn_native) {
        true
    } else {
        debug_assert!(x1.ct_eq(&r_can), "honest fill: x1 not in {{r, r+n}}");
        false
    };

    // r, n public columns.
    place_limbs(trace, layout.r_base, row, r_scalar_fe);
    place_limbs(trace, layout.n_const_base, row, &n_fe);

    // r_plus_n = freeze(r + n).
    fill_add_gadget(trace, row, &layout.add_rn, r_scalar_fe, &n_fe);
    let rn_raw = read_fe_row(trace, layout.add_rn.c_limbs_base, row);
    fill_freeze_gadget(trace, row, &layout.freeze_rn, &rn_raw);
    let r_plus_n = read_fe_row(trace, layout.freeze_rn.c_limbs_base, row);

    // Cross-multiply.
    fill_mul_gadget(trace, row, &layout.mul_r, r_scalar_fe, &r_z3);
    fill_mul_gadget(trace, row, &layout.mul_rn, &r_plus_n, &r_z3);
    let mul_r_c = read_fe_row(trace, layout.mul_r.c_limbs_base, row);
    let mul_rn_c = read_fe_row(trace, layout.mul_rn.c_limbs_base, row);

    // select: sel ? mul_rn : mul_r.
    fill_select_gadget(trace, row, &layout.select, &mul_rn_c, &mul_r_c, sel);
}

/// ROUTED "direct-fill" analogue of `fill_ecdsa_verify_multirow` that
/// stores ONLY the columns in `strand_cols` (sorted global indices) into
/// `strand_trace` (len == `strand_cols.len()`, each column length
/// `n_trace`), WITHOUT ever allocating the full ~196k-column trace.
///
/// ## How it stays byte-identical to `build_full` + `extract`
///
/// Every P256 field/group/step gadget filler writes cells only within the
/// single `row` it is handed (the multi-row / cross-row dataflow lives
/// entirely in the OUTER loops of `fill_ecdsa_double_multirow` /
/// `fill_ecdsa_verify_multirow`, which pass native `FieldElement`s around).
/// So this routine keeps a single-row FULL-WIDTH scratch buffer (~1.5 MB
/// of `F` + Vec overhead ≈ a few MB), reproduces the outer control flow
/// EXACTLY — same fill calls, same native-value dataflow (accumulator
/// carry via reading the step's `select` outputs; the tail's group-add /
/// r+n / cross-multiply / select) — and after each trace row copies out
/// just the strand's held columns.
///
/// Because the scratch is zero-initialised, exactly matching the full
/// trace's `vec![vec![F::zero(); n_trace]; width]` background, every cell
/// never written by an active gadget stores 0 in both — so
/// `strand_trace[local][row] == full[strand_cols[local]][row]` for every
/// cell.  This equality is enforced by the `gway_strand_fill_byte_equals_full`
/// guard test for G ∈ {4, 8, 16}.
///
/// This reuses the existing gadget fillers VERBATIM (no return-value or
/// value-logic changes anywhere), so behaviour for RSA / Ed25519 / ML-DSA
/// — which never call this function — is untouched.
#[allow(clippy::too_many_arguments)]
pub fn fill_ecdsa_verify_multirow_strand(
    strand_cols: &[usize],
    strand_trace: &mut [Vec<F>],
    layout: &EcdsaVerifyMultirowLayout,
    n_trace: usize,
    a_initial: (&FieldElement, &FieldElement, &FieldElement),
    a_base: (&FieldElement, &FieldElement, &FieldElement),
    a_bits: &[bool],
    b_initial: (&FieldElement, &FieldElement, &FieldElement),
    b_base: (&FieldElement, &FieldElement, &FieldElement),
    b_bits: &[bool],
    r_scalar_fe: &FieldElement,
) {
    let k = layout.k_steps;
    assert!(n_trace.is_power_of_two());
    assert!(n_trace >= k + 1, "need a tail row at index k_steps");
    assert_eq!(a_bits.len(), k);
    assert_eq!(b_bits.len(), k);
    assert_eq!(
        strand_trace.len(),
        strand_cols.len(),
        "strand_trace must have one column per strand column"
    );
    debug_assert!(
        strand_trace.iter().all(|col| col.len() == n_trace),
        "each strand column must have length n_trace"
    );

    let width = layout.width;
    let dsm = &layout.dsm;

    // Single-row full-width scratch.  Zero background == full trace init.
    let mut scratch: Vec<Vec<F>> = vec![vec![F::zero(); 1]; width];

    type Proj = (FieldElement, FieldElement, FieldElement);

    // Fill one trace row's two scalar-mult step gadgets into scratch@0,
    // mirroring the per-row body of `fill_ecdsa_double_multirow`.  Returns
    // the native next accumulators (read back from the `select` outputs).
    let fill_chain_row = |scratch: &mut [Vec<F>], r: usize, a_acc: &Proj, b_acc: &Proj| -> (Proj, Proj) {
        // ── chain A ──
        place_limbs(scratch, dsm.step_a.base_x_base, 0, a_base.0);
        place_limbs(scratch, dsm.step_a.base_y_base, 0, a_base.1);
        place_limbs(scratch, dsm.step_a.base_z_base, 0, a_base.2);
        place_limbs(scratch, dsm.step_a.acc_x_base, 0, &a_acc.0);
        place_limbs(scratch, dsm.step_a.acc_y_base, 0, &a_acc.1);
        place_limbs(scratch, dsm.step_a.acc_z_base, 0, &a_acc.2);
        let a_bit = if r < k { a_bits[r] } else { false };
        scratch[dsm.step_a.bit_cell][0] = F::from(a_bit as u64);
        fill_scalar_mul_step_gadget(
            scratch, 0, &dsm.step_a, &a_acc.0, &a_acc.1, &a_acc.2, a_base.0, a_base.1, a_base.2, a_bit,
        );
        let na = (
            read_fe_row(scratch, dsm.step_a.select_x.c_limbs_base, 0),
            read_fe_row(scratch, dsm.step_a.select_y.c_limbs_base, 0),
            read_fe_row(scratch, dsm.step_a.select_z.c_limbs_base, 0),
        );
        // ── chain B ──
        place_limbs(scratch, dsm.step_b.base_x_base, 0, b_base.0);
        place_limbs(scratch, dsm.step_b.base_y_base, 0, b_base.1);
        place_limbs(scratch, dsm.step_b.base_z_base, 0, b_base.2);
        place_limbs(scratch, dsm.step_b.acc_x_base, 0, &b_acc.0);
        place_limbs(scratch, dsm.step_b.acc_y_base, 0, &b_acc.1);
        place_limbs(scratch, dsm.step_b.acc_z_base, 0, &b_acc.2);
        let b_bit = if r < k { b_bits[r] } else { false };
        scratch[dsm.step_b.bit_cell][0] = F::from(b_bit as u64);
        fill_scalar_mul_step_gadget(
            scratch, 0, &dsm.step_b, &b_acc.0, &b_acc.1, &b_acc.2, b_base.0, b_base.1, b_base.2, b_bit,
        );
        let nb = (
            read_fe_row(scratch, dsm.step_b.select_x.c_limbs_base, 0),
            read_fe_row(scratch, dsm.step_b.select_y.c_limbs_base, 0),
            read_fe_row(scratch, dsm.step_b.select_z.c_limbs_base, 0),
        );
        (na, nb)
    };

    // ── Pass 1: run the chains to capture R_a, R_b at row k-1 (the same
    //    values the two-pass `fill_ecdsa_verify_multirow` captures). ──
    let mut a_acc: Proj = (*a_initial.0, *a_initial.1, *a_initial.2);
    let mut b_acc: Proj = (*b_initial.0, *b_initial.1, *b_initial.2);
    let mut r_a: Proj = (FieldElement::zero(), FieldElement::zero(), FieldElement::zero());
    let mut r_b: Proj = r_a;
    for r in 0..k {
        let (na, nb) = fill_chain_row(&mut scratch, r, &a_acc, &b_acc);
        if r == k - 1 {
            r_a = na;
            r_b = nb;
        }
        a_acc = na;
        b_acc = nb;
    }

    // Reset scratch to the zero background before the storing pass.
    for col in scratch.iter_mut() {
        col[0] = F::zero();
    }

    // ── Pass 2: refill every row with captured r_proj, fill the tail at
    //    row k, and copy the strand's columns out row by row. ──
    let n_fe = order_n_field();
    let mut a_acc: Proj = (*a_initial.0, *a_initial.1, *a_initial.2);
    let mut b_acc: Proj = (*b_initial.0, *b_initial.1, *b_initial.2);
    for r in 0..n_trace {
        let (na, nb) = fill_chain_row(&mut scratch, r, &a_acc, &b_acc);

        // r_proj columns: replicated captured values (constant per row).
        place_limbs(&mut scratch, dsm.r_a_proj_x_base, 0, &r_a.0);
        place_limbs(&mut scratch, dsm.r_a_proj_y_base, 0, &r_a.1);
        place_limbs(&mut scratch, dsm.r_a_proj_z_base, 0, &r_a.2);
        place_limbs(&mut scratch, dsm.r_b_proj_x_base, 0, &r_b.0);
        place_limbs(&mut scratch, dsm.r_b_proj_y_base, 0, &r_b.1);
        place_limbs(&mut scratch, dsm.r_b_proj_z_base, 0, &r_b.2);

        if r == k {
            // ── tail (byte-for-byte the same as fill_ecdsa_verify_multirow) ──
            fill_group_add_gadget(
                &mut scratch, 0, &layout.group_add, &r_a.0, &r_a.1, &r_a.2, &r_b.0, &r_b.1, &r_b.2,
            );
            let r_x3 = read_fe_row(&scratch, layout.group_add.result_x3_limbs_base, 0);
            let r_z3 = read_fe_row(&scratch, layout.group_add.result_z3_limbs_base, 0);

            let mut x1 = r_x3.mul(&r_z3.invert());
            x1.freeze();
            let mut r_can = *r_scalar_fe;
            r_can.freeze();
            let mut rn_native = r_scalar_fe.add(&n_fe);
            rn_native.freeze();
            let sel = if x1.ct_eq(&rn_native) {
                true
            } else {
                debug_assert!(x1.ct_eq(&r_can), "honest strand fill: x1 not in {{r, r+n}}");
                false
            };

            place_limbs(&mut scratch, layout.r_base, 0, r_scalar_fe);
            place_limbs(&mut scratch, layout.n_const_base, 0, &n_fe);

            fill_add_gadget(&mut scratch, 0, &layout.add_rn, r_scalar_fe, &n_fe);
            let rn_raw = read_fe_row(&scratch, layout.add_rn.c_limbs_base, 0);
            fill_freeze_gadget(&mut scratch, 0, &layout.freeze_rn, &rn_raw);
            let r_plus_n = read_fe_row(&scratch, layout.freeze_rn.c_limbs_base, 0);

            fill_mul_gadget(&mut scratch, 0, &layout.mul_r, r_scalar_fe, &r_z3);
            fill_mul_gadget(&mut scratch, 0, &layout.mul_rn, &r_plus_n, &r_z3);
            let mul_r_c = read_fe_row(&scratch, layout.mul_r.c_limbs_base, 0);
            let mul_rn_c = read_fe_row(&scratch, layout.mul_rn.c_limbs_base, 0);

            fill_select_gadget(&mut scratch, 0, &layout.select, &mul_rn_c, &mul_r_c, sel);
        }

        // Copy this row's strand-held columns out of scratch.
        for (local, &c) in strand_cols.iter().enumerate() {
            strand_trace[local][r] = scratch[c][0];
        }

        if r == k {
            // Clear the tail region so padding rows (r > k) store zeros,
            // exactly as the full trace leaves them.
            for c in dsm.width..width {
                scratch[c][0] = F::zero();
            }
        }

        a_acc = na;
        b_acc = nb;
    }
}

/// Per-row evaluator (transition-aware).  Order MUST match
/// `ecdsa_verify_multirow_constraints`.
pub fn eval_ecdsa_verify_multirow_per_row(
    cur: &[F],
    nxt: &[F],
    trace_row: usize,
    _n_trace: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
) -> Vec<F> {
    use crate::p256_scalar_mul_air::eval_scalar_mul_step_gadget;

    let k = layout.k_steps;
    let total = ecdsa_verify_multirow_constraints(layout);
    let mut out = Vec::with_capacity(total);

    let in_chain = trace_row < k; // rows 0..k-1 run the scalar mult
    let is_chain_last = trace_row + 1 == k; // row k-1: bind r_proj
    let is_tail = trace_row == k; // row k: the verify tail

    // (1) DSM local: both step gadgets, gated to chain rows.
    let dsm_local = ecdsa_double_multirow_local_constraints(&layout.dsm);
    if in_chain {
        out.extend(eval_scalar_mul_step_gadget(cur, &layout.dsm.step_a));
        out.extend(eval_scalar_mul_step_gadget(cur, &layout.dsm.step_b));
        debug_assert_eq!(out.len(), dsm_local);
    } else {
        out.resize(dsm_local, F::zero());
    }

    // (2) DSM boundary: bind chain outputs to r_proj cols at row k-1.
    let push_boundary = |out: &mut Vec<F>, chain_base: usize, proj_base: usize| {
        for i in 0..NUM_LIMBS {
            if is_chain_last {
                out.push(cur[chain_base + i] - cur[proj_base + i]);
            } else {
                out.push(F::zero());
            }
        }
    };
    push_boundary(&mut out, layout.dsm.step_a.select_x.c_limbs_base, layout.dsm.r_a_proj_x_base);
    push_boundary(&mut out, layout.dsm.step_a.select_y.c_limbs_base, layout.dsm.r_a_proj_y_base);
    push_boundary(&mut out, layout.dsm.step_a.select_z.c_limbs_base, layout.dsm.r_a_proj_z_base);
    push_boundary(&mut out, layout.dsm.step_b.select_x.c_limbs_base, layout.dsm.r_b_proj_x_base);
    push_boundary(&mut out, layout.dsm.step_b.select_y.c_limbs_base, layout.dsm.r_b_proj_y_base);
    push_boundary(&mut out, layout.dsm.step_b.select_z.c_limbs_base, layout.dsm.r_b_proj_z_base);

    // (3) DSM acc transition: acc[r+1] = select[r], for r in 0..k-2.
    let acc_link = trace_row + 1 < k;
    if acc_link {
        for (acc, sel) in [
            (layout.dsm.step_a.acc_x_base, layout.dsm.step_a.select_x.c_limbs_base),
            (layout.dsm.step_a.acc_y_base, layout.dsm.step_a.select_y.c_limbs_base),
            (layout.dsm.step_a.acc_z_base, layout.dsm.step_a.select_z.c_limbs_base),
            (layout.dsm.step_b.acc_x_base, layout.dsm.step_b.select_x.c_limbs_base),
            (layout.dsm.step_b.acc_y_base, layout.dsm.step_b.select_y.c_limbs_base),
            (layout.dsm.step_b.acc_z_base, layout.dsm.step_b.select_z.c_limbs_base),
        ] {
            for i in 0..NUM_LIMBS {
                out.push(nxt[acc + i] - cur[sel + i]);
            }
        }
    } else {
        let base = out.len();
        out.resize(base + DSM_ACC_TRANSITION, F::zero());
    }

    // (4) DSM r_proj column-constancy, for r in 0..k-1 (links k-1 -> k).
    let rproj_link = trace_row < k;
    if rproj_link {
        for base in &[
            layout.dsm.r_a_proj_x_base, layout.dsm.r_a_proj_y_base, layout.dsm.r_a_proj_z_base,
            layout.dsm.r_b_proj_x_base, layout.dsm.r_b_proj_y_base, layout.dsm.r_b_proj_z_base,
        ] {
            for i in 0..NUM_LIMBS {
                out.push(nxt[*base + i] - cur[*base + i]);
            }
        }
    } else {
        let base = out.len();
        out.resize(base + DSM_RPROJ_CONSTANCY, F::zero());
    }

    // (5) TAIL at row k.
    let tail_count = ecdsa_verify_tail_constraints(layout);
    if is_tail {
        let tail_start = out.len();
        out.extend(eval_group_add_gadget(cur, &layout.group_add));
        out.extend(eval_add_gadget(cur, &layout.add_rn));
        out.extend(eval_freeze_gadget(cur, &layout.freeze_rn));
        out.extend(eval_mul_gadget(cur, &layout.mul_r));
        out.extend(eval_mul_gadget(cur, &layout.mul_rn));
        out.extend(eval_select_gadget(cur, &layout.select));
        // R.X == selected.
        for i in 0..NUM_LIMBS {
            out.push(cur[layout.group_add.result_x3_limbs_base + i] - cur[layout.select.c_limbs_base + i]);
        }
        // n column == n constant.
        let n_fe = order_n_field();
        for i in 0..NUM_LIMBS {
            out.push(cur[layout.n_const_base + i] - F::from(n_fe.limbs[i] as u64));
        }
        debug_assert_eq!(out.len() - tail_start, tail_count);
    } else {
        let base = out.len();
        out.resize(base + tail_count, F::zero());
    }

    // (6) PUBLIC-INPUT BINDING: pin trace public cells to the public
    // values the verifier supplies.  On chain rows: u1/u2 bit cells, the
    // generator-G base columns (chain A) and the public-key-Q base
    // columns (chain B).  On the tail row: the signature-r column.
    let pin_start = out.len();
    // u1-bit, u2-bit pins (per chain row).
    if in_chain {
        out.push(cur[layout.dsm.step_a.bit_cell] - pub_inputs.u1_bits[trace_row]);
        out.push(cur[layout.dsm.step_b.bit_cell] - pub_inputs.u2_bits[trace_row]);
    } else {
        out.push(F::zero());
        out.push(F::zero());
    }
    // Gx, Gy (chain A base) and Qx, Qy (chain B base) pins (per chain row).
    let push_limb_pin = |out: &mut Vec<F>, fire: bool, base: usize, want: &[F; NUM_LIMBS]| {
        for i in 0..NUM_LIMBS {
            if fire {
                out.push(cur[base + i] - want[i]);
            } else {
                out.push(F::zero());
            }
        }
    };
    push_limb_pin(&mut out, in_chain, layout.dsm.step_a.base_x_base, &pub_inputs.gx);
    push_limb_pin(&mut out, in_chain, layout.dsm.step_a.base_y_base, &pub_inputs.gy);
    push_limb_pin(&mut out, in_chain, layout.dsm.step_b.base_x_base, &pub_inputs.qx);
    push_limb_pin(&mut out, in_chain, layout.dsm.step_b.base_y_base, &pub_inputs.qy);
    // Signature-r column pin (tail row).
    push_limb_pin(&mut out, is_tail, layout.r_base, &pub_inputs.r);
    debug_assert_eq!(out.len() - pin_start, PUBLIC_INPUT_PINS);

    debug_assert_eq!(out.len(), total);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_group::GENERATOR;

    fn z_one() -> FieldElement {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    }
    fn identity() -> (FieldElement, FieldElement, FieldElement) {
        // Projective point at infinity (0:1:0).
        let mut y = FieldElement::zero();
        y.limbs[0] = 1;
        (FieldElement::zero(), y, FieldElement::zero())
    }

    // Small smoke test: K=4 scalar mult + tail, native cross-check via
    // a constructed (R, r) that we KNOW lands on the equality.
    #[test]
    fn verify_multirow_k4_tail_consistent() {
        let k = 4usize;
        let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
        let n_trace = (k + 1).next_power_of_two(); // 8

        let g = *GENERATOR;
        let q = g.double();
        let zo = z_one();
        let (ix, iy, iz) = identity();

        // Drive both chains with bits; the resulting R is some real
        // point.  We must set r = R.x mod n for the tail equality.
        let a_bits = vec![true, false, true, true];
        let b_bits = vec![false, true, true, false];

        // Compute the chains natively-ish by filling pass 1 to read R_a,R_b,
        // then group_add, then derive r = affine_x(R) mod ... we just read
        // it back after a trial fill below.
        let mut trace = vec![vec![F::zero(); n_trace]; total];

        // First fill with a placeholder r to obtain R, then recompute r.
        // We do a throwaway pass to read R, choosing r afterwards.
        let placeholder_r = FieldElement::zero();
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g.x, &g.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits,
            &placeholder_r,
        );
        // Read affine x1 of R from the (correct) group_add output at row k.
        let r_x3 = read_fe_row(&trace, layout.group_add.result_x3_limbs_base, k);
        let r_z3 = read_fe_row(&trace, layout.group_add.result_z3_limbs_base, k);
        let mut x1 = r_x3.mul(&r_z3.invert());
        x1.freeze();
        // Use r := x1 (as a mod-p element; sel=0 branch).  This is a
        // self-consistent in-circuit check of the cross-multiply.
        let r_fe = x1;

        // Refill with the real r.
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g.x, &g.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits,
            &r_fe,
        );
        let pubin = EcdsaVerifyPublicInputs::new(&a_bits, &b_bits, &g.x, &g.y, &q.x, &q.y, &r_fe);

        let mut failures = 0usize;
        for r in 0..n_trace {
            let cur: Vec<F> = (0..total).map(|c| trace[c][r]).collect();
            let nxt: Vec<F> = (0..total).map(|c| trace[c][(r + 1) % n_trace]).collect();
            let cons = eval_ecdsa_verify_multirow_per_row(&cur, &nxt, r, n_trace, &layout, &pubin);
            failures += cons.iter().filter(|v| !v.is_zero()).count();
        }
        assert_eq!(failures, 0, "verify-multirow K=4 had {failures} non-zero constraints");
    }

    #[test]
    fn verify_multirow_tampered_r_violates() {
        let k = 4usize;
        let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
        let n_trace = (k + 1).next_power_of_two();
        let g = *GENERATOR;
        let q = g.double();
        let zo = z_one();
        let (ix, iy, iz) = identity();
        let a_bits = vec![true, false, true, true];
        let b_bits = vec![false, true, true, false];

        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g.x, &g.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits,
            &FieldElement::zero(),
        );
        let r_x3 = read_fe_row(&trace, layout.group_add.result_x3_limbs_base, k);
        let r_z3 = read_fe_row(&trace, layout.group_add.result_z3_limbs_base, k);
        let mut x1 = r_x3.mul(&r_z3.invert());
        x1.freeze();

        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g.x, &g.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits,
            &x1,
        );
        let pubin = EcdsaVerifyPublicInputs::new(&a_bits, &b_bits, &g.x, &g.y, &q.x, &q.y, &x1);
        // Tamper the r public column -> mul_r position identity fires.
        trace[layout.r_base][k] += F::from(1u64);

        let mut failures = 0usize;
        for r in 0..n_trace {
            let cur: Vec<F> = (0..total).map(|c| trace[c][r]).collect();
            let nxt: Vec<F> = (0..total).map(|c| trace[c][(r + 1) % n_trace]).collect();
            let cons = eval_ecdsa_verify_multirow_per_row(&cur, &nxt, r, n_trace, &layout, &pubin);
            failures += cons.iter().filter(|v| !v.is_zero()).count();
        }
        assert!(failures >= 1, "tampered r must violate >=1 constraint");
    }
}
