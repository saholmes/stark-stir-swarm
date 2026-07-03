// ed25519_verify_stranded_gway.rs — BALANCED G-WAY low-memory "stranded"
// PROVER for the END-TO-END Ed25519 verify-air **v16** (RFC 8032 §5.1.7
// cofactored verify).
//
// ## What this is (Ed25519 analogue of `ecdsa_verify_stranded_gway`)
//
// The monolithic v16 verify AIR has `width = 41_519` columns / `70_602`
// constraints per row at k_scalar=256; proving it in one shot LDEs the
// whole trace → ~6.2 GB peak RSS at blowup=4.  This module cuts the AIR
// into `G` column-group STRANDS of ≈equal width, each of which LDEs ONLY
// its own columns and is proved independently; the strands are spliced by
// OOD SEAMS on every cross-strand column.  Peak per-strand RSS ≈ 1/G of
// the monolith.
//
// ## Structural difference from the ECDSA AIR (why the cut is different)
//
// The Ed25519 layout is **MAX-width, not SUM-width** (`verify_air_layout_v3`
// takes `width = max(sha, reduce, decompress, scalar_mult_row)`):
//
//   * columns `[0, 14_941)` are a SHARED POOL — SHA-512, scalar-reduce,
//     point-decompress and BOTH scalar-mult ladders are OVERLAID on the
//     same low columns, distinguished only by ROW band (SHA rows
//     `0..k_hash`; reduce `k_hash`; decompress `k_hash+1/2`; ladders
//     `k_hash+3..`).
//   * columns `[14_941, 41_519)` are the TAIL — column-disjoint gadgets
//     (`scalar_block`/`r_thread`, result, cofactor `dbl`, threads,
//     `point_add_R1`, `point_add_R2`, …) each used only at specific rows.
//
// A strand that holds a shared-pool column therefore emits EVERY phase's
// constraints that read it.  We resolve this by cutting COLUMNS into `G`
// contiguous ranges whose first boundary is snapped OUTSIDE the
// SHA/reduce/decompress low read-ranges (so strand 0 absorbs those three
// phases whole, with no seams), and assigning each constraint block to the
// strand owning its "home" column.  The dominant `mult` gadget (14_941
// cols, shared by both ladders) is decomposed into its LEAF field-gadgets
// (`eval_scalar_mult_per_row = point_double ++ cond_add`, each a clean
// concatenation of Mul/Add/Sub/Select leaves), so it splits across strands.
//
// ## Hybrid-slice evaluation (no gadget-math re-transcription)
//
// A strand's per-row constraint evaluator SCATTERS its held columns into a
// full-width zero buffer, calls the VERIFIED monolith evaluator
// `eval_verify_air_v16_per_row`, and keeps ONLY the constraint indices
// assigned to that strand (a set of `[start, start+len)` slices).  Because
// each strand holds every column its assigned constraint blocks read
// (seams pull cross-strand reads in), the kept values are byte-identical
// to the monolith; the discarded values (blocks owned by other strands,
// reading columns that are 0 in this strand's scatter) are unused.  This
// reuses the AIR's exact constraint logic verbatim — no re-implementation.
//
// ## Soundness
//
//   * Each strand is a standard `sub_air_with_trace` proof (trace-LDE
//     Merkle commitment folded into pi_hash, per-query trace openings,
//     per-query `c_eval·Z_H == Σ αⱼ Φⱼ` re-check).  Tampering an interior
//     witness cell makes some Φⱼ non-zero on H → that strand rejects.
//   * Every column held by ≥2 strands is a SEAM, OOD-bound across its
//     holders at a common FS point (`commit_binding_cells` +
//     `verify_ood_consistency`) — including the cross-row TRANSITION seams
//     (thread-constancy v7/v11/v12/v13; residual→dbl binding v16).
//   * CONSTRAINT COMPLETENESS is structural: the block list partitions
//     `[0, verify_v16_per_row_constraints(k))`, each block goes to exactly
//     one strand, so `Σ strand_nc == monolith` (asserted).
//
// This module changes NOTHING in the AIR, its evaluator, its filler, or the
// verifier core — it only orchestrates existing primitives.  There is NO
// routed direct-fill: strands are extracted from a full trace that is built
// then DROPPED before proving (the full trace is only ~340 MB and never
// enters the LDE/prove phase).

#![allow(non_snake_case, clippy::too_many_arguments, clippy::type_complexity)]

use std::collections::BTreeMap;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::ed25519_field::{NUM_LIMBS, LIMB_WIDTHS, FieldElement, D, D2};
use crate::ed25519_field_air::{
    AddGadgetLayout, MulGadgetLayout, SelectGadgetLayout, SubGadgetLayout,
    ADD_GADGET_CONSTRAINTS, ADD_GADGET_OWNED_CELLS, ELEMENT_BIT_CELLS,
    MUL_GADGET_CONSTRAINTS, MUL_GADGET_OWNED_CELLS, SELECT_GADGET_CONSTRAINTS,
    SUB_GADGET_CONSTRAINTS, SUB_GADGET_OWNED_CELLS,
    eval_add_gadget, eval_mul_gadget, eval_sub_gadget, eval_select_gadget,
};
use crate::ed25519_group::{EdwardsPoint, ED25519_BASEPOINT};
use crate::ed25519_group_air::{
    CondAddGadgetLayout, PointAddGadgetLayout, PointDecompressGadgetLayout,
    PointDoubleGadgetLayout,
};
use crate::ed25519_scalar_air::{
    ScalarReduceGadgetLayout, eval_scalar_reduce_gadget,
    CARRY_BITS, PRODUCT_LIMBS, SCALAR_REDUCE_CONSTRAINTS,
};
use crate::ed25519_scalar_mult_air::{
    ScalarMultRowLayout, SCALAR_MULT_TRANSITION_CONSTRAINTS,
};
use crate::ed25519_verify_air::{
    eval_verify_air_v16_per_row, verify_v16_per_row_constraints, VerifyAirLayoutV16,
    DIGEST_BITS, VERIFY_V1_FORMAT_CONS,
};
use crate::sha512_air::{
    eval_sha512_constraints, NUM_CONSTRAINTS as SHA512_CONSTRAINTS, OFF_H0_LO,
    WIDTH as SHA512_WIDTH,
};

use crate::binding_cells_commit::{
    commit_binding_cells, verify_ood_consistency, BindingCellsCommit,
};
use crate::fri::DeepFriParams;
use crate::sub_air_with_trace::{
    prove_one_sub_air_with_trace_capturing, verify_one_sub_air_with_trace,
    SubAirProofWithTrace,
};

/// FS separator on every seam so all strands' OOD points align.
pub const SEAM_SEP: &[u8] = b"ed25519_verify_stranded_gway/seam/v1";

const SELECT_OWNED_LIMBS: usize = NUM_LIMBS; // select owns 10 c-limbs (+ its bit)

fn rng(base: usize, n: usize) -> impl Iterator<Item = usize> {
    base..base + n
}

// ═══════════════════════════════════════════════════════════════════
//  Constraint segments — an ordered partition of the monolith's
//  per-row constraint vector, mirroring `eval_verify_air_v16_per_row`.
// ═══════════════════════════════════════════════════════════════════

/// One contiguous constraint block: the slice `[start, start+len)` of the
/// monolith's per-row output, plus the trace COLUMNS it touches (owned
/// output ∪ reads, both cur and nxt) and a `home` column used to assign
/// the block to a strand.
#[derive(Clone, Debug)]
struct Seg {
    start: usize,
    len: usize,
    cols: Vec<usize>,
    home: usize,
    strand: usize,
}

/// Builder that appends segments while tracking the running constraint
/// index, so `start` is exact by construction.
struct SegBuilder {
    at: usize,
    segs: Vec<Seg>,
}

impl SegBuilder {
    fn new() -> Self {
        Self { at: 0, segs: Vec::new() }
    }
    /// Push a block that emits `len` constraint slots and touches `cols`.
    fn block(&mut self, len: usize, cols: Vec<usize>) {
        let home = cols.iter().copied().min().unwrap_or(0);
        self.segs.push(Seg { start: self.at, len, cols, home, strand: 0 });
        self.at += len;
    }
    /// Push a leaf gadget whose `home` is its output column (`c_limbs`),
    /// so multi-instance leaves (sB vs kA ladder rows) co-locate.
    fn leaf(&mut self, len: usize, home: usize, cols: Vec<usize>) {
        self.segs.push(Seg { start: self.at, len, cols, home, strand: 0 });
        self.at += len;
    }
    fn mul(&mut self, m: &MulGadgetLayout) {
        let cols: Vec<usize> = rng(m.a_limbs_base, NUM_LIMBS)
            .chain(rng(m.b_limbs_base, NUM_LIMBS))
            .chain(rng(m.c_limbs_base, MUL_GADGET_OWNED_CELLS))
            .collect();
        self.leaf(MUL_GADGET_CONSTRAINTS, m.c_limbs_base, cols);
    }
    fn add(&mut self, a: &AddGadgetLayout) {
        let cols: Vec<usize> = rng(a.a_limbs_base, NUM_LIMBS)
            .chain(rng(a.b_limbs_base, NUM_LIMBS))
            .chain(rng(a.c_limbs_base, ADD_GADGET_OWNED_CELLS))
            .collect();
        self.leaf(ADD_GADGET_CONSTRAINTS, a.c_limbs_base, cols);
    }
    fn sub(&mut self, s: &SubGadgetLayout) {
        let cols: Vec<usize> = rng(s.a_limbs_base, NUM_LIMBS)
            .chain(rng(s.b_limbs_base, NUM_LIMBS))
            .chain(rng(s.c_limbs_base, SUB_GADGET_OWNED_CELLS))
            .collect();
        self.leaf(SUB_GADGET_CONSTRAINTS, s.c_limbs_base, cols);
    }
    fn select(&mut self, sl: &SelectGadgetLayout) {
        let cols: Vec<usize> = rng(sl.a_limbs_base, NUM_LIMBS)
            .chain(rng(sl.b_limbs_base, NUM_LIMBS))
            .chain(std::iter::once(sl.bit_cell))
            .chain(rng(sl.c_limbs_base, SELECT_OWNED_LIMBS))
            .collect();
        self.leaf(SELECT_GADGET_CONSTRAINTS, sl.c_limbs_base, cols);
    }
    fn point_double(&mut self, d: &PointDoubleGadgetLayout) {
        self.mul(&d.sq_A);
        self.mul(&d.sq_B);
        self.mul(&d.sq_zz);
        self.add(&d.add_C);
        self.add(&d.add_H);
        self.add(&d.add_xy);
        self.mul(&d.sq_xy);
        self.sub(&d.sub_E);
        self.sub(&d.sub_G);
        self.add(&d.add_F);
        self.mul(&d.mul_X3);
        self.mul(&d.mul_Y3);
        self.mul(&d.mul_T3);
        self.mul(&d.mul_Z3);
    }
    fn point_add(&mut self, pa: &PointAddGadgetLayout) {
        // (1) D2 constant pin: NUM_LIMBS cons, touches d2_base block.
        self.leaf(NUM_LIMBS, pa.d2_base, rng(pa.d2_base, NUM_LIMBS).collect());
        self.sub(&pa.sub_ym1);
        self.sub(&pa.sub_ym2);
        self.add(&pa.add_yp1);
        self.add(&pa.add_yp2);
        self.mul(&pa.mul_A);
        self.mul(&pa.mul_B);
        self.mul(&pa.mul_tt);
        self.mul(&pa.mul_C);
        self.mul(&pa.mul_zz);
        self.add(&pa.add_D);
        self.sub(&pa.sub_E);
        self.sub(&pa.sub_F);
        self.add(&pa.add_G);
        self.add(&pa.add_H);
        self.mul(&pa.mul_X3);
        self.mul(&pa.mul_Y3);
        self.mul(&pa.mul_T3);
        self.mul(&pa.mul_Z3);
    }
    fn cond_add(&mut self, ca: &CondAddGadgetLayout) {
        self.point_add(&ca.add);
        self.select(&ca.sel_x);
        self.select(&ca.sel_y);
        self.select(&ca.sel_z);
        self.select(&ca.sel_t);
    }
    fn scalar_mult_per_row(&mut self, m: &ScalarMultRowLayout) {
        self.point_double(&m.dbl);
        self.cond_add(&m.cond_add);
    }
    /// Split the point-decompress gadget into its head (D-pin + x range),
    /// leaf gadgets (4 muls + 3 subs), eq-check and sign block — mirroring
    /// `eval_point_decompress_gadget` — so its ~3.7k columns distribute
    /// across strands instead of flooring a single strand.
    fn point_decompress(&mut self, dc: &PointDecompressGadgetLayout) {
        // head: D pin (NUM_LIMBS) + x range (255 booleanity + NUM_LIMBS pack).
        let head_cols: Vec<usize> = rng(dc.d_base, NUM_LIMBS)
            .chain(rng(dc.x_limbs, NUM_LIMBS))
            .chain(rng(dc.x_bits, ELEMENT_BIT_CELLS))
            .collect();
        self.block(NUM_LIMBS + ELEMENT_BIT_CELLS + NUM_LIMBS, head_cols);
        self.mul(&dc.sq_x);
        self.mul(&dc.sq_y);
        self.mul(&dc.mul_dx2);
        self.mul(&dc.mul_dxy);
        self.sub(&dc.sub_y2m1);
        self.sub(&dc.sub_lhs);
        self.sub(&dc.sub_eq);
        // eq check: sub_eq.c_limbs all zero (NUM_LIMBS).
        self.block(NUM_LIMBS, rng(dc.sub_eq.c_limbs_base, NUM_LIMBS).collect());
        // sign booleanity + match (reads sign_bit and x_bits[0]).
        self.block(2, vec![dc.sign_bit, dc.x_bits]);
    }
}

fn reduce_cols(reduce: &ScalarReduceGadgetLayout) -> Vec<usize> {
    // The scalar-reduce gadget occupies a contiguous block starting at
    // column 0 (input_limbs_base) up to carry_bits_base + its size.
    let end = reduce.carry_bits_base + PRODUCT_LIMBS * CARRY_BITS;
    (0..end).collect()
}

/// Columns read by the two ladder TRANSITION blocks / initial-acc / v6
/// per-row bindings live inside `mult`; helper to name the small sets.
fn mult_thread_cols(m: &ScalarMultRowLayout) -> Vec<usize> {
    rng(m.base_x, NUM_LIMBS)
        .chain(rng(m.base_y, NUM_LIMBS))
        .chain(rng(m.base_z, NUM_LIMBS))
        .chain(rng(m.base_t, NUM_LIMBS))
        .chain(rng(m.acc_x, NUM_LIMBS))
        .chain(rng(m.acc_y, NUM_LIMBS))
        .chain(rng(m.acc_z, NUM_LIMBS))
        .chain(rng(m.acc_t, NUM_LIMBS))
        .chain(rng(m.cond_add.out_x, NUM_LIMBS))
        .chain(rng(m.cond_add.out_y, NUM_LIMBS))
        .chain(rng(m.cond_add.out_z, NUM_LIMBS))
        .chain(rng(m.cond_add.out_t, NUM_LIMBS))
        .collect()
}

/// Build the ordered segment list mirroring `eval_verify_air_v16_per_row`
/// (call chain v3→v4→v5→v6→v7→v10→v11→v12→v13→v14→v15→v16).
fn v16_segments(L: &VerifyAirLayoutV16) -> Vec<Seg> {
    let k = L.k_scalar;
    let m = &L.mult;
    let mut b = SegBuilder::new();

    // ── v3 base ──
    // B1 SHA-512 (cur+nxt), sha state columns.
    b.block(SHA512_CONSTRAINTS, (0..SHA512_WIDTH).collect());
    // B2 scalar-reduce.
    b.block(SCALAR_REDUCE_CONSTRAINTS, reduce_cols(&L.reduce));
    // B3 format conversion (v1): digest bits + H-state + reduce.input(nxt).
    b.block(
        DIGEST_BITS + 16 + 32, // 512 booleanity + 16 pack + 32 limb-recompose
        (0..L.digest_bit_base + DIGEST_BITS).collect(),
    );
    // B4/B5 decompress R, A (same decomp columns, different rows) — split
    // into leaves so the ~3.7k-col gadget distributes across strands.
    b.point_decompress(&L.decomp);
    b.point_decompress(&L.decomp);
    // B6 sB per-row (point_double ++ cond_add on the shared mult columns).
    b.scalar_mult_per_row(m);
    // B7 sB transition.
    b.block(SCALAR_MULT_TRANSITION_CONSTRAINTS, mult_thread_cols(m));
    // B8 sB initial-acc.
    b.block(4 * NUM_LIMBS, rng(m.acc_x, 4 * NUM_LIMBS).collect());
    // B9 kA per-row (SAME mult columns → leaves co-locate with sB by home).
    b.scalar_mult_per_row(m);
    // B10 kA transition.
    b.block(SCALAR_MULT_TRANSITION_CONSTRAINTS, mult_thread_cols(m));
    // B11 kA initial-acc.
    b.block(4 * NUM_LIMBS, rng(m.acc_x, 4 * NUM_LIMBS).collect());

    // ── v4 base boundaries (sB, kA) — read mult.base_* ──
    let base_cols: Vec<usize> = rng(m.base_x, 4 * NUM_LIMBS).collect();
    b.block(4 * NUM_LIMBS, base_cols.clone());
    b.block(4 * NUM_LIMBS, base_cols);

    // ── v5 R/A y+sign pins (decomp columns) ──
    b.block(NUM_LIMBS + 1, rng(L.decomp.y_limbs, NUM_LIMBS).chain(std::iter::once(L.decomp.sign_bit)).collect());
    b.block(NUM_LIMBS + 1, rng(L.decomp.y_limbs, NUM_LIMBS).chain(std::iter::once(L.decomp.sign_bit)).collect());

    // ── v6 scalar shift chains (sB) ──
    let sblk = L.scalar_block_sB_base;
    let kblk = L.scalar_block_kA_base;
    let bit = m.cond_add.bit_cell;
    b.block(k, rng(sblk, k).collect()); // sB boundary
    b.block(1, vec![bit, sblk]); // sB per-row binding
    b.block(k - 1, rng(sblk, k).collect()); // sB shift transition (cur+nxt)
    b.block(k, rng(kblk, k).collect()); // kA boundary
    b.block(1, vec![bit, kblk]); // kA per-row binding
    b.block(k - 1, rng(kblk, k).collect()); // kA shift transition

    // ── v7 r-thread ──
    let rth = L.r_thread_base;
    // reduce_row boundary: thread[i] = reduce.r_bits[k-1-i]
    b.block(
        k,
        rng(rth, k).chain(rng(L.reduce.r_bits_base, k)).collect(),
    );
    // thread constancy (UNGATED, cur+nxt) — transition seam if r_thread split.
    b.block(k, rng(rth, k).collect());
    // kA_first boundary: scalar_block_kA[i] = thread[i]
    b.block(k, rng(kblk, k).chain(rng(rth, k)).collect());

    // ── v10 delta = v8 verdict ++ v9 dbl ++ dbl-chain ++ v10 result binding ──
    // v8 verdict (result_row): zero_const pin + 3 SUBs + 3 c-zero checks.
    {
        let mut cols: Vec<usize> = rng(L.zero_const_base, NUM_LIMBS).collect();
        cols.extend(seg_sub_cols(&L.sub_X));
        cols.extend(seg_sub_cols(&L.sub_T));
        cols.extend(seg_sub_cols(&L.sub_YZ));
        b.block(NUM_LIMBS + 3 * SUB_GADGET_CONSTRAINTS + 3 * NUM_LIMBS, cols);
    }
    // v9 point_double gadget (cofactor dbl), gated dbl_1/2/3 — split to leaves.
    b.point_double(&L.dbl);
    // dbl-input chaining (nxt.dbl_input = cur.dbl.mul_*3.c), gated dbl_1/dbl_2.
    b.block(
        3 * NUM_LIMBS,
        rng(L.dbl_input_X_base, NUM_LIMBS)
            .chain(rng(L.dbl_input_Y_base, NUM_LIMBS))
            .chain(rng(L.dbl_input_Z_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_X3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_Y3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_Z3.c_limbs_base, NUM_LIMBS))
            .collect(),
    );
    // v10 result binding (nxt.result_* = cur.dbl.mul_*3.c), gated dbl_3.
    b.block(
        4 * NUM_LIMBS,
        rng(L.result_X_base, NUM_LIMBS)
            .chain(rng(L.result_Y_base, NUM_LIMBS))
            .chain(rng(L.result_Z_base, NUM_LIMBS))
            .chain(rng(L.result_T_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_X3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_Y3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_Z3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.dbl.mul_T3.c_limbs_base, NUM_LIMBS))
            .collect(),
    );

    // ── v11 sB output thread ──
    b.block(
        4 * NUM_LIMBS,
        rng(L.thread_sB_X_base, NUM_LIMBS)
            .chain(rng(L.thread_sB_Y_base, NUM_LIMBS))
            .chain(rng(L.thread_sB_Z_base, NUM_LIMBS))
            .chain(rng(L.thread_sB_T_base, NUM_LIMBS))
            .chain(rng(m.cond_add.out_x, NUM_LIMBS))
            .chain(rng(m.cond_add.out_y, NUM_LIMBS))
            .chain(rng(m.cond_add.out_z, NUM_LIMBS))
            .chain(rng(m.cond_add.out_t, NUM_LIMBS))
            .collect(),
    );
    b.block(
        4 * NUM_LIMBS,
        rng(L.thread_sB_X_base, NUM_LIMBS)
            .chain(rng(L.thread_sB_Y_base, NUM_LIMBS))
            .chain(rng(L.thread_sB_Z_base, NUM_LIMBS))
            .chain(rng(L.thread_sB_T_base, NUM_LIMBS))
            .collect(),
    ); // constancy (cur+nxt)

    // ── v12 kA output thread ──
    b.block(
        4 * NUM_LIMBS,
        rng(L.thread_kA_X_base, NUM_LIMBS)
            .chain(rng(L.thread_kA_Y_base, NUM_LIMBS))
            .chain(rng(L.thread_kA_Z_base, NUM_LIMBS))
            .chain(rng(L.thread_kA_T_base, NUM_LIMBS))
            .chain(rng(m.cond_add.out_x, NUM_LIMBS))
            .chain(rng(m.cond_add.out_y, NUM_LIMBS))
            .chain(rng(m.cond_add.out_z, NUM_LIMBS))
            .chain(rng(m.cond_add.out_t, NUM_LIMBS))
            .collect(),
    );
    b.block(
        4 * NUM_LIMBS,
        rng(L.thread_kA_X_base, NUM_LIMBS)
            .chain(rng(L.thread_kA_Y_base, NUM_LIMBS))
            .chain(rng(L.thread_kA_Z_base, NUM_LIMBS))
            .chain(rng(L.thread_kA_T_base, NUM_LIMBS))
            .collect(),
    ); // constancy

    // ── v13 R thread + one_const + mul_R_T ──
    b.block(
        4 * NUM_LIMBS,
        rng(L.thread_R_X_base, NUM_LIMBS)
            .chain(rng(L.thread_R_Y_base, NUM_LIMBS))
            .chain(rng(L.thread_R_Z_base, NUM_LIMBS))
            .chain(rng(L.thread_R_T_base, NUM_LIMBS))
            .chain(rng(L.decomp.x_limbs, NUM_LIMBS))
            .chain(rng(L.decomp.y_limbs, NUM_LIMBS))
            .chain(rng(L.one_const_R_base, NUM_LIMBS))
            .chain(rng(L.mul_R_T.c_limbs_base, NUM_LIMBS))
            .collect(),
    ); // decompress_R_row boundary
    b.block(NUM_LIMBS, rng(L.one_const_R_base, NUM_LIMBS).collect()); // one_const pin
    b.block(
        MUL_GADGET_CONSTRAINTS,
        rng(L.mul_R_T.a_limbs_base, NUM_LIMBS)
            .chain(rng(L.mul_R_T.b_limbs_base, NUM_LIMBS))
            .chain(rng(L.mul_R_T.c_limbs_base, MUL_GADGET_OWNED_CELLS))
            .collect(),
    ); // mul_R_T
    b.block(
        4 * NUM_LIMBS,
        rng(L.thread_R_X_base, NUM_LIMBS)
            .chain(rng(L.thread_R_Y_base, NUM_LIMBS))
            .chain(rng(L.thread_R_Z_base, NUM_LIMBS))
            .chain(rng(L.thread_R_T_base, NUM_LIMBS))
            .collect(),
    ); // R thread constancy

    // ── v14 residual_1 = sB − R (zero_const_R1 pin + 2 SUBs + point_add_R1) ──
    b.block(NUM_LIMBS, rng(L.zero_const_R1_base, NUM_LIMBS).collect());
    b.sub(&L.sub_negR_X);
    b.sub(&L.sub_negR_T);
    b.point_add(&L.point_add_R1);

    // ── v15 residual_2 = residual_1 − kA (2 SUBs + point_add_R2) ──
    b.sub(&L.sub_negkA_X);
    b.sub(&L.sub_negkA_T);
    b.point_add(&L.point_add_R2);

    // ── v16 residual_2 → dbl_1 input binding (nxt.dbl_input = cur.pa_R2.out) ──
    b.block(
        3 * NUM_LIMBS,
        rng(L.dbl_input_X_base, NUM_LIMBS)
            .chain(rng(L.dbl_input_Y_base, NUM_LIMBS))
            .chain(rng(L.dbl_input_Z_base, NUM_LIMBS))
            .chain(rng(L.point_add_R2.mul_X3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.point_add_R2.mul_Y3.c_limbs_base, NUM_LIMBS))
            .chain(rng(L.point_add_R2.mul_Z3.c_limbs_base, NUM_LIMBS))
            .collect(),
    );

    let total: usize = b.segs.iter().map(|s| s.len).sum();
    let want = verify_v16_per_row_constraints(k);
    assert_eq!(
        total, want,
        "segment list total ({total}) must equal monolith per-row constraints ({want})"
    );
    b.segs
}

fn seg_sub_cols(s: &SubGadgetLayout) -> Vec<usize> {
    // The verdict block reads the SUB gadget AND its c-limbs zero-check.
    rng(s.a_limbs_base, NUM_LIMBS)
        .chain(rng(s.b_limbs_base, NUM_LIMBS))
        .chain(rng(s.c_limbs_base, SUB_GADGET_OWNED_CELLS))
        .collect()
}

// ═══════════════════════════════════════════════════════════════════
//  NATIVE per-strand evaluator
// ═══════════════════════════════════════════════════════════════════
//
// The hybrid-slice evaluator (`eval_strand`) SCATTERS the strand's held
// columns into a FULL-WIDTH (41_519) zero buffer, calls the monolith
// `eval_verify_air_v16_per_row` (computing ALL 70_606 constraints), and
// keeps only the strand's slices.  That is a fixed per-point memory /
// compute floor independent of `G`.
//
// The NATIVE evaluator below computes ONLY the strand's assigned
// constraint blocks, reading ONLY the strand's local (narrow) columns at
// their LOCAL indices.  It reuses the VERIFIED per-gadget/per-block
// evaluators (`eval_mul_gadget`, `eval_add_gadget`, `eval_sub_gadget`,
// `eval_select_gadget`, `eval_scalar_reduce_gadget`,
// `eval_sha512_constraints`) with a per-strand REMAPPED layout, and
// re-transcribes the small inline binding/boundary/transition blocks
// verbatim from the monolith's v0..v16 chain.
//
// The ordered `Op` list produced by `v16_ops` mirrors `v16_segments`
// block-for-block (same order, same lengths — asserted in
// `build_native_ops`).  Each `Op` carries the ABSOLUTE column bases; a
// per-strand column map `L(c) = rank of c in strand_cols[s]` remaps them
// to local positions.  Because every gadget reads a set of CONTIGUOUS,
// fully-held column runs, `L` is affine on each run
// (`L(base+i) == L(base)+i`), so the reused evaluators index correctly
// against the narrow local buffer.
//
// SOUNDNESS: identical `c_eval` ⇒ identical proofs ⇒ existing gates are
// preserved by construction (checked byte-for-byte by
// `native_eval_matches_hybrid`).

/// Row-gate for a constraint block, mirroring the `if row == … { … } else
/// { zeros }` structure of the monolith's v0..v16 evaluators.
#[derive(Clone, Copy, Debug)]
enum Gate {
    /// Fires on every row (ungated transition / constancy blocks).
    Always,
    /// `row == r`.
    Row(usize),
    /// `row + 1 < k_hash`  (SHA-512 active band, excluding the wrap row).
    ShaWrap(usize),
    /// `a <= row <= b`  (per-row phase band, e.g. a scalar-mult ladder).
    Band(usize, usize),
    /// `a <= row < b`   (transition band — fires on adjacent row pairs).
    BandTrans(usize, usize),
    /// `row ∈ {a, b}`   (dbl-input chaining across the 3-step cofactor).
    Or2(usize, usize),
    /// `row ∈ {a, b, c}` (the 3 cofactor-doubling rows).
    Or3(usize, usize, usize),
}

impl Gate {
    #[inline]
    fn active(&self, row: usize) -> bool {
        match *self {
            Gate::Always => true,
            Gate::Row(r) => row == r,
            Gate::ShaWrap(kh) => row + 1 < kh,
            Gate::Band(a, b) => a <= row && row <= b,
            Gate::BandTrans(a, b) => a <= row && row < b,
            Gate::Or2(a, b) => row == a || row == b,
            Gate::Or3(a, b, c) => row == a || row == b || row == c,
        }
    }
}

/// One constraint block's compute recipe.  Column bases are ABSOLUTE when
/// produced by `v16_ops`; `remap` rewrites them to per-strand LOCAL
/// positions.  `eval` computes the block's ACTIVE values (the gate is
/// checked by the caller; off-gate the block contributes `len` zeros).
#[derive(Clone, Debug)]
enum Op {
    // ── reused verified evaluators (remapped layout) ──
    Sha,
    Reduce(ScalarReduceGadgetLayout),
    Mul(MulGadgetLayout),
    Add(AddGadgetLayout),
    Sub(SubGadgetLayout),
    Select(SelectGadgetLayout),
    // ── re-transcribed inline blocks ──
    /// v1 format-conversion (512 booleanity + 16 H-pack + 32 input-bind).
    Format { digest: usize, h0lo: usize, input: usize },
    /// point-decompress head: D-pin (10) + x range (255 + 10).
    DecompHead { d: usize, xl: usize, xb: usize },
    /// point-decompress sign block (booleanity + x_bits[0] match).
    DecompSign { sb: usize, xb: usize },
    /// point-add D2 constant pin (10).
    D2Pin { base: usize },
    /// `push cur[base+i]` for `i in 0..n` (zero-const pins, c-limb checks).
    Cells { base: usize, n: usize },
    /// `push cur[base+i] - vals[i]` (constant boundary pins).
    ConstPin { base: usize, vals: Vec<u64> },
    /// one-const pin (canonical F25519 `1`).
    OneConstPin { base: usize },
    /// scalar-mult per-row transition (base constancy ++ acc = cond_add.out).
    SMultTrans {
        bx: usize, by: usize, bz: usize, bt: usize,
        ax: usize, ay: usize, az: usize, at: usize,
        ox: usize, oy: usize, oz: usize, ot: usize,
    },
    /// scalar-mult initial-acc boundary (acc = identity, interleaved).
    SMultInitAcc {
        ax: usize, ay: usize, az: usize, at: usize,
        idx: [u64; NUM_LIMBS], idy: [u64; NUM_LIMBS],
        idz: [u64; NUM_LIMBS], idt: [u64; NUM_LIMBS],
    },
    /// v6 per-row scalar-bit binding: `cur[bit_cell] - cur[blk]`.
    PerRowBind { bit_cell: usize, blk: usize },
    /// v6 shift transition: `nxt[blk+i] - cur[blk+i+1]` for `i in 0..k-1`.
    ShiftTrans { blk: usize, k: usize },
    /// v7 reduce boundary: `cur[rth+i] - cur[rbits + k-1-i]`.
    RThreadReduceBoundary { rth: usize, rbits: usize, k: usize },
    /// v7 kA_first boundary: `cur[dst+i] - cur[src+i]` for `i in 0..k`.
    CurBindRun { dst: usize, src: usize, k: usize },
    /// per-row constancy: `nxt[base+i] - cur[base+i]` for `i in 0..n`.
    Constancy { base: usize, n: usize },
    /// v8 verdict: 10 zero-pins ++ 3 SUB gadgets ++ 3×10 c-limb-zero checks.
    Verdict { zc: usize, sub_x: SubGadgetLayout, sub_t: SubGadgetLayout, sub_yz: SubGadgetLayout },
    /// `nxt[dst[j]+k] - cur[src[j]+k]` per coord `j`, limb `k` (forward binds).
    NxtBind { dst: Vec<usize>, src: Vec<usize> },
    /// `cur[dst[j]+k] - cur[src[j]+k]` per coord `j`, limb `k` (same-row binds).
    CurBind { dst: Vec<usize>, src: Vec<usize> },
}

#[inline]
fn f_one() -> F {
    F::from(1u64)
}

impl Op {
    fn len(&self) -> usize {
        match self {
            Op::Sha => SHA512_CONSTRAINTS,
            Op::Reduce(_) => SCALAR_REDUCE_CONSTRAINTS,
            Op::Mul(_) => MUL_GADGET_CONSTRAINTS,
            Op::Add(_) => ADD_GADGET_CONSTRAINTS,
            Op::Sub(_) => SUB_GADGET_CONSTRAINTS,
            Op::Select(_) => SELECT_GADGET_CONSTRAINTS,
            Op::Format { .. } => VERIFY_V1_FORMAT_CONS,
            Op::DecompHead { .. } => NUM_LIMBS + ELEMENT_BIT_CELLS + NUM_LIMBS,
            Op::DecompSign { .. } => 2,
            Op::D2Pin { .. } => NUM_LIMBS,
            Op::Cells { n, .. } => *n,
            Op::ConstPin { vals, .. } => vals.len(),
            Op::OneConstPin { .. } => NUM_LIMBS,
            Op::SMultTrans { .. } => 8 * NUM_LIMBS,
            Op::SMultInitAcc { .. } => 4 * NUM_LIMBS,
            Op::PerRowBind { .. } => 1,
            Op::ShiftTrans { k, .. } => k - 1,
            Op::RThreadReduceBoundary { k, .. } => *k,
            Op::CurBindRun { k, .. } => *k,
            Op::Constancy { n, .. } => *n,
            Op::Verdict { .. } => NUM_LIMBS + 3 * SUB_GADGET_CONSTRAINTS + 3 * NUM_LIMBS,
            Op::NxtBind { dst, .. } => dst.len() * NUM_LIMBS,
            Op::CurBind { dst, .. } => dst.len() * NUM_LIMBS,
        }
    }

    /// Remap every ABSOLUTE column base through `m` (→ per-strand local
    /// indices).  Constants are unchanged.
    fn remap(&self, m: &impl Fn(usize) -> usize) -> Op {
        let rm_mul = |g: &MulGadgetLayout| MulGadgetLayout {
            a_limbs_base: m(g.a_limbs_base),
            b_limbs_base: m(g.b_limbs_base),
            c_limbs_base: m(g.c_limbs_base),
            c_bits_base: m(g.c_bits_base),
            carry_bits_base: m(g.carry_bits_base),
        };
        let rm_add = |g: &AddGadgetLayout| AddGadgetLayout {
            a_limbs_base: m(g.a_limbs_base),
            b_limbs_base: m(g.b_limbs_base),
            c_limbs_base: m(g.c_limbs_base),
            c_bits_base: m(g.c_bits_base),
            carries_base: m(g.carries_base),
        };
        let rm_sub = |g: &SubGadgetLayout| SubGadgetLayout {
            a_limbs_base: m(g.a_limbs_base),
            b_limbs_base: m(g.b_limbs_base),
            c_limbs_base: m(g.c_limbs_base),
            c_bits_base: m(g.c_bits_base),
            c_pos_base: m(g.c_pos_base),
            c_neg_base: m(g.c_neg_base),
        };
        let rm_sel = |g: &SelectGadgetLayout| SelectGadgetLayout {
            a_limbs_base: m(g.a_limbs_base),
            b_limbs_base: m(g.b_limbs_base),
            bit_cell: m(g.bit_cell),
            c_limbs_base: m(g.c_limbs_base),
        };
        let rm_reduce = |g: &ScalarReduceGadgetLayout| ScalarReduceGadgetLayout {
            input_limbs_base: m(g.input_limbs_base),
            q_limbs_base: m(g.q_limbs_base),
            q_bits_base: m(g.q_bits_base),
            r_limbs_base: m(g.r_limbs_base),
            r_bits_base: m(g.r_bits_base),
            slack_limbs_base: m(g.slack_limbs_base),
            slack_bits_base: m(g.slack_bits_base),
            carry_bits_base: m(g.carry_bits_base),
        };
        let mv = |v: &[usize]| v.iter().map(|&c| m(c)).collect::<Vec<_>>();
        match self {
            Op::Sha => Op::Sha,
            Op::Reduce(g) => Op::Reduce(rm_reduce(g)),
            Op::Mul(g) => Op::Mul(rm_mul(g)),
            Op::Add(g) => Op::Add(rm_add(g)),
            Op::Sub(g) => Op::Sub(rm_sub(g)),
            Op::Select(g) => Op::Select(rm_sel(g)),
            Op::Format { digest, h0lo, input } =>
                Op::Format { digest: m(*digest), h0lo: m(*h0lo), input: m(*input) },
            Op::DecompHead { d, xl, xb } =>
                Op::DecompHead { d: m(*d), xl: m(*xl), xb: m(*xb) },
            Op::DecompSign { sb, xb } => Op::DecompSign { sb: m(*sb), xb: m(*xb) },
            Op::D2Pin { base } => Op::D2Pin { base: m(*base) },
            Op::Cells { base, n } => Op::Cells { base: m(*base), n: *n },
            Op::ConstPin { base, vals } => Op::ConstPin { base: m(*base), vals: vals.clone() },
            Op::OneConstPin { base } => Op::OneConstPin { base: m(*base) },
            Op::SMultTrans { bx, by, bz, bt, ax, ay, az, at, ox, oy, oz, ot } =>
                Op::SMultTrans {
                    bx: m(*bx), by: m(*by), bz: m(*bz), bt: m(*bt),
                    ax: m(*ax), ay: m(*ay), az: m(*az), at: m(*at),
                    ox: m(*ox), oy: m(*oy), oz: m(*oz), ot: m(*ot),
                },
            Op::SMultInitAcc { ax, ay, az, at, idx, idy, idz, idt } =>
                Op::SMultInitAcc {
                    ax: m(*ax), ay: m(*ay), az: m(*az), at: m(*at),
                    idx: *idx, idy: *idy, idz: *idz, idt: *idt,
                },
            Op::PerRowBind { bit_cell, blk } =>
                Op::PerRowBind { bit_cell: m(*bit_cell), blk: m(*blk) },
            Op::ShiftTrans { blk, k } => Op::ShiftTrans { blk: m(*blk), k: *k },
            Op::RThreadReduceBoundary { rth, rbits, k } =>
                Op::RThreadReduceBoundary { rth: m(*rth), rbits: m(*rbits), k: *k },
            Op::CurBindRun { dst, src, k } =>
                Op::CurBindRun { dst: m(*dst), src: m(*src), k: *k },
            Op::Constancy { base, n } => Op::Constancy { base: m(*base), n: *n },
            Op::Verdict { zc, sub_x, sub_t, sub_yz } =>
                Op::Verdict { zc: m(*zc), sub_x: rm_sub(sub_x), sub_t: rm_sub(sub_t), sub_yz: rm_sub(sub_yz) },
            Op::NxtBind { dst, src } => Op::NxtBind { dst: mv(dst), src: mv(src) },
            Op::CurBind { dst, src } => Op::CurBind { dst: mv(dst), src: mv(src) },
        }
    }

    /// Compute the block's ACTIVE constraint values against the LOCAL
    /// buffers `cur`/`nxt` (column bases already remapped).  Byte-identical
    /// to the corresponding slice of `eval_verify_air_v16_per_row`.
    fn eval(&self, cur: &[F], nxt: &[F], row: usize, n_blocks: usize) -> Vec<F> {
        let one = f_one();
        match self {
            Op::Sha => eval_sha512_constraints(cur, nxt, row, n_blocks),
            Op::Reduce(g) => eval_scalar_reduce_gadget(cur, g),
            Op::Mul(g) => eval_mul_gadget(cur, g),
            Op::Add(g) => eval_add_gadget(cur, g),
            Op::Sub(g) => eval_sub_gadget(cur, g),
            Op::Select(g) => eval_select_gadget(cur, g),
            Op::Format { digest, h0lo, input } => {
                let mut out = Vec::with_capacity(VERIFY_V1_FORMAT_CONS);
                for k in 0..8 {
                    for i in 0..64 {
                        let b = cur[digest + 64 * k + i];
                        out.push(b * (one - b));
                    }
                }
                let pow2_lo: [F; 32] = core::array::from_fn(|i| F::from(1u64 << i));
                for k in 0..8 {
                    let mut sum_lo = F::zero();
                    let mut sum_hi = F::zero();
                    for i in 0..32 {
                        sum_lo += pow2_lo[i] * cur[digest + 64 * k + i];
                        sum_hi += pow2_lo[i] * cur[digest + 64 * k + 32 + i];
                    }
                    out.push(cur[h0lo + 2 * k] - sum_lo);
                    out.push(cur[h0lo + 2 * k + 1] - sum_hi);
                }
                let pow2_16: [F; 16] = core::array::from_fn(|i| F::from(1u64 << i));
                for k in 0..8 {
                    for mm in 0..4 {
                        let low_byte_base = 56 - 16 * mm;
                        let high_byte_base = low_byte_base - 8;
                        let mut sum = F::zero();
                        for j in 0..8 {
                            sum += pow2_16[j] * cur[digest + 64 * k + low_byte_base + j];
                        }
                        for j in 0..8 {
                            sum += pow2_16[8 + j] * cur[digest + 64 * k + high_byte_base + j];
                        }
                        out.push(nxt[input + 4 * k + mm] - sum);
                    }
                }
                out
            }
            Op::DecompHead { d, xl, xb } => {
                let dd = *D;
                let mut out = Vec::with_capacity(NUM_LIMBS + ELEMENT_BIT_CELLS + NUM_LIMBS);
                for k in 0..NUM_LIMBS {
                    out.push(cur[d + k] - F::from(dd.limbs[k] as u64));
                }
                let mut bit_off = 0usize;
                for i in 0..NUM_LIMBS {
                    for b in 0..LIMB_WIDTHS[i] as usize {
                        let cell = cur[xb + bit_off + b];
                        out.push(cell * (one - cell));
                    }
                    bit_off += LIMB_WIDTHS[i] as usize;
                }
                let mut bit_off = 0usize;
                for i in 0..NUM_LIMBS {
                    let mut sum_bits = F::zero();
                    for b in 0..LIMB_WIDTHS[i] as usize {
                        sum_bits += F::from(1u64 << b) * cur[xb + bit_off + b];
                    }
                    out.push(cur[xl + i] - sum_bits);
                    bit_off += LIMB_WIDTHS[i] as usize;
                }
                out
            }
            Op::DecompSign { sb, xb } => {
                let s = cur[*sb];
                vec![s * (one - s), cur[*xb] - s]
            }
            Op::D2Pin { base } => {
                let d2 = *D2;
                (0..NUM_LIMBS).map(|k| cur[base + k] - F::from(d2.limbs[k] as u64)).collect()
            }
            Op::Cells { base, n } => (0..*n).map(|i| cur[base + i]).collect(),
            Op::ConstPin { base, vals } =>
                (0..vals.len()).map(|i| cur[base + i] - F::from(vals[i])).collect(),
            Op::OneConstPin { base } => {
                let onef = FieldElement::one();
                (0..NUM_LIMBS).map(|i| cur[base + i] - F::from(onef.limbs[i] as u64)).collect()
            }
            Op::SMultTrans { bx, by, bz, bt, ax, ay, az, at, ox, oy, oz, ot } => {
                let mut out = Vec::with_capacity(8 * NUM_LIMBS);
                for k in 0..NUM_LIMBS {
                    out.push(nxt[bx + k] - cur[bx + k]);
                    out.push(nxt[by + k] - cur[by + k]);
                    out.push(nxt[bz + k] - cur[bz + k]);
                    out.push(nxt[bt + k] - cur[bt + k]);
                }
                for k in 0..NUM_LIMBS {
                    out.push(nxt[ax + k] - cur[ox + k]);
                    out.push(nxt[ay + k] - cur[oy + k]);
                    out.push(nxt[az + k] - cur[oz + k]);
                    out.push(nxt[at + k] - cur[ot + k]);
                }
                out
            }
            Op::SMultInitAcc { ax, ay, az, at, idx, idy, idz, idt } => {
                let mut out = Vec::with_capacity(4 * NUM_LIMBS);
                for k in 0..NUM_LIMBS {
                    out.push(cur[ax + k] - F::from(idx[k]));
                    out.push(cur[ay + k] - F::from(idy[k]));
                    out.push(cur[az + k] - F::from(idz[k]));
                    out.push(cur[at + k] - F::from(idt[k]));
                }
                out
            }
            Op::PerRowBind { bit_cell, blk } => vec![cur[*bit_cell] - cur[*blk]],
            Op::ShiftTrans { blk, k } =>
                (0..k - 1).map(|i| nxt[blk + i] - cur[blk + i + 1]).collect(),
            Op::RThreadReduceBoundary { rth, rbits, k } =>
                (0..*k).map(|i| cur[rth + i] - cur[rbits + k - 1 - i]).collect(),
            Op::CurBindRun { dst, src, k } =>
                (0..*k).map(|i| cur[dst + i] - cur[src + i]).collect(),
            Op::Constancy { base, n } =>
                (0..*n).map(|i| nxt[base + i] - cur[base + i]).collect(),
            Op::Verdict { zc, sub_x, sub_t, sub_yz } => {
                let mut out = Vec::with_capacity(NUM_LIMBS + 3 * SUB_GADGET_CONSTRAINTS + 3 * NUM_LIMBS);
                for i in 0..NUM_LIMBS {
                    out.push(cur[zc + i]);
                }
                out.extend(eval_sub_gadget(cur, sub_x));
                out.extend(eval_sub_gadget(cur, sub_t));
                out.extend(eval_sub_gadget(cur, sub_yz));
                for i in 0..NUM_LIMBS {
                    out.push(cur[sub_x.c_limbs_base + i]);
                }
                for i in 0..NUM_LIMBS {
                    out.push(cur[sub_t.c_limbs_base + i]);
                }
                for i in 0..NUM_LIMBS {
                    out.push(cur[sub_yz.c_limbs_base + i]);
                }
                out
            }
            Op::NxtBind { dst, src } => {
                let mut out = Vec::with_capacity(dst.len() * NUM_LIMBS);
                for j in 0..dst.len() {
                    for k in 0..NUM_LIMBS {
                        out.push(nxt[dst[j] + k] - cur[src[j] + k]);
                    }
                }
                out
            }
            Op::CurBind { dst, src } => {
                let mut out = Vec::with_capacity(dst.len() * NUM_LIMBS);
                for j in 0..dst.len() {
                    for k in 0..NUM_LIMBS {
                        out.push(cur[dst[j] + k] - cur[src[j] + k]);
                    }
                }
                out
            }
        }
    }
}

/// Canonical-form limb array (freeze) of a field element.
fn limbs10(fe: &FieldElement) -> [u64; NUM_LIMBS] {
    let mut c = *fe;
    c.freeze();
    core::array::from_fn(|i| c.limbs[i] as u64)
}

/// Builder for the ordered `(Gate, Op)` list — mirrors `SegBuilder` /
/// `v16_segments` block-for-block.
struct OpBuilder {
    ops: Vec<(Gate, Op)>,
}

impl OpBuilder {
    fn new() -> Self {
        Self { ops: Vec::new() }
    }
    fn push(&mut self, gate: Gate, op: Op) {
        self.ops.push((gate, op));
    }
    fn mul(&mut self, gate: Gate, m: &MulGadgetLayout) {
        self.push(gate, Op::Mul(*m));
    }
    fn add(&mut self, gate: Gate, a: &AddGadgetLayout) {
        self.push(gate, Op::Add(*a));
    }
    fn sub(&mut self, gate: Gate, s: &SubGadgetLayout) {
        self.push(gate, Op::Sub(*s));
    }
    fn select(&mut self, gate: Gate, s: &SelectGadgetLayout) {
        self.push(gate, Op::Select(*s));
    }
    fn point_double(&mut self, gate: Gate, d: &PointDoubleGadgetLayout) {
        self.mul(gate, &d.sq_A);
        self.mul(gate, &d.sq_B);
        self.mul(gate, &d.sq_zz);
        self.add(gate, &d.add_C);
        self.add(gate, &d.add_H);
        self.add(gate, &d.add_xy);
        self.mul(gate, &d.sq_xy);
        self.sub(gate, &d.sub_E);
        self.sub(gate, &d.sub_G);
        self.add(gate, &d.add_F);
        self.mul(gate, &d.mul_X3);
        self.mul(gate, &d.mul_Y3);
        self.mul(gate, &d.mul_T3);
        self.mul(gate, &d.mul_Z3);
    }
    fn point_add(&mut self, gate: Gate, pa: &PointAddGadgetLayout) {
        self.push(gate, Op::D2Pin { base: pa.d2_base });
        self.sub(gate, &pa.sub_ym1);
        self.sub(gate, &pa.sub_ym2);
        self.add(gate, &pa.add_yp1);
        self.add(gate, &pa.add_yp2);
        self.mul(gate, &pa.mul_A);
        self.mul(gate, &pa.mul_B);
        self.mul(gate, &pa.mul_tt);
        self.mul(gate, &pa.mul_C);
        self.mul(gate, &pa.mul_zz);
        self.add(gate, &pa.add_D);
        self.sub(gate, &pa.sub_E);
        self.sub(gate, &pa.sub_F);
        self.add(gate, &pa.add_G);
        self.add(gate, &pa.add_H);
        self.mul(gate, &pa.mul_X3);
        self.mul(gate, &pa.mul_Y3);
        self.mul(gate, &pa.mul_T3);
        self.mul(gate, &pa.mul_Z3);
    }
    fn cond_add(&mut self, gate: Gate, ca: &CondAddGadgetLayout) {
        self.point_add(gate, &ca.add);
        self.select(gate, &ca.sel_x);
        self.select(gate, &ca.sel_y);
        self.select(gate, &ca.sel_z);
        self.select(gate, &ca.sel_t);
    }
    fn scalar_mult_per_row(&mut self, gate: Gate, m: &ScalarMultRowLayout) {
        self.point_double(gate, &m.dbl);
        self.cond_add(gate, &m.cond_add);
    }
    fn point_decompress(&mut self, gate: Gate, dc: &PointDecompressGadgetLayout) {
        self.push(gate, Op::DecompHead { d: dc.d_base, xl: dc.x_limbs, xb: dc.x_bits });
        self.mul(gate, &dc.sq_x);
        self.mul(gate, &dc.sq_y);
        self.mul(gate, &dc.mul_dx2);
        self.mul(gate, &dc.mul_dxy);
        self.sub(gate, &dc.sub_y2m1);
        self.sub(gate, &dc.sub_lhs);
        self.sub(gate, &dc.sub_eq);
        self.push(gate, Op::Cells { base: dc.sub_eq.c_limbs_base, n: NUM_LIMBS });
        self.push(gate, Op::DecompSign { sb: dc.sign_bit, xb: dc.x_bits });
    }
}

/// Ordered `(Gate, Op)` list mirroring `v16_segments` block-for-block.
/// Column bases are ABSOLUTE; concatenating every block's gated output
/// reproduces `eval_verify_air_v16_per_row` exactly.
fn v16_ops(L: &VerifyAirLayoutV16) -> Vec<(Gate, Op)> {
    let k = L.k_scalar;
    let m = &L.mult;
    let kh = L.k_hash;
    let sB_last = L.sB_first_row + k - 1;
    let kA_last = L.kA_first_row + k - 1;
    let mut b = OpBuilder::new();

    // ── v3 base ──
    b.push(Gate::ShaWrap(kh), Op::Sha);
    b.push(Gate::Row(L.reduce_row), Op::Reduce(L.reduce));
    b.push(
        Gate::Row(kh - 1),
        Op::Format {
            digest: L.digest_bit_base,
            h0lo: OFF_H0_LO,
            input: L.reduce.input_limbs_base,
        },
    );
    b.point_decompress(Gate::Row(L.decompress_R_row), &L.decomp);
    b.point_decompress(Gate::Row(L.decompress_A_row), &L.decomp);
    // B6 sB per-row.
    b.scalar_mult_per_row(Gate::Band(L.sB_first_row, sB_last), m);
    // B7 sB transition.
    b.push(
        Gate::BandTrans(L.sB_first_row, sB_last),
        Op::SMultTrans {
            bx: m.base_x, by: m.base_y, bz: m.base_z, bt: m.base_t,
            ax: m.acc_x, ay: m.acc_y, az: m.acc_z, at: m.acc_t,
            ox: m.cond_add.out_x, oy: m.cond_add.out_y,
            oz: m.cond_add.out_z, ot: m.cond_add.out_t,
        },
    );
    // B8 sB initial-acc.
    let id = EdwardsPoint::identity();
    let (idx, idy, idz, idt) =
        (limbs10(&id.X), limbs10(&id.Y), limbs10(&id.Z), limbs10(&id.T));
    b.push(
        Gate::Row(L.sB_first_row),
        Op::SMultInitAcc { ax: m.acc_x, ay: m.acc_y, az: m.acc_z, at: m.acc_t, idx, idy, idz, idt },
    );
    // B9 kA per-row.
    b.scalar_mult_per_row(Gate::Band(L.kA_first_row, kA_last), m);
    // B10 kA transition.
    b.push(
        Gate::BandTrans(L.kA_first_row, kA_last),
        Op::SMultTrans {
            bx: m.base_x, by: m.base_y, bz: m.base_z, bt: m.base_t,
            ax: m.acc_x, ay: m.acc_y, az: m.acc_z, at: m.acc_t,
            ox: m.cond_add.out_x, oy: m.cond_add.out_y,
            oz: m.cond_add.out_z, ot: m.cond_add.out_t,
        },
    );
    // B11 kA initial-acc.
    b.push(
        Gate::Row(L.kA_first_row),
        Op::SMultInitAcc { ax: m.acc_x, ay: m.acc_y, az: m.acc_z, at: m.acc_t, idx, idy, idz, idt },
    );

    // ── v4 base boundaries ──
    let bp = *ED25519_BASEPOINT;
    let mut bp_vals: Vec<u64> = Vec::with_capacity(4 * NUM_LIMBS);
    bp_vals.extend_from_slice(&limbs10(&bp.X));
    bp_vals.extend_from_slice(&limbs10(&bp.Y));
    bp_vals.extend_from_slice(&limbs10(&bp.Z));
    bp_vals.extend_from_slice(&limbs10(&bp.T));
    b.push(Gate::Row(L.sB_first_row), Op::ConstPin { base: m.base_x, vals: bp_vals });
    let mut a_vals: Vec<u64> = Vec::with_capacity(4 * NUM_LIMBS);
    for coord in 0..4 {
        for i in 0..NUM_LIMBS {
            a_vals.push(L.a_point_limbs[coord].limbs[i] as u64);
        }
    }
    b.push(Gate::Row(L.kA_first_row), Op::ConstPin { base: m.base_x, vals: a_vals });

    // ── v5 R/A y+sign pins ──
    let mut ry_vals: Vec<u64> = (0..NUM_LIMBS).map(|i| L.r_y.limbs[i] as u64).collect();
    ry_vals.push(if L.r_sign { 1 } else { 0 });
    b.push(Gate::Row(L.decompress_R_row), Op::ConstPin { base: L.decomp.y_limbs, vals: ry_vals });
    let mut ay_vals: Vec<u64> = (0..NUM_LIMBS).map(|i| L.a_y.limbs[i] as u64).collect();
    ay_vals.push(if L.a_sign { 1 } else { 0 });
    b.push(Gate::Row(L.decompress_A_row), Op::ConstPin { base: L.decomp.y_limbs, vals: ay_vals });

    // ── v6 scalar shift chains ──
    let sblk = L.scalar_block_sB_base;
    let kblk = L.scalar_block_kA_base;
    let bit = m.cond_add.bit_cell;
    b.push(Gate::Row(L.sB_first_row), Op::ConstPin { base: sblk, vals: L.s_bits.iter().map(|&x| x as u64).collect() });
    b.push(Gate::Band(L.sB_first_row, sB_last), Op::PerRowBind { bit_cell: bit, blk: sblk });
    b.push(Gate::BandTrans(L.sB_first_row, sB_last), Op::ShiftTrans { blk: sblk, k });
    b.push(Gate::Row(L.kA_first_row), Op::ConstPin { base: kblk, vals: L.k_bits.iter().map(|&x| x as u64).collect() });
    b.push(Gate::Band(L.kA_first_row, kA_last), Op::PerRowBind { bit_cell: bit, blk: kblk });
    b.push(Gate::BandTrans(L.kA_first_row, kA_last), Op::ShiftTrans { blk: kblk, k });

    // ── v7 r-thread ──
    let rth = L.r_thread_base;
    b.push(Gate::Row(L.reduce_row), Op::RThreadReduceBoundary { rth, rbits: L.reduce.r_bits_base, k });
    b.push(Gate::Always, Op::Constancy { base: rth, n: k });
    b.push(Gate::Row(L.kA_first_row), Op::CurBindRun { dst: kblk, src: rth, k });

    // ── v8/v9/v10 verdict + cofactor dbl chain ──
    b.push(Gate::Row(L.result_row), Op::Verdict { zc: L.zero_const_base, sub_x: L.sub_X, sub_t: L.sub_T, sub_yz: L.sub_YZ });
    b.point_double(Gate::Or3(L.dbl_1_row, L.dbl_2_row, L.dbl_3_row), &L.dbl);
    b.push(
        Gate::Or2(L.dbl_1_row, L.dbl_2_row),
        Op::NxtBind {
            dst: vec![L.dbl_input_X_base, L.dbl_input_Y_base, L.dbl_input_Z_base],
            src: vec![L.dbl.mul_X3.c_limbs_base, L.dbl.mul_Y3.c_limbs_base, L.dbl.mul_Z3.c_limbs_base],
        },
    );
    b.push(
        Gate::Row(L.dbl_3_row),
        Op::NxtBind {
            dst: vec![L.result_X_base, L.result_Y_base, L.result_Z_base, L.result_T_base],
            src: vec![L.dbl.mul_X3.c_limbs_base, L.dbl.mul_Y3.c_limbs_base, L.dbl.mul_Z3.c_limbs_base, L.dbl.mul_T3.c_limbs_base],
        },
    );

    // ── v11 sB output thread ──
    b.push(
        Gate::Row(L.sB_last_row),
        Op::CurBind {
            dst: vec![L.thread_sB_X_base, L.thread_sB_Y_base, L.thread_sB_Z_base, L.thread_sB_T_base],
            src: vec![m.cond_add.out_x, m.cond_add.out_y, m.cond_add.out_z, m.cond_add.out_t],
        },
    );
    b.push(Gate::Always, Op::Constancy { base: L.thread_sB_X_base, n: 4 * NUM_LIMBS });

    // ── v12 kA output thread ──
    b.push(
        Gate::Row(L.kA_last_row),
        Op::CurBind {
            dst: vec![L.thread_kA_X_base, L.thread_kA_Y_base, L.thread_kA_Z_base, L.thread_kA_T_base],
            src: vec![m.cond_add.out_x, m.cond_add.out_y, m.cond_add.out_z, m.cond_add.out_t],
        },
    );
    b.push(Gate::Always, Op::Constancy { base: L.thread_kA_X_base, n: 4 * NUM_LIMBS });

    // ── v13 R thread + one_const + mul_R_T ──
    b.push(
        Gate::Row(L.decompress_R_row),
        Op::CurBind {
            dst: vec![L.thread_R_X_base, L.thread_R_Y_base, L.thread_R_Z_base, L.thread_R_T_base],
            src: vec![L.decomp.x_limbs, L.decomp.y_limbs, L.one_const_R_base, L.mul_R_T.c_limbs_base],
        },
    );
    b.push(Gate::Row(L.decompress_R_row), Op::OneConstPin { base: L.one_const_R_base });
    b.push(Gate::Row(L.decompress_R_row), Op::Mul(L.mul_R_T));
    b.push(Gate::Always, Op::Constancy { base: L.thread_R_X_base, n: 4 * NUM_LIMBS });

    // ── v14 residual_1 = sB − R ──
    b.push(Gate::Row(L.residual_row), Op::Cells { base: L.zero_const_R1_base, n: NUM_LIMBS });
    b.sub(Gate::Row(L.residual_row), &L.sub_negR_X);
    b.sub(Gate::Row(L.residual_row), &L.sub_negR_T);
    b.point_add(Gate::Row(L.residual_row), &L.point_add_R1);

    // ── v15 residual_2 = residual_1 − kA ──
    b.sub(Gate::Row(L.residual_row), &L.sub_negkA_X);
    b.sub(Gate::Row(L.residual_row), &L.sub_negkA_T);
    b.point_add(Gate::Row(L.residual_row), &L.point_add_R2);

    // ── v16 residual_2 → dbl_1 input binding ──
    b.push(
        Gate::Row(L.residual_row),
        Op::NxtBind {
            dst: vec![L.dbl_input_X_base, L.dbl_input_Y_base, L.dbl_input_Z_base],
            src: vec![L.point_add_R2.mul_X3.c_limbs_base, L.point_add_R2.mul_Y3.c_limbs_base, L.point_add_R2.mul_Z3.c_limbs_base],
        },
    );

    b.ops
}

/// A strand's native evaluator: the ordered `(Gate, Op)` list for the
/// blocks it owns, with columns remapped to the strand's LOCAL indices.
pub struct StrandNativeEval {
    ops: Vec<(Gate, Op)>,
    n_blocks: usize,
    k_scalar: usize,
    result_row: usize,
    strand_nc: usize,
}

/// Build the native evaluator for strand `s` (owned blocks only, columns
/// remapped to `strand_cols[s]`-local positions).  Asserts block-for-block
/// lockstep against `v16_segments` (same order, same lengths).
pub fn build_strand_native_eval(
    cut: &GwayCut,
    s: usize,
    layout: &VerifyAirLayoutV16,
) -> StrandNativeEval {
    let ops_abs = v16_ops(layout);
    assert_eq!(
        ops_abs.len(),
        cut.segs.len(),
        "v16_ops block count ({}) != v16_segments block count ({})",
        ops_abs.len(),
        cut.segs.len()
    );
    let cols = &cut.strand_cols[s];
    let map = |c: usize| -> usize {
        cols.binary_search(&c).expect("owned block reads a column not held by the strand")
    };
    let mut ops: Vec<(Gate, Op)> = Vec::with_capacity(cut.strand_segs[s].len());
    for &si in &cut.strand_segs[s] {
        let (gate, op) = &ops_abs[si];
        debug_assert_eq!(
            op.len(),
            cut.segs[si].len,
            "op len {} != seg len {} at block {si}",
            op.len(),
            cut.segs[si].len
        );
        ops.push((*gate, op.remap(&map)));
    }
    StrandNativeEval {
        ops,
        n_blocks: layout.n_blocks,
        k_scalar: cut.k_scalar,
        result_row: cut.result_row,
        strand_nc: cut.strand_nc[s],
    }
}

impl StrandNativeEval {
    /// Evaluate the strand's owned constraint blocks against LOCAL row
    /// buffers `cur`/`nxt` (only the strand's held columns, LOCAL order).
    /// Byte-identical to `eval_strand` for the same strand and row.
    pub fn eval(&self, cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
        // Verdict gate at reduced scalar width (matches `eval_strand`).
        if self.k_scalar < 256 && row == self.result_row {
            return vec![F::zero(); self.strand_nc];
        }
        let mut out = Vec::with_capacity(self.strand_nc);
        for (gate, op) in &self.ops {
            if gate.active(row) {
                out.extend(op.eval(cur, nxt, row, self.n_blocks));
            } else {
                out.resize(out.len() + op.len(), F::zero());
            }
        }
        debug_assert_eq!(out.len(), self.strand_nc);
        out
    }
}

// ═══════════════════════════════════════════════════════════════════
//  The cut
// ═══════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct SeamGroup {
    pub holders: Vec<usize>,
    pub cols: Vec<usize>,
}

pub struct GwayCut {
    pub g: usize,
    pub k_scalar: usize,
    pub full_width: usize,
    pub result_row: usize,
    segs: Vec<Seg>,
    /// Per strand: sorted list of held global columns.
    pub strand_cols: Vec<Vec<usize>>,
    /// Per strand: indices into `segs` assigned to it (constraint order).
    strand_segs: Vec<Vec<usize>>,
    /// Per strand: constraint count (Σ owned segs' len).
    pub strand_nc: Vec<usize>,
    /// Distinct seam groups (holder-set-keyed).
    pub seams: Vec<SeamGroup>,
    /// Column-range boundaries (len g+1): strand s owns columns
    /// `[bnd[s], bnd[s+1])` for home-assignment purposes.
    pub bnd: Vec<usize>,
}

impl GwayCut {
    pub fn width(&self, s: usize) -> usize {
        self.strand_cols[s].len()
    }
    fn local(&self, s: usize, c: usize) -> usize {
        self.strand_cols[s]
            .binary_search(&c)
            .expect("seam column must be held by strand")
    }
    fn colstrand(&self, c: usize) -> usize {
        // Largest i with bnd[i] <= c.
        match self.bnd.binary_search(&c) {
            Ok(i) => i.min(self.g - 1),
            Err(i) => (i - 1).min(self.g - 1),
        }
    }
}

/// Build the balanced, phase-overlay-aware G-way cut.
pub fn compute_gway_cut(layout: &VerifyAirLayoutV16, g: usize) -> GwayCut {
    assert!(g >= 2, "G must be ≥ 2");
    let full_width = layout.width;
    let k = layout.k_scalar;

    let mut segs = v16_segments(layout);

    // LOW_END = one past the highest column read by the ATOMIC shared low
    // phases (SHA-512 and scalar-reduce, both homed at column 0 and read as
    // one block).  Snapping the first strand boundary ≥ LOW_END keeps those
    // phases seam-free inside strand 0.  (The format-conversion and
    // point-decompress blocks are split/small, so they need no headroom.)
    let reduce_end = layout.reduce.carry_bits_base + PRODUCT_LIMBS * CARRY_BITS;
    let low_end = SHA512_WIDTH.max(reduce_end);

    // Column-range boundaries: ≈ equal width, first snapped ≥ LOW_END.
    let mut bnd = vec![0usize];
    for i in 1..g {
        let mut b = i * full_width / g;
        if i == 1 {
            b = b.max(low_end);
        }
        b = b.max(bnd[i - 1] + 1).min(full_width);
        bnd.push(b);
    }
    bnd.push(full_width);

    let colstrand = |c: usize| -> usize {
        match bnd.binary_search(&c) {
            Ok(i) => i.min(g - 1),
            Err(i) => (i - 1).min(g - 1),
        }
    };

    // Assign each segment to the strand owning its home column.
    for s in segs.iter_mut() {
        s.strand = colstrand(s.home);
    }

    // Column holders: which strands touch each column.
    let mut holders: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for s in &segs {
        for &c in &s.cols {
            let e = holders.entry(c).or_default();
            if !e.contains(&s.strand) {
                e.push(s.strand);
            }
        }
    }

    let mut strand_cols: Vec<Vec<usize>> = vec![vec![]; g];
    for (&col, hs) in holders.iter() {
        for &s in hs {
            strand_cols[s].push(col);
        }
    }
    for cols in strand_cols.iter_mut() {
        cols.sort_unstable();
        cols.dedup();
    }

    // Seam groups keyed by holder-set (columns held by ≥2 strands).
    let mut group_map: BTreeMap<Vec<usize>, Vec<usize>> = BTreeMap::new();
    for (&col, hs) in holders.iter() {
        if hs.len() >= 2 {
            let mut key = hs.clone();
            key.sort_unstable();
            group_map.entry(key).or_default().push(col);
        }
    }
    let seams: Vec<SeamGroup> = group_map
        .into_iter()
        .map(|(holders, mut cols)| {
            cols.sort_unstable();
            SeamGroup { holders, cols }
        })
        .collect();

    // Per-strand segment indices (constraint/eval order) + constraint counts.
    let mut strand_segs: Vec<Vec<usize>> = vec![vec![]; g];
    let mut strand_nc: Vec<usize> = vec![0; g];
    for (i, s) in segs.iter().enumerate() {
        strand_segs[s.strand].push(i);
        strand_nc[s.strand] += s.len;
    }

    let monolith = verify_v16_per_row_constraints(k);
    let sum: usize = strand_nc.iter().sum();
    assert_eq!(sum, monolith, "Σ strand_nc ({sum}) must equal monolith ({monolith})");

    GwayCut {
        g,
        k_scalar: k,
        full_width,
        result_row: layout.result_row,
        segs,
        strand_cols,
        strand_segs,
        strand_nc,
        seams,
        bnd,
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Per-strand evaluation (HYBRID-SLICE of the verified monolith)
// ═══════════════════════════════════════════════════════════════════

/// Evaluate strand `s`'s constraints on FULL-WIDTH scattered rows by
/// running the verified monolith evaluator and keeping only this strand's
/// assigned constraint slices.  Emits EXACTLY `strand_nc[s]` values.
fn eval_strand(
    cut: &GwayCut,
    s: usize,
    cur: &[F],
    nxt: &[F],
    row: usize,
    layout: &VerifyAirLayoutV16,
) -> Vec<F> {
    // Verdict gate: at reduced scalar width the cofactored verdict cannot
    // hold on a truncated-scalar witness, so the whole result_row is
    // excluded (identically on prover + verifier), matching the bound bench.
    if cut.k_scalar < 256 && row == cut.result_row {
        return vec![F::zero(); cut.strand_nc[s]];
    }
    let full = eval_verify_air_v16_per_row(cur, nxt, row, layout);
    let mut out = Vec::with_capacity(cut.strand_nc[s]);
    for &si in &cut.strand_segs[s] {
        let seg = &cut.segs[si];
        out.extend_from_slice(&full[seg.start..seg.start + seg.len]);
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  DEEP-ALI merge over a strand LDE (copied from the M2 ECDSA pattern)
// ═══════════════════════════════════════════════════════════════════

fn poly_div_zh_local(dividend: &[F], m: usize) -> Vec<F> {
    let n = dividend.len();
    if n <= m {
        return vec![F::zero()];
    }
    let q_len = n - m;
    let mut q = vec![F::zero(); q_len];
    for k in (m..n).rev() {
        let qk = if k < q_len { q[k] } else { F::zero() };
        q[k - m] = dividend[k] + qk;
    }
    q
}

fn strand_merge<E>(
    lde: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    comb_coeffs: &[F],
    full_width: usize,
    cols: &[usize],
    eval_on_full: E,
) -> Vec<F>
where
    E: Fn(&[F], &[F], usize) -> Vec<F> + Sync,
{
    let n = n_trace * blowup;
    let kc = comb_coeffs.len();
    for col in lde {
        assert_eq!(col.len(), n);
    }
    let eval_at = |fc: &mut Vec<F>, fx: &mut Vec<F>, i: usize| -> F {
        let nxt_idx = (i + blowup) % n;
        for (j, &c) in cols.iter().enumerate() {
            fc[c] = lde[j][i];
            fx[c] = lde[j][nxt_idx];
        }
        let cvals = eval_on_full(fc, fx, i / blowup);
        debug_assert_eq!(cvals.len(), kc);
        let mut acc = F::zero();
        for j in 0..kc {
            acc += comb_coeffs[j] * cvals[j];
        }
        acc
    };
    let mk_bufs = || (vec![F::zero(); full_width], vec![F::zero(); full_width]);

    #[cfg(feature = "parallel")]
    let phi_eval: Vec<F> = (0..n)
        .into_par_iter()
        .map_init(mk_bufs, |(fc, fx), i| eval_at(fc, fx, i))
        .collect();
    #[cfg(not(feature = "parallel"))]
    let phi_eval: Vec<F> = {
        let (mut fc, mut fx) = mk_bufs();
        (0..n).map(|i| eval_at(&mut fc, &mut fx, i)).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh_local(&phi_coeffs, n_trace);
    let mut padded = c_coeffs;
    padded.resize(n, F::zero());
    domain.fft(&padded)
}

/// NATIVE merge — identical `c_eval` to `strand_merge` but WITHOUT the
/// full-width scatter buffer and WITHOUT the full 70_606-constraint Vec.
///
/// Per LDE point it fills a NARROW local buffer (`cols.len()` wide, = the
/// strand's own width) and runs the strand's native evaluator (owned
/// blocks only), producing exactly `strand_nc` values.  The IFFT/÷Z_H/FFT
/// tail is bit-identical to `strand_merge`, so the emitted `c_eval` is
/// byte-for-byte equal (verified by `native_eval_matches_hybrid`).
fn strand_merge_native(
    lde: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    comb_coeffs: &[F],
    width: usize,
    native: &StrandNativeEval,
) -> Vec<F> {
    let n = n_trace * blowup;
    let kc = comb_coeffs.len();
    for col in lde {
        assert_eq!(col.len(), n);
    }
    let eval_at = |lc: &mut Vec<F>, lx: &mut Vec<F>, i: usize| -> F {
        let nxt_idx = (i + blowup) % n;
        for j in 0..width {
            lc[j] = lde[j][i];
            lx[j] = lde[j][nxt_idx];
        }
        let cvals = native.eval(lc, lx, i / blowup);
        debug_assert_eq!(cvals.len(), kc);
        let mut acc = F::zero();
        for j in 0..kc {
            acc += comb_coeffs[j] * cvals[j];
        }
        acc
    };
    // NARROW per-thread buffers (strand width), NOT full_width.
    let mk_bufs = || (vec![F::zero(); width], vec![F::zero(); width]);

    #[cfg(feature = "parallel")]
    let phi_eval: Vec<F> = (0..n)
        .into_par_iter()
        .map_init(mk_bufs, |(lc, lx), i| eval_at(lc, lx, i))
        .collect();
    #[cfg(not(feature = "parallel"))]
    let phi_eval: Vec<F> = {
        let (mut lc, mut lx) = mk_bufs();
        (0..n).map(|i| eval_at(&mut lc, &mut lx, i)).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh_local(&phi_coeffs, n_trace);
    let mut padded = c_coeffs;
    padded.resize(n, F::zero());
    domain.fft(&padded)
}

/// `NATIVE_EVAL=1` selects the native per-strand evaluator in the prover.
pub fn native_eval_enabled() -> bool {
    std::env::var("NATIVE_EVAL").ok().as_deref() == Some("1")
}

// ═══════════════════════════════════════════════════════════════════
//  Proof bundle
// ═══════════════════════════════════════════════════════════════════

pub struct StrandedProofG {
    pub proofs: Vec<SubAirProofWithTrace>,
    pub seam_commits: Vec<Vec<(usize, Vec<BindingCellsCommit>)>>,
}

pub fn strand_domain(s: usize) -> Vec<u8> {
    let mut v = b"ed25519_verify_stranded_gway/strand/".to_vec();
    v.extend_from_slice(&(s as u32).to_le_bytes());
    v
}

/// Prove one strand (given ITS trace = only its held columns) and commit
/// every seam group it holds.
pub fn prove_one_strand<P>(
    strand_trace: &[Vec<F>],
    cut: &GwayCut,
    s: usize,
    layout: &VerifyAirLayoutV16,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    params_fn: P,
) -> (SubAirProofWithTrace, Vec<(usize, Vec<BindingCellsCommit>)>)
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    let cols = &cut.strand_cols[s];
    // NATIVE_EVAL=1 → narrow-buffer native evaluator (no full-width scatter,
    // no 70_606-element Vec).  Default → verified hybrid-slice path.
    let native = if native_eval_enabled() {
        Some(build_strand_native_eval(cut, s, layout))
    } else {
        None
    };
    let width = cols.len();
    let (proof, lde, _tree) = prove_one_sub_air_with_trace_capturing(
        strand_trace,
        n_trace,
        blowup,
        pi_hash,
        domain_sep,
        cut.strand_nc[s],
        |lde, nt, bw, cc| {
            if let Some(native) = &native {
                strand_merge_native(lde, nt, bw, cc, width, native)
            } else {
                strand_merge(lde, nt, bw, cc, cut.full_width, cols, |c, x, r| {
                    eval_strand(cut, s, c, x, r, layout)
                })
            }
        },
        params_fn,
    );

    let mut commits = Vec::new();
    for (gid, sg) in cut.seams.iter().enumerate() {
        if !sg.holders.contains(&s) {
            continue;
        }
        let col_commits: Vec<BindingCellsCommit> = sg
            .cols
            .iter()
            .map(|&c| {
                commit_binding_cells(
                    &lde, &[cut.local(s, c)], n_trace, blowup, pi_hash, SEAM_SEP, params_fn,
                )
                .0
            })
            .collect();
        commits.push((gid, col_commits));
    }
    (proof, commits)
}

/// Verify one strand's sub-AIR proof (FRI + per-query constraint check).
pub fn verify_one_strand<P>(
    proof: &SubAirProofWithTrace,
    cut: &GwayCut,
    s: usize,
    layout: &VerifyAirLayoutV16,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams,
{
    let cols = cut.strand_cols[s].clone();
    verify_one_sub_air_with_trace(
        proof,
        n_trace,
        blowup,
        pi_hash,
        domain_sep,
        cut.width(s),
        cut.strand_nc[s],
        |cur_local, nxt_local, row| {
            let w = cut.full_width;
            let mut cur = vec![F::zero(); w];
            let mut nxt = vec![F::zero(); w];
            for (j, &c) in cols.iter().enumerate() {
                cur[c] = cur_local[j];
                nxt[c] = nxt_local[j];
            }
            eval_strand(cut, s, &cur, &nxt, row, layout)
        },
        params_fn,
    )
    .map_err(|e| format!("strand {s}: {e}"))
}

/// Verify all seam groups: every group's columns must OOD-agree across all
/// strands holding them (reference = holders[0]).
pub fn verify_seams<P>(
    proof: &StrandedProofG,
    cut: &GwayCut,
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    let find = |s: usize, gid: usize| -> Option<&Vec<BindingCellsCommit>> {
        proof.seam_commits[s].iter().find(|(g, _)| *g == gid).map(|(_, c)| c)
    };
    for (gid, sg) in cut.seams.iter().enumerate() {
        let refs = sg.holders[0];
        let ref_commits = find(refs, gid)
            .ok_or_else(|| format!("seam group {gid}: missing ref commits (strand {refs})"))?;
        for &h in &sg.holders[1..] {
            let hc = find(h, gid)
                .ok_or_else(|| format!("seam group {gid}: missing commits (strand {h})"))?;
            if ref_commits.len() != hc.len() || hc.len() != sg.cols.len() {
                return Err(format!("seam group {gid}: commit-count mismatch"));
            }
            for (j, (ca, cb)) in ref_commits.iter().zip(hc.iter()).enumerate() {
                verify_ood_consistency(ca, cb, pi_hash, params_fn).map_err(|e| {
                    format!("seam group {gid} col {} (strands {refs}~{h}): {e}", sg.cols[j])
                })?;
            }
        }
    }
    Ok(())
}

/// Verify a full spliced G-way proof.
pub fn verify_stranded_g<P>(
    proof: &StrandedProofG,
    cut: &GwayCut,
    layout: &VerifyAirLayoutV16,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    for s in 0..cut.g {
        let sep = strand_domain(s);
        verify_one_strand(
            &proof.proofs[s], cut, s, layout, n_trace, blowup, pi_hash, &sep, params_fn,
        )?;
    }
    verify_seams(proof, cut, pi_hash, params_fn)?;
    Ok(())
}

/// Extract strand `s`'s columns from a full trace.
pub fn extract_strand(full: &[Vec<F>], cut: &GwayCut, s: usize) -> Vec<Vec<F>> {
    cut.strand_cols[s].iter().map(|&c| full[c].clone()).collect()
}

// ═══════════════════════════════════════════════════════════════════
//  Tests (small k_scalar, run --release)
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ed25519_scalar::reduce_mod_l_wide;
    use crate::ed25519_verify_air::{fill_verify_air_v16, r_thread_bits_for_kA};
    use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
    use curve25519_dalek::scalar::Scalar;
    use rand::{Rng, SeedableRng};
    use sha2::{Digest as _, Sha512};

    fn tparams(n0: usize, ph: [u8; 32]) -> DeepFriParams {
        DeepFriParams {
            schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
            r: 8,
            seed_z: 0xDEEFu64,
            coeff_commit_final: true,
            d_final: 1,
            stir: false,
            s0: 8,
            public_inputs_hash: Some(ph),
        }
    }

    fn rand_scalar(rng: &mut rand::rngs::StdRng) -> Scalar {
        let mut b = [0u8; 32];
        rng.fill(&mut b[..]);
        Scalar::from_bytes_mod_order(b)
    }

    /// Build a real (verdict-gated at k<256) Ed25519 v16 trace at scalar
    /// width `k_scalar`, padded to n_trace.
    fn build_case(k_scalar: usize) -> (VerifyAirLayoutV16, Vec<Vec<F>>, usize) {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xED25519_ABCD);
        let a = rand_scalar(&mut rng);
        let a_point = ED25519_BASEPOINT_POINT * a;
        let a_pub: [u8; 32] = a_point.compress().to_bytes();
        let r_n = rand_scalar(&mut rng);
        let r_point = ED25519_BASEPOINT_POINT * r_n;
        let r_pub: [u8; 32] = r_point.compress().to_bytes();
        let m: &[u8] = b"stranded gway ed25519 test";

        let mut input = Vec::new();
        input.extend_from_slice(&r_pub);
        input.extend_from_slice(&a_pub);
        input.extend_from_slice(m);
        let digest: [u8; 64] = Sha512::digest(&input).into();
        let k_canonical = reduce_mod_l_wide(&digest);
        let k_dalek: Scalar =
            Option::from(Scalar::from_canonical_bytes(k_canonical)).unwrap();
        let s = r_n + k_dalek * a;
        let s_canonical: [u8; 32] = s.to_bytes();

        let s_bits = r_thread_bits_for_kA(&s_canonical, k_scalar);
        let k_bits = r_thread_bits_for_kA(&k_canonical, k_scalar);

        let (trace, layout, _k) =
            fill_verify_air_v16(&input, &r_pub, &a_pub, &s_bits, &k_bits).expect("v16 fill");
        let n_trace = layout.height.next_power_of_two();
        let padded: Vec<Vec<F>> = trace
            .into_iter()
            .map(|mut c| {
                c.resize(n_trace, F::zero());
                c
            })
            .collect();
        (layout, padded, n_trace)
    }

    /// Σ strand_nc == monolith, for several G.
    #[test]
    fn gway_cut_complete() {
        let (layout, _trace, _n) = build_case(8);
        let mono = verify_v16_per_row_constraints(layout.k_scalar);
        for g in [2usize, 4, 8, 16] {
            let cut = compute_gway_cut(&layout, g);
            let sum: usize = cut.strand_nc.iter().sum();
            assert_eq!(sum, mono, "G={g}: Σ strand_nc != monolith");
        }
    }

    /// Full stranded prove/verify + tamper-reject at small k, G=4.
    #[test]
    fn gway_honest_accepts_tampers_reject() {
        let g = 4usize;
        let blowup = 4usize;
        let (layout, trace, n_trace) = build_case(8);
        let cut = compute_gway_cut(&layout, g);
        let pi_hash = [0x42u8; 32];
        let params = |n0: usize, ph: [u8; 32]| tparams(n0, ph);

        let prove_all = |trace: &[Vec<F>]| -> StrandedProofG {
            let mut proofs = Vec::with_capacity(g);
            let mut seam_commits = Vec::with_capacity(g);
            for s in 0..g {
                let strand = extract_strand(trace, &cut, s);
                let sep = strand_domain(s);
                let (p, c) = prove_one_strand(
                    &strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params,
                );
                proofs.push(p);
                seam_commits.push(c);
            }
            StrandedProofG { proofs, seam_commits }
        };

        let proof = prove_all(&trace);
        verify_stranded_g(&proof, &cut, &layout, n_trace, blowup, pi_hash, params)
            .expect("honest G-way proof must accept");

        let seam_cols: std::collections::BTreeSet<usize> =
            cut.seams.iter().flat_map(|sg| sg.cols.iter().copied()).collect();

        // Interior tamper per strand.
        for s in 0..g {
            let interior = cut.strand_cols[s]
                .iter()
                .copied()
                .find(|c| !seam_cols.contains(c));
            let Some(col) = interior else { continue };
            let mut bad = trace.clone();
            for row in 0..n_trace {
                bad[col][row] += F::from(1u64);
            }
            let strand = extract_strand(&bad, &cut, s);
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(
                &strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params,
            );
            let mut proofs = proof.proofs.clone();
            let mut sc = proof.seam_commits.clone();
            proofs[s] = ps;
            sc[s] = cs;
            let spliced = StrandedProofG { proofs, seam_commits: sc };
            let res = verify_stranded_g(&spliced, &cut, &layout, n_trace, blowup, pi_hash, params);
            assert!(res.is_err(), "interior tamper in strand {s} (col {col}) must reject");
        }

        // Seam-group tamper (incl. transition seams).
        for (gid, sg) in cut.seams.iter().enumerate() {
            let s = sg.holders[0];
            let col = sg.cols[0];
            let mut bad = trace.clone();
            for row in 0..n_trace {
                bad[col][row] += F::from(1u64);
            }
            let strand = extract_strand(&bad, &cut, s);
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(
                &strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params,
            );
            let mut proofs = proof.proofs.clone();
            let mut sc = proof.seam_commits.clone();
            proofs[s] = ps;
            sc[s] = cs;
            let spliced = StrandedProofG { proofs, seam_commits: sc };
            let res = verify_stranded_g(&spliced, &cut, &layout, n_trace, blowup, pi_hash, params);
            assert!(res.is_err(), "seam group {gid} tamper (col {col}) must reject");
        }
    }

    /// Concatenate every `v16_ops` block's gated output (ABSOLUTE columns,
    /// full-width buffer) — must reproduce `eval_verify_air_v16_per_row`.
    /// Validates the native transcription independent of the strand cut.
    #[test]
    fn native_ops_reproduce_monolith() {
        let (layout, trace, n_trace) = build_case(8);
        let ops = super::v16_ops(&layout);
        let w = layout.width;
        for row in 0..n_trace - 1 {
            let cur: Vec<F> = (0..w).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..w).map(|c| trace[c][row + 1]).collect();
            let mut native = Vec::new();
            for (gate, op) in &ops {
                if gate.active(row) {
                    native.extend(op.eval(&cur, &nxt, row, layout.n_blocks));
                } else {
                    native.resize(native.len() + op.len(), F::zero());
                }
            }
            let mono = eval_verify_air_v16_per_row(&cur, &nxt, row, &layout);
            assert_eq!(
                native.len(),
                mono.len(),
                "length mismatch at row {row}: native {} vs monolith {}",
                native.len(),
                mono.len()
            );
            for (i, (a, b)) in native.iter().zip(mono.iter()).enumerate() {
                assert_eq!(a, b, "native op #{i} != monolith at row {row}");
            }
        }
    }

    /// LDE one strand's columns onto the size-`n` evaluation domain (the
    /// natural domain the sub-AIR prover extends over).
    fn lde_strand(strand_trace: &[Vec<F>], n_trace: usize, blowup: usize) -> Vec<Vec<F>> {
        let n = n_trace * blowup;
        let dt = GeneralEvaluationDomain::<F>::new(n_trace).unwrap();
        let dn = GeneralEvaluationDomain::<F>::new(n).unwrap();
        strand_trace
            .iter()
            .map(|col| {
                let mut coeffs = dt.ifft(col);
                coeffs.resize(n, F::zero());
                dn.fft(&coeffs)
            })
            .collect()
    }

    /// ★ MANDATORY SOUNDNESS GUARD.  For G∈{4,8} (k_scalar=8) the NATIVE
    /// per-strand evaluator's output is BYTE-IDENTICAL to the hybrid-slice
    /// evaluator, for EVERY strand and EVERY LDE point.  Identical
    /// per-point constraint values ⇒ identical `c_eval` ⇒ identical proofs
    /// ⇒ all existing soundness gates preserved by construction.
    #[test]
    fn native_eval_matches_hybrid() {
        let blowup = 4usize;
        let (layout, trace, n_trace) = build_case(8);
        let n = n_trace * blowup;
        let w = layout.width;

        for g in [4usize, 8] {
            let cut = compute_gway_cut(&layout, g);
            for s in 0..g {
                let native = build_strand_native_eval(&cut, s, &layout);
                let strand_trace = extract_strand(&trace, &cut, s);
                let lde = lde_strand(&strand_trace, n_trace, blowup);
                let cols = &cut.strand_cols[s];
                let width = cols.len();

                // Reusable full-width + narrow scratch buffers.
                let mut fc = vec![F::zero(); w];
                let mut fx = vec![F::zero(); w];
                let mut lc = vec![F::zero(); width];
                let mut lx = vec![F::zero(); width];

                for i in 0..n {
                    let row = i / blowup;
                    let nxt_idx = (i + blowup) % n;
                    for (j, &c) in cols.iter().enumerate() {
                        fc[c] = lde[j][i];
                        fx[c] = lde[j][nxt_idx];
                        lc[j] = lde[j][i];
                        lx[j] = lde[j][nxt_idx];
                    }
                    let hy = eval_strand(&cut, s, &fc, &fx, row, &layout);
                    let na = native.eval(&lc, &lx, row);
                    assert_eq!(
                        hy.len(),
                        na.len(),
                        "G={g} strand {s} point {i}: length mismatch"
                    );
                    if hy != na {
                        let bad = hy
                            .iter()
                            .zip(na.iter())
                            .position(|(a, b)| a != b)
                            .unwrap();
                        panic!(
                            "G={g} strand {s} point {i} (row {row}): NATIVE != HYBRID at \
                             constraint #{bad}: hybrid={:?} native={:?}",
                            hy[bad], na[bad]
                        );
                    }
                }
            }
        }
    }
}
