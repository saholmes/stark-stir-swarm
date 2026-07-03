// ecdsa_verify_stranded_gway.rs — BALANCED G-WAY low-memory "stranded"
// PROVER for the END-TO-END P256 ECDSA-verify AIR.
//
// ## What this is (M2 — generalises the M1 2-strand PoC)
//
// The monolithic verify AIR has ~196k columns.  Proving it in one shot
// LDEs the whole trace → ~5.9 GB peak RSS at blowup=4.  M1 split it into
// TWO column-group strands, but the cut was unbalanced (strand B = 61%
// width) and the bench built the full trace then cloned, so peak RSS did
// not drop.
//
// M2 fixes BOTH:
//
//  1. BALANCED CUT.  The AIR is a DAG of *leaf field-gadgets*
//     (mul / add / sub / freeze / select).  Each leaf reads ONLY its
//     input-limb columns (a_limbs, b_limbs, and sel_cell for select) and
//     writes ONLY its own contiguous owned block; its constraint
//     evaluator (`eval_mul_gadget`, …) touches nothing else.  We
//     enumerate every leaf gadget, every primary column block
//     (acc / base / bit / r_proj / r / n / the curve-constant b blocks),
//     and every glue-constraint group (the DSM boundary / acc-transition
//     / r_proj-constancy / public-input pins / tail equalities), then
//     BIN-PACK them into G groups of ≈equal owned width by walking the
//     units in column order and snapping the G-1 boundaries to whole-unit
//     (= gadget) edges.  No constraint is ever split across strands: a
//     leaf gadget's constraints are emitted entirely in the strand that
//     owns the gadget.
//
//  2. SEAMS.  A column present in ≥2 strands (a leaf output consumed by a
//     gadget in another strand, or a shared primary input) is a SEAM.
//     Every seam column is bound across the strands holding it via
//     `commit_binding_cells` + `verify_ood_consistency` (the same tested
//     v2 OOD pattern M1 used for `r_a_proj`).  Seam columns that share the
//     exact same holder-set are packed into ONE binding commitment per
//     holder, so the seam-commit count is O(#distinct holder-sets), not
//     O(#seam columns).
//
// ## Soundness
//
//  * Each strand is a standard `sub_air_with_trace` proof: trace-LDE
//    Merkle commitment bound into pi_hash, per-query trace openings,
//    per-query `c_eval·Z_H == Σ α_j Φ_j` re-check.  Tampering any interior
//    witness cell makes some Φ_j non-zero on H → that strand's FRI /
//    per-query check rejects.
//  * Every shared column is OOD-bound at a common FS point z_0.  If two
//    strands disagree on a seam column as polynomials, the OOD check
//    rejects (Schwartz-Zippel over F_ext).  Hence the union of strands
//    behaves exactly as the monolith over the shared columns.
//  * CONSTRAINT COMPLETENESS is structural: every monolith constraint
//    belongs to exactly one unit, each unit is assigned to exactly one
//    strand, so Σ_g num_constraints_g == monolith total by construction
//    (asserted in `compute_gway_cut`).
//
// This module adds NO change to the AIR, its evaluator, its filler, or
// the verifier core — it only orchestrates existing primitives.  The leaf
// evaluators (`eval_mul_gadget`, `eval_add_gadget`, …) are reused verbatim
// via a full-width scatter, exactly as M1 reused `eval_scalar_mul_step`.

#![allow(non_snake_case, clippy::too_many_arguments, clippy::type_complexity)]

use std::collections::BTreeMap;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::p256_field::NUM_LIMBS;
use crate::p256_field_air::{
    eval_add_gadget, eval_freeze_gadget, eval_mul_gadget, eval_select_gadget,
    eval_sub_gadget, AddGadgetLayout, FreezeGadgetLayout, MulGadgetLayout,
    SelectGadgetLayout, SubGadgetLayout, ADD_GADGET_CONSTRAINTS,
    ADD_GADGET_OWNED_CELLS, ELEMENT_CELLS, FREEZE_GADGET_CONSTRAINTS,
    FREEZE_GADGET_OWNED_CELLS, MUL_GADGET_CONSTRAINTS, MUL_GADGET_OWNED_CELLS,
    SELECT_GADGET_CONSTRAINTS, SUB_GADGET_CONSTRAINTS, SUB_GADGET_OWNED_CELLS,
};
use crate::p256_group_air::{GroupAddGadgetLayout, GroupDoubleGadgetLayout};
use crate::p256_scalar_mul_air::ScalarMulStepGadgetLayout;
use crate::p256_ecdsa_verify_multirow_air::{
    ecdsa_verify_multirow_constraints, order_n_field, EcdsaVerifyMultirowLayout,
    EcdsaVerifyPublicInputs,
};
use crate::binding_cells_commit::{
    commit_binding_cells, verify_ood_consistency, BindingCellsCommit,
};
use crate::fri::DeepFriParams;
use crate::sub_air_with_trace::{
    prove_one_sub_air_with_trace_capturing, verify_one_sub_air_with_trace,
    SubAirProofWithTrace,
};

/// One shared FS separator on every seam so all strands' OOD points
/// align (per-group commits share `seed_z`, `n0`, `pi_hash`, sep).
pub const SEAM_SEP: &[u8] = b"ecdsa_verify_stranded_gway/seam/v1";

/// Owned c-limb+c-bit block of a select gadget (270); the `sel_cell` is
/// a *read*, not owned (it is a shared primary column: the scalar bit, or
/// the tail's dedicated selector column).
const SELECT_OWNED_CELLS: usize = ELEMENT_CELLS; // 270

// ═══════════════════════════════════════════════════════════════════
//  Units
// ═══════════════════════════════════════════════════════════════════

/// Row-gate for a unit's constraints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Gate {
    /// Leaf gadget in a scalar-mult chain: fires on chain rows (row < k).
    InChain,
    /// Leaf gadget in the verify tail: fires on the tail row (row == k).
    IsTail,
    /// A glue-constraint group (its own internal gating).
    Glue,
    /// A pure column carrier (no constraints).
    None,
}

/// What a unit *is* — determines how its constraints are evaluated.
#[derive(Clone, Debug)]
enum Kind {
    Mul(MulGadgetLayout),
    Add(AddGadgetLayout),
    Sub(SubGadgetLayout),
    Freeze(FreezeGadgetLayout),
    Select(SelectGadgetLayout),
    /// Pure column carrier (primary input / constant-b block).
    Cols,
    // ── glue groups (own no columns) ──
    BoundaryA,
    AccTransA,
    RprojConstA,
    PinsA,
    BoundaryB,
    AccTransB,
    RprojConstB,
    PinsB,
    TailRxEq,
    TailNConst,
    PinR,
}

/// A schedulable unit: a leaf gadget, a primary-column block, or a glue
/// group.  `owned` is a contiguous column range this unit exclusively
/// produces; `reads` are the (external) columns its constraints read.
#[derive(Clone, Debug)]
struct Unit {
    kind: Kind,
    gate: Gate,
    /// (base, len) of the owned contiguous column block (len 0 for glue).
    owned: (usize, usize),
    /// External columns read by this unit's constraints (for seams).
    reads: Vec<usize>,
    /// Number of constraint slots this unit emits.
    nc: usize,
    /// Sort key (column position): min owned col, or min read col.
    pos: usize,
    /// Assigned strand (filled by bin-packing).
    strand: usize,
}

fn limb_range(base: usize) -> Vec<usize> {
    (base..base + NUM_LIMBS).collect()
}

fn leaf_mul(m: &MulGadgetLayout, gate: Gate) -> Unit {
    let mut reads = limb_range(m.a_limbs_base);
    reads.extend(limb_range(m.b_limbs_base));
    Unit {
        kind: Kind::Mul(*m),
        gate,
        owned: (m.c_limbs_base, MUL_GADGET_OWNED_CELLS),
        reads,
        nc: MUL_GADGET_CONSTRAINTS,
        pos: m.c_limbs_base,
        strand: 0,
    }
}
fn leaf_add(a: &AddGadgetLayout, gate: Gate) -> Unit {
    let mut reads = limb_range(a.a_limbs_base);
    reads.extend(limb_range(a.b_limbs_base));
    Unit {
        kind: Kind::Add(*a),
        gate,
        owned: (a.c_limbs_base, ADD_GADGET_OWNED_CELLS),
        reads,
        nc: ADD_GADGET_CONSTRAINTS,
        pos: a.c_limbs_base,
        strand: 0,
    }
}
fn leaf_sub(s: &SubGadgetLayout, gate: Gate) -> Unit {
    let mut reads = limb_range(s.a_limbs_base);
    reads.extend(limb_range(s.b_limbs_base));
    Unit {
        kind: Kind::Sub(*s),
        gate,
        owned: (s.c_limbs_base, SUB_GADGET_OWNED_CELLS),
        reads,
        nc: SUB_GADGET_CONSTRAINTS,
        pos: s.c_limbs_base,
        strand: 0,
    }
}
fn leaf_freeze(fz: &FreezeGadgetLayout, gate: Gate) -> Unit {
    Unit {
        kind: Kind::Freeze(*fz),
        gate,
        owned: (fz.diff_limbs_base, FREEZE_GADGET_OWNED_CELLS),
        reads: limb_range(fz.a_limbs_base),
        nc: FREEZE_GADGET_CONSTRAINTS,
        pos: fz.diff_limbs_base,
        strand: 0,
    }
}
fn leaf_select(sl: &SelectGadgetLayout, gate: Gate) -> Unit {
    let mut reads = limb_range(sl.a_limbs_base);
    reads.extend(limb_range(sl.b_limbs_base));
    reads.push(sl.sel_cell);
    Unit {
        kind: Kind::Select(*sl),
        gate,
        owned: (sl.c_limbs_base, SELECT_OWNED_CELLS),
        reads,
        nc: SELECT_GADGET_CONSTRAINTS,
        pos: sl.c_limbs_base,
        strand: 0,
    }
}
fn cols_unit(base: usize, len: usize) -> Unit {
    Unit {
        kind: Kind::Cols,
        gate: Gate::None,
        owned: (base, len),
        reads: vec![],
        nc: 0,
        pos: base,
        strand: 0,
    }
}
fn glue(kind: Kind, nc: usize, reads: Vec<usize>) -> Unit {
    let pos = reads.iter().copied().min().unwrap_or(0);
    Unit { kind, gate: Gate::Glue, owned: (0, 0), reads, nc, pos, strand: 0 }
}

fn push_double_leaves(units: &mut Vec<Unit>, d: &GroupDoubleGadgetLayout, gate: Gate) {
    units.push(cols_unit(d.b_base, ELEMENT_CELLS));
    for m in &d.muls {
        units.push(leaf_mul(m, gate));
    }
    for a in &d.adds {
        units.push(leaf_add(a, gate));
    }
    for s in &d.subs {
        units.push(leaf_sub(s, gate));
    }
    for fz in d.freezes_after_adds.iter().chain(d.freezes_after_subs.iter()) {
        units.push(leaf_freeze(fz, gate));
    }
}
fn push_add_leaves(units: &mut Vec<Unit>, ga: &GroupAddGadgetLayout, gate: Gate) {
    units.push(cols_unit(ga.b_base, ELEMENT_CELLS));
    for m in &ga.muls {
        units.push(leaf_mul(m, gate));
    }
    for a in &ga.adds {
        units.push(leaf_add(a, gate));
    }
    for s in &ga.subs {
        units.push(leaf_sub(s, gate));
    }
    for fz in ga.freezes_after_adds.iter().chain(ga.freezes_after_subs.iter()) {
        units.push(leaf_freeze(fz, gate));
    }
}
fn push_step_leaves(units: &mut Vec<Unit>, step: &ScalarMulStepGadgetLayout) {
    push_double_leaves(units, &step.double_layout, Gate::InChain);
    push_add_leaves(units, &step.add_layout, Gate::InChain);
    units.push(leaf_select(&step.select_x, Gate::InChain));
    units.push(leaf_select(&step.select_y, Gate::InChain));
    units.push(leaf_select(&step.select_z, Gate::InChain));
}

// ═══════════════════════════════════════════════════════════════════
//  The cut
// ═══════════════════════════════════════════════════════════════════

/// A group of seam columns that are all held by the SAME set of strands.
#[derive(Clone, Debug)]
pub struct SeamGroup {
    /// Strands holding these columns (sorted, len ≥ 2).
    pub holders: Vec<usize>,
    /// Global column indices in this group (sorted).
    pub cols: Vec<usize>,
}

/// The complete G-way partition.
pub struct GwayCut {
    pub g: usize,
    pub k: usize,
    pub full_width: usize,
    units: Vec<Unit>,
    /// Per strand: sorted list of held global columns.
    pub strand_cols: Vec<Vec<usize>>,
    /// Per strand: indices into `units` assigned to it (constraint order).
    strand_units: Vec<Vec<usize>>,
    /// Per strand: constraint count (Σ owned units' nc).
    pub strand_nc: Vec<usize>,
    /// Distinct seam groups (holder-set-keyed).
    pub seams: Vec<SeamGroup>,
}

impl GwayCut {
    pub fn width(&self, s: usize) -> usize {
        self.strand_cols[s].len()
    }
    /// Local index of global column `c` within strand `s` (binary search).
    fn local(&self, s: usize, c: usize) -> usize {
        self.strand_cols[s]
            .binary_search(&c)
            .expect("seam column must be held by strand")
    }
}

/// Build the balanced G-way cut from the verify-AIR layout.
pub fn compute_gway_cut(layout: &EcdsaVerifyMultirowLayout, k: usize, g: usize) -> GwayCut {
    assert!(g >= 2, "G must be ≥ 2");
    let d = &layout.dsm;
    let full_width = layout.width;
    let ra = 3 * NUM_LIMBS;

    let mut units: Vec<Unit> = Vec::new();

    // ── primary column blocks ──
    units.push(cols_unit(d.step_a.acc_x_base, 3 * NUM_LIMBS)); // acc_a (x,y,z)
    units.push(cols_unit(d.step_a.base_x_base, 3 * NUM_LIMBS)); // base_a
    units.push(cols_unit(d.step_a.bit_cell, 1)); // bit_a
    // chain-A step leaves
    push_step_leaves(&mut units, &d.step_a);

    units.push(cols_unit(d.step_b.acc_x_base, 3 * NUM_LIMBS)); // acc_b
    units.push(cols_unit(d.step_b.base_x_base, 3 * NUM_LIMBS)); // base_b
    units.push(cols_unit(d.step_b.bit_cell, 1)); // bit_b
    push_step_leaves(&mut units, &d.step_b);

    units.push(cols_unit(d.r_a_proj_x_base, ra)); // r_a_proj (seam producer)
    units.push(cols_unit(d.r_b_proj_x_base, ra)); // r_b_proj

    // ── tail leaves ──
    push_add_leaves(&mut units, &layout.group_add, Gate::IsTail);
    units.push(cols_unit(layout.r_base, NUM_LIMBS)); // r
    units.push(cols_unit(layout.n_const_base, NUM_LIMBS)); // n
    units.push(leaf_add(&layout.add_rn, Gate::IsTail));
    units.push(leaf_freeze(&layout.freeze_rn, Gate::IsTail));
    units.push(leaf_mul(&layout.mul_r, Gate::IsTail));
    units.push(leaf_mul(&layout.mul_rn, Gate::IsTail));
    units.push(cols_unit(layout.select.sel_cell, 1)); // tail selector column
    units.push(leaf_select(&layout.select, Gate::IsTail));

    // ── glue-constraint groups ──
    // Boundary A: bind select_a → r_a_proj at row k-1.
    let sel_a: Vec<usize> = [
        d.step_a.select_x.c_limbs_base,
        d.step_a.select_y.c_limbs_base,
        d.step_a.select_z.c_limbs_base,
    ]
    .iter()
    .flat_map(|&b| limb_range(b))
    .collect();
    let rproj_a: Vec<usize> = [d.r_a_proj_x_base, d.r_a_proj_y_base, d.r_a_proj_z_base]
        .iter()
        .flat_map(|&b| limb_range(b))
        .collect();
    let acc_a: Vec<usize> = [d.step_a.acc_x_base, d.step_a.acc_y_base, d.step_a.acc_z_base]
        .iter()
        .flat_map(|&b| limb_range(b))
        .collect();
    {
        let mut r = sel_a.clone();
        r.extend(rproj_a.iter().copied());
        units.push(glue(Kind::BoundaryA, 3 * NUM_LIMBS, r));
        let mut r = acc_a.clone();
        r.extend(sel_a.iter().copied());
        units.push(glue(Kind::AccTransA, 3 * NUM_LIMBS, r));
        units.push(glue(Kind::RprojConstA, 3 * NUM_LIMBS, rproj_a.clone()));
        let mut r = vec![d.step_a.bit_cell];
        r.extend(limb_range(d.step_a.base_x_base));
        r.extend(limb_range(d.step_a.base_y_base));
        units.push(glue(Kind::PinsA, 1 + 2 * NUM_LIMBS, r));
    }
    let sel_b: Vec<usize> = [
        d.step_b.select_x.c_limbs_base,
        d.step_b.select_y.c_limbs_base,
        d.step_b.select_z.c_limbs_base,
    ]
    .iter()
    .flat_map(|&b| limb_range(b))
    .collect();
    let rproj_b: Vec<usize> = [d.r_b_proj_x_base, d.r_b_proj_y_base, d.r_b_proj_z_base]
        .iter()
        .flat_map(|&b| limb_range(b))
        .collect();
    let acc_b: Vec<usize> = [d.step_b.acc_x_base, d.step_b.acc_y_base, d.step_b.acc_z_base]
        .iter()
        .flat_map(|&b| limb_range(b))
        .collect();
    {
        let mut r = sel_b.clone();
        r.extend(rproj_b.iter().copied());
        units.push(glue(Kind::BoundaryB, 3 * NUM_LIMBS, r));
        let mut r = acc_b.clone();
        r.extend(sel_b.iter().copied());
        units.push(glue(Kind::AccTransB, 3 * NUM_LIMBS, r));
        units.push(glue(Kind::RprojConstB, 3 * NUM_LIMBS, rproj_b.clone()));
        let mut r = vec![d.step_b.bit_cell];
        r.extend(limb_range(d.step_b.base_x_base));
        r.extend(limb_range(d.step_b.base_y_base));
        units.push(glue(Kind::PinsB, 1 + 2 * NUM_LIMBS, r));
    }
    // Tail equalities.
    {
        let mut r = limb_range(layout.group_add.result_x3_limbs_base);
        r.extend(limb_range(layout.select.c_limbs_base));
        units.push(glue(Kind::TailRxEq, NUM_LIMBS, r));
        units.push(glue(Kind::TailNConst, NUM_LIMBS, limb_range(layout.n_const_base)));
        units.push(glue(Kind::PinR, NUM_LIMBS, limb_range(layout.r_base)));
    }

    // ── sanity: owned columns partition the full width exactly ──
    let total_owned: usize = units.iter().map(|u| u.owned.1).sum();
    assert_eq!(
        total_owned, full_width,
        "unit owned columns ({total_owned}) must partition full width ({full_width})"
    );
    let total_nc: usize = units.iter().map(|u| u.nc).sum();
    let monolith_nc = ecdsa_verify_multirow_constraints(layout);
    assert_eq!(
        total_nc, monolith_nc,
        "Σ unit constraints ({total_nc}) must equal monolith ({monolith_nc})"
    );

    // ── bin-pack: sort by column position, snap G-1 boundaries to unit
    //    (= gadget) edges by cumulative owned width. ──
    units.sort_by_key(|u| u.pos);
    let target = full_width as f64 / g as f64;
    let mut bin = 0usize;
    let mut acc = 0usize;
    for u in units.iter_mut() {
        u.strand = bin;
        acc += u.owned.1;
        if bin + 1 < g && (acc as f64) >= target * (bin as f64 + 1.0) {
            bin += 1;
        }
    }

    // ── column holders (owned ∪ reads) → seam detection ──
    let mut holders: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let touch = |col: usize, s: usize, m: &mut BTreeMap<usize, Vec<usize>>| {
        let e = m.entry(col).or_default();
        if !e.contains(&s) {
            e.push(s);
        }
    };
    for u in &units {
        let (b, l) = u.owned;
        for c in b..b + l {
            touch(c, u.strand, &mut holders);
        }
        for &c in &u.reads {
            touch(c, u.strand, &mut holders);
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

    // Seam groups keyed by holder-set (only columns held by ≥2 strands).
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

    // Per-strand unit indices (constraint order = enumeration order after
    // sort) and constraint counts.
    let mut strand_units: Vec<Vec<usize>> = vec![vec![]; g];
    let mut strand_nc: Vec<usize> = vec![0; g];
    for (i, u) in units.iter().enumerate() {
        if u.nc > 0 {
            strand_units[u.strand].push(i);
            strand_nc[u.strand] += u.nc;
        }
    }

    GwayCut {
        g,
        k,
        full_width,
        units,
        strand_cols,
        strand_units,
        strand_nc,
        seams,
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Per-unit evaluation (reuses monolith leaf evaluators verbatim)
// ═══════════════════════════════════════════════════════════════════

/// Evaluate one unit's constraints on FULL-WIDTH scattered rows.  Emits
/// EXACTLY `unit.nc` values (zeros when the unit's row-gate is inactive).
fn eval_unit(
    u: &Unit,
    cur: &[F],
    nxt: &[F],
    trace_row: usize,
    k: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pubin: &EcdsaVerifyPublicInputs,
) -> Vec<F> {
    let in_chain = trace_row < k;
    let is_chain_last = trace_row + 1 == k;
    let is_tail = trace_row == k;
    let acc_link = trace_row + 1 < k;
    let rproj_link = trace_row < k;
    let d = &layout.dsm;

    let active = match u.gate {
        Gate::InChain => in_chain,
        Gate::IsTail => is_tail,
        _ => true,
    };

    match &u.kind {
        Kind::Mul(m) => {
            if active {
                eval_mul_gadget(cur, m)
            } else {
                vec![F::zero(); u.nc]
            }
        }
        Kind::Add(a) => {
            if active {
                eval_add_gadget(cur, a)
            } else {
                vec![F::zero(); u.nc]
            }
        }
        Kind::Sub(s) => {
            if active {
                eval_sub_gadget(cur, s)
            } else {
                vec![F::zero(); u.nc]
            }
        }
        Kind::Freeze(fz) => {
            if active {
                eval_freeze_gadget(cur, fz)
            } else {
                vec![F::zero(); u.nc]
            }
        }
        Kind::Select(sl) => {
            if active {
                eval_select_gadget(cur, sl)
            } else {
                vec![F::zero(); u.nc]
            }
        }
        Kind::Cols => vec![],
        // ── glue groups ──
        Kind::BoundaryA => boundary(cur, is_chain_last, d.step_a.select_x.c_limbs_base,
            d.step_a.select_y.c_limbs_base, d.step_a.select_z.c_limbs_base,
            d.r_a_proj_x_base, d.r_a_proj_y_base, d.r_a_proj_z_base),
        Kind::BoundaryB => boundary(cur, is_chain_last, d.step_b.select_x.c_limbs_base,
            d.step_b.select_y.c_limbs_base, d.step_b.select_z.c_limbs_base,
            d.r_b_proj_x_base, d.r_b_proj_y_base, d.r_b_proj_z_base),
        Kind::AccTransA => acc_trans(cur, nxt, acc_link,
            d.step_a.acc_x_base, d.step_a.acc_y_base, d.step_a.acc_z_base,
            d.step_a.select_x.c_limbs_base, d.step_a.select_y.c_limbs_base,
            d.step_a.select_z.c_limbs_base),
        Kind::AccTransB => acc_trans(cur, nxt, acc_link,
            d.step_b.acc_x_base, d.step_b.acc_y_base, d.step_b.acc_z_base,
            d.step_b.select_x.c_limbs_base, d.step_b.select_y.c_limbs_base,
            d.step_b.select_z.c_limbs_base),
        Kind::RprojConstA => constancy(cur, nxt, rproj_link,
            d.r_a_proj_x_base, d.r_a_proj_y_base, d.r_a_proj_z_base),
        Kind::RprojConstB => constancy(cur, nxt, rproj_link,
            d.r_b_proj_x_base, d.r_b_proj_y_base, d.r_b_proj_z_base),
        Kind::PinsA => pins_chain(cur, in_chain, trace_row, d.step_a.bit_cell,
            &pubin.u1_bits, d.step_a.base_x_base, &pubin.gx, d.step_a.base_y_base, &pubin.gy),
        Kind::PinsB => pins_chain(cur, in_chain, trace_row, d.step_b.bit_cell,
            &pubin.u2_bits, d.step_b.base_x_base, &pubin.qx, d.step_b.base_y_base, &pubin.qy),
        Kind::TailRxEq => {
            let mut out = Vec::with_capacity(NUM_LIMBS);
            for i in 0..NUM_LIMBS {
                out.push(if is_tail {
                    cur[layout.group_add.result_x3_limbs_base + i] - cur[layout.select.c_limbs_base + i]
                } else {
                    F::zero()
                });
            }
            out
        }
        Kind::TailNConst => {
            let n_fe = order_n_field();
            let mut out = Vec::with_capacity(NUM_LIMBS);
            for i in 0..NUM_LIMBS {
                out.push(if is_tail {
                    cur[layout.n_const_base + i] - F::from(n_fe.limbs[i] as u64)
                } else {
                    F::zero()
                });
            }
            out
        }
        Kind::PinR => {
            let mut out = Vec::with_capacity(NUM_LIMBS);
            for i in 0..NUM_LIMBS {
                out.push(if is_tail {
                    cur[layout.r_base + i] - pubin.r[i]
                } else {
                    F::zero()
                });
            }
            out
        }
    }
}

fn boundary(cur: &[F], fire: bool, sx: usize, sy: usize, sz: usize, px: usize, py: usize, pz: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(3 * NUM_LIMBS);
    for (s, p) in [(sx, px), (sy, py), (sz, pz)] {
        for i in 0..NUM_LIMBS {
            out.push(if fire { cur[s + i] - cur[p + i] } else { F::zero() });
        }
    }
    out
}
fn acc_trans(cur: &[F], nxt: &[F], fire: bool, ax: usize, ay: usize, az: usize, sx: usize, sy: usize, sz: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(3 * NUM_LIMBS);
    for (a, s) in [(ax, sx), (ay, sy), (az, sz)] {
        for i in 0..NUM_LIMBS {
            out.push(if fire { nxt[a + i] - cur[s + i] } else { F::zero() });
        }
    }
    out
}
fn constancy(cur: &[F], nxt: &[F], fire: bool, bx: usize, by: usize, bz: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(3 * NUM_LIMBS);
    for b in [bx, by, bz] {
        for i in 0..NUM_LIMBS {
            out.push(if fire { nxt[b + i] - cur[b + i] } else { F::zero() });
        }
    }
    out
}
fn pins_chain(cur: &[F], fire: bool, row: usize, bit_cell: usize, bits: &[F], bx: usize, wantx: &[F; NUM_LIMBS], by: usize, wanty: &[F; NUM_LIMBS]) -> Vec<F> {
    let mut out = Vec::with_capacity(1 + 2 * NUM_LIMBS);
    out.push(if fire { cur[bit_cell] - bits[row] } else { F::zero() });
    for i in 0..NUM_LIMBS {
        out.push(if fire { cur[bx + i] - wantx[i] } else { F::zero() });
    }
    for i in 0..NUM_LIMBS {
        out.push(if fire { cur[by + i] - wanty[i] } else { F::zero() });
    }
    out
}

/// Evaluate ALL of strand `s`'s constraints, in unit order.
fn eval_strand(
    cut: &GwayCut,
    s: usize,
    cur: &[F],
    nxt: &[F],
    trace_row: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pubin: &EcdsaVerifyPublicInputs,
) -> Vec<F> {
    let mut out = Vec::with_capacity(cut.strand_nc[s]);
    for &ui in &cut.strand_units[s] {
        out.extend(eval_unit(&cut.units[ui], cur, nxt, trace_row, cut.k, layout, pubin));
    }
    out
}

// ═══════════════════════════════════════════════════════════════════
//  DEEP-ALI merge over a strand LDE (copied from the M1 pattern)
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

// ═══════════════════════════════════════════════════════════════════
//  Proof bundle
// ═══════════════════════════════════════════════════════════════════

pub struct StrandedProofG {
    pub proofs: Vec<SubAirProofWithTrace>,
    /// `seam_commits[s]` = for each seam group that strand `s` holds,
    /// `(group_id, one single-column commit per column in the group)`.
    /// One BCC per column (num_cols = 1) keeps every packed LDE
    /// power-of-two, matching the M1 tested pattern.
    pub seam_commits: Vec<Vec<(usize, Vec<BindingCellsCommit>)>>,
}

/// Prove one strand (given ITS trace = only its held columns) and commit
/// every seam group it holds.  The strand LDE (dominant allocation) is
/// built inside, used for the seam commits, then dropped on return.
pub fn prove_one_strand<P>(
    strand_trace: &[Vec<F>],
    cut: &GwayCut,
    s: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pubin: &EcdsaVerifyPublicInputs,
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
    let (proof, lde, _tree) = prove_one_sub_air_with_trace_capturing(
        strand_trace,
        n_trace,
        blowup,
        pi_hash,
        domain_sep,
        cut.strand_nc[s],
        |lde, nt, bw, cc| {
            strand_merge(lde, nt, bw, cc, cut.full_width, cols, |c, x, r| {
                eval_strand(cut, s, c, x, r, layout, pubin)
            })
        },
        params_fn,
    );

    // Seam commits: for each seam group this strand holds, commit each
    // of the group's columns individually (num_cols = 1 → packed LDE is
    // power-of-two), mapped to this strand's local index.
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
    layout: &EcdsaVerifyMultirowLayout,
    pubin: &EcdsaVerifyPublicInputs,
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
            // scatter strand-local rows into full-width, then eval.
            let w = cut.full_width;
            let mut cur = vec![F::zero(); w];
            let mut nxt = vec![F::zero(); w];
            for (j, &c) in cols.iter().enumerate() {
                cur[c] = cur_local[j];
                nxt[c] = nxt_local[j];
            }
            eval_strand(cut, s, &cur, &nxt, row, layout, pubin)
        },
        params_fn,
    )
    .map_err(|e| format!("strand {s}: {e}"))
}

/// Verify all seam groups: every group's columns must OOD-agree across
/// all strands holding them (reference = holders[0]).
pub fn verify_seams<P>(
    proof: &StrandedProofG,
    cut: &GwayCut,
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    // Index: (strand, group) -> per-column commits.
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

/// Domain separator for strand `s` (distinct per strand).
pub fn strand_domain(s: usize) -> Vec<u8> {
    let mut v = b"ecdsa_verify_stranded_gway/strand/".to_vec();
    v.extend_from_slice(&(s as u32).to_le_bytes());
    v
}

/// Verify a full spliced G-way proof.
pub fn verify_stranded_g<P>(
    proof: &StrandedProofG,
    cut: &GwayCut,
    layout: &EcdsaVerifyMultirowLayout,
    pubin: &EcdsaVerifyPublicInputs,
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
            &proof.proofs[s], cut, s, layout, pubin, n_trace, blowup, pi_hash, &sep, params_fn,
        )?;
    }
    verify_seams(proof, cut, pi_hash, params_fn)?;
    Ok(())
}

// ═══════════════════════════════════════════════════════════════════
//  Tests (K=4, run --release)
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, fill_ecdsa_verify_multirow,
    };
    use crate::p256_field::{FieldElement, NUM_LIMBS};
    use crate::p256_group::GENERATOR;
    use ark_ff::PrimeField;

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
    fn z_one() -> FieldElement {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    }
    fn identity() -> (FieldElement, FieldElement, FieldElement) {
        let mut y = FieldElement::zero();
        y.limbs[0] = 1;
        (FieldElement::zero(), y, FieldElement::zero())
    }

    fn build_k4(g: usize) -> (
        EcdsaVerifyMultirowLayout,
        GwayCut,
        Vec<Vec<F>>, // full trace
        EcdsaVerifyPublicInputs,
        usize,
        [u8; 32],
    ) {
        let k = 4usize;
        let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
        let n_trace = (k + 1).next_power_of_two();
        let g_pt = *GENERATOR;
        let q = g_pt.double();
        let zo = z_one();
        let (ix, iy, iz) = identity();
        let a_bits = vec![true, false, true, true];
        let b_bits = vec![false, true, true, false];
        let read_fe = |trace: &[Vec<F>], base: usize, row: usize| -> FieldElement {
            let mut limbs = [0i64; NUM_LIMBS];
            for i in 0..NUM_LIMBS {
                limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
            }
            FieldElement { limbs }
        };
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &FieldElement::zero(),
        );
        let r_x3 = read_fe(&trace, layout.group_add.result_x3_limbs_base, k);
        let r_z3 = read_fe(&trace, layout.group_add.result_z3_limbs_base, k);
        let mut x1 = r_x3.mul(&r_z3.invert());
        x1.freeze();
        let r_fe = x1;
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &r_fe,
        );
        let pubin =
            EcdsaVerifyPublicInputs::new(&a_bits, &b_bits, &g_pt.x, &g_pt.y, &q.x, &q.y, &r_fe);
        let cut = compute_gway_cut(&layout, k, g);
        (layout, cut, trace, pubin, n_trace, [0x42u8; 32])
    }

    fn extract(full: &[Vec<F>], cols: &[usize]) -> Vec<Vec<F>> {
        cols.iter().map(|&c| full[c].clone()).collect()
    }

    /// ★ MANDATORY GUARD: the routed `fill_ecdsa_verify_multirow_strand`
    /// (direct-fill, never allocates the full trace) must produce columns
    /// BYTE-IDENTICAL to `extract(full_trace, strand_cols)` for every
    /// strand, at G ∈ {4, 8, 16}.  If this ever mismatches, the routed fill
    /// is wrong and direct-fill proofs would diverge from the full-fill
    /// path — DO NOT weaken this check.
    #[test]
    fn gway_strand_fill_byte_equals_full() {
        use crate::p256_ecdsa_verify_multirow_air::{
            build_ecdsa_verify_multirow_layout, fill_ecdsa_verify_multirow,
            fill_ecdsa_verify_multirow_strand,
        };

        let k = 4usize;
        let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
        let n_trace = (k + 1).next_power_of_two();
        let g_pt = *GENERATOR;
        let q = g_pt.double();
        let zo = z_one();
        let (ix, iy, iz) = identity();
        let a_bits = vec![true, false, true, true];
        let b_bits = vec![false, true, true, false];
        let read_fe = |trace: &[Vec<F>], base: usize, row: usize| -> FieldElement {
            let mut limbs = [0i64; NUM_LIMBS];
            for i in 0..NUM_LIMBS {
                limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
            }
            FieldElement { limbs }
        };

        // Derive a self-consistent signature-r (sel=0 branch), same as the
        // bench / build_k4 does.
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &FieldElement::zero(),
        );
        let r_x3 = read_fe(&trace, layout.group_add.result_x3_limbs_base, k);
        let r_z3 = read_fe(&trace, layout.group_add.result_z3_limbs_base, k);
        let mut x1 = r_x3.mul(&r_z3.invert());
        x1.freeze();
        let r_fe = x1;

        // Reference FULL trace (what build_full + extract would use).
        let mut full = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut full, &layout, n_trace,
            (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &r_fe,
        );

        for g in [4usize, 8, 16] {
            let cut = compute_gway_cut(&layout, k, g);
            for s in 0..g {
                let cols = &cut.strand_cols[s];
                let mut strand = vec![vec![F::zero(); n_trace]; cols.len()];
                fill_ecdsa_verify_multirow_strand(
                    cols, &mut strand, &layout, n_trace,
                    (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
                    (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &r_fe,
                );
                for (local, &c) in cols.iter().enumerate() {
                    for row in 0..n_trace {
                        assert_eq!(
                            strand[local][row], full[c][row],
                            "G={g} strand {s} local {local} (col {c}) row {row}: routed != full"
                        );
                    }
                }
            }
        }
    }

    /// Pure-CPU check (no FRI): honest full trace satisfies every strand's
    /// constraints, and Σ strand_nc == monolith total.  Fast.
    #[test]
    fn gway_k4_cut_is_complete_and_zero() {
        for g in [3usize, 4, 6] {
            let (layout, cut, trace, pubin, n_trace, _ph) = build_k4(g);
            let mono = ecdsa_verify_multirow_constraints(&layout);
            let sum: usize = cut.strand_nc.iter().sum();
            assert_eq!(sum, mono, "G={g}: Σ strand_nc != monolith");
            for s in 0..g {
                for row in 0..n_trace {
                    let cur: Vec<F> = (0..layout.width).map(|c| trace[c][row]).collect();
                    let nxt: Vec<F> =
                        (0..layout.width).map(|c| trace[c][(row + 1) % n_trace]).collect();
                    let cons = eval_strand(&cut, s, &cur, &nxt, row, &layout, &pubin);
                    let bad = cons.iter().filter(|v| !v.is_zero()).count();
                    assert_eq!(bad, 0, "G={g} strand {s} row {row}: {bad} nonzero");
                }
            }
        }
    }

    /// Full stranded prove/verify + tamper-reject at K=4, G=4.
    #[test]
    fn gway_k4_honest_accepts_tampers_reject() {
        let g = 4usize;
        let blowup = 4usize;
        let (layout, cut, trace, pubin, n_trace, pi_hash) = build_k4(g);
        let params = |n0: usize, ph: [u8; 32]| tparams(n0, ph);

        let prove_all = |trace: &[Vec<F>]| -> StrandedProofG {
            let mut proofs = Vec::with_capacity(g);
            let mut seam_commits = Vec::with_capacity(g);
            for s in 0..g {
                let strand = extract(trace, &cut.strand_cols[s]);
                let sep = strand_domain(s);
                let (p, c) = prove_one_strand(
                    &strand, &cut, s, &layout, &pubin, n_trace, blowup, pi_hash, &sep, params,
                );
                proofs.push(p);
                seam_commits.push(c);
            }
            StrandedProofG { proofs, seam_commits }
        };

        let proof = prove_all(&trace);
        verify_stranded_g(&proof, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params)
            .expect("honest G-way proof must accept");

        // Tamper one interior witness cell in EACH strand → that strand
        // (or a seam it feeds) must reject.
        for s in 0..g {
            // pick a column owned by a leaf gadget in strand s: use the
            // first held column that is NOT a seam (interior).
            let seam_cols: std::collections::BTreeSet<usize> = cut
                .seams
                .iter()
                .flat_map(|sg| sg.cols.iter().copied())
                .collect();
            let interior = cut.strand_cols[s]
                .iter()
                .copied()
                .find(|c| !seam_cols.contains(c));
            let Some(col) = interior else { continue };
            let mut bad = trace.clone();
            // Tamper every row so the owning gadget's active row is hit
            // regardless of whether it is a chain (rows 0..k-1) or tail
            // (row k) gadget.
            for row in 0..n_trace {
                bad[col][row] += F::from(1u64);
            }
            // Re-prove only strand s (others reuse honest proof).
            let strand = extract(&bad, &cut.strand_cols[s]);
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(
                &strand, &cut, s, &layout, &pubin, n_trace, blowup, pi_hash, &sep, params,
            );
            let mut proofs = proof.proofs.clone();
            let mut seam_commits = proof.seam_commits.clone();
            proofs[s] = ps;
            seam_commits[s] = cs;
            let spliced = StrandedProofG { proofs, seam_commits };
            let res =
                verify_stranded_g(&spliced, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params);
            assert!(res.is_err(), "interior tamper in strand {s} must reject");
        }

        // Tamper one column of EACH seam group in its reference strand →
        // seam OOD must reject.
        for (gid, sg) in cut.seams.iter().enumerate() {
            let s = sg.holders[0];
            let col = sg.cols[0];
            let mut bad = trace.clone();
            bad[col][0] += F::from(1u64);
            let strand = extract(&bad, &cut.strand_cols[s]);
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(
                &strand, &cut, s, &layout, &pubin, n_trace, blowup, pi_hash, &sep, params,
            );
            let mut proofs = proof.proofs.clone();
            let mut seam_commits = proof.seam_commits.clone();
            proofs[s] = ps;
            seam_commits[s] = cs;
            let spliced = StrandedProofG { proofs, seam_commits };
            let res =
                verify_stranded_g(&spliced, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params);
            assert!(res.is_err(), "seam group {gid} tamper must reject");
        }
    }
}
