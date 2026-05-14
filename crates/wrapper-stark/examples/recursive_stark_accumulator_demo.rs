//! Accumulator-AIR composition demo — exercises all three sub-circuit
//! step-2 AIR encodings together on a synthetic inner-proof scenario.
//!
//! Builds on `recursive_stark_native_demo.rs` (step 1 native oracles)
//! by running the NEW step-2 accumulator AIRs end-to-end:
//!
//!   1. Constraint composition: `Σ α · Φ = y` via additive accumulator
//!   2. OOD residue:            `Σ α · (f − g) = 0` via residue accumulator
//!   3. Perm-arg:               `Π (γ + l) = Π (γ + r)` via Π accumulator
//!
//! Each accumulator AIR is the in-AIR polynomial encoding ready to
//! plug into deep_fri_prove via a per-sub-circuit FieldRowSchema
//! (step 3, pending).
//!
//! # Run
//!
//! ```text
//! cargo run --release -p wrapper-stark \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features \
//!     --example recursive_stark_accumulator_demo
//! ```

use ark_goldilocks::Goldilocks;

use wrapper_stark::bit_constraint::{BitOp, CellRef};
use wrapper_stark::deep_ali_verifier_air::{
    binding_cells_ood_verifier::{
        OodAccumulatorTrace, OodClaimBundle, OodEqualityClaim,
        verify_ood_accumulator_trace,
    },
    constraint_composition_verifier::{
        AccumulatorTrace, CompositionClaim, verify_accumulator_trace,
    },
    permutation_argument_verifier::{
        PermArgAccumulatorTrace, PermArgClaim, verify_perm_arg_accumulator_trace,
    },
};

fn gf(x: u64) -> Goldilocks { Goldilocks::from(x) }

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("RECURSIVE ML-DSA STARK — Accumulator AIR Composition Demo");
    println!("═══════════════════════════════════════════════════════════");
    println!();
    println!("All three sub-circuits at STEP 2 (in-AIR polynomial");
    println!("constraints) — accumulator AIRs ready to plug into");
    println!("deep_fri_prove.");
    println!();

    // ─── 1. Constraint composition AIR ─────────────────────────────
    println!("[1] CONSTRAINT COMPOSITION ACCUMULATOR AIR");
    println!("    Encodes: Σ α_j · Φ_j(values) = expected  via running sum");

    let comp_claim = CompositionClaim::<Goldilocks> {
        column_values: vec![
            (CellRef::new(0, 0), gf(1)),  // a
            (CellRef::new(0, 1), gf(0)),  // b
            (CellRef::new(0, 2), gf(1)),  // c
        ],
        constraints: vec![
            BitOp::Boolean { b: CellRef::new(0, 1) },
            BitOp::Xor { c: CellRef::new(0, 2), a: CellRef::new(0, 0), b: CellRef::new(0, 1) },
        ],
        alphas: vec![gf(7), gf(11)],
        expected: gf(0),
    };
    let comp_trace = AccumulatorTrace::synthesise(&comp_claim);
    println!("    trace: {} rows × 3 cols", comp_trace.n_rows);
    println!("    final partial_sum: {:?}", comp_trace.partial_sum[comp_trace.n_rows - 1]);
    let comp_ok = verify_accumulator_trace(&comp_trace, comp_claim.expected);
    println!("    Verdict: {}", if comp_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(comp_ok);

    // Tamper test
    let mut comp_bad = comp_trace.clone();
    comp_bad.partial_sum[1] = gf(99);
    let comp_bad_ok = verify_accumulator_trace(&comp_bad, comp_claim.expected);
    println!("    Tampered partial_sum → {}",
        if !comp_bad_ok { "REJECT (correct)" } else { "ACCEPT (bug!)" });
    assert!(!comp_bad_ok);
    println!();

    // ─── 2. OOD residue accumulator AIR ────────────────────────────
    println!("[2] OOD RESIDUE ACCUMULATOR AIR");
    println!("    Encodes: Σ α_j · (f_j − g_j) = 0  via residue running sum");

    let z = gf(0xC0FFEE_DEAD_BEEFu64);
    let v = gf(0x12345);
    let ood_bundle = OodClaimBundle::<Goldilocks> {
        claims: vec![
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2a" },
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2b" },
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2c" },
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L3" },
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L4" },
            OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L5" },
        ],
    };
    let ood_alphas: Vec<Goldilocks> = (1..=7u64).map(gf).collect();
    let ood_trace = OodAccumulatorTrace::synthesise(&ood_bundle, &ood_alphas);
    println!("    trace: {} rows × 5 cols (7 binding-cells OOD claims)", ood_trace.n_rows);
    println!("    final partial_sum: {:?}",
             ood_trace.partial_sum[ood_trace.n_rows - 1]);
    let ood_ok = verify_ood_accumulator_trace(&ood_trace);
    println!("    Verdict: {}", if ood_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(ood_ok);

    // Tamper one of the residues.
    let mut ood_bad = ood_trace.clone();
    ood_bad.residue[3] = gf(7);  // non-zero residue
    let ood_bad_ok = verify_ood_accumulator_trace(&ood_bad);
    println!("    Tampered residue → {}",
        if !ood_bad_ok { "REJECT (correct)" } else { "ACCEPT (bug!)" });
    assert!(!ood_bad_ok);
    println!();

    // ─── 3. Perm-arg Π running-product accumulator AIR ─────────────
    println!("[3] PERM-ARG Π RUNNING-PRODUCT ACCUMULATOR AIR");
    println!("    Encodes: ∏(γ + l_i) = ∏(γ + r_i)  via dual running products");

    let perm_claim = PermArgClaim {
        left:  vec![gf(11), gf(22), gf(33), gf(44), gf(55)],
        right: vec![gf(33), gf(11), gf(55), gf(22), gf(44)],  // permuted
        gamma: gf(0xDEAD_C0DE),
        perm_tag: "T_MEM",
    };
    let perm_trace = PermArgAccumulatorTrace::synthesise(&perm_claim);
    println!("    trace: {} rows × 4 cols (5-element multiset)", perm_trace.n_rows);
    let final_left = perm_trace.running_left[perm_trace.n_rows - 1];
    let final_right = perm_trace.running_right[perm_trace.n_rows - 1];
    println!("    final running_left:  {:?}", final_left);
    println!("    final running_right: {:?}", final_right);
    println!("    equal? {}", if final_left == final_right { "YES" } else { "NO" });
    let perm_ok = verify_perm_arg_accumulator_trace(&perm_trace);
    println!("    Verdict: {}", if perm_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(perm_ok);

    // Tamper one running product.
    let mut perm_bad = perm_trace.clone();
    perm_bad.running_left[2] = gf(99);
    let perm_bad_ok = verify_perm_arg_accumulator_trace(&perm_bad);
    println!("    Tampered running_left → {}",
        if !perm_bad_ok { "REJECT (correct)" } else { "ACCEPT (bug!)" });
    assert!(!perm_bad_ok);
    println!();

    // ─── Summary ───────────────────────────────────────────────────
    println!("═══════════════════════════════════════════════════════════");
    println!("  ✓ All three sub-circuits at STEP 2 (in-AIR encoding):");
    println!();
    println!("    1. Composition accumulator   ({} rows, additive)", comp_trace.n_rows);
    println!("    2. OOD residue accumulator   ({} rows, additive)", ood_trace.n_rows);
    println!("    3. Perm-arg Π accumulator    ({} rows, multiplicative)", perm_trace.n_rows);
    println!();
    println!("  All synthesised traces satisfy their AIR constraints;");
    println!("  tampering each in turn correctly rejects.");
    println!();
    println!("  These are the building blocks for the recursive ML-DSA");
    println!("  STARK.  Once steps 3-6 land (trace synthesiser →");
    println!("  FRI integration → boundary → composition), each");
    println!("  accumulator becomes part of one outer FRI proof's c_eval,");
    println!("  attesting that the inner deep_ali_merge proof verifies.");
    println!("═══════════════════════════════════════════════════════════");
}
