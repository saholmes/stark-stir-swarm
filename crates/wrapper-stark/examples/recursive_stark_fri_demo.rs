//! Recursive ML-DSA STARK — step 4 runnable demo.
//!
//! Builds on `recursive_stark_accumulator_demo.rs` (in-AIR constraint
//! validation only) by running the three sub-circuit provers through
//! `deep_fri_prove`/`deep_fri_verify`, producing real STARK proofs and
//! reporting per-sub-circuit prove time, verify time, and proof size.
//!
//! These are the building blocks of the eventual single-outer-FRI
//! recursive STARK: each accumulator's c_eval is a polynomial that
//! one outer FRI proof would low-degree-test against.  For now, each
//! sub-circuit gets its own FRI proof; composition into one outer
//! proof is step 6.
//!
//! # Run
//!
//! ```text
//! cargo run --release -p wrapper-stark \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features \
//!     --example recursive_stark_fri_demo
//! ```

use std::time::Instant;

use ark_goldilocks::Goldilocks;
use ark_serialize::CanonicalSerialize;

use wrapper_stark::bit_constraint::{BitOp, CellRef};
use wrapper_stark::deep_ali_verifier_air::{
    binding_cells_ood_verifier::{OodClaimBundle, OodEqualityClaim},
    constraint_composition_verifier::CompositionClaim,
    permutation_argument_verifier::PermArgClaim,
};
use wrapper_stark::recursive_prover::{
    OodAccumulatorClaim,
    prove_composition_accumulator, verify_composition_accumulator,
    prove_ood_accumulator, verify_ood_accumulator,
    prove_perm_arg_accumulator, verify_perm_arg_accumulator,
};

fn gf(x: u64) -> Goldilocks { Goldilocks::from(x) }

fn format_kib(bytes: usize) -> String {
    format!("{:.1} KiB", bytes as f64 / 1024.0)
}

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("RECURSIVE ML-DSA STARK — Step 4 FRI Demo");
    println!("═══════════════════════════════════════════════════════════");
    println!();
    println!("Each sub-circuit is proven through deep_fri_prove +");
    println!("verified through deep_fri_verify.  DEEP-FRI at blowup=4");
    println!("and r=54 queries (NIST PQ Level 1 soundness profile).");
    println!();

    let blowup: usize = 4;
    let r: usize = 54;
    let use_stir = false;

    // ─── Sub-circuit 1: constraint composition ─────────────────────
    println!("[1] CONSTRAINT COMPOSITION ACCUMULATOR — FRI round-trip");
    let comp_claim = {
        let mut vals: Vec<u8> = vec![1, 0];
        for i in 0..6 { vals.push(vals[i] ^ vals[i + 1]); }
        let column_values: Vec<(CellRef, Goldilocks)> = (0..8)
            .map(|i| (CellRef::new(0, i), gf(vals[i] as u64))).collect();
        let constraints: Vec<BitOp> = (0..6).map(|i| BitOp::Xor {
            c: CellRef::new(0, i + 2),
            a: CellRef::new(0, i),
            b: CellRef::new(0, i + 1),
        }).collect();
        let alphas: Vec<Goldilocks> = (1..=6u64).map(gf).collect();
        CompositionClaim { column_values, constraints, alphas, expected: gf(0) }
    };
    let t = Instant::now();
    let comp_proof = prove_composition_accumulator(&comp_claim, blowup, r, use_stir)
        .expect("composition prove must succeed");
    let comp_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let t = Instant::now();
    let comp_ok = verify_composition_accumulator(&comp_proof);
    let comp_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let mut buf = Vec::new();
    comp_proof.fri_proof.serialize_compressed(&mut buf).unwrap();
    let comp_size = buf.len();
    println!("    n_trace={}  n_constraints={}",
        comp_proof.n_trace, comp_proof.public.n_constraints);
    println!("    prove: {comp_prove_ms:.1} ms   verify: {comp_verify_ms:.2} ms   proof: {}",
        format_kib(comp_size));
    println!("    Verdict: {}", if comp_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(comp_ok);
    println!();

    // ─── Sub-circuit 2: OOD residue accumulator ────────────────────
    println!("[2] OOD RESIDUE ACCUMULATOR — FRI round-trip");
    let z = gf(0xC0FFEE_DEAD_BEEFu64);
    let v = gf(0x12345);
    let ood_claim = OodAccumulatorClaim {
        bundle: OodClaimBundle {
            claims: vec![
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2a" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2b" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2c" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L3" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L4" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L5" },
            ],
        },
        alphas: (1..=7u64).map(gf).collect(),
    };
    let t = Instant::now();
    let ood_proof = prove_ood_accumulator(&ood_claim, blowup, r, use_stir)
        .expect("OOD prove must succeed");
    let ood_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let t = Instant::now();
    let ood_ok = verify_ood_accumulator(&ood_proof);
    let ood_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let mut buf = Vec::new();
    ood_proof.fri_proof.serialize_compressed(&mut buf).unwrap();
    let ood_size = buf.len();
    println!("    n_trace={}  n_claims={}",
        ood_proof.n_trace, ood_proof.public.n_claims);
    println!("    prove: {ood_prove_ms:.1} ms   verify: {ood_verify_ms:.2} ms   proof: {}",
        format_kib(ood_size));
    println!("    Verdict: {}", if ood_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(ood_ok);
    println!();

    // ─── Sub-circuit 3: perm-arg Π running-product accumulator ─────
    println!("[3] PERM-ARG Π RUNNING-PRODUCT ACCUMULATOR — FRI round-trip");
    let perm_claim = PermArgClaim {
        left:  vec![gf(11), gf(22), gf(33), gf(44), gf(55)],
        right: vec![gf(33), gf(11), gf(55), gf(22), gf(44)],
        gamma: gf(0xDEAD_C0DE),
        perm_tag: "T_MEM",
    };
    let t = Instant::now();
    let perm_proof = prove_perm_arg_accumulator(&perm_claim, blowup, r, use_stir)
        .expect("perm-arg prove must succeed");
    let perm_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let t = Instant::now();
    let perm_ok = verify_perm_arg_accumulator(&perm_proof);
    let perm_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let mut buf = Vec::new();
    perm_proof.fri_proof.serialize_compressed(&mut buf).unwrap();
    let perm_size = buf.len();
    println!("    n_trace={}  n_elements={}",
        perm_proof.n_trace, perm_proof.public.n_elements);
    println!("    prove: {perm_prove_ms:.1} ms   verify: {perm_verify_ms:.2} ms   proof: {}",
        format_kib(perm_size));
    println!("    Verdict: {}", if perm_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(perm_ok);
    println!();

    // ─── Composite summary ────────────────────────────────────────
    let total_prove = comp_prove_ms + ood_prove_ms + perm_prove_ms;
    let total_verify = comp_verify_ms + ood_verify_ms + perm_verify_ms;
    let total_size = comp_size + ood_size + perm_size;

    println!("═══════════════════════════════════════════════════════════");
    println!("  All three sub-circuit FRI proofs ACCEPTED on honest");
    println!("  witnesses.  Composite (three independent proofs):");
    println!();
    println!("    prove:  {total_prove:.1} ms (composition + OOD + perm-arg)");
    println!("    verify: {total_verify:.2} ms");
    println!("    size:   {}", format_kib(total_size));
    println!();
    println!("  Step 6 (single outer FRI proof composing all three");
    println!("  sub-circuits' c_evals) will collapse the three proofs");
    println!("  into one — replacing three Merkle roots, three FRI");
    println!("  fold schedules, and three query sets with a single");
    println!("  shared LDE.  Target: ~200-500 KiB total, ~5-15 ms");
    println!("  verify at L1 with blowup=32 and r=54.");
    println!();
    println!("  Step-4 milestone: each sub-circuit now produces a real,");
    println!("  paper-grade DeepFriProof<SexticExt> — same path used by");
    println!("  the production SHA-3 PoK and Merkle path gadgets.");
    println!("═══════════════════════════════════════════════════════════");
}
