//! Native composition demo — all three deep_ali_verifier_air sub-circuit
//! foundations exercised together on a synthetic inner-proof setup.
//!
//! This is **the architectural skeleton** of what the eventual recursive
//! ML-DSA STARK will encode in-AIR.  Each sub-circuit's native oracle
//! is used here; the AIR-level versions follow the same constraint
//! shape as the two shipped gadgets (SHA-3 PoK + Merkle path).
//!
//! # Run
//!
//! ```text
//! cargo run --release -p wrapper-stark \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features \
//!     --example recursive_stark_native_demo
//! ```

use ark_goldilocks::Goldilocks;

use wrapper_stark::bit_constraint::{BitOp, CellRef};
use wrapper_stark::deep_ali_verifier_air::{
    binding_cells_ood_verifier::{OodClaimBundle, OodEqualityClaim},
    constraint_composition_verifier::{CompositionClaim, composition_verify_native},
    permutation_argument_verifier::PermArgClaim,
    RecursiveStarkPublicInputs,
};
use wrapper_stark::sha3_absorb_air::Sha3Variant;

fn gf(x: u64) -> Goldilocks { Goldilocks::from(x) }

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("RECURSIVE ML-DSA STARK — Native Composition Demo");
    println!("═══════════════════════════════════════════════════════════");
    println!();
    println!("Demonstrates the three sub-circuits of deep_ali_verifier_air");
    println!("composed on a synthetic inner-proof scenario.  Each check is");
    println!("the AIR-side analogue of one step the inner FRI verifier does.");
    println!();

    // ─── Synthetic inner-proof setup ──────────────────────────────
    //
    // Imagine we have an inner deep_ali_merge ML-DSA proof.  At an
    // FS-derived query point z, the prover has revealed:
    //   - Column values for the inner trace at z
    //   - Two FRI-committed polynomials' OOD evaluations (the
    //     binding_cells_commit pair)
    //   - The T_MEM perm-arg log (left/right multisets)
    //
    // The recursive STARK verifier-AIR checks all three:
    //   1. Σ α·Φ(column_vals) == claimed composed value
    //   2. f(z) == g(z) for each binding-cells OOD pair (7 of them)
    //   3. ∏ (γ + left_i) == ∏ (γ + right_i) for the perm-arg log

    let inner_pi_hash = [0xBEu8; 32];
    let public = RecursiveStarkPublicInputs::for_inner(
        Sha3Variant::Sha3_256, inner_pi_hash,
    );
    println!("[setup] inner pi_hash:  {}", hex(&public.inner_pi_hash));
    println!("[setup] outer pi_hash:  {}", hex(&public.outer_pi_hash));
    println!();

    // ─── 1. Constraint composition check ───────────────────────────
    //
    // Inner trace columns at z (synthetic): a=1, b=0, c=1.
    // Inner AIR has one Xor constraint: c = a XOR b.
    // FS-derived α: 99.  Composed value = α · Φ(values) = 99·0 = 0.
    println!("[1] CONSTRAINT COMPOSITION VERIFIER");
    println!("    Statement: Σ_j α_j · Φ_j(column_vals(z)) = expected_composed");

    let comp_claim = CompositionClaim {
        column_values: vec![
            (CellRef::new(0, 0), gf(1)),  // a
            (CellRef::new(0, 1), gf(0)),  // b
            (CellRef::new(0, 2), gf(1)),  // c
        ],
        constraints: vec![BitOp::Xor {
            c: CellRef::new(0, 2),
            a: CellRef::new(0, 0),
            b: CellRef::new(0, 1),
        }],
        alphas: vec![gf(99)],
        expected: gf(0),
    };
    let comp_ok = composition_verify_native(&comp_claim);
    println!("    Verdict: {}",
        if comp_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(comp_ok);

    // Tamper: claim wrong expected.
    let mut comp_bad = comp_claim.clone();
    comp_bad.expected = gf(42);
    let comp_bad_ok = composition_verify_native(&comp_bad);
    println!("    Tampered expected → {}",
        if !comp_bad_ok { "REJECT (correct)" } else { "ACCEPT (bug!)" });
    assert!(!comp_bad_ok);
    println!();

    // ─── 2. binding_cells_commit OOD verifier ──────────────────────
    //
    // 7 binding-cells OOD checks for inner ML-DSA-65 v2: L1/L2a/L2b/
    // L2c/L3/L4/L5.  Synthetic claim: all 7 evaluations agree at z.
    println!("[2] BINDING_CELLS OOD VERIFIER");
    println!("    Statement: For 7 (f, g) pairs, f(z) = g(z) by Schwartz-Zippel");

    let z = gf(0xC0FFEE_DEAD_BEEFu64);
    let v = gf(0x12345);  // common value all OOD evals match at z
    let bundle = OodClaimBundle::<Goldilocks> {
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
    let bundle_ok = bundle.check_all_native();
    println!("    Verdict: {}  ({} of 7 OOD pairs verified)",
        if bundle_ok { "ACCEPT" } else { "REJECT (bug!)" },
        bundle.claims.len());
    assert!(bundle_ok);

    // Tamper L3's right-side evaluation.
    let mut bundle_bad = bundle.clone();
    bundle_bad.claims[4].g_at_z = gf(0xFFFF);
    let bundle_bad_ok = bundle_bad.check_all_native();
    let failing_idx = bundle_bad.first_failing();
    println!("    Tampered L3.g(z) → {}  (first failing: {:?})",
        if !bundle_bad_ok { "REJECT (correct)" } else { "ACCEPT (bug!)" },
        failing_idx);
    assert!(!bundle_bad_ok);
    assert_eq!(failing_idx, Some(4));
    println!();

    // ─── 3. T_MEM permutation argument verifier ────────────────────
    //
    // Synthetic perm-arg: prover claims two multisets are equal.
    // Verifier picks γ + checks Π(γ+l_i) = Π(γ+r_i).
    println!("[3] PERMUTATION ARGUMENT VERIFIER");
    println!("    Statement: ∏(γ + left_i) = ∏(γ + right_i)");
    let left  = vec![gf(11), gf(22), gf(33), gf(44), gf(55)];
    let right = vec![gf(33), gf(11), gf(55), gf(22), gf(44)];  // permuted
    let perm_claim = PermArgClaim {
        left: left.clone(), right: right.clone(),
        gamma: gf(0xDEAD_C0DE),
        perm_tag: "T_MEM",
    };
    let perm_ok = perm_claim.check_native();
    println!("    Multiset sizes: |left|={}, |right|={}",
        perm_claim.left.len(), perm_claim.right.len());
    println!("    Verdict: {}",
        if perm_ok { "ACCEPT" } else { "REJECT (bug!)" });
    assert!(perm_ok);

    // Tamper one right-side element.
    let mut perm_bad = perm_claim.clone();
    perm_bad.right[2] = gf(99);
    let perm_bad_ok = perm_bad.check_native();
    println!("    Tampered right[2] → {}",
        if !perm_bad_ok { "REJECT (correct)" } else { "ACCEPT (bug!)" });
    assert!(!perm_bad_ok);
    println!();

    // ─── Composition: all three sub-circuits agree ────────────────
    println!("[*] FULL RECURSIVE STARK STATEMENT (native composition)");
    println!("    All three sub-circuit native checks ACCEPT on the");
    println!("    honest inner-proof witnesses, REJECT on tampering.");
    println!();
    println!("═══════════════════════════════════════════════════════════");
    println!();
    println!("  This is the architectural skeleton of the recursive");
    println!("  ML-DSA STARK.  Once each sub-circuit's in-AIR constraints,");
    println!("  trace synthesiser, and FRI integration land (~5-9 commits");
    println!("  each), the gadget will produce a single outer FRI proof");
    println!("  attesting that an inner deep_ali_merge proof verifies —");
    println!("  with target ~200-500 KiB proof + ~5-15 ms verify.");
    println!();
    println!("  Combined with the two shipped wrapper-stark gadgets");
    println!("  (SHA-3 PoK + Merkle path), the full recursive STARK");
    println!("  delivers the RSA-2048 edge profile for ML-DSA under");
    println!("  the dual-hash architecture's unconditional NIST PQ");
    println!("  soundness (paper §8 + Theorem 6).");
    println!();
    println!("═══════════════════════════════════════════════════════════");
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
}
