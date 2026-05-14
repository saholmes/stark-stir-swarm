//! Runnable demo: extract real F2b OOD evaluations from a live v2
//! ML-DSA proof into the recursive STARK gadget's OOD claim bundle.
//!
//! This is the first wiring between the inner v2 ML-DSA verify STARK
//! and the wrapper-stark recursive prover's sub-circuit 2 (binding-
//! cells OOD).  The synthetic Goldilocks claims used in
//! `recursive_stark_fri_demo` are replaced here by **real**
//! `SexticExt`-typed OOD evaluations from a freshly proven v2 inner
//! proof.
//!
//! # Run
//!
//! ```text
//! cargo run --release -p wrapper-stark \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features \
//!     --example v2_recursion_bridge_demo
//! ```

use std::time::Instant;

use deep_ali::ml_dsa::params::C_TILDE_BYTES;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    prove_v2_real, synthesize_demo_witness, verify_v2_real,
};

use wrapper_stark::v2_recursion_bridge::extract_v2_bcc_pair_ood_bundle;

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("V2 → RECURSIVE-PROVER OOD BRIDGE — runnable demo");
    println!("═══════════════════════════════════════════════════════════════");
    println!();
    println!("Proves one inner v2 ML-DSA verify STARK, extracts the F2b L2a");
    println!("+ L3 OOD evaluations from the resulting V2ProofReal into Ext-");
    println!("typed claims, and checks the bundle natively.  This is the");
    println!("input shape the recursive STARK's OOD sub-circuit will consume.");
    println!();

    let blowup: usize = 4;
    let seed: u64 = 0xC0FFEE;

    println!("[1/4] Synthesise V2Witness (seed = 0x{seed:X}) …");
    let t = Instant::now();
    let w = synthesize_demo_witness(seed);
    let c_tilde: [u8; C_TILDE_BYTES] =
        ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
    println!("      synth + c_tilde derived in {:.2} ms", t.elapsed().as_secs_f64() * 1000.0);
    println!();

    println!("[2/4] Run prove_v2_real (10 inner FRI sub-proofs + F2b OOD BCCs) …");
    let t = Instant::now();
    let proof = prove_v2_real(&w, &c_tilde, blowup);
    let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let proof_bytes = proof.to_bytes();
    println!(
        "      prove {prove_ms:.1} ms · proof {} ({:.1} KiB compressed)",
        proof_bytes.len(), proof_bytes.len() as f64 / 1024.0,
    );
    println!();

    println!("[3/4] Native verify_v2_real (sanity check) …");
    let t = Instant::now();
    verify_v2_real(&w, &c_tilde, &proof, blowup)
        .expect("honest v2 must verify");
    println!("      verify_v2_real ACCEPT in {:.2} ms", t.elapsed().as_secs_f64() * 1000.0);
    println!();

    println!("[4/4] Extract F2b OOD bundle (L2a + L3) for recursive prover …");
    let t = Instant::now();
    let bundle = extract_v2_bcc_pair_ood_bundle(&proof)
        .expect("OOD bundle extraction must succeed on a well-formed v2 proof");
    println!("      extract {:.2} ms · {} claims",
        t.elapsed().as_secs_f64() * 1000.0, bundle.claims.len());
    println!();

    for c in &bundle.claims {
        let resid = c.residue();
        let zero = c.check_native();
        println!(
            "      {tag:<3}  residue.is_zero = {zero:<5}  (f − g)",
            tag = c.binding_tag, zero = zero,
        );
        let _ = resid;
    }
    println!();

    let ok = bundle.check_all_native();
    println!("═══════════════════════════════════════════════════════════════");
    println!("  bundle.check_all_native() = {ok}");
    println!("  first_failing()           = {:?}", bundle.first_failing());
    println!();
    if ok {
        println!("  ✓  All L2a + L3 F2b OOD pairs satisfy f(z) = g(z) at the FS-");
        println!("     derived z_0 inside each BindingCellsCommit.  This is the");
        println!("     Schwartz-Zippel binding that ties Decompose↔UseHint and");
        println!("     UseHint↔W1Encode trace cells across v2's sub-AIRs without");
        println!("     a permutation argument.  Sound to ≤ d/|Fp⁶| ≈ 2⁻³⁷⁰ at");
        println!("     n_trace ≈ 2¹⁴.");
        println!();
        println!("  This bundle is now exactly the input shape the recursive");
        println!("  STARK's sub-circuit 2 (binding-cells OOD accumulator) needs.");
        println!("  Next step: lift the recursive prover's OOD AIR to operate");
        println!("  over Ext so we can feed Ext-typed claims directly, then");
        println!("  produce ONE outer FRI proof attesting all F2b OOD legs.");
    } else {
        println!("  ✗  Bundle check failed — v2 proof is inconsistent (this");
        println!("     should not happen on an honest run).");
        std::process::exit(1);
    }
    println!("═══════════════════════════════════════════════════════════════");
}
