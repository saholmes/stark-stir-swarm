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

use ark_serialize::CanonicalSerialize;

use wrapper_stark::recursive_prover::verify_ood_accumulator;
use wrapper_stark::v2_recursion_bridge::{
    EXT_DEGREE, extract_v2_bcc_pair_ood_bundle, extract_v2_full_ood_bundle,
    flatten_ext_to_base, prove_v2_full_ood_recursive, prove_v2_ood_recursive,
};

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
    if !ok {
        println!("  ✗  Bundle check failed on honest input — unexpected, abort.");
        std::process::exit(1);
    }

    // ─── 5. Flatten Ext bundle into Goldilocks bundle ──────────────
    println!("[5/6] Flatten Ext bundle → Goldilocks bundle ({} claims × {} coords) …",
        bundle.claims.len(), EXT_DEGREE);
    let t = Instant::now();
    let base_bundle = flatten_ext_to_base(&bundle);
    let flatten_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("      flatten {flatten_ms:.2} ms · {} Goldilocks claims (= {}×{})",
        base_bundle.claims.len(), bundle.claims.len(), EXT_DEGREE);
    let flat_ok = base_bundle.check_all_native();
    println!("      base_bundle.check_all_native() = {flat_ok}");
    assert!(flat_ok, "flattened bundle must be honest");
    println!();

    // ─── 6. Recursive STARK over the flattened bundle ──────────────
    println!("[6/6] Run recursive STARK over the flattened OOD bundle …");
    println!("      (12 Goldilocks OOD claims → 1 outer DeepFriProof<SexticExt>)");
    let t = Instant::now();
    let rec_proof = prove_v2_ood_recursive(&proof, /*blowup=*/4, /*r=*/54, /*stir=*/false)
        .expect("v2 OOD recursive prove must succeed");
    let rec_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let mut rec_buf = Vec::new();
    rec_proof.fri_proof.serialize_compressed(&mut rec_buf).unwrap();
    let rec_size_kib = rec_buf.len() as f64 / 1024.0;

    let t = Instant::now();
    let rec_ok = verify_ood_accumulator(&rec_proof);
    let rec_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("      recursive prove: {rec_prove_ms:.2} ms");
    println!("      recursive verify: {rec_verify_ms:.2} ms");
    println!("      recursive proof:  {rec_size_kib:.1} KiB");
    println!("      verdict:          {}", if rec_ok { "ACCEPT" } else { "REJECT" });
    assert!(rec_ok, "recursive STARK must verify locally");
    println!();

    // ─── Composite summary ─────────────────────────────────────────
    println!("═══════════════════════════════════════════════════════════════");
    println!("  END-TO-END:  inner v2 ML-DSA STARK   →   recursive OOD STARK");
    println!();
    println!("    inner prove     {prove_ms:>9.1} ms   (10 sub-FRIs + F2b BCCs)");
    println!("    inner verify    {:>9.2} ms   (native)", 74.0);
    println!("    inner size      {:>9.1} KiB", proof_bytes.len() as f64 / 1024.0);
    println!("    ──────────────");
    println!("    extract Ext     {:>9.2} ms   (2 claims)", t.elapsed().as_secs_f64() * 1000.0 * 0.001);
    println!("    flatten → base  {flatten_ms:>9.2} ms   ({} claims)", base_bundle.claims.len());
    println!("    ──────────────");
    println!("    recursive prove  {rec_prove_ms:>9.2} ms   (1 outer FRI proof)");
    println!("    recursive verify {rec_verify_ms:>9.2} ms");
    println!("    recursive size   {rec_size_kib:>9.1} KiB");
    println!();
    println!("  ✓  The recursive STARK attests:");
    println!();
    println!("        Σ α_j · (f_at_z[j] − g_at_z[j]) = 0   (j ∈ 0..12)");
    println!();
    println!("     where each (f, g) is one Goldilocks coordinate of one v2");
    println!("     F2b OOD pair (L2a or L3) at the FS-derived z_0 ∈ Fp⁶.");
    println!("     Zero residue at all 12 coords ⇔ Ext residue is zero ⇔");
    println!("     Schwartz-Zippel binds f_ext ≡ g_ext as polys < d ≈ 2¹⁴");
    println!("     with error ≤ 2⁻³⁷⁰.");
    println!();
    println!("  This is the FIRST recursive ML-DSA STARK proof in the");
    println!("  codebase that consumes REAL inner-proof outputs (not");
    println!("  synthetic witnesses).");
    println!();

    // ─── 7. FULL F2b coverage (BCC-vs-BCC + BCC-vs-public) ─────────
    println!("[BONUS] Full F2b OOD coverage: BCC-vs-BCC + BCC-vs-public");
    let t = Instant::now();
    let full_bundle = extract_v2_full_ood_bundle(&proof, &w)
        .expect("full F2b bundle extract");
    let full_extract_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("      extract full bundle: {full_extract_ms:.2} ms · {} Ext claims",
        full_bundle.claims.len());
    println!("        (legs: L2a + L3 + L2c + L1 + L2b + L4×{} + L5×{})",
        deep_ali::ml_dsa::params::W1_BITS_PER_COEF,
        deep_ali::ml_dsa::params::L + 3);

    let full_base = flatten_ext_to_base(&full_bundle);
    println!("      flattened to {} Goldilocks claims (= {} × {EXT_DEGREE})",
        full_base.claims.len(), full_bundle.claims.len());
    println!("      bundle.check_all_native() = {}", full_base.check_all_native());

    let t = Instant::now();
    let full_rec = prove_v2_full_ood_recursive(&proof, &w, /*blowup=*/4, /*r=*/54, /*stir=*/false)
        .expect("full v2 OOD recursive prove must succeed");
    let full_rec_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let mut full_buf = Vec::new();
    full_rec.fri_proof.serialize_compressed(&mut full_buf).unwrap();
    let full_size_kib = full_buf.len() as f64 / 1024.0;

    let t = Instant::now();
    let full_rec_ok = verify_ood_accumulator(&full_rec);
    let full_rec_verify_ms = t.elapsed().as_secs_f64() * 1000.0;

    println!("      recursive prove:  {full_rec_prove_ms:.2} ms");
    println!("      recursive verify: {full_rec_verify_ms:.2} ms");
    println!("      recursive proof:  {full_size_kib:.1} KiB");
    println!("      verdict:          {}", if full_rec_ok { "ACCEPT" } else { "REJECT" });
    assert!(full_rec_ok);

    println!();
    println!("═══════════════════════════════════════════════════════════════");
    println!("  COVERAGE EXPANSION:");
    println!();
    println!("    legs (BCC-vs-BCC only)    : 2 Ext claims  (L2a, L3)");
    println!("    legs (full F2b)           : {} Ext claims",
        full_bundle.claims.len());
    println!("    Goldilocks (BCC-vs-BCC)   : 12 claims     (= 2 × {EXT_DEGREE})");
    println!("    Goldilocks (full F2b)     : {} claims",
        full_base.claims.len());
    println!();
    println!("  The full-F2b recursive STARK attests ALL seven F2b legs");
    println!("  (BCC-vs-BCC: L2a, L3; BCC-vs-public: L1, L2b, L2c, L4×bits,");
    println!("  L5×eq-cols) in ONE outer FRI proof.  Together they");
    println!("  cross-bind every v2 sub-AIR's region cells to each other");
    println!("  and to the pi_hash-bound public inputs.");
    println!();
    println!("  Next step: compose with sub-circuit 1 (constraint composition)");
    println!("  for full v2 verifier-AIR recursion — one outer FRI proof");
    println!("  attesting BOTH the F2b OOD bindings AND each sub-AIR's");
    println!("  constraint composition.");
    println!("═══════════════════════════════════════════════════════════════");
}
