//! End-to-end demo: SHA-3 pre-image proof-of-knowledge gadget.
//!
//! Demonstrates wrapper-stark as a **library of composable AIR gadgets**.
//! This example uses ONE gadget (`prove_sha3_air` / `verify_sha3_air`)
//! to prove "I know `m` such that SHA-3(m) = D" without revealing m.
//!
//! Later gadgets (verifier-as-AIR for `deep_ali_merge`, Merkle-path
//! verification, binding-cells-commit OOD) will follow the same shape
//! and compose with this one to form the recursive ML-DSA wrapper.
//!
//! # Run
//!
//! ```text
//! cargo run --release -p wrapper-stark \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features \
//!     --example sha3_preimage_pok
//! ```
//!
//! # Statement
//!
//! Public:  variant ∈ {SHA3-256, SHA3-384, SHA3-512}, digest D
//! Witness: message m
//! Claim:   SHA-3_variant(m) = D, and the prover knows m
//!
//! # Output shape (example, M4 release, L1 STIR, blowup=4)
//!
//!   prove:  ~340 ms
//!   verify:   ~0.3 ms
//!   proof:   ~81 KiB

use std::time::Instant;

use ark_serialize::CanonicalSerialize;

use wrapper_stark::sha3_absorb_air::Sha3Variant;
use wrapper_stark::wrapper_prover::{
    Sha3StarkProof, Sha3StarkPublicInputs, prove_sha3_air, verify_sha3_air,
};

fn main() {
    // ─── 1. Pick the variant and a secret message ─────────────────
    //
    // The variant is fixed at compile time by the cargo --features
    // selection.  The example below selects which one we exercise
    // at runtime (matching whatever feature is active).
    #[cfg(feature = "sha3-256")] let variant = Sha3Variant::Sha3_256;
    #[cfg(all(feature = "sha3-384", not(feature = "sha3-256")))]
        let variant = Sha3Variant::Sha3_384;
    #[cfg(all(feature = "sha3-512", not(feature = "sha3-256"), not(feature = "sha3-384")))]
        let variant = Sha3Variant::Sha3_512;

    let message: &[u8] = b"the password is open-sesame";
    let blowup = 4;
    let r = match variant {
        Sha3Variant::Sha3_256 => 54,
        Sha3Variant::Sha3_384 => 79,
        Sha3Variant::Sha3_512 => 105,
    };
    let use_stir = true;  // 4.4× smaller proof + 3.7× faster verify vs FRI

    println!("═══════════════════════════════════════════════════════════");
    println!("SHA-3 PRE-IMAGE PROOF-OF-KNOWLEDGE  ({:?}, r={r}, blowup={blowup})", variant);
    println!("═══════════════════════════════════════════════════════════");
    println!();

    // ─── 2. Prover: compute the digest and produce a proof ────────
    println!("[prover] computing digest from secret message ({} bytes)...",
             message.len());
    let public_expected = Sha3StarkPublicInputs::for_message(variant, message);
    println!("[prover] digest = {}", hex(&public_expected.digest));

    let t0 = Instant::now();
    let proof: Sha3StarkProof = prove_sha3_air(message, variant, blowup, r, use_stir)
        .expect("prove must succeed on a valid witness");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let mut proof_bytes = Vec::new();
    proof.fri_proof.serialize_compressed(&mut proof_bytes)
        .expect("serialise proof");
    println!("[prover] prove time : {prove_ms:.0} ms");
    println!("[prover] proof size : {:.1} KiB", proof_bytes.len() as f64 / 1024.0);
    println!("[prover] pi_hash    : {}", hex(&proof.public.pi_hash));
    println!();

    // ─── 3. Verifier: receives (variant, digest, proof) ──────────
    //
    // The verifier sees the PUBLIC digest, the proof, and the public
    // inputs.  They do NOT learn `message`.  They check:
    // (a) the digest in the proof's public inputs matches what they expect
    // (b) the FRI proof verifies, which transitively attests that
    //     state_out[last] = digest via the row-uniform AIR + boundary
    println!("[verifier] expected digest = {}", hex(&public_expected.digest));
    println!("[verifier] proof's digest  = {}", hex(&proof.public.digest));
    assert_eq!(proof.public.digest, public_expected.digest,
        "verifier's expected digest must match proof's public-input digest");

    let t_v = Instant::now();
    let ok = verify_sha3_air(&proof);
    let verify_ms = t_v.elapsed().as_secs_f64() * 1000.0;
    println!("[verifier] verify time : {verify_ms:.2} ms");
    println!("[verifier] verdict     : {}", if ok { "ACCEPT" } else { "REJECT" });
    assert!(ok, "honest verifier must accept honest proof");
    println!();

    // ─── 4. Soundness demo: tamper the claimed digest, expect reject ─
    println!("[soundness] flipping a byte of the claimed digest...");
    let mut tampered = clone_proof(&proof);
    tampered.public.digest[0] ^= 0xFF;
    // The verifier rederives pi_hash from the (tampered) digest so it
    // matches the public inputs.  The FRI verify still rejects because
    // the boundary constraint was committed against the original digest.
    tampered.public = Sha3StarkPublicInputs::for_digest(
        tampered.public.variant, &tampered.public.digest,
    );
    let bad_ok = verify_sha3_air(&tampered);
    println!("[soundness] tampered verdict: {}",
             if bad_ok { "ACCEPT  (BUG!)" } else { "REJECT  (correct)" });
    assert!(!bad_ok, "verifier MUST reject when claimed digest doesn't match the trace");
    println!();

    println!("═══════════════════════════════════════════════════════════");
    println!("  ✓ Statement proven:");
    println!("    \"I know a pre-image m such that SHA-3({:?})(m) = D\"", variant);
    println!("    where D = {}", hex(&proof.public.digest));
    println!();
    println!("  ✓ Soundness validated: tampering the claimed digest");
    println!("    breaks the boundary commit + FS-derived FRI challenges.");
    println!();
    println!("  prove={prove_ms:.0}ms verify={verify_ms:.2}ms proof={:.1}KiB",
             proof_bytes.len() as f64 / 1024.0);
    println!("═══════════════════════════════════════════════════════════");
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
}

/// Sha3StarkProof contains a DeepFriProof<SexticExt> which doesn't
/// implement Clone, so we reconstruct via prove for the tamper demo.
/// In this small example we just reprove — for larger setups a real
/// implementation would clone via serialise/deserialise.
fn clone_proof(p: &Sha3StarkProof) -> Sha3StarkProof {
    // For this demo, just re-prove from the same message that produced
    // the original proof.  This isn't a real clone path; the tamper
    // demo just needs a fresh Sha3StarkProof we can mutate.
    let message: &[u8] = b"the password is open-sesame";
    prove_sha3_air(
        message, p.public.variant, p.blowup, p.r, p.use_stir,
    ).expect("reprove for tamper demo")
}
