//! ML-DSA recursive rollup demo — N inner v2 proofs → N recursive STARKs
//! → 1 outer HashRollup STARK.
//!
//! Companion to `ml_dsa_rollup_demo` (commit f1f947b).  Instead of
//! aggregating raw 7.4-MiB `V2ProofReal` outputs, this demo:
//!
//!   1. Produces each inner v2 ML-DSA verify STARK (`prove_v2_real`).
//!   2. Wraps it in a recursive STARK (`prove_v2_all_subairs_composed_recursive`)
//!      that compresses 7.4 MiB → 600 KiB (12.3× at L1 smoke).
//!   3. Aggregates the N recursive-STARK `outer_pi_hash`-es via
//!      `prove_outer_rollup` into one HashRollup outer FRI proof.
//!
//! Wire format per record drops from 7.4 MiB to 600 KiB; the outer
//! rollup is essentially free (~97 KiB STIR).  At N=8: ~5 MiB bundle
//! vs ~60 MiB for the non-recursive variant — **12× compression** of
//! the per-signature edge profile, with one outer FRI proof attesting
//! the Merkle commitment over all N recursive STARK pi_hashes.
//!
//! Architecturally, this is the "blockchain-style ML-DSA signature
//! rollup with recursive per-signature STARK compression" shape the
//! paper has been targeting.  Each on-chain signature ships as a
//! KiB-scale recursive STARK, and L+1 signatures aggregate into a
//! constant-size outer rollup.
//!
//! # Run
//!
//! ```bash
//! ROLLUP_N=4 ROLLUP_BLOWUP=4 ROLLUP_LDT=stir \
//!   cargo run --release -p swarm-dns --example ml_dsa_recursive_rollup_demo
//! ```
//!
//! Environment overrides:
//!
//!   ROLLUP_N        — number of inner signatures               (default 4)
//!   ROLLUP_BLOWUP   — inner v2 + recursive FRI blowup factor   (default 4)
//!   ROLLUP_LDT      — `fri` (default) or `stir` for the outer

use std::time::Instant;

use ark_serialize::CanonicalSerialize;

use deep_ali::ml_dsa::params::C_TILDE_BYTES;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    prove_v2_real, synthesize_demo_witness, verify_v2_real,
};

use swarm_dns::prover::{LdtMode, prove_outer_rollup};
use wrapper_stark::recursive_prover::verify_recursive_stark;
use wrapper_stark::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive;

fn parse_env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn format_kib(bytes: usize) -> String { format!("{:.1} KiB", bytes as f64 / 1024.0) }

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("ML-DSA RECURSIVE ROLLUP DEMO");
    println!("    (N inner v2 STARKs  →  N recursive STARKs  →  1 outer rollup)");
    println!("═══════════════════════════════════════════════════════════════");
    println!();

    let n: usize = parse_env_usize("ROLLUP_N", 4);
    // ROLLUP_BLOWUP controls the OUTER recursive STARK's blowup.  The
    // inner v2 ML-DSA verify STARK is held at its canonical blowup=4
    // (the wrapper-stark v2 bridge currently assumes this when
    // extracting per-sub-AIR residues).  Separating them lets us
    // sweep the recursive STARK's blowup independently while keeping
    // the inner proof shape stable.
    let blowup: usize = parse_env_usize("ROLLUP_BLOWUP", 4);
    let inner_blowup: usize = 4;

    // Auto-detect NIST level from build features.  The (sha3-*,
    // mldsa-*) feature pair determines both the inner v2 level and
    // the recursive STARK's bit-budget calibration.
    #[cfg(feature = "mldsa-44")] let nist_level: &str = "L1";
    #[cfg(feature = "mldsa-65")] let nist_level: &str = "L3";
    #[cfg(feature = "mldsa-87")] let nist_level: &str = "L5";
    #[cfg(feature = "sha3-256")] let sha3_label: &str = "sha3-256";
    #[cfg(all(feature = "sha3-384", not(feature = "sha3-256")))]
        let sha3_label: &str = "sha3-384";
    #[cfg(all(feature = "sha3-512", not(feature = "sha3-256"), not(feature = "sha3-384")))]
        let sha3_label: &str = "sha3-512";

    // Calibrated r per (level, blowup) from
    // scripts/results/r-vs-blowup-calibration.md.
    // Maintains the paper's per-level total bit budget (L1=135,
    // L3=197.5, L5=262.5) across all blowups.
    let recursive_r: usize = match (nist_level, blowup) {
        ("L1", 4)  => 135, ("L1", 8) => 90, ("L1", 16) => 68, ("L1", 32) => 54,
        ("L3", 4)  => 198, ("L3", 8) => 132, ("L3", 16) => 99, ("L3", 32) => 79,
        ("L5", 4)  => 263, ("L5", 8) => 175, ("L5", 16) => 132, ("L5", 32) => 105,
        _ => 54,
    };
    let recursive_r: usize = parse_env_usize("ROLLUP_R", recursive_r);
    let use_stir = std::env::var("ROLLUP_LDT").ok().as_deref() == Some("stir");
    let outer_ldt = if use_stir { LdtMode::Stir } else { LdtMode::Fri };

    // Auto-detect old hardcoded label and replace.
    println!("Configuration:");
    println!("  N (inner signatures):         {n}");
    println!("  NIST level:                   {nist_level} ({sha3_label})");
    println!("  Inner v2 blowup (fixed):      {inner_blowup}");
    println!("  Recursive STARK blowup:       {blowup}");
    println!("  Recursive r (calibrated):     {recursive_r}");
    println!("  Outer rollup LDT:             {}", if use_stir { "STIR" } else { "FRI" });
    println!();

    let mut inner_pi_hashes: Vec<[u8; 32]>     = Vec::with_capacity(n);
    let mut recursive_pi_hashes: Vec<[u8; 32]> = Vec::with_capacity(n);

    let mut total_inner_prove_ms = 0.0_f64;
    let mut total_inner_verify_ms = 0.0_f64;
    let mut total_inner_bytes = 0usize;

    let mut total_recursive_prove_ms = 0.0_f64;
    let mut total_recursive_verify_ms = 0.0_f64;
    let mut total_recursive_bytes = 0usize;

    println!("[1/3] Per-signature inner v2 prove + recursive STARK wrap …");
    println!();
    for sig_idx in 0..n {
        let w = synthesize_demo_witness(sig_idx as u64);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

        // Inner v2 ML-DSA verify STARK.
        let t = Instant::now();
        let v2_proof = prove_v2_real(&w, &c_tilde, inner_blowup);
        let inner_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
        total_inner_prove_ms += inner_prove_ms;

        // Verify the inner proof natively (sanity).
        let t = Instant::now();
        verify_v2_real(&w, &c_tilde, &v2_proof, inner_blowup)
            .expect("inner v2 verify must accept");
        let inner_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        total_inner_verify_ms += inner_verify_ms;

        let inner_bytes = v2_proof.to_bytes();
        total_inner_bytes += inner_bytes.len();

        // Recursive STARK wrap.
        let t = Instant::now();
        let rec = prove_v2_all_subairs_composed_recursive(
            &v2_proof, &w, blowup, recursive_r, /*stir=*/false,
        ).expect("recursive STARK wrap must succeed");
        let rec_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
        total_recursive_prove_ms += rec_prove_ms;

        // Verify recursive STARK locally.
        let t = Instant::now();
        let rec_ok = verify_recursive_stark(&rec);
        let rec_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        total_recursive_verify_ms += rec_verify_ms;
        assert!(rec_ok, "recursive STARK must verify locally on honest input");

        let mut rec_buf = Vec::new();
        rec.fri_proof.serialize_compressed(&mut rec_buf).unwrap();
        total_recursive_bytes += rec_buf.len();

        let compression = inner_bytes.len() as f64 / rec_buf.len() as f64;
        println!(
            "  sig {sig_idx:>2}:  inner prove {inner_prove:>7.1} ms · {inner_size:>9}   \
             →   rec prove {rec_prove:>7.1} ms · {rec_size:>8}  ({comp:.1}×)",
            inner_prove = inner_prove_ms, inner_size = format_kib(inner_bytes.len()),
            rec_prove = rec_prove_ms, rec_size = format_kib(rec_buf.len()),
            comp = compression,
        );

        inner_pi_hashes.push(v2_proof.pi_hash);
        recursive_pi_hashes.push(rec.public.outer_pi_hash);
    }
    println!();

    // ─── Outer rollup over the RECURSIVE pi_hashes ─────────────────
    println!("[2/3] Outer HashRollup STARK over {n} recursive outer_pi_hashes …");
    let outer_pk_hash: [u8; 32] = {
        use ::sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        Digest::update(&mut h, b"ML-DSA-RECURSIVE-ROLLUP-DEMO-V1");
        Digest::update(&mut h, (n as u64).to_le_bytes());
        Digest::finalize(h).into()
    };
    let outer = prove_outer_rollup(&recursive_pi_hashes, &outer_pk_hash, outer_ldt);
    println!(
        "  outer:  prove {:>7.1} ms   verify {:>5.2} ms   size {:>9}   n_trace={}",
        outer.prove_ms, outer.local_verify_ms,
        format_kib(outer.proof_bytes), outer.n_trace,
    );
    println!();

    // ─── Bundle totals ──────────────────────────────────────────────
    println!("[3/3] Bundle composition");
    let inner_only_bundle = total_inner_bytes + outer.proof_bytes;
    let recursive_bundle = total_recursive_bytes + outer.proof_bytes;
    let bundle_compression = inner_only_bundle as f64 / recursive_bundle as f64;
    println!();
    println!("  ─── inner-only path (raw v2 proofs aggregated, baseline) ───");
    println!("        Σ inner prove:        {:>9.1} ms",  total_inner_prove_ms);
    println!("        Σ inner size:         {:>9}",        format_kib(total_inner_bytes));
    println!("        outer rollup size:    {:>9}",        format_kib(outer.proof_bytes));
    println!("        on-wire bundle:       {:>9}",        format_kib(inner_only_bundle));
    println!();
    println!("  ─── recursive path (this demo) ───");
    println!("        Σ inner prove:        {:>9.1} ms  (still required for the inner proof)",
        total_inner_prove_ms);
    println!("        Σ recursive prove:    {:>9.1} ms  (per-sig wrap)",
        total_recursive_prove_ms);
    println!("        Σ recursive verify:   {:>9.2} ms",  total_recursive_verify_ms);
    println!("        Σ recursive size:     {:>9}",        format_kib(total_recursive_bytes));
    println!("        outer rollup size:    {:>9}",        format_kib(outer.proof_bytes));
    println!("        on-wire bundle:       {:>9}",        format_kib(recursive_bundle));
    println!();
    println!("═══════════════════════════════════════════════════════════════");
    println!("  HEADLINE: ML-DSA SIGNATURE ROLLUP — WIRE-SIZE COMPRESSION");
    println!();
    println!("    metric                  inner-only       recursive       ratio");
    println!("    on-wire bundle          {:>10}     {:>10}    {bundle_compression:>5.1}×",
        format_kib(inner_only_bundle), format_kib(recursive_bundle));
    println!("    per-signature           {:>10}     {:>10}    {:>5.1}×",
        format_kib(total_inner_bytes / n.max(1)),
        format_kib(total_recursive_bytes / n.max(1)),
        total_inner_bytes as f64 / total_recursive_bytes as f64);
    println!();
    println!("  The recursive path adds ~{:.0} ms/sig of additional prove",
        total_recursive_prove_ms / n as f64);
    println!("  time for the recursive wrap.  In return, each signature");
    println!("  ships as a KiB-scale recursive STARK proof, and N");
    println!("  signatures aggregate into a constant-size outer rollup.");
    println!();
    println!("  Statement attested by the outer rollup:");
    println!("    ∃ {n} recursive ML-DSA STARK proofs whose outer_pi_hashes");
    println!("    Merkle-commit to a root committed into the outer FRI");
    println!("    proof's public-inputs hash.  Each recursive STARK in");
    println!("    turn attests sub-circuits 1-3 over a real v2 ML-DSA");
    println!("    verify STARK at the selected NIST PQ level.");
    println!("═══════════════════════════════════════════════════════════════");

    // Drop large objects before exit.
    let _ = (inner_pi_hashes, recursive_pi_hashes);
}
