//! ML-DSA-{44,65,87} signature rollup demo.
//!
//! Models a "blockchain-style rollup of ML-DSA signatures":
//! N inner ML-DSA verify STARKs (one per signature) aggregated into
//! ONE outer rollup STARK that commits to all N inner `pi_hash`-es
//! through the existing `HashRollup` AIR in `swarm-dns::prover`.
//!
//! Architecture:
//!
//! ```text
//!   sig 0 → V2Witness → prove_v2_real → V2ProofReal → pi_hash[0]   ┐
//!   sig 1 → V2Witness → prove_v2_real → V2ProofReal → pi_hash[1]   │
//!     ...                                                          ├─► prove_outer_rollup
//!   sig N-1 → V2Witness → prove_v2_real → V2ProofReal → pi_hash[N-1]┘     │
//!                                                                          ▼
//!                                                       DeepFriProof (outer)
//!                                                       attesting the bundle
//! ```
//!
//! The outer rollup AIR (`AirType::HashRollup`) is signature-algorithm-
//! oblivious: it just commits to N×32-byte digests.  Result is the
//! same shape used by `prove_outer_rollup` for DNS megazone shards
//! — re-purposed here for ML-DSA per-signature aggregation.
//!
//! # Run
//!
//! ```bash
//! # L1 — ML-DSA-44 (NIST PQ Level 1, SHA3-256)
//! cargo run --release -p swarm-dns --example ml_dsa_rollup_demo \
//!     --features "sha3-256" --no-default-features
//!
//! # L3 — ML-DSA-65 (NIST PQ Level 3, SHA3-384)
//! cargo run --release -p swarm-dns --example ml_dsa_rollup_demo \
//!     --no-default-features
//!     # but L3/L5 need recompiling deep_ali with the matching
//!     # mldsa-65/87 feature; see scripts/ml-dsa-rollup-demo.sh
//! ```
//!
//! Environment overrides:
//!
//! - `ROLLUP_N`: number of inner signatures (default 4)
//! - `ROLLUP_BLOWUP`: inner FRI blowup factor (default 4, smoke)
//! - `ROLLUP_LDT`: `fri` (default) or `stir`

use std::time::Instant;

use deep_ali::ml_dsa::params::C_TILDE_BYTES;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    V2ProofReal, prove_v2_real, synthesize_demo_witness, verify_v2_real,
};
use swarm_dns::prover::{LdtMode, prove_outer_rollup};

fn parse_env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn format_kib(bytes: usize) -> String { format!("{:.1} KiB", bytes as f64 / 1024.0) }

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("ML-DSA SIGNATURE ROLLUP DEMO");
    println!("═══════════════════════════════════════════════════════════════");
    println!();

    let n: usize = parse_env_usize("ROLLUP_N", 4);
    let blowup: usize = parse_env_usize("ROLLUP_BLOWUP", 4);
    let use_stir = std::env::var("ROLLUP_LDT").ok().as_deref() == Some("stir");
    let outer_ldt = if use_stir { LdtMode::Stir } else { LdtMode::Fri };

    #[cfg(feature = "sha3-256")]
    let nist_level = "L1 (sha3-256 + ML-DSA-44)";
    #[cfg(all(feature = "sha3-384", not(feature = "sha3-256")))]
    let nist_level = "L3 (sha3-384 + ML-DSA-65)";
    #[cfg(all(feature = "sha3-512", not(feature = "sha3-256"), not(feature = "sha3-384")))]
    let nist_level = "L5 (sha3-512 + ML-DSA-87)";

    println!("Configuration:");
    println!("  N (inner signatures):  {n}");
    println!("  Inner blowup:          {blowup}");
    println!("  Inner LDT:             {} (fixed FRI for per-sig)", "FRI");
    println!("  Outer LDT:             {}", if use_stir { "STIR" } else { "FRI" });
    println!("  NIST level:            {nist_level}");
    println!();

    // ─── Per-signature inner STARK proving ─────────────────────────
    println!("[INNER] Proving {n} ML-DSA verify STARKs sequentially…");
    println!();
    let mut pi_hashes: Vec<[u8; 32]> = Vec::with_capacity(n);
    let mut inner_proofs: Vec<V2ProofReal> = Vec::with_capacity(n);
    let mut inner_witnesses = Vec::with_capacity(n);
    let mut inner_c_tildes = Vec::with_capacity(n);
    let mut total_inner_prove_ms = 0.0_f64;
    let mut total_inner_verify_ms = 0.0_f64;
    let mut total_inner_bytes = 0usize;

    for sig_idx in 0..n {
        let t0 = Instant::now();
        let w = synthesize_demo_witness(sig_idx as u64);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let synth_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let t_prove = Instant::now();
        let proof = prove_v2_real(&w, &c_tilde, blowup);
        let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;
        total_inner_prove_ms += prove_ms;

        let t_verify = Instant::now();
        verify_v2_real(&w, &c_tilde, &proof, blowup)
            .expect("inner ML-DSA verify must accept honest proof");
        let verify_ms = t_verify.elapsed().as_secs_f64() * 1000.0;
        total_inner_verify_ms += verify_ms;

        let proof_bytes = proof.to_bytes();
        total_inner_bytes += proof_bytes.len();

        println!(
            "  sig {sig_idx:>2}:  synth {synth_ms:>6.1} ms   prove {prove_ms:>7.1} ms   \
             verify {verify_ms:>6.2} ms   size {:>9}   pi_hash={:02x}{:02x}{:02x}{:02x}…",
            format_kib(proof_bytes.len()),
            proof.pi_hash[0], proof.pi_hash[1], proof.pi_hash[2], proof.pi_hash[3],
        );

        pi_hashes.push(proof.pi_hash);
        inner_proofs.push(proof);
        inner_witnesses.push(w);
        inner_c_tildes.push(c_tilde);
    }

    // Pi_hashes must be unique — confirm seed-varied mu_bytes did its job.
    let mut sorted = pi_hashes.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), n, "pi_hashes collided — seed variance is broken");

    println!();
    println!(
        "  ─── inner totals: prove {total_inner_prove_ms:.1} ms · \
         verify {total_inner_verify_ms:.2} ms · size {} ───",
        format_kib(total_inner_bytes),
    );
    println!();

    // ─── Outer rollup STARK ─────────────────────────────────────────
    println!("[OUTER] Aggregating {n} pi_hashes into one HashRollup STARK…");
    let outer_pk_hash: [u8; 32] = {
        use ::sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        Digest::update(&mut h, b"ML-DSA-ROLLUP-DEMO-V1");
        Digest::update(&mut h, (n as u64).to_le_bytes());
        Digest::finalize(h).into()
    };

    let outer = prove_outer_rollup(&pi_hashes, &outer_pk_hash, outer_ldt);

    println!(
        "  outer:  prove {:>7.1} ms   verify {:>6.2} ms   size {:>9}   n_trace={}",
        outer.prove_ms, outer.local_verify_ms,
        format_kib(outer.proof_bytes), outer.n_trace,
    );
    println!();

    // ─── Composite summary ─────────────────────────────────────────
    let composite_prove = total_inner_prove_ms + outer.prove_ms;
    let composite_verify = total_inner_verify_ms + outer.local_verify_ms;
    let composite_size = total_inner_bytes + outer.proof_bytes;

    println!("═══════════════════════════════════════════════════════════════");
    println!("  ML-DSA ROLLUP COMPOSITE ({n} sigs → 1 outer rollup):");
    println!();
    println!("    inner total prove:    {total_inner_prove_ms:>9.1} ms ({n} × ML-DSA verify STARK)");
    println!("    inner total verify:   {total_inner_verify_ms:>9.2} ms");
    println!("    inner total size:     {:>9}", format_kib(total_inner_bytes));
    println!();
    println!("    outer rollup prove:   {:>9.1} ms (HashRollup over {n} pi_hashes)",
        outer.prove_ms);
    println!("    outer rollup verify:  {:>9.2} ms",   outer.local_verify_ms);
    println!("    outer rollup size:    {:>9}",        format_kib(outer.proof_bytes));
    println!();
    println!("    end-to-end prove:     {composite_prove:>9.1} ms");
    println!("    end-to-end verify:    {composite_verify:>9.2} ms");
    println!("    bundle on-wire size:  {:>9}",        format_kib(composite_size));
    println!();
    println!("    outer/inner overhead: prove {:.1}%   verify {:.1}%   size {:.1}%",
        100.0 * outer.prove_ms / total_inner_prove_ms,
        100.0 * outer.local_verify_ms / total_inner_verify_ms,
        100.0 * outer.proof_bytes as f64 / total_inner_bytes as f64);
    println!();
    println!("  Statement attested by the outer rollup:");
    println!("    ∃ {n} ML-DSA signature witnesses whose pi_hash-es ");
    println!("    Merkle-commit to a root committed into the outer FRI proof's");
    println!("    public-inputs hash.  Per-sig soundness from FRI/STIR at the");
    println!("    selected NIST PQ level; rollup soundness from SHA-3 CR over");
    println!("    the HashRollup AIR + outer FRI/STIR.");
    println!("═══════════════════════════════════════════════════════════════");

    // Drop references to large objects to release memory before exit.
    drop(inner_proofs);
    drop(inner_witnesses);
    drop(inner_c_tildes);
}
