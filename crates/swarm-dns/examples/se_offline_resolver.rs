//! STARK-DNS Phase 3 offline resolver — paper §IV-D.
//!
//! Reads the .se epoch package produced by `se_zone_demo`, verifies it
//! end-to-end (ML-DSA-65 signature + outer STARK FRI proof), then
//! answers DNS queries OFFLINE against the committed corpus via Merkle
//! inclusion proofs.  **NO network access** after the one-time epoch
//! package load — true offline DNSSEC resolution with post-quantum
//! integrity guarantees.
//!
//! # Run
//!
//! ```bash
//! # Step 1: produce the epoch package from real .se DNS data
//! cargo run --release -p swarm-dns --example se_zone_demo \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features
//!
//! # Step 2: offline-resolve queries from the package
//! cargo run --release -p swarm-dns --example se_offline_resolver \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features
//! ```

use std::time::Instant;

use ark_serialize::{CanonicalDeserialize, Compress, Validate};

use deep_ali::fri::{DeepFriParams, deep_fri_verify};
use deep_ali::sextic_ext::SexticExt;

use swarm_dns::prover::{BLOWUP, LdtMode, NUM_QUERIES, SEED_Z, make_schedule};
use swarm_dns::se_epoch_package::{
    InclusionResult, ML_DSA_CTX, SeEpochPackage, load_from_file, resolve,
};

type Ext = SexticExt;

/// Re-construct the FRI params the outer-rollup prover used to produce
/// `package.outer_stark_proof`.  Mirrors `prove_outer_rollup` in
/// `swarm_dns::prover` so the resolver can re-verify offline.
fn outer_fri_params(package: &SeEpochPackage, pk_hash: [u8; 32]) -> DeepFriParams {
    let n0 = package.outer_n_trace * BLOWUP;
    DeepFriParams {
        schedule: make_schedule(n0, LdtMode::Stir),
        r: NUM_QUERIES,
        seed_z: SEED_Z,
        coeff_commit_final: true,
        d_final: 1,
        stir: true,
        s0: NUM_QUERIES,
        public_inputs_hash: Some(pk_hash),
    }
}

fn verify_package(package: &SeEpochPackage) -> Result<f64, String> {
    use fips204::ml_dsa_65;
    use fips204::traits::{SerDes, Verifier};

    // 1. ML-DSA-65 signature verify.
    let t_total = Instant::now();
    let pk_bytes: [u8; ml_dsa_65::PK_LEN] = package.authority_pk.as_slice()
        .try_into().map_err(|_|
            format!("authority_pk wrong length: expected {} B, got {} B",
                ml_dsa_65::PK_LEN, package.authority_pk.len()))?;
    let pk = ml_dsa_65::PublicKey::try_from_bytes(pk_bytes)
        .map_err(|e| format!("malformed ML-DSA pk: {e:?}"))?;
    let sig_bytes: [u8; ml_dsa_65::SIG_LEN] = package.authority_sig.as_slice()
        .try_into().map_err(|_|
            format!("authority_sig wrong length: expected {} B, got {} B",
                ml_dsa_65::SIG_LEN, package.authority_sig.len()))?;
    let binding = package.binding_hash();
    let t_mldsa = Instant::now();
    if !pk.verify(&binding, &sig_bytes, ML_DSA_CTX) {
        return Err("ML-DSA-65 signature verification FAILED".into());
    }
    let mldsa_ms = t_mldsa.elapsed().as_secs_f64() * 1000.0;

    // 2. Outer STARK FRI verify.
    let t_outer = Instant::now();
    let outer_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        package.outer_stark_proof.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|e| format!("outer STARK proof malformed: {e:?}"))?;
    // For the FS binding we recompute the same `fs_binding_32` the
    // prover used.  In `se_zone_demo` that's
    //   SHA3-256("STARK-DNS-SE-DEMO-SHARD-FS-V1" || merkle_root).
    use sha3::{Digest, Sha3_256};
    let mut h = Sha3_256::new();
    h.update(b"STARK-DNS-SE-DEMO-SHARD-FS-V1");
    h.update(package.merkle_root);
    let fs_binding: [u8; 32] = h.finalize().into();

    let outer_params = outer_fri_params(package, fs_binding);
    if !deep_fri_verify::<Ext>(&outer_params, &outer_proof) {
        return Err("outer STARK FRI verify FAILED".into());
    }
    let outer_ms = t_outer.elapsed().as_secs_f64() * 1000.0;
    let total_ms = t_total.elapsed().as_secs_f64() * 1000.0;

    println!("  ✓ ML-DSA-65 signature verify:  {mldsa_ms:>6.3} ms");
    println!("  ✓ Outer STARK FRI verify:      {outer_ms:>6.3} ms");
    println!("  ─────────────────────────────");
    println!("  ✓ One-time epoch acceptance:   {total_ms:>6.3} ms");
    Ok(total_ms)
}

fn show_inclusion(domain: &str, rtype: u16, result: &InclusionResult) {
    let r = result.record;
    let rdata_preview = if r.rdata.len() > 16 {
        format!("{}…", hex::encode(&r.rdata[..16]))
    } else {
        hex::encode(&r.rdata)
    };
    println!(
        "  {domain:24} type={rtype:>3}  alg={:<3}  idx={:>4}  depth={:>2}  rdata={}",
        r.algorithm, result.leaf_index, result.merkle_path.len(),
        rdata_preview,
    );
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("STARK-DNS — Phase 3 OFFLINE resolver (.se HNPL)");
    println!("    NO NETWORK — verifies epoch package + serves queries");
    println!("    against committed corpus via Merkle inclusion proofs");
    println!("═══════════════════════════════════════════════════════════════");
    println!();

    let package_path = std::path::PathBuf::from(
        std::env::var("SE_EPOCH_PACKAGE_PATH")
            .unwrap_or_else(|_| "target/se-epoch-package.bin".to_string())
    );
    println!("[Phase 2 read] Loading epoch package from {} …", package_path.display());
    let t_load = Instant::now();
    let package = match load_from_file(&package_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("ERROR: could not load epoch package: {e}");
            eprintln!("Run `cargo run --example se_zone_demo …` first to produce one.");
            std::process::exit(1);
        }
    };
    let load_ms = t_load.elapsed().as_secs_f64() * 1000.0;
    let raw_size = std::fs::metadata(&package_path)
        .map(|m| m.len()).unwrap_or(0);
    println!("  loaded {} bytes ({:.1} KiB) in {load_ms:.1} ms",
        raw_size, raw_size as f64 / 1024.0);
    println!("  format version: {}", package.version);
    println!("  epoch T:        {}  seq={}", package.epoch_t, package.epoch_seq);
    println!("  records:        {} committed", package.records.len());
    println!("  merkle root:    {}", hex::encode(&package.merkle_root[..16]));
    println!();

    // ─── Verify the package ─────────────────────────────────────────
    println!("[Phase 3 verify] One-time epoch acceptance:");
    let _verify_ms = match verify_package(&package) {
        Ok(ms) => ms,
        Err(e) => {
            eprintln!("  ✗ {e}");
            eprintln!("EPOCH REJECTED — refusing to serve queries.");
            std::process::exit(2);
        }
    };
    println!();

    // ─── Offline DNS queries ────────────────────────────────────────
    println!("[Phase 3 resolve] Offline queries against committed corpus:");
    println!();
    println!("  {:<24} {:<10} {:<6} {:<5} {:<5} rdata", "domain", "type", "alg", "idx", "depth");
    println!("  {:─<80}", "");

    // Pick up to 8 records spanning different algorithms for the demo.
    let mut algos_seen = std::collections::HashSet::new();
    let mut demo_targets: Vec<(String, u16)> = Vec::new();
    for r in &package.records {
        if algos_seen.insert(r.algorithm) {
            demo_targets.push((r.domain.clone(), r.record_type));
        }
        if demo_targets.len() >= 8 { break; }
    }
    if demo_targets.len() < 5 {
        for r in package.records.iter().take(8) {
            let key = (r.domain.clone(), r.record_type);
            if !demo_targets.contains(&key) {
                demo_targets.push(key);
            }
            if demo_targets.len() >= 8 { break; }
        }
    }

    let mut total_query_time_us = 0.0_f64;
    let mut accepted = 0usize;
    let mut rejected = 0usize;
    for (domain, rtype) in &demo_targets {
        let t = Instant::now();
        let result = resolve(&package, domain, *rtype);
        let dt_us = t.elapsed().as_secs_f64() * 1_000_000.0;
        total_query_time_us += dt_us;
        match result {
            Some(r) => {
                accepted += 1;
                show_inclusion(domain, *rtype, &r);
            }
            None => {
                rejected += 1;
                println!("  {domain:24} type={rtype:>3}  NOT FOUND or Merkle path mismatch");
            }
        }
    }
    let avg_us = if !demo_targets.is_empty() {
        total_query_time_us / demo_targets.len() as f64
    } else { 0.0 };

    println!();
    println!("  Queries answered: {accepted}/{}, average lookup: {avg_us:.1} µs",
        demo_targets.len());
    if rejected > 0 {
        println!("  Rejected (not found / inclusion mismatch): {rejected}");
    }
    println!();

    // ─── Tamper-detection demo ──────────────────────────────────────
    println!("[Tamper test] Mutate one byte of authority_sig and re-verify:");
    let mut tampered = package.clone();
    tampered.authority_sig[0] ^= 0xFF;
    match verify_package(&tampered) {
        Ok(_) => println!("  ✗ FAILED — tampered sig wrongly accepted (this is a bug)"),
        Err(e) => println!("  ✓ correctly rejected:  {e}"),
    }
    println!();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  TRUE OFFLINE DNS RESOLUTION DEMONSTRATED");
    println!();
    println!("  ✓ Loaded a self-contained {:.1} KiB epoch package",
        raw_size as f64 / 1024.0);
    println!("  ✓ Verified once via ML-DSA-65 + outer STARK FRI");
    println!("  ✓ Answered {accepted} DNS queries in {:.1} µs total ({avg_us:.1} µs avg)",
        total_query_time_us);
    println!("  ✓ NO NETWORK calls; NO secret state; NO ongoing trust");
    println!();
    println!("  Post-quantum integrity: STARK soundness rests on SHA-3");
    println!("  collision resistance + ML-DSA-65 EUF-CMA — both PQ-secure.");
    println!("  A future CRQC adversary breaking RSA/ECDSA cannot forge");
    println!("  any record committed in this epoch package.");
    println!("═══════════════════════════════════════════════════════════════");
}
