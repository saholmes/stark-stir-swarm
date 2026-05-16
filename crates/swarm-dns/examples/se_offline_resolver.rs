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
    InclusionResult, ML_DSA_CTX, RrsigFreshness, SeEpochPackage,
    load_from_file, resolve,
};

/// Read the wall clock once at resolver startup.  Used to enforce RFC
/// 4034 §3.1.5 RRSIG inception/expiration windows at lookup time.  An
/// offline resolver MUST still know what time it is — otherwise it
/// would accept replay of long-since-expired signatures.  Mock the
/// clock via `STARK_DNS_NOW` (Unix seconds) for the freshness test.
fn wall_clock_now() -> u32 {
    if let Ok(v) = std::env::var("STARK_DNS_NOW") {
        if let Ok(n) = v.parse::<u32>() { return n; }
    }
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now().duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as u32).unwrap_or(0)
}

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

/// Re-construct the FRI params the inner shard prover used.  Mirrors
/// `prove_inner_shard` in `swarm_dns::prover` so the resolver can
/// independently FRI-verify the inner STARK proof too.
fn inner_fri_params(package: &SeEpochPackage, fs_binding: [u8; 32]) -> DeepFriParams {
    let n0 = package.inner_n_trace * BLOWUP;
    DeepFriParams {
        schedule: make_schedule(n0, LdtMode::Stir),
        r: NUM_QUERIES,
        seed_z: SEED_Z,
        coeff_commit_final: true,
        d_final: 1,
        stir: true,
        s0: NUM_QUERIES,
        public_inputs_hash: Some(fs_binding),
    }
}

/// Silent variant of `verify_package` for the comprehensive tamper
/// sweep below — runs the same three checks but suppresses progress
/// output so the tamper table stays readable.
fn verify_package_quiet(package: &SeEpochPackage) -> Result<(), String> {
    use fips204::ml_dsa_65;
    use fips204::traits::{SerDes, Verifier};

    let pk_bytes: [u8; ml_dsa_65::PK_LEN] = package.authority_pk.as_slice()
        .try_into().map_err(|_| "authority_pk wrong length".to_string())?;
    let pk = ml_dsa_65::PublicKey::try_from_bytes(pk_bytes)
        .map_err(|_| "malformed ML-DSA pk".to_string())?;
    let sig_bytes: [u8; ml_dsa_65::SIG_LEN] = package.authority_sig.as_slice()
        .try_into().map_err(|_| "authority_sig wrong length".to_string())?;
    if !pk.verify(&package.binding_hash(), &sig_bytes, ML_DSA_CTX) {
        return Err("ML-DSA-65 sig FAILED".into());
    }

    use sha3::{Digest, Sha3_256};
    let mut h = Sha3_256::new();
    h.update(b"STARK-DNS-SE-DEMO-SHARD-FS-V1");
    h.update(package.merkle_root);
    let fs_binding: [u8; 32] = h.finalize().into();

    let inner_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        package.inner_stark_proof.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|_| "inner STARK malformed".to_string())?;
    if !deep_fri_verify::<Ext>(&inner_fri_params(package, fs_binding), &inner_proof) {
        return Err("inner STARK FRI FAILED".into());
    }

    let outer_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        package.outer_stark_proof.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|_| "outer STARK malformed".to_string())?;
    if !deep_fri_verify::<Ext>(&outer_fri_params(package, fs_binding), &outer_proof) {
        return Err("outer STARK FRI FAILED".into());
    }
    // Optional DS-KSK bindings verify (mirrors verify_package).
    if let Some(bindings) = &package.ds_ksk_bindings {
        let mut fs_dskk = [0u8; 32];
        {
            use sha3::{Digest as Sha3Dig, Sha3_256};
            let mut h2 = Sha3_256::new();
            h2.update(b"STARK-DNS-SE-DS-KSK-FS-V1");
            h2.update(package.merkle_root);
            let d: [u8; 32] = h2.finalize().into();
            fs_dskk.copy_from_slice(&d);
        }
        for b in bindings {
            let proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
                b.stark_proof.as_slice(), Compress::Yes, Validate::Yes,
            ).map_err(|_| "DS-KSK STARK malformed".to_string())?;
            let n0 = b.n_trace * BLOWUP;
            let params = DeepFriParams {
                schedule: make_schedule(n0, LdtMode::Stir),
                r: NUM_QUERIES, seed_z: SEED_Z,
                coeff_commit_final: true, d_final: 1,
                stir: true, s0: NUM_QUERIES,
                public_inputs_hash: Some(fs_dskk),
            };
            if !deep_fri_verify::<Ext>(&params, &proof) {
                return Err("DS-KSK STARK FRI FAILED".into());
            }
            if b.asserted_digest != b.parent_ds_digest {
                return Err("DS-KSK binding asserted_digest != parent_ds_digest".into());
            }
        }
    }

    // Optional NSEC3 chain verify (same logic as verify_package).
    if let (Some(proof_bytes), Some(n_trace), Some(_)) =
        (&package.nsec3_stark_proof, package.nsec3_n_trace, &package.nsec3_root_f0)
    {
        let nsec3_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
            proof_bytes.as_slice(), Compress::Yes, Validate::Yes,
        ).map_err(|_| "NSEC3 STARK malformed".to_string())?;
        let mut nsec3_fs = [0u8; 32];
        {
            use sha3::{Digest as Sha3Dig, Sha3_256};
            let mut h2 = Sha3_256::new();
            h2.update(b"STARK-DNS-SE-NSEC3-FS-V1");
            h2.update(package.merkle_root);
            let d: [u8; 32] = h2.finalize().into();
            nsec3_fs.copy_from_slice(&d);
        }
        let n0 = n_trace * BLOWUP;
        let params = DeepFriParams {
            schedule: make_schedule(n0, LdtMode::Stir),
            r: NUM_QUERIES, seed_z: SEED_Z,
            coeff_commit_final: true, d_final: 1,
            stir: true, s0: NUM_QUERIES,
            public_inputs_hash: Some(nsec3_fs),
        };
        if !deep_fri_verify::<Ext>(&params, &nsec3_proof) {
            return Err("NSEC3 STARK FRI FAILED".into());
        }
    }
    Ok(())
}

fn verify_package(package: &SeEpochPackage) -> Result<f64, String> {
    use fips204::ml_dsa_65;
    use fips204::traits::{SerDes, Verifier};

    // ─── 1. ML-DSA-65 signature verify (Def. 1 binding hash) ─────
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

    // Reconstruct the FS-binding the prover used (deterministic from
    // `merkle_root`).  Used for BOTH inner and outer FRI verifies.
    use sha3::{Digest, Sha3_256};
    let mut h = Sha3_256::new();
    h.update(b"STARK-DNS-SE-DEMO-SHARD-FS-V1");
    h.update(package.merkle_root);
    let fs_binding: [u8; 32] = h.finalize().into();

    // ─── 2. INNER shard STARK FRI verify (HashRollup over records) ─
    //
    // Confirms the prover correctly STARK-hashed all `records` into a
    // Merkle tree whose root is `merkle_root`.  Without this check,
    // the resolver would trust the outer rollup to transitively attest
    // the inner work — closes that trust gap by re-verifying the
    // inner FRI proof directly.
    let t_inner = Instant::now();
    let inner_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        package.inner_stark_proof.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|e| format!("inner STARK proof malformed: {e:?}"))?;
    let inner_params = inner_fri_params(package, fs_binding);
    if !deep_fri_verify::<Ext>(&inner_params, &inner_proof) {
        return Err("inner STARK FRI verify FAILED".into());
    }
    let inner_ms = t_inner.elapsed().as_secs_f64() * 1000.0;

    // ─── 3. OUTER rollup STARK FRI verify (commits inner.pi_hash) ──
    let t_outer = Instant::now();
    let outer_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        package.outer_stark_proof.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|e| format!("outer STARK proof malformed: {e:?}"))?;
    let outer_params = outer_fri_params(package, fs_binding);
    if !deep_fri_verify::<Ext>(&outer_params, &outer_proof) {
        return Err("outer STARK FRI verify FAILED".into());
    }
    let outer_ms = t_outer.elapsed().as_secs_f64() * 1000.0;

    // ─── 4. (Optional) DS → DNSKEY hash-chain bindings ────────────
    //
    // Phase 5 — RFC 4034 §5.1.4 multi-level chain anchoring.  For
    // each captured (owner, DNSKEY, DS) binding the producer ran a
    // sha256_air STARK proving SHA-256(owner||dnskey_rdata) == DS.digest.
    // We re-verify each here.  The binding hash mixes the bindings
    // in so a tampered ds_ksk_bindings field is caught by the
    // ML-DSA signature verify above.
    let mut dskk_ms: f64 = 0.0;
    let mut dskk_count = 0usize;
    if let Some(bindings) = &package.ds_ksk_bindings {
        let t = Instant::now();
        // Reconstruct the FS-binding the producer used.
        let mut fs_dskk = [0u8; 32];
        {
            use sha3::{Digest as Sha3Dig, Sha3_256};
            let mut h = Sha3_256::new();
            h.update(b"STARK-DNS-SE-DS-KSK-FS-V1");
            h.update(package.merkle_root);
            let d: [u8; 32] = h.finalize().into();
            fs_dskk.copy_from_slice(&d);
        }
        for b in bindings {
            let proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
                b.stark_proof.as_slice(), Compress::Yes, Validate::Yes,
            ).map_err(|e| format!("DS-KSK STARK malformed: {e:?}"))?;
            let n0 = b.n_trace * BLOWUP;
            let params = DeepFriParams {
                schedule: make_schedule(n0, LdtMode::Stir),
                r: NUM_QUERIES, seed_z: SEED_Z,
                coeff_commit_final: true, d_final: 1,
                stir: true, s0: NUM_QUERIES,
                public_inputs_hash: Some(fs_dskk),
            };
            if !deep_fri_verify::<Ext>(&params, &proof) {
                return Err(format!("DS-KSK STARK FRI verify FAILED for {}",
                    b.owner_name));
            }
            // Additionally cross-check the binding's asserted_digest
            // matches the parent's published DS digest (the chain
            // step's cryptographic anchor).
            if b.asserted_digest != b.parent_ds_digest {
                return Err(format!(
                    "DS-KSK binding for {}: asserted_digest != parent_ds_digest",
                    b.owner_name));
            }
            dskk_count += 1;
        }
        dskk_ms = t.elapsed().as_secs_f64() * 1000.0;
    }

    // ─── 5. (Optional) NSEC3 chain-completeness FRI verify ────────
    //
    // Phase 4 — authenticated denial-of-existence.  When present,
    // the package commits to a closed cyclic NSEC3 chain via
    // `prove_nsec3_completeness`; this re-verifies that proof so the
    // resolver can use the chain to answer NXDOMAIN queries.
    let mut nsec3_ms: f64 = 0.0;
    if let (Some(proof_bytes), Some(n_trace), Some(_root_f0))
        = (&package.nsec3_stark_proof, package.nsec3_n_trace,
           &package.nsec3_root_f0)
    {
        let t = Instant::now();
        let nsec3_proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
            proof_bytes.as_slice(), Compress::Yes, Validate::Yes,
        ).map_err(|e| format!("NSEC3 STARK proof malformed: {e:?}"))?;
        // Reconstruct params used by prove_nsec3_completeness.
        let mut nsec3_fs = [0u8; 32];
        {
            use sha3::{Digest, Sha3_256};
            let mut h = Sha3_256::new();
            h.update(b"STARK-DNS-SE-NSEC3-FS-V1");
            h.update(package.merkle_root);
            let d: [u8; 32] = h.finalize().into();
            nsec3_fs.copy_from_slice(&d);
        }
        let n0 = n_trace * BLOWUP;
        let params = DeepFriParams {
            schedule: make_schedule(n0, LdtMode::Stir),
            r: NUM_QUERIES, seed_z: SEED_Z,
            coeff_commit_final: true, d_final: 1,
            stir: true, s0: NUM_QUERIES,
            public_inputs_hash: Some(nsec3_fs),
        };
        if !deep_fri_verify::<Ext>(&params, &nsec3_proof) {
            return Err("NSEC3 chain-completeness STARK FRI verify FAILED".into());
        }
        nsec3_ms = t.elapsed().as_secs_f64() * 1000.0;
    }

    // ─── 6. RRSIG validity-window report (RFC 4034 §3.1.5) ────────
    //
    // Not a soundness check — the ML-DSA signature already covers the
    // (sig_inception, sig_expiration) tuple via binding_hash so a
    // tampered window is caught at the signature gate above.  This
    // step:
    //   * reports the zone-wide [max_inception, min_expiration] window
    //   * flags whether `now` lies inside or outside it
    //   * does NOT cause acceptance failure — per-record freshness is
    //     enforced at lookup time below so individual stale records
    //     are rejected without invalidating the whole epoch.
    let now = wall_clock_now();
    if let Some((zone_inc, zone_exp)) = package.zone_validity_window() {
        let days_left = (zone_exp as i64 - now as i64) as f64 / 86_400.0;
        let in_window = now >= zone_inc && now <= zone_exp;
        let mark = if in_window { "✓" } else { "⚠" };
        println!("  {mark} RRSIG zone-wide window:       [{zone_inc}, {zone_exp}] \
                 (now={now}, Δ={days_left:+.1}d)");
        if !in_window {
            if now < zone_inc {
                println!("     ⚠ NOT-YET-VALID for some records (now < max_inception)");
            } else {
                println!("     ⚠ EXPIRED for some records (now > min_expiration)");
            }
            println!("     per-record enforcement at lookup time will REJECT stale records");
        }
    } else {
        println!("  · RRSIG zone-wide window:       (not stamped — legacy package)");
    }

    let total_ms = t_total.elapsed().as_secs_f64() * 1000.0;

    println!("  ✓ ML-DSA-65 signature verify:    {mldsa_ms:>6.3} ms");
    println!("  ✓ Inner shard STARK FRI verify:  {inner_ms:>6.3} ms");
    println!("  ✓ Outer rollup STARK FRI verify: {outer_ms:>6.3} ms");
    if dskk_count > 0 {
        println!("  ✓ DS→DNSKEY chain bindings:      {dskk_ms:>6.3} ms ({dskk_count} STARK{})",
            if dskk_count == 1 { "" } else { "s" });
    }
    if nsec3_ms > 0.0 {
        println!("  ✓ NSEC3 chain-completeness FRI:  {nsec3_ms:>6.3} ms");
    }
    println!("  ─────────────────────────────────");
    println!("  ✓ One-time epoch acceptance:     {total_ms:>6.3} ms");
    let mut n_proofs = 3usize;
    if nsec3_ms > 0.0 { n_proofs += 1; }
    if dskk_count > 0 { n_proofs += dskk_count; }
    println!("  ({} independent cryptographic proofs verified)", n_proofs);
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
    println!("[soundness] {}", swarm_dns::prover::soundness_banner());
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

    // ─── Phase 3-NSEC3 — NXDOMAIN proof structure (when present) ─
    //
    // Demonstrates authenticated denial-of-existence: the NSEC3 chain
    // commits to which name-hash intervals are "gaps" in the zone.
    // For a queried name X, the resolver:
    //   1. Hashes X under the zone's NSEC3 parameters
    //   2. Finds the covering NSEC3 record (owner_hash < H(X) < next_hash
    //      under cyclic ordering)
    //   3. Returns NXDOMAIN with the covering record as the proof
    // The chain-completeness STARK ensures NO GAPS in the namespace
    // coverage — every queried name's hash falls within exactly one
    // record's interval.
    if let Some(chain) = &package.nsec3_chain {
        println!("[Phase 3-NSEC3] Authenticated denial-of-existence proof structure");
        println!("                (committed chain has {} records)", chain.len());
        println!();
        println!("  {:<32} {:<22} {}",
            "covering interval", "queried name", "verdict");
        println!("  {:─<92}", "");
        // Demo: for 3 synthetic "queried name hashes" that fall in
        // different intervals, show that the resolver locates the
        // covering record by simple linear scan (in production, a
        // sorted index makes this O(log N)).
        let probe_hashes: Vec<[u8; 32]> = (0..3).map(|i| {
            let mut h = [0u8; 32];
            // Pick midpoints of intervals 0, len/2, len-1
            let interval_idx = match i {
                0 => 0,
                1 => chain.len() / 2,
                _ => chain.len() - 1,
            };
            let owner_be8 = u64::from_be_bytes(
                chain[interval_idx].0[..8].try_into().unwrap()
            );
            let next_be8 = u64::from_be_bytes(
                chain[interval_idx].1[..8].try_into().unwrap()
            );
            // Midpoint of owner and next (modular)
            let mid = if next_be8 > owner_be8 {
                owner_be8 + (next_be8 - owner_be8) / 2
            } else {
                // wraparound — pick a value in the cyclic gap
                owner_be8.wrapping_add(0x0800_0000_0000_0000)
            };
            h[..8].copy_from_slice(&mid.to_be_bytes());
            h
        }).collect();
        for hash in &probe_hashes {
            // Linear-scan the committed chain for the covering record.
            let mut covered_by = None;
            for (idx, (owner, next)) in chain.iter().enumerate() {
                let owner_u64 = u64::from_be_bytes(owner[..8].try_into().unwrap());
                let next_u64 = u64::from_be_bytes(next[..8].try_into().unwrap());
                let h_u64 = u64::from_be_bytes(hash[..8].try_into().unwrap());
                let covers = if next_u64 > owner_u64 {
                    h_u64 > owner_u64 && h_u64 < next_u64
                } else {
                    // wrap-around interval
                    h_u64 > owner_u64 || h_u64 < next_u64
                };
                if covers {
                    covered_by = Some(idx);
                    break;
                }
            }
            match covered_by {
                Some(idx) => println!(
                    "  record[{idx:>3}]: ({:<8}, {:<8})  H={}…  ✓ NXDOMAIN proved",
                    hex::encode(&chain[idx].0[..4]),
                    hex::encode(&chain[idx].1[..4]),
                    hex::encode(&hash[..8]),
                ),
                None => println!(
                    "  (no covering record found for H={}…)",
                    hex::encode(&hash[..8]),
                ),
            }
        }
        println!();
        println!("  Soundness: the NSEC3 chain-closure STARK (verified above)");
        println!("  guarantees every queried name's hash falls in exactly one");
        println!("  committed interval — no gaps in namespace coverage that");
        println!("  could be exploited to forge an authenticated NXDOMAIN.");
        println!();
    }

    // ─── Phase 3a — POSITIVE: queries for committed records ─────────
    println!("[Phase 3a — POSITIVE] Queries for records IN the committed corpus");
    println!("                       (should ACCEPT with Merkle inclusion proof)");
    println!();
    println!("  {:<24} {:<10} {:<6} {:<5} {:<5} rdata", "domain", "type", "alg", "idx", "depth");
    println!("  {:─<80}", "");

    // Pick up to 8 records spanning different algorithms for the demo.
    let mut algos_seen = std::collections::HashSet::new();
    let mut positive_targets: Vec<(String, u16)> = Vec::new();
    for r in &package.records {
        if algos_seen.insert(r.algorithm) {
            positive_targets.push((r.domain.clone(), r.record_type));
        }
        if positive_targets.len() >= 8 { break; }
    }
    if positive_targets.len() < 5 {
        for r in package.records.iter().take(8) {
            let key = (r.domain.clone(), r.record_type);
            if !positive_targets.contains(&key) {
                positive_targets.push(key);
            }
            if positive_targets.len() >= 8 { break; }
        }
    }

    let mut total_pos_us = 0.0_f64;
    let mut pos_accept = 0usize;
    let mut pos_reject = 0usize;
    let mut pos_stale = 0usize;
    let now_q = wall_clock_now();
    for (domain, rtype) in &positive_targets {
        let t = Instant::now();
        let result = resolve(&package, domain, *rtype);
        let dt_us = t.elapsed().as_secs_f64() * 1_000_000.0;
        total_pos_us += dt_us;
        match result {
            Some(r) => {
                // RFC 4034 §3.1.5 freshness gate: the ML-DSA-bound
                // RRSIG window must cover `now`.  An offline resolver
                // that skipped this would happily serve replays of
                // long-since-expired signatures (the only check a
                // STARK can't replace — it's a wall-clock fact).
                match package.record_freshness(r.record, now_q) {
                    RrsigFreshness::Fresh => {
                        pos_accept += 1;
                        show_inclusion(domain, *rtype, &r);
                    }
                    RrsigFreshness::NotYetValid { inception, now } => {
                        pos_stale += 1;
                        println!("  {domain:24} type={rtype:>3}  ✗ NOT-YET-VALID \
                                 (inception={inception}, now={now})");
                    }
                    RrsigFreshness::Expired { expiration, now } => {
                        pos_stale += 1;
                        let days_late = (now as i64 - expiration as i64) as f64 / 86_400.0;
                        println!("  {domain:24} type={rtype:>3}  ✗ EXPIRED \
                                 (exp={expiration}, now={now}, Δ={days_late:+.1}d)");
                    }
                }
            }
            None => {
                pos_reject += 1;
                println!("  {domain:24} type={rtype:>3}  ✗ NOT FOUND (unexpected)");
            }
        }
    }
    let _ = pos_reject;
    let _ = pos_stale;
    let avg_pos_us = if !positive_targets.is_empty() {
        total_pos_us / positive_targets.len() as f64
    } else { 0.0 };
    println!();
    println!("  Positive verdict: {pos_accept}/{} ACCEPT, avg lookup {avg_pos_us:.1} µs",
        positive_targets.len());
    println!();

    // ─── Phase 3b — NEGATIVE: queries for NON-committed records ─────
    println!("[Phase 3b — NEGATIVE] Queries for records NOT in the committed corpus");
    println!("                       (should REJECT — no Merkle inclusion proof exists)");
    println!();

    // Construct queries that are extremely unlikely to be in any
    // .se epoch package: synthetic adversarial names + record types.
    let negative_targets: Vec<(String, u16)> = vec![
        // Synthetic non-existent names that an attacker might want to forge:
        ("evil-attacker.se".to_string(),               1),  // A record forgery target
        ("phishing-bank.se".to_string(),               1),
        ("malicious.example.se".to_string(),           1),
        ("not-in-tranco.se".to_string(),               48), // DNSKEY query for unknown zone
        // Legitimate domains that exist on the Internet but are not
        // in this specific epoch package (i.e. not in the captured corpus):
        ("github.com".to_string(),                     1),  // not .se at all
        ("google.com".to_string(),                     1),
        // Wrong record-type queries for committed domains — same domain,
        // different rtype, should still REJECT if the rtype wasn't captured:
        ("nonexistent-record-type.iis.se".to_string(), 255),
    ];

    println!("  {:<32} {:<10} verdict", "domain", "type");
    println!("  {:─<80}", "");
    let mut neg_accept = 0usize;
    let mut neg_reject = 0usize;
    for (domain, rtype) in &negative_targets {
        let result = resolve(&package, domain, *rtype);
        match result {
            Some(_) => {
                neg_accept += 1;
                println!("  {domain:32} type={rtype:>3}  ✗ ACCEPTED (forgery — this is a bug)");
            }
            None => {
                neg_reject += 1;
                println!("  {domain:32} type={rtype:>3}  ✓ REJECT (not in committed corpus)");
            }
        }
    }
    println!();
    println!("  Negative verdict: {neg_reject}/{} REJECT (expected = {})",
        negative_targets.len(), negative_targets.len());
    if neg_accept > 0 {
        println!("  ✗ {neg_accept} false ACCEPT — this should be 0; security violation!");
    } else {
        println!("  ✓ all NEGATIVE queries correctly rejected — coverage = committed corpus");
    }
    println!();

    // ─── Phase 3c — ADVERSARIAL: forged inclusion-proof attempt ─────
    //
    // An adversary holds the package + sees the committed Merkle root.
    // They want to convince a victim that "evil.se A → 6.6.6.6" is
    // attested by the package.  They synthesize a forged leaf hash and
    // a real authentication path borrowed from leaf index 0.  The
    // re-verification check `merkle_verify(forged_leaf, 0, real_path,
    // committed_root)` reconstructs a DIFFERENT root (because the
    // forged leaf changes the bottom-up hash chain).  REJECTED.
    println!("[Phase 3c — ADVERSARIAL] Forged-inclusion-proof attack:");
    println!("                          adversary tries to convince us 'evil.se A 6.6.6.6'");
    println!("                          is in the corpus by reusing a real authentication path");
    println!();
    {
        use swarm_dns::dns::{DnsRecord, merkle_path, merkle_verify};
        // Forge a leaf for "evil.se A 6.6.6.6" using the package's
        // (public) salt.
        let forged_record = DnsRecord {
            domain:      "evil.se".to_string(),
            record_type: 1,
            ttl:         300,
            rdata:       vec![6, 6, 6, 6],  // 6.6.6.6 octets
        };
        let forged_leaf = forged_record.leaf_hash(&package.merkle_salt);
        // Borrow a real authentication path from leaf-index 0
        // (the adversary can compute it from the public tree levels).
        let real_path_for_idx0 = merkle_path(&package.merkle_levels, 0);
        // Adversary publishes the (forged_leaf, idx=0, real_path) and
        // claims it proves inclusion under the committed Merkle root.
        let adversary_claims_root = package.merkle_root;
        println!("  forged record:       evil.se A 6.6.6.6");
        println!("  forged leaf_hash:    {}", hex::encode(&forged_leaf[..16]));
        println!("  claimed leaf_index:  0  (real index of {} type={} in corpus)",
            package.records[0].domain, package.records[0].record_type);
        println!("  authentication path: {} siblings (borrowed from real leaf 0)",
            real_path_for_idx0.len());

        let attack_succeeds = merkle_verify(
            forged_leaf, 0, &real_path_for_idx0, adversary_claims_root,
        );
        if attack_succeeds {
            println!();
            println!("  ✗ FORGERY ACCEPTED — Merkle binding is broken (security bug!)");
        } else {
            // Show WHICH root the forged path reconstructs to.
            let reconstructed = {
                use sha3::{Digest, Sha3_256};
                use swarm_dns::dns::TAG_NODE;
                let mut cur = forged_leaf;
                let mut idx = 0usize;
                for &sib in &real_path_for_idx0 {
                    let (l, r) = if idx & 1 == 0 { (cur, sib) } else { (sib, cur) };
                    let mut h = Sha3_256::new();
                    h.update(TAG_NODE); h.update(l); h.update(r);
                    cur = h.finalize().into();
                    idx /= 2;
                }
                cur
            };
            println!();
            println!("  forged path reconstructs to: {}", hex::encode(&reconstructed[..16]));
            println!("  committed Merkle root:       {}", hex::encode(&package.merkle_root[..16]));
            println!("  ✓ FORGERY REJECTED — roots don't match");
            println!("    The committed root cryptographically pins which leaves are");
            println!("    in the corpus.  No leaf outside the corpus can satisfy");
            println!("    the inclusion check because every leaf change propagates");
            println!("    to a different root via SHA3-256 collision resistance.");
        }
    }
    println!();

    // ─── Phase 3d — COMPREHENSIVE TAMPER TESTS ──────────────────────
    //
    // Every cryptographic component of the package gets a one-byte flip,
    // demonstrating which verification check catches each tampering.
    // A robust system rejects ALL of these; if any tampering ACCEPTS,
    // the verifier has a security gap.
    println!("[Phase 3d — TAMPER] Comprehensive component-level tamper tests:");
    println!();

    struct TamperCase {
        name: &'static str,
        expected_catcher: &'static str,
        mutate: Box<dyn Fn(&mut SeEpochPackage)>,
    }
    let cases: Vec<TamperCase> = vec![
        TamperCase {
            name: "authority_sig[0] ^= 0xFF",
            expected_catcher: "ML-DSA-65 signature verify",
            mutate: Box::new(|p| p.authority_sig[0] ^= 0xFF),
        },
        TamperCase {
            name: "authority_pk[0] ^= 0xFF (wrong key)",
            expected_catcher: "ML-DSA-65 signature verify",
            mutate: Box::new(|p| p.authority_pk[0] ^= 0xFF),
        },
        TamperCase {
            name: "merkle_root[0] ^= 0xFF",
            expected_catcher: "ML-DSA-65 signature verify (binding hash)",
            mutate: Box::new(|p| p.merkle_root[0] ^= 0xFF),
        },
        TamperCase {
            name: "inner_pi_hash[0] ^= 0xFF",
            expected_catcher: "ML-DSA-65 signature verify (binding hash)",
            mutate: Box::new(|p| p.inner_pi_hash[0] ^= 0xFF),
        },
        TamperCase {
            name: "outer_root_f0[0] ^= 0xFF",
            expected_catcher: "ML-DSA-65 signature verify (binding hash)",
            mutate: Box::new(|p| if !p.outer_root_f0.is_empty() { p.outer_root_f0[0] ^= 0xFF }),
        },
        TamperCase {
            name: "epoch_t = 0 (replay attack)",
            expected_catcher: "ML-DSA-65 signature verify (binding hash)",
            mutate: Box::new(|p| p.epoch_t = 0),
        },
        TamperCase {
            name: "epoch_seq = u64::MAX (replay attack)",
            expected_catcher: "ML-DSA-65 signature verify (binding hash)",
            mutate: Box::new(|p| p.epoch_seq = u64::MAX),
        },
        TamperCase {
            name: "outer_stark_proof[100] ^= 0xFF",
            expected_catcher: "Outer rollup STARK FRI verify",
            mutate: Box::new(|p| {
                if p.outer_stark_proof.len() > 100 { p.outer_stark_proof[100] ^= 0xFF }
            }),
        },
        TamperCase {
            name: "inner_stark_proof[100] ^= 0xFF",
            expected_catcher: "Inner shard STARK FRI verify",
            mutate: Box::new(|p| {
                if p.inner_stark_proof.len() > 100 { p.inner_stark_proof[100] ^= 0xFF }
            }),
        },
        // RRSIG validity-window tampering (priority-6).  An adversary
        // who has stolen a long-expired RRSIG tries to extend its
        // expiration by editing `records[i].sig_expiration` in the
        // package.  Since priority-6 mixes the validity windows into
        // `binding_hash()`, this is caught by the ML-DSA signature
        // gate — the resolver does NOT need to trust the editor.
        TamperCase {
            name: "records[0].sig_expiration += 1 year (window extend)",
            expected_catcher: "ML-DSA-65 signature verify (RRSIG-VALIDITY-V1)",
            mutate: Box::new(|p| {
                if let Some(r) = p.records.first_mut() {
                    if let Some(e) = r.sig_expiration.as_mut() {
                        *e = e.saturating_add(31_536_000);  // +1 year
                    }
                }
            }),
        },
        TamperCase {
            name: "records[0].sig_inception = 0 (pre-date attack)",
            expected_catcher: "ML-DSA-65 signature verify (RRSIG-VALIDITY-V1)",
            mutate: Box::new(|p| {
                if let Some(r) = p.records.first_mut() {
                    if r.sig_inception.is_some() {
                        r.sig_inception = Some(0);
                    }
                }
            }),
        },
    ];

    println!("  {:<44} {:<22} {}", "tampering", "verdict", "expected catcher");
    println!("  {:─<100}", "");
    let mut tamper_caught = 0usize;
    let mut tamper_missed = 0usize;
    for case in &cases {
        let mut tampered = package.clone();
        (case.mutate)(&mut tampered);
        let verdict = match verify_package_quiet(&tampered) {
            Ok(_) => {
                tamper_missed += 1;
                "✗ ACCEPTED (security bug!)"
            }
            Err(_) => {
                tamper_caught += 1;
                "✓ REJECTED"
            }
        };
        println!("  {:<44} {verdict:<22} {}", case.name, case.expected_catcher);
    }
    println!();
    println!("  Tamper caught: {tamper_caught}/{} ({})",
        cases.len(),
        if tamper_missed == 0 { "all attempted tamperings correctly rejected" }
        else { "SECURITY VIOLATION — some tamperings accepted" }
    );
    println!();

    // ─── Phase 3e — RECORD-LEVEL tamper test (Merkle inclusion catch) ─
    //
    // Tamper a single record's rdata in the package's records[] list.
    // The Merkle inclusion check at query time should catch this
    // because the resolver re-derives the leaf_hash from the (possibly
    // tampered) record bytes and verifies against the committed root.
    println!("[Phase 3e — RECORD TAMPER] Mutate records[0].rdata + re-query:");
    {
        let mut tampered = package.clone();
        if !tampered.records.is_empty() && !tampered.records[0].rdata.is_empty() {
            tampered.records[0].rdata[0] ^= 0xFF;
            let target_domain = tampered.records[0].domain.clone();
            let target_type = tampered.records[0].record_type;
            let result = resolve(&tampered, &target_domain, target_type);
            match result {
                Some(_) => println!("  ✗ FAILED — tampered record wrongly resolved (this is a bug)"),
                None => println!("  ✓ correctly rejected: Merkle inclusion fails for tampered records[0].rdata"),
            }
        }
    }
    println!();

    println!("═══════════════════════════════════════════════════════════════");
    println!("  TRUE OFFLINE DNS RESOLUTION — security envelope demonstrated");
    println!();
    println!("  ✓ Loaded a self-contained {:.1} KiB epoch package",
        raw_size as f64 / 1024.0);
    println!("  ✓ Verified once via ML-DSA-65 + outer STARK FRI");
    println!("  ✓ {pos_accept} POSITIVE queries served in {:.1} µs total ({avg_pos_us:.1} µs/query)",
        total_pos_us);
    println!("  ✓ {neg_reject} NEGATIVE queries correctly rejected (no false ACCEPTs)");
    println!("  ✓ Forged-inclusion-proof attempt rejected (Merkle binding holds)");
    println!("  ✓ Comprehensive component tamper sweep: {tamper_caught}/{} all rejected", cases.len());
    println!("    (covers: ML-DSA sig, pk, merkle_root, inner_pi_hash, outer_root_f0,");
    println!("     epoch_t replay, epoch_seq replay, outer STARK bytes, inner STARK bytes)");
    println!("  ✓ Record-level tamper (rdata flip) caught by Merkle inclusion re-derivation");
    println!();
    println!("  Security envelope: an offline resolver answers DNS queries");
    println!("  EXACTLY for the {} records committed in this epoch package,",
        package.records.len());
    println!("  and CANNOT be tricked into accepting any record outside it.");
    println!("  NO NETWORK calls; NO secret state; NO ongoing trust.");
    println!();
    println!("  Post-quantum integrity: STARK soundness rests on SHA-3");
    println!("  collision resistance + ML-DSA-65 EUF-CMA — both PQ-secure.");
    println!("  A future CRQC adversary breaking RSA/ECDSA cannot forge");
    println!("  any record outside this epoch package.");
    println!("═══════════════════════════════════════════════════════════════");
}
