//! F2 — recursive STARK-of-STARK aggregation for the DNS epoch.
//!
//! Wires the wrapper-stark recursion pipeline (master recursion +
//! FRI-Merkle binding) onto DNS-relevant inner proofs: each inner is a
//! per-record **ML-DSA-65 signature verification** STARK (the v2 AIR that
//! the PQ-signed-record path uses).  The pipeline is:
//!
//!   N inner v2 ML-DSA STARKs
//!     → N recursive STARKs            (prove_v2_all_subairs_composed_recursive)
//!     → 1 master STARK                (prove_master_recursive, FS-absorbs every
//!                                      inner FRI root)
//!     + per-inner FRI-Merkle binding  (in-AIR SHA-3 Merkle-path verify of the
//!                                      inner FRI openings under their roots)
//!
//! The edge verifies the single master bundle once and obtains full STARK
//! soundness over all N records — no per-shard auditor trust.  This is the
//! sharded-mode endpoint of \S\ref{sec:eval:fri-merkle-binding} applied to
//! the DNS epoch.
//!
//! Inner witnesses are synthesised demo ML-DSA signatures (a real FIPS-204
//! verification relation; the witness stands in for a per-record RRSIG
//! under ML-DSA).  Cost is dominated by the per-inner FRI-Merkle binding,
//! so the binding subset size `DNS_REC_B` and record count `DNS_REC_N` are
//! env-configurable with small defaults.
//!
//! Run (slow — minutes; the FRI-Merkle binding is the heavy part):
//!     DNS_REC_N=2 DNS_REC_B=4 \
//!     cargo run --release -p swarm-dns --example dns_recursive_master_demo \
//!         --features sha3-256,mldsa-44,parallel --no-default-features

use std::time::Instant;

use deep_ali::ml_dsa::params::C_TILDE_BYTES;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    prove_v2_real, synthesize_demo_witness, verify_v2_real,
};
use wrapper_stark::recursive_prover::RecursiveStarkProof;
use wrapper_stark::master_recursion_bridge::{
    extract_fri_merkle_openings, prove_master_with_fri_merkle_binding,
    verify_master_with_fri_merkle_binding,
};
use wrapper_stark::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive;

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

fn main() {
    // Smoke L1 calibration (matches the wrapper-stark Phase-3 test).
    let n            = env_usize("DNS_REC_N", 2);
    let binding_b    = env_usize("DNS_REC_B", 4);
    let inner_blowup = 4usize;
    let outer_blowup = 4usize;
    let outer_r      = 54usize;
    let master_blowup = 4usize;
    let master_r      = 54usize;
    let binding_blowup = 4usize;
    let binding_r      = 54usize;

    println!("\n┌─ F2 recursive STARK-of-STARK for the DNS epoch ───────────");
    println!("│  inner   : per-record ML-DSA-65 verify STARK (v2 AIR)");
    println!("│  recurse : N inner → N recursive STARK → 1 master + FRI-Merkle binding");
    println!("│  edge    : ONE bundle, full STARK soundness, no per-shard auditor");
    println!("│  calib   : smoke L1, blowup=4, r=54, binding subset B={binding_b}");
    println!("└────────────────────────────────────────────────────────────\n");

    // ── 1. N inner v2 ML-DSA proofs → N recursive STARKs ───────────────
    println!("[1/3] Build N={n} per-record ML-DSA inner + recursive STARK pairs …");
    let mut inners: Vec<RecursiveStarkProof> = Vec::with_capacity(n);
    let mut t_inner = 0.0f64;
    let mut t_rec = 0.0f64;
    for i in 0..n {
        let w = synthesize_demo_witness(i as u64 + 1);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

        let t = Instant::now();
        let v2 = prove_v2_real(&w, &c_tilde, inner_blowup);
        t_inner += t.elapsed().as_secs_f64() * 1e3;
        verify_v2_real(&w, &c_tilde, &v2, inner_blowup).expect("inner v2 must verify");

        let t = Instant::now();
        let rec = prove_v2_all_subairs_composed_recursive(
            &v2, &w, inner_blowup, outer_blowup, outer_r, /*stir=*/false,
        ).expect("recursive STARK wrap");
        t_rec += t.elapsed().as_secs_f64() * 1e3;
        inners.push(rec);
        println!("    record {i}: inner + recursive wrap done");
    }

    // Binding subset: B indices spread across the inner's r·L FRI openings.
    let full = extract_fri_merkle_openings(&inners[0])
        .expect("extract openings").batch_size();
    let b = binding_b.min(full).max(1);
    let subset: Vec<usize> = (0..b).map(|j| (j * full) / b).collect();
    println!("    inner FRI openings r·L = {full}; binding subset B = {b}");

    // ── 2. Master STARK + per-inner FRI-Merkle binding ─────────────────
    println!("[2/3] Master recursion + per-inner FRI-Merkle binding (slow) …");
    let t = Instant::now();
    let bundle = prove_master_with_fri_merkle_binding(
        &inners[..],
        master_blowup, master_r, /*master_stir=*/false,
        binding_blowup, binding_r, /*binding_stir=*/false,
        Some(&subset),
    ).expect("master + FRI-Merkle binding prove");
    let t_master = t.elapsed().as_secs_f64() * 1e3;

    // ── 3. Edge verifies the single bundle (3-piece soundness chain) ───
    println!("[3/3] Edge verify (master FRI + per-inner binding + re-derive) …");
    let t = Instant::now();
    let ok = verify_master_with_fri_merkle_binding(&bundle, &inners[..], Some(&subset));
    let t_verify = t.elapsed().as_secs_f64() * 1e3;
    assert!(ok, "master+binding bundle must verify end-to-end");

    let mut master_bytes = Vec::new();
    use ark_serialize::CanonicalSerialize;
    bundle.master.fri_proof.serialize_compressed(&mut master_bytes).unwrap();

    println!("\n┌─ Results (N={n} records, smoke L1) ───────────────────────");
    println!("│  inner v2 prove (total)   : {t_inner:>8.1} ms  ({:.1} ms/record)", t_inner / n as f64);
    println!("│  recursive wrap (total)   : {t_rec:>8.1} ms  ({:.1} ms/record)", t_rec / n as f64);
    println!("│  master + binding prove   : {t_master:>8.1} ms");
    println!("│  edge verify (3-piece)    : {t_verify:>8.2} ms");
    println!("│  master FRI proof         : {:>8} B ({} KiB)", master_bytes.len(), master_bytes.len() / 1024);
    println!("│  per-inner bindings       : {} (batch_size {})", bundle.fri_merkle_bindings.len(), bundle.fri_merkle_bindings[0].batch_size);
    println!("└────────────────────────────────────────────────────────────");
    println!("\n  ✓ {n} per-record ML-DSA STARKs aggregated into ONE master proof,");
    println!("    FRI-Merkle-bound and verified end-to-end.  The edge gets full");
    println!("    STARK soundness over the whole epoch from a single bundle —");
    println!("    no per-shard auditor trust (the F2 sharded-mode endpoint).\n");
}
