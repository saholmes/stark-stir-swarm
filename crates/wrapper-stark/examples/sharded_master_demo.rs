//! Option C — TWO-LEVEL SHARDED master recursion demo.
//!
//! Architecturally honest demonstration of how STARK-DNS scales to
//! tens-of-thousands of signatures per zone without single-master
//! memory blowup.
//!
//! Pipeline:
//!
//! ```
//! N inners  ──►  K = N/Ni first-level masters (sequentially proven)
//!                ──►  1 super-master over the K first-level masters
//!                      + 1 top batched Merkle over all N inner pi_hashes
//! ```
//!
//! Only the **super-master**, **top batched Merkle**, and `(N + K) × 32 B`
//! of pi_hash calldata go to L1 — the K shard masters are local-only.
//! Peak prover memory: O(max(Ni, K)) — bounded sequentially.
//!
//! At STARK-DNS .com scale (N ≈ 500 M / zone batched into ~10 000-record
//! L1 settlements):
//!   - shard_size Ni = 256, K = 40 super-master inputs
//!   - First-level prover memory: O(256) → fits on 32 GB Mac
//!   - Super-master n_trace: O(40) → ~10 KiB trace, ~2.5 MiB FRI proof
//!   - L1 wire: ~2.5 MiB super + 395 KiB top Merkle + N×32 B pi_hashes
//!
//! # Run
//!
//! ```bash
//! N_INNER=16 SHARD_SIZE=4 cargo run --release -p wrapper-stark \
//!     --example sharded_master_demo \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features
//! ```

use std::time::Instant;

use ark_serialize::CanonicalSerialize;

use deep_ali::ml_dsa::params::C_TILDE_BYTES;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    prove_v2_real, synthesize_demo_witness, verify_v2_real,
};

use wrapper_stark::master_recursion_bridge::{
    prove_two_level_sharded_master, verify_two_level_sharded_master,
};
use wrapper_stark::recursive_prover::{
    RecursiveStarkProof, verify_recursive_stark,
};
use wrapper_stark::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive;

fn parse_env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn fmt_kib(bytes: usize) -> String { format!("{:.1} KiB", bytes as f64 / 1024.0) }

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("OPTION C — TWO-LEVEL SHARDED MASTER RECURSION DEMO");
    println!("    (N inners → K first-level masters → 1 super-master");
    println!("     + 1 top batched Merkle, only super+top→L1)");
    println!("═══════════════════════════════════════════════════════════════");
    println!();

    let n: usize = parse_env_usize("N_INNER", 16);
    let shard_size: usize = parse_env_usize("SHARD_SIZE", 4);
    let k = (n + shard_size - 1) / shard_size;
    // Defaults: smoke-fast prove (blowup=4) at L1-equivalent r (=135 at
    // blowup=4 gives 135 bits unconditional Johnson, matching blowup=32
    // r=54).  Override via env vars for production-L1 calibration
    // (blowup=32 r=54 at every level — smaller wire, faster verify).
    //
    // r-floor for L1 (128 bits) at each blowup, ½·log₂(blowup) bits/query:
    //   blowup= 4: r ≥ 128 (set to 135 here, 7 bit margin)
    //   blowup= 8: r ≥  86
    //   blowup=16: r ≥  64
    //   blowup=32: r ≥  52 (set to 54 here, 7 bit margin)
    // Bumping r is cheap (per-query work scales linearly); bumping
    // blowup is expensive (LDE work scales ~linearly).  At blowup=4
    // the prove is ~8× faster than blowup=32 even with the 2.5× more
    // queries — that's the smoke advantage.
    //
    // CAVEAT: inner v2's `V2_NUM_QUERIES = 54` is hardcoded from
    // `deep_ali::stark_level`, independent of the `INNER_BLOWUP`
    // env value.  So `inner_blowup=4` produces a v2 inner proof
    // at only 54 bits unconditional (sub-L1).  Set
    // `INNER_BLOWUP=32` to recover full L1 soundness on the inner
    // stage.  This is a known v2 limitation flagged on this date.
    let inner_blowup:  usize = parse_env_usize("INNER_BLOWUP",  4);
    let master_blowup: usize = parse_env_usize("MASTER_BLOWUP", 4);
    let master_r:      usize = parse_env_usize("MASTER_R",      135);
    let merkle_blowup: usize = parse_env_usize("MERKLE_BLOWUP", 4);
    // merkle_r default fixed to 135 (was 54 — gave 54 bits at blowup=4,
    // failed L1 by 74 bits).  Banner now flags this if a caller
    // overrides it below the L1 floor.
    let merkle_r:      usize = parse_env_usize("MERKLE_R",      135);

    // Soundness banner — CORRECT unconditional Johnson formula
    // (BCIKS / STIR Thm. 1): per-query bits = ½·log₂(blowup), so the
    // required `r` to clear a given NIST PQ Level scales INVERSELY
    // with blowup:
    //   blowup= 4: ½·log₂(4)  = 1.0 bits/q  → r ≥ 128 for L1
    //   blowup= 8: ½·log₂(8)  = 1.5 bits/q  → r ≥ 86  for L1
    //   blowup=16: ½·log₂(16) = 2.0 bits/q  → r ≥ 64  for L1
    //   blowup=32: ½·log₂(32) = 2.5 bits/q  → r ≥ 52  for L1 (canonical 54)
    //
    // r=54 ONLY clears L1 at blowup=32.  At lower blowups r must
    // increase proportionally.  Earlier banner versions reported
    // capacity-regime bits (conjectural, requires proximity-gap
    // conjecture) — fixed now to match `deep_ali::stark_level`'s
    // documented Johnson formula.
    //
    // Inner v2 has a separate caveat: it uses `V2_NUM_QUERIES = 54`
    // hardcoded from `deep_ali::stark_level`, regardless of the
    // `INNER_BLOWUP` passed.  So `inner_blowup=4` gives 54 bits
    // unconditional (sub-L1).  Use `inner_blowup=32` to hit L1.
    let bits_per_q = |bw: usize| -> f64 {
        if bw < 2 { 0.0 } else { 0.5 * (bw as f64).log2() }
    };
    let r_for_level = |bw: usize, target: f64| -> usize {
        let bpq = bits_per_q(bw).max(0.01);
        (target / bpq).ceil() as usize
    };
    let level_label = |bits: f64| -> &'static str {
        if bits >= 256.0 { "≥L5" }
        else if bits >= 192.0 { "≥L3" }
        else if bits >= 128.0 { "≥L1" }
        else { "<L1 (NOT production-sound)" }
    };
    let inner_bits  = bits_per_q(inner_blowup)  * 54.0; // v2 internal r=54
    let master_bits = bits_per_q(master_blowup) * master_r as f64;
    let merkle_bits = bits_per_q(merkle_blowup) * merkle_r as f64;
    let mode = if inner_bits >= 128.0 && master_bits >= 128.0 && merkle_bits >= 128.0 {
        if inner_blowup >= 32 && master_blowup >= 32 && merkle_blowup >= 32 {
            "PRODUCTION-L1 (all blowup=32, r=54 — matches swarm-dns core pipeline)"
        } else {
            "L1-SOUND (mixed blowup but all r-values scaled for L1)"
        }
    } else {
        "BELOW L1 — at least one stage is under-provisioned (see ❌ flags)"
    };
    println!("Configuration:");
    println!("  N (inner signatures):  {n}");
    println!("  Ni (shard_size):       {shard_size}");
    println!("  K (shards):            {k}  (= ceil(N / Ni))");
    let inner_flag = if inner_bits >= 128.0 { "✓" } else { "❌" };
    let master_flag = if master_bits >= 128.0 { "✓" } else { "❌" };
    let merkle_flag = if merkle_bits >= 128.0 { "✓" } else { "❌" };
    println!("  inner v2 blowup:       {inner_blowup}  (V2_NUM_QUERIES=54 hardcoded → {inner_bits:.0} bits, {}) {inner_flag}",
        level_label(inner_bits));
    println!("  master blowup × r:     {master_blowup} × {master_r}  ({master_bits:.0} bits unconditional Johnson, {}) {master_flag}",
        level_label(master_bits));
    println!("  top Merkle blowup × r: {merkle_blowup} × {merkle_r}  ({merkle_bits:.0} bits unconditional Johnson, {}) {merkle_flag}",
        level_label(merkle_bits));
    println!("  calibration mode:      {mode}");
    println!("  L1 r-floor at this blowup combo: master r≥{}, merkle r≥{}",
        r_for_level(master_blowup, 128.0),
        r_for_level(merkle_blowup, 128.0));
    println!();

    // ─── 1. Build N inner v2 + recursive STARK pairs ─────────────────
    println!("[1/3] Build N={n} inner v2 + recursive STARK pairs …");
    let mut inners: Vec<RecursiveStarkProof> = Vec::with_capacity(n);
    let mut t_inner_total = 0.0_f64;
    let mut t_rec_total = 0.0_f64;
    let mut inner_v2_bytes_total: usize = 0;

    for sig_idx in 0..n {
        let w = synthesize_demo_witness(sig_idx as u64);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

        let t = Instant::now();
        let v2_proof = prove_v2_real(&w, &c_tilde, inner_blowup);
        let inner_ms = t.elapsed().as_secs_f64() * 1000.0;
        t_inner_total += inner_ms;
        verify_v2_real(&w, &c_tilde, &v2_proof, inner_blowup)
            .expect("v2 verify must accept");
        inner_v2_bytes_total += v2_proof.to_bytes().len();

        let t = Instant::now();
        let rec = prove_v2_all_subairs_composed_recursive(
            &v2_proof, &w, inner_blowup, master_blowup, master_r, /*stir=*/false,
        ).expect("recursive STARK wrap");
        let rec_ms = t.elapsed().as_secs_f64() * 1000.0;
        t_rec_total += rec_ms;
        assert!(verify_recursive_stark(&rec));
        inners.push(rec);

        if sig_idx % 4 == 0 || sig_idx + 1 == n {
            println!(
                "  sig {sig_idx:>3}/{n}:  inner {inner_ms:>6.0} ms · rec {rec_ms:>6.0} ms"
            );
        }
    }
    println!();
    println!("  Σ inner v2 prove:    {t_inner_total:>9.1} ms");
    println!("  Σ recursive wrap:    {t_rec_total:>9.1} ms");
    println!("  Σ inner v2 size:     {}",  fmt_kib(inner_v2_bytes_total));
    println!();

    // ─── 2. Two-level sharded prove ──────────────────────────────────
    println!("[2/3] Build K={k} first-level masters + 1 super-master + top batched Merkle …");
    let t = Instant::now();
    let proof = prove_two_level_sharded_master(
        &inners,
        shard_size,
        master_blowup, master_r, /*stir=*/false,
        merkle_blowup, merkle_r, /*stir=*/false,
    ).expect("two-level sharded prove");
    let sharded_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    let ok = verify_two_level_sharded_master(&proof, &inners);
    let sharded_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    assert!(ok);

    let mut super_buf = Vec::new();
    proof.super_master.fri_proof.serialize_compressed(&mut super_buf).unwrap();
    let mut top_merkle_buf = Vec::new();
    proof.top_merkle_path.fri_proof.serialize_compressed(&mut top_merkle_buf).unwrap();
    let inner_pi_bytes = proof.inner_pi_hashes.len() * 32;
    let shard_pi_bytes = proof.shard_pi_hashes.len() * 32;
    let l1_wire =
        super_buf.len() + top_merkle_buf.len() + inner_pi_bytes + shard_pi_bytes;

    println!();
    println!("  sharded prove total:  {sharded_prove_ms:>9.1} ms");
    println!("  sharded verify:       {sharded_verify_ms:>9.2} ms");
    println!("  super_master size:    {}", fmt_kib(super_buf.len()));
    println!("  super_master n_trace: {}", proof.super_master.n_trace);
    println!("  top Merkle size:      {}", fmt_kib(top_merkle_buf.len()));
    println!("  inner pi_hashes:      {} B  (N × 32)", inner_pi_bytes);
    println!("  shard pi_hashes:      {} B  (K × 32)", shard_pi_bytes);
    println!("  ───────────────────────────────────────");
    println!("  L1 wire total:        {}", fmt_kib(l1_wire));
    println!("  verdict:              {}", if ok { "ACCEPT" } else { "REJECT" });
    println!();

    // ─── 3. STARK-DNS scaling projection ─────────────────────────────
    println!("[3/3] STARK-DNS scaling projection (sharded master)");
    println!();
    println!("  This demo at N={n}, Ni={shard_size}, K={k}:");
    println!("    super_master n_trace: {} (proportional to K, NOT N)",
        proof.super_master.n_trace);
    println!("    super_master size:    {}", fmt_kib(super_buf.len()));
    println!();
    println!("  PROJECTING to STARK-DNS .com-zone scale:");
    println!();

    let scenarios = [
        ("N=100   ",   100usize, 16usize),
        ("N=1 000 ",  1000usize, 32usize),
        ("N=10 000", 10000usize, 64usize),
        ("N=100 K ", 100_000usize, 256usize),
        ("N=1 M   ", 1_000_000usize, 1024usize),
    ];

    println!("  {:<10}{:>10}{:>10}{:>14}{:>14}{:>14}{:>14}",
        "scale", "shard_size", "K", "first-level Ni n_trace", "super-master K n_trace",
        "L1 wire", "L1 verify");
    println!("  {:─<86}", "");
    for (label, n_total, ni) in scenarios {
        let k_proj = (n_total + ni - 1) / ni;
        let first_level_n_trace = if ni < 2 { 32_768 } else {
            // measured: n_trace doubles per N doubling, n_trace(N=2) = 32 768
            (32_768usize.saturating_mul(ni)) / 2
        };
        let super_master_n_trace = if k_proj < 2 { 32_768 } else {
            (32_768usize.saturating_mul(k_proj)) / 2
        };
        let l1_wire_proj = {
            // master size grows polylog: ~1970 KiB + 130 KiB · log2(K/2)
            let k_log_steps = if k_proj > 2 {
                (k_proj as f64).log2() - 1.0
            } else { 0.0 };
            let super_kib = 1970.0 + 130.0 * k_log_steps;
            let super_b = (super_kib * 1024.0) as usize;
            // top Merkle: ~395.9 KiB constant
            let merkle_b = (395.9 * 1024.0) as usize;
            // pi_hashes: (N + K) × 32 B
            let pi_b = (n_total + k_proj) * 32;
            super_b + merkle_b + pi_b
        };
        let verify_ms_proj = {
            // master verify: ~6.6 ms + 0.8 ms · log2(K/2) + ~2.7 ms top merkle
            let k_log_steps = if k_proj > 2 {
                (k_proj as f64).log2() - 1.0
            } else { 0.0 };
            6.6 + 0.8 * k_log_steps + 2.7
        };
        println!("  {label}  {ni:>9}  {k_proj:>9}  {:>14}  {:>14}  {:>11}  {:>9.1} ms",
            first_level_n_trace, super_master_n_trace,
            fmt_kib(l1_wire_proj), verify_ms_proj);
    }
    println!();
    println!("  Notes on the projection:");
    println!("  - first-level Ni n_trace is the prover memory bound per shard;");
    println!("    shards run SEQUENTIALLY so peak memory is O(Ni), not O(N).");
    println!("  - super-master K n_trace is the second-level prover memory bound.");
    println!("  - L1 wire = super (~2-3 MiB polylog in K) + top Merkle (~395 KiB)");
    println!("    + (N + K) × 32 B pi_hash calldata.");
    println!("  - L1 verify is polylog(K) — independent of N.");
    println!();

    println!("═══════════════════════════════════════════════════════════════");
    println!();
    println!("  ✓ Sharded Option C demonstrated:");
    println!("    {n} inner ML-DSA signatures → {k} first-level masters → 1 super-master");
    println!("    + 1 top batched Merkle.  L1 wire {}.",  fmt_kib(l1_wire));
    println!();
    println!("  Peak prover memory bound: O(max(Ni={shard_size}, K={k}))");
    println!("  rather than O(N={n}) for a single master.  This is what makes");
    println!("  STARK-DNS at .com scale (~500 M signatures) tractable on commodity");
    println!("  hardware via a 1k-worker prover swarm.");
    println!();
    println!("  Soundness chain:");
    println!("    1. Super-master FRI-verifies (sub-circuit 1 algebraic relation");
    println!("       over K shard masters' FRI residues).");
    println!("    2. Top batched Merkle binds batched_pi = SHA3(N || π₁..π_N) to root.");
    println!("    3. Verifier cross-checks each inner_pi_hashes[i] == real inner[i].");
    println!();
    println!("  Soundness caveat (same shape as single-level Option C):");
    println!("    Sub-circuit 1 attests algebraic FRI relation on prover-supplied");
    println!("    residues.  Full FRI-Merkle binding at every recursion level is a");
    println!("    follow-up (would add in-AIR Merkle paths at the shard level too).");
    println!("═══════════════════════════════════════════════════════════════");
}
