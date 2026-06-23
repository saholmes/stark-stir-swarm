//! Per-layer folding-arity Pareto sweep for the STIR paper.
//!
//! Proves the Fibonacci AIR at the paper's headline config
//! (`T=2^16`, `rho_0=1/32` so `|H_0|=2^21`, L1, `Fp6`, SHA3-256, `r=54`)
//! under a single folding schedule chosen by the `SCHED` env var, and
//! prints proof size + prove time.  Run once per schedule (a driver runs
//! it under `/usr/bin/time -l` to capture peak RSS) to map the
//! (proof-size, prove-time, prover-RSS) Pareto frontier across folding
//! arities --- the per-layer arity optimum, not previously charted.
//!
//! `SCHED` values:
//!   fri            arity-2 binary FRI (stir off)
//!   u4 u8 u16 u32  uniform STIR arity (+ residual fold)
//!   taper          highest-arity-first taper (16 then 8 then residual)
//!   "16,16,8,4"    explicit per-layer arity list
//!
//! Run (one schedule):
//!   SCHED=taper cargo run --release -p swarm-dns --example arity_pareto_bench \
//!     --features sha3-256,mldsa-44,parallel --no-default-features

use std::time::Instant;

use ark_goldilocks::Goldilocks as F;
use deep_ali::{
    air_workloads::{build_execution_trace, AirType},
    deep_ali_merge_general,
    fri::{deep_fri_proof_size_bytes, deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain},
    trace_import::lde_trace_columns,
};
use swarm_dns::prover::{Ext, BLOWUP, SEED_Z};

/// Build a fold schedule from a spec string for a domain of `log_n0` bits.
/// Returns `(schedule, use_stir)`.  Each entry is the per-layer fold arity;
/// the product of entries must equal `n0` (sum of `log2` = `log_n0`).
fn schedule_from_spec(spec: &str, log_n0: usize) -> (Vec<usize>, bool) {
    let uniform = |m_log: usize| -> Vec<usize> {
        let mut rem = log_n0;
        let mut s = Vec::new();
        while rem >= m_log { s.push(1usize << m_log); rem -= m_log; }
        if rem > 0 { s.push(1usize << rem); }
        s
    };
    match spec {
        "fri" => (vec![2usize; log_n0], false),
        // FRI at higher arity via the same deep-ali-merge coset fold
        // (stir=false); tests whether FRI-at-arity-m is already supported.
        "fri4"  => (uniform(2), false),
        "fri8"  => (uniform(3), false),
        "fri16" => (uniform(4), false),
        "fri32" => (uniform(5), false),
        "u4"  => (uniform(2), true),
        "u8"  => (uniform(3), true),
        "u16" => (uniform(4), true),
        "u32" => (uniform(5), true),
        "taper" => {
            let mut rem = log_n0;
            let mut s = Vec::new();
            while rem >= 4 { s.push(16usize); rem -= 4; }
            while rem >= 3 { s.push(8usize);  rem -= 3; }
            if rem > 0 { s.push(1usize << rem); }
            (s, true)
        }
        explicit => {
            let s: Vec<usize> = explicit.split(',')
                .map(|t| t.trim().parse::<usize>().expect("arity int"))
                .collect();
            (s, true)
        }
    }
}

fn main() {
    let sched_spec = std::env::var("SCHED").unwrap_or_else(|_| "taper".into());
    let log_t: u32 = std::env::var("LOG_T").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
    // Blowup (rate denominator rho_0 = 1/blowup); default matches the const.
    let blowup: usize = std::env::var("BLOWUP").ok().and_then(|v| v.parse().ok()).unwrap_or(BLOWUP);
    assert!(blowup.is_power_of_two() && blowup >= 2, "blowup must be pow2 >= 2");
    // AIR selection (AIR env): FIB (narrow, w=2) | SHA256 (wide, w=756,
    // the DS->KSK / RSA-hash core) | ED25519 (wide).  Tests whether the
    // arity optimum is AIR-width-dependent.
    let air_spec = std::env::var("AIR").unwrap_or_else(|_| "FIB".into());
    let (air, min_log_t, air_name): (AirType, u32, &str) = match air_spec.as_str() {
        "SHA256"  => (AirType::Sha256DsKsk,   7, "SHA256-w756"),
        "ED25519" => (AirType::Ed25519ZskKsk, 7, "Ed25519"),
        "POSEIDON"=> (AirType::PoseidonChain, 4, "Poseidon-w16"),
        _         => (AirType::Fibonacci,     4, "Fibonacci-w2"),
    };
    let log_t = log_t.max(min_log_t);
    let n_trace = 1usize << log_t;
    let n0 = n_trace * blowup;
    let log_n0 = n0.trailing_zeros() as usize;
    // r is set per (blowup, NIST level) to clear the level's IT-soundness
    // target: the canonical `num_queries_for_blowup` =
    // ceil(TARGET_IT_BITS / (0.5*log2(blowup))) + 2, where TARGET_IT_BITS
    // (128/192/256) is the COMPILE-TIME level via the sha3-256/384/512
    // feature.  Lower blowup ⇒ fewer bits/query ⇒ more queries.  `R`
    // overrides for a fixed-r study.  The active level's digest size also
    // changes the proof (SHA3-256/384/512 = 32/48/64-byte nodes), so the
    // level sweep is three feature builds.
    let r: usize = std::env::var("R").ok().and_then(|v| v.parse().ok())
        .unwrap_or_else(|| deep_ali::stark_level::num_queries_for_blowup(blowup));
    let bits_per_q = 0.5_f64 * (blowup as f64).log2();
    let it_bits = (r as f64 * bits_per_q) as usize;

    let (schedule, use_stir) = schedule_from_spec(&sched_spec, log_n0);
    // Validity: product of arities == n0.
    let sched_log: usize = schedule.iter().map(|m| m.trailing_zeros() as usize).sum();
    assert_eq!(sched_log, log_n0,
        "schedule {schedule:?} (sum log {sched_log}) must fold n0=2^{log_n0}");

    // AIR composition → c_eval codeword.
    let domain = FriDomain::new_radix2(n0);
    let trace = build_execution_trace(air, n_trace);
    let lde = lde_trace_columns(&trace, n_trace, blowup).expect("LDE");
    let coeffs: Vec<F> = (0..air.num_constraints())
        .map(|i| F::from((i + 1) as u64)).collect();
    let (c_eval, _) = deep_ali_merge_general(
        &lde, &coeffs, air, domain.omega, n_trace, blowup);

    let params = DeepFriParams {
        schedule: schedule.clone(),
        r, seed_z: SEED_Z,
        coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r,
        public_inputs_hash: Some([0x5Au8; 32]),
    };

    let t = Instant::now();
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    let tv = Instant::now();
    assert!(deep_fri_verify::<Ext>(&params, &proof), "proof must verify");
    let verify_ms = tv.elapsed().as_secs_f64() * 1e3;
    let bytes = deep_fri_proof_size_bytes::<Ext>(&proof, params.stir);

    let ldt = if use_stir { "STIR" } else { "FRI " };
    let nist = deep_ali::stark_level::NIST_LEVEL;
    println!(
        "L{nist} air={air_name:<12} SCHED={sched_spec:<8} bw={blowup:<3} r={r:<3} ({it_bits}b) \
         ldt={ldt} layers={:>2} |H0|=2^{log_n0} proof={:>5} KiB  prove={prove_ms:>8.1} ms  \
         verify={verify_ms:>6.2} ms",
        schedule.len(), bytes / 1024,
    );
}
