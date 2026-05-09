//! Trace-size scaling sweep for the simple AIRs (Fibonacci,
//! PoseidonChain, RegisterMachine), matching the FRI paper's
//! k=11..24 measurement methodology.
//!
//! Runs each AIR at log2(trace_size) values supplied via CLI args,
//! producing one CSV-friendly stdout line per measurement.  The
//! caller (aws-bench/bench-simple-scaling.sh) handles the (level,
//! hash) matrix via Cargo features at build time.
//!
//! Each measurement: prove + verify (median of 3 verify runs).
//! Reports prove_ms, verify_ms, proof_kib, peak_rss_mib (best-effort).
//!
//! Run:
//!     cargo run --release -p cairo-bench --example simple_air_scaling -- \
//!         --air Fibonacci 11 14 18 22 24
//!     cargo run --release -p cairo-bench --example simple_air_scaling -- \
//!         --air PoseidonChain 11 14 18
//!     cargo run --release -p cairo-bench --example simple_air_scaling -- \
//!         --air RegisterMachine 11 14 18 22

use std::env;
use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;

use deep_ali::{
    air_workloads::{build_execution_trace, AirType},
    deep_ali_merge_general,
    fri::{deep_fri_proof_size_bytes, deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain},
    sextic_ext::SexticExt,
    trace_import::lde_trace_columns,
};

type Ext = SexticExt;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "Usage: simple_air_scaling --air <Fibonacci|PoseidonChain|RegisterMachine> <log2_size>..."
        );
        std::process::exit(1);
    }

    let mut air_name = "Fibonacci";
    let mut log2_sizes: Vec<usize> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--air" => {
                i += 1;
                air_name = match args.get(i).map(|s| s.as_str()) {
                    Some("Fibonacci")       => "Fibonacci",
                    Some("PoseidonChain")   => "PoseidonChain",
                    Some("RegisterMachine") => "RegisterMachine",
                    Some(other) => { eprintln!("unknown air: {other}"); std::process::exit(1); }
                    None        => { eprintln!("--air needs a value");   std::process::exit(1); }
                };
            }
            other => {
                if let Ok(k) = other.parse() { log2_sizes.push(k); }
                else { eprintln!("bad arg: {other}"); std::process::exit(1); }
            }
        }
        i += 1;
    }
    if log2_sizes.is_empty() {
        log2_sizes = (11..=18).collect();  // sensible default
    }

    let blowup: usize = env::var("BENCH_BLOWUP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(32);
    let r: usize = env::var("BENCH_QUERIES")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(54);

    let air = match air_name {
        "Fibonacci"       => AirType::Fibonacci,
        "PoseidonChain"   => AirType::PoseidonChain,
        "RegisterMachine" => AirType::RegisterMachine,
        _                 => unreachable!(),
    };

    eprintln!("=== simple_air_scaling: AIR={air_name}, blowup={blowup}, r={r} ===");

    for k in log2_sizes {
        let n_trace: usize = 1 << k;

        // ── Build trace ──
        let trace: Vec<Vec<F>> = build_execution_trace(air, n_trace);

        // ── Prove ──
        let n0 = n_trace * blowup;
        let domain = FriDomain::new_radix2(n0);
        let kk = air.num_constraints();
        let comb_coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();

        let pi_hash: [u8; 32] = {
            use sha3::{Digest, Sha3_256};
            let mut h = Sha3_256::new();
            h.update(b"deep_ali/simple_air_scaling/v1");
            h.update(air_name.as_bytes());
            h.update(&(k as u64).to_le_bytes());
            h.finalize().into()
        };
        let params = DeepFriParams {
            schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
            r,
            seed_z: 0xDEEFu64,
            coeff_commit_final: true,
            d_final: 1,
            stir: false,
            s0: r,
            public_inputs_hash: Some(pi_hash),
        };

        let t0 = Instant::now();
        let lde = lde_trace_columns(&trace, n_trace, blowup).expect("LDE");
        let (c_eval, _) = deep_ali_merge_general(
            &lde, &comb_coeffs, air, F::zero(), n_trace, blowup,
        );
        let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let proof_kib = deep_fri_proof_size_bytes(&proof, false) as f64 / 1024.0;

        // ── Verify (3 runs, median) ──
        let mut samples: Vec<f64> = Vec::with_capacity(3);
        for _ in 0..3 {
            let t0 = Instant::now();
            let ok = deep_fri_verify::<Ext>(&params, &proof);
            samples.push(t0.elapsed().as_secs_f64() * 1000.0);
            assert!(ok, "{air_name}@k={k} verify rejected");
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let verify_ms = samples[1];

        // CSV-friendly stdout.  bench-simple-scaling.sh parses `key=value`
        // tokens and lifts the (sha3, mldsa) Cargo features via env.
        println!(
            "simple_air_scaling air={air_name} log2_n={k} n_trace={n_trace} \
             blowup={blowup} r={r} prove_ms={prove_ms:.0} \
             verify_ms={verify_ms:.2} proof_kib={proof_kib:.1}"
        );
    }
}
