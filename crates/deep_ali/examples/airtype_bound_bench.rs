//! GENERIC witness-binding demonstrator for AirType-dispatched AIRs.
//!
//! Routes any `AirType` (NSEC3 chain, SHA-256 DS, Ed25519-ZskKsk, HashRollup,
//! …) through `sub_air_with_trace::{prove,verify}_one_sub_air_with_trace`
//! instead of the non-binding `deep_ali_merge_general -> deep_fri_prove(c_eval)`
//! path.  For each AIR it proves an honest trace (must ACCEPT) and a
//! one-cell-tampered trace (must REJECT), demonstrating the same generic
//! fix that made the RSA exp AIR sound applies across AIR classes.
//!
//! Run: AIR=nsec3 cargo run --release -p deep_ali --example airtype_bound_bench \
//!        --no-default-features --features sha3-256,mldsa-44,parallel
//!   AIR ∈ {nsec3, ds, ed25519, hashrollup}

use std::time::Instant;

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use deep_ali::{
    air_workloads::{build_execution_trace, evaluate_constraints, AirType},
    deep_ali_merge_general,
    fri::DeepFriParams,
    sub_air_with_trace::{prove_one_sub_air_with_trace, verify_one_sub_air_with_trace},
};

fn mk_params(n0: usize, r: usize, use_stir: bool, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64, coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r, public_inputs_hash: Some(ph),
    }
}
const PI_HASH: [u8; 32] = [0x22; 32];

fn prove_then_verify(air: AirType, trace: &[Vec<F>], n_trace: usize, blowup: usize, r: usize, use_stir: bool)
    -> (f64, f64, usize, bool)
{
    let width = air.width();
    let kk = air.num_constraints();
    let t0 = Instant::now();
    let proof = prove_one_sub_air_with_trace(
        trace, n_trace, blowup, PI_HASH, b"airtype_bound", kk,
        |lde, nt, bw, cc| deep_ali_merge_general(lde, cc, air, F::zero(), nt, bw).0,
        |n0, ph| mk_params(n0, r, use_stir, ph),
    );
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t0 = Instant::now();
    let res = verify_one_sub_air_with_trace(
        &proof, n_trace, blowup, PI_HASH, b"airtype_bound", width, kk,
        |cur, nxt, row| evaluate_constraints(air, cur, nxt, row),
        |n0, ph| mk_params(n0, r, use_stir, ph),
    );
    let verify_ms = t0.elapsed().as_secs_f64() * 1000.0;
    (prove_ms, verify_ms, proof.fri_proof_bytes.len(), res.is_ok())
}

fn main() {
    let air = match std::env::var("AIR").as_deref().unwrap_or("nsec3") {
        "nsec3" => AirType::Nsec3Chain,
        "ds"    => AirType::Sha256DsKsk,
        "ed25519" => AirType::Ed25519ZskKsk,
        "hashrollup" => AirType::HashRollup,
        other => { eprintln!("unknown AIR '{other}', using nsec3"); AirType::Nsec3Chain }
    };
    let n_trace = std::env::var("NTRACE").ok().and_then(|s| s.parse().ok()).unwrap_or(64usize);
    let blowup = 32usize;
    let r = deep_ali::stark_level::NUM_QUERIES_LEVEL;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    eprintln!("=== airtype_bound_bench: AIR={air:?} (w={}, k={}), n_trace={n_trace}, r={r} ===",
        air.width(), air.num_constraints());

    // ── Honest: ACCEPT ──
    let honest = build_execution_trace(air, n_trace);
    let (p_ms, v_ms, fri_b, ok) = prove_then_verify(air, &honest, n_trace, blowup, r, use_stir);
    eprintln!("[honest]   prove {p_ms:.1} ms, verify {v_ms:.2} ms, fri {} KiB -> verify={ok}", fri_b / 1024);
    assert!(ok, "BINDING BROKEN: honest {air:?} trace must verify");

    // ── Tampered: flip one constraint-relevant cell -> REJECT ──
    let mut bad = honest.clone();
    bad[0][1] += F::one(); // column 0, row 1 (transition-constrained in every AIR here)
    let (_, _, _, bad_ok) = prove_then_verify(air, &bad, n_trace, blowup, r, use_stir);
    eprintln!("[tampered] cell[0][1]+=1 -> verify={bad_ok}");

    println!("airtype_bound AIR={air:?} n_trace={n_trace} r={r} prove_ms={p_ms:.1} verify_ms={v_ms:.2} \
              honest_verify={ok} tampered_verify={bad_ok}");
    if !bad_ok {
        println!("=> WITNESS-BINDING WORKS for {air:?}: honest accepts, tampered REJECTS");
    } else {
        println!("=> {air:?} STILL NON-BINDING (or cell[0][1] unconstrained — try another cell)");
    }
}
