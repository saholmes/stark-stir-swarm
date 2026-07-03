//! WITNESS-BINDING narrow multi-row P256 ECDSA (the width-efficient fix).
//!
//! Binds the StarkWare-style multi-row double-scalar-mult AIR
//! (`p256_ecdsa_double_multirow_air`: one step/row, accumulator threaded by
//! transition constraints) with the existing
//! `sub_air_with_trace::{prove,verify}_one_sub_air_with_trace`.  Because the
//! per-row width is ONE step (not the whole unrolled chain), the openings
//! (`r × per-row-width`) are small — no OOM, unlike the single-row v2 layout.
//!
//! MILESTONE (K=4): honest double-scalar-mult ACCEPTS; a bogus projective
//! output (`r_proj`) REJECTS — the in-circuit verdict binds the witness.
//! The transition AIR uses `nxt`, so the FULL binding is required.
//!
//! Run: cargo run --release -p deep_ali --example ecdsa_multirow_bound_bench \
//!        --no-default-features --features sha3-256,mldsa-44,parallel

use std::time::Instant;

use ark_ff::{PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;

use deep_ali::{
    deep_ali_merge_ecdsa_double_multirow_streaming,
    fri::DeepFriParams,
    p256_ecdsa_double_multirow_air::{
        build_ecdsa_double_multirow_layout, ecdsa_double_multirow_constraints,
        eval_ecdsa_double_multirow_per_row, fill_ecdsa_double_multirow, EcdsaDoubleMultirowLayout,
    },
    p256_field::{FieldElement, NUM_LIMBS},
    p256_group::GENERATOR,
    sub_air_with_trace::{prove_one_sub_air_with_trace, verify_one_sub_air_with_trace},
};

const PI_HASH: [u8; 32] = [0x44; 32];

fn mk_params(n0: usize, r: usize, use_stir: bool, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64, coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r, public_inputs_hash: Some(ph),
    }
}

fn read_fe(trace: &[Vec<F>], base: usize, row: usize) -> FieldElement {
    let mut limbs = [0i64; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        let bi = trace[base + i][row].into_bigint();
        limbs[i] = bi.as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let r = deep_ali::stark_level::NUM_QUERIES_LEVEL;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(16usize);
    let k = std::env::var("KSTEPS").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    let n_trace = k.next_power_of_two().max(2);
    eprintln!("=== ecdsa_multirow_bound_bench: narrow multi-row P256 ECDSA, K={k}, n_trace={n_trace}, \
               NIST L{level}, Fp{ext_deg}, r={r}, blowup={blowup} ===");

    let (layout, total) = build_ecdsa_double_multirow_layout(0);
    let kk = ecdsa_double_multirow_constraints(&layout);
    eprintln!("    per-row width = {total} cells, constraints = {kk}");

    let g = *GENERATOR;
    let q = g.double();
    let z_one = { let mut t = FieldElement::zero(); t.limbs[0] = 1; t };
    let a_bits: Vec<bool> = (0..k).map(|i| i % 2 == 0).collect();
    let b_bits: Vec<bool> = (0..k).map(|i| i % 3 == 0).collect();

    // Two-pass fill: pass 1 (r_proj=0) captures the real chain outputs.
    let zfe = FieldElement::zero();
    let fill = |trace: &mut [Vec<F>], rp: &[FieldElement; 6]| {
        fill_ecdsa_double_multirow(
            trace, &layout, n_trace, k, k,
            &g.x, &g.y, &z_one, &g.x, &g.y, &z_one, &a_bits,
            &q.x, &q.y, &z_one, &q.x, &q.y, &z_one, &b_bits,
            &rp[0], &rp[1], &rp[2], &rp[3], &rp[4], &rp[5],
        );
    };
    let mut t0 = vec![vec![F::zero(); n_trace]; total];
    fill(&mut t0, &[zfe; 6]);
    let last = n_trace - 1;
    let rp = [
        read_fe(&t0, layout.step_a.select_x.c_limbs_base, last),
        read_fe(&t0, layout.step_a.select_y.c_limbs_base, last),
        read_fe(&t0, layout.step_a.select_z.c_limbs_base, last),
        read_fe(&t0, layout.step_b.select_x.c_limbs_base, last),
        read_fe(&t0, layout.step_b.select_y.c_limbs_base, last),
        read_fe(&t0, layout.step_b.select_z.c_limbs_base, last),
    ];

    let prove_verify = |trace: &[Vec<F>]| -> (f64, f64, usize, bool) {
        let t = Instant::now();
        let proof = prove_one_sub_air_with_trace(
            trace, n_trace, blowup, PI_HASH, b"ecdsa_multirow", kk,
            |lde, nt, bw, cc| deep_ali_merge_ecdsa_double_multirow_streaming(lde, cc, &layout, nt, bw).0,
            |n0, ph| mk_params(n0, r, use_stir, ph),
        );
        let p_ms = t.elapsed().as_secs_f64() * 1000.0;
        let t = Instant::now();
        let ok = verify_one_sub_air_with_trace(
            &proof, n_trace, blowup, PI_HASH, b"ecdsa_multirow", total, kk,
            |cur, nxt, row| eval_ecdsa_double_multirow_per_row(cur, nxt, row, n_trace, &layout),
            |n0, ph| mk_params(n0, r, use_stir, ph),
        ).is_ok();
        (p_ms, t.elapsed().as_secs_f64() * 1000.0, proof.fri_proof_bytes.len(), ok)
    };

    // Honest: ACCEPT.
    let mut honest = vec![vec![F::zero(); n_trace]; total];
    fill(&mut honest, &rp);
    let (p_ms, v_ms, fri_b, ok) = prove_verify(&honest);
    eprintln!("[honest]   prove {p_ms:.1} ms, verify {v_ms:.2} ms, fri {} KiB -> verify={ok}", fri_b / 1024);
    assert!(ok, "BINDING BROKEN: honest multi-row ECDSA must verify");

    // Tampered: bogus r_proj (claimed output != actual) -> REJECT.
    let bogus = FieldElement { limbs: [7i64; NUM_LIMBS] };
    let mut bad = vec![vec![F::zero(); n_trace]; total];
    fill(&mut bad, &[bogus, bogus, bogus, rp[3], rp[4], rp[5]]);
    let (_, _, _, bad_ok) = prove_verify(&bad);
    eprintln!("[tampered] bogus r_proj_a -> verify={bad_ok}");

    println!(
        "ecdsa_multirow K={k} n_trace={n_trace} per_row_width={total} r={r} blowup={blowup} \
         prove_ms={p_ms:.1} verify_ms={v_ms:.2} fri_kib={} honest_verify={ok} tampered_verify={bad_ok}",
        fri_b / 1024
    );
    if ok && !bad_ok {
        println!("=> WITNESS-BINDING WORKS for narrow multi-row ECDSA: honest accepts, tampered REJECTS");
    } else {
        println!("=> FAILED: honest={ok} tampered={bad_ok}");
    }
}
