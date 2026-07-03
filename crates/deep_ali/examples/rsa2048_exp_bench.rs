//! Compact RSA-2048 exp-chain verify STARK measurement (paper config).
//!
//! Proves+verifies the **compact** exponentiation-chain RSA-2048 AIR
//! (`rsa2048_exp_air`, 17 active rows, `n_trace = 32`, `n0 = 1024`) — the
//! short-wide layout the paper's `tab:phase-rsa` reports (0.68 s class),
//! as opposed to the tall-narrow stacked AIR (`rsa2048_bench`, n_trace=4096).
//!
//! NIST-level-aware: the extension field, query count, and SHA-3 instance
//! all follow the active `sha3-256|384|512` feature —
//!   L1: Fp6, r=55, SHA3-256 | L3: Fp6, r=81, SHA3-384 | L5: Fp8, r=108, SHA3-512
//! (slack Johnson floor `deep_ali::stark_level::NUM_QUERIES_LEVEL`).
//!
//! Run (per level):
//!   cargo run --release -p deep_ali --example rsa2048_exp_bench \
//!     --no-default-features --features sha3-256,mldsa-44,parallel   # L1
//!     --no-default-features --features sha3-384,mldsa-44,parallel   # L3
//!     --no-default-features --features sha3-512,mldsa-44,parallel   # L5

use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_serialize::{CanonicalSerialize, Compress};
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

use deep_ali::{
    deep_ali_merge_rsa_exp_streaming,
    fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain},
    rsa2048_exp_air::{
        build_rsa_exp_multirow_layout, fill_rsa_exp_multirow,
        rsa_exp_multirow_constraints,
    },
    trace_import::lde_trace_columns,
};

// Feature-gated extension field — Fp6 (L1/L3) or Fp8 (L5).  This is the
// field the FS soundness rests on, so it MUST track the level (unlike
// rsa2048_bench, which hardcodes SexticExt).
type Ext = deep_ali::permutation_argument::ExtField;

fn gen_biguint(rng: &mut rand::rngs::StdRng, bits: u32) -> BigUint {
    let bytes = (bits as usize + 7) / 8;
    let mut buf = vec![0u8; bytes];
    rng.fill(&mut buf[..]);
    let extra = (bytes * 8) - bits as usize;
    if extra > 0 {
        buf[0] &= 0xFF >> extra;
    }
    BigUint::from_bytes_be(&buf)
}

fn gen_biguint_below(rng: &mut rand::rngs::StdRng, n: &BigUint) -> BigUint {
    let bits = n.bits() as u32;
    loop {
        let candidate = gen_biguint(rng, bits);
        if &candidate < n {
            return candidate;
        }
    }
}

/// Build the LDE + merge + DeepFriParams for a (possibly tampered) em.
fn prove_one(n: &BigUint, s: &BigUint, em: &BigUint, blowup: usize, r: usize, use_stir: bool)
    -> (Vec<F>, DeepFriParams, FriDomain, usize, usize)
{
    let n_trace = 32usize; // 17 active rows + padding; n0 = 32*32 = 1024
    let (layout, width) = build_rsa_exp_multirow_layout(0);
    let mut trace: Vec<Vec<F>> = (0..width).map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_exp_multirow(&mut trace, &layout, n_trace, n, s, em);

    let kk = rsa_exp_multirow_constraints(&layout);
    let n0 = n_trace * blowup;
    let domain = FriDomain::new_radix2(n0);
    let pi_hash: [u8; 32] = {
        use sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        h.update(b"deep_ali/rsa2048_exp_bench/v1");
        h.finalize().into()
    };
    let params = DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64,
        coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r,
        public_inputs_hash: Some(pi_hash),
    };

    let lde = lde_trace_columns(&trace, n_trace, blowup).expect("LDE");
    let comb_coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
    let (c_eval, _info) = deep_ali_merge_rsa_exp_streaming(
        &lde, &comb_coeffs, &layout, F::zero(), n_trace, blowup,
    );
    (c_eval, params, domain, n_trace, kk)
}

fn main() {
    let rayon_threads = rayon::current_num_threads();
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    eprintln!(
        "=== rsa2048_exp_bench: compact exp-chain RSA-2048 AIR (1 record), \
         NIST L{level}, Fp{ext_deg}, threads={rayon_threads} ==="
    );

    let mut rng = rand::rngs::StdRng::seed_from_u64(0xDEAD);
    let n = (gen_biguint(&mut rng, 2046) << 1) | BigUint::from(1u8);
    let s = gen_biguint_below(&mut rng, &n);
    let em = s.modpow(&BigUint::from(65_537u32), &n);

    let blowup: usize = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(32);
    // Default r = the slack Johnson floor for the ACTIVE level (55/81/108).
    let r: usize = std::env::var("BENCH_QUERIES").ok().and_then(|s| s.parse().ok())
        .unwrap_or(deep_ali::stark_level::NUM_QUERIES_LEVEL);
    let use_stir: bool = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let ldt_label = if use_stir { "stir" } else { "fri" };

    // ── Positive: honest record proves + verifies ──
    let (c_eval, params, domain, n_trace, kk) = prove_one(&n, &s, &em, blowup, r, use_stir);
    eprintln!("trace cols: {}, rows: {n_trace}, constraints: {kk}, blowup: {blowup}, r: {r}, ldt: {ldt_label}",
        { let (l, w) = build_rsa_exp_multirow_layout(0); let _ = l; w });

    let t0 = Instant::now();
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).expect("serialize");
    let proof_kib = buf.len() as f64 / 1024.0;

    let mut samples: Vec<f64> = Vec::with_capacity(3);
    for _ in 0..3 {
        let t0 = Instant::now();
        let ok = deep_fri_verify::<Ext>(&params, &proof);
        samples.push(t0.elapsed().as_secs_f64() * 1000.0);
        assert!(ok, "compact RSA-2048 verify rejected an honest proof — bench broken");
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let verify_ms = samples[1];

    // ── Negative (soundness): a wrong em must FAIL the low-degree test ──
    let bogus_em = (&em + BigUint::from(1u8)) % &n;
    let (bad_c, bad_params, bad_domain, _, _) = prove_one(&n, &s, &bogus_em, blowup, r, use_stir);
    let bad_proof = deep_fri_prove::<Ext>(bad_c, bad_domain, &bad_params);
    let bad_ok = deep_fri_verify::<Ext>(&bad_params, &bad_proof);
    assert!(!bad_ok, "SOUNDNESS FAILURE: tampered em (s^65537+1) produced a verifying proof");
    eprintln!("[soundness] tampered em -> verify rejected ✓");

    println!(
        "rsa2048_exp_bench level=L{level} field=Fp{ext_deg} n_trace={n_trace} blowup={blowup} r={r} \
         threads={rayon_threads} prove_ms={prove_ms:.1} verify_ms={verify_ms:.2} proof_kib={proof_kib:.1}"
    );
}
