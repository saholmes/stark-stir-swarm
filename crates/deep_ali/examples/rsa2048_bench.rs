//! RSA-2048 verify STARK measurement.
//!
//! Runs one full prove + verify of the stacked-RSA-2048 verify AIR
//! (single record) and reports prove_ms / verify_ms / proof_kib in a
//! CSV-friendly format.  Intended for aws-bench/bench-rsa2048.sh.
//!
//! Run:
//!     cargo run --release -p deep_ali --example rsa2048_bench \
//!         --features "parallel sha3-256 mldsa-44" --no-default-features

use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_serialize::{CanonicalSerialize, Compress};
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

use deep_ali::{
    deep_ali_merge_rsa_stacked_streaming,
    fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain},
    rsa2048_stacked_air::{
        build_rsa_stacked_layout, fill_rsa_stacked,
        rsa_stacked_constraints, RsaStackedRecord,
    },
    sextic_ext::SexticExt,
    trace_import::lde_trace_columns,
};

type Ext = SexticExt;

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

fn main() {
    eprintln!("=== rsa2048_bench: stacked RSA-2048 verify AIR (1 record) ===");

    // ── Synthesise one honest RSA verification record ──
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xDEAD);
    let n = (gen_biguint(&mut rng, 2046) << 1) | BigUint::from(1u8);
    let s = gen_biguint_below(&mut rng, &n);
    let em = s.modpow(&BigUint::from(65_537u32), &n);
    let records = vec![RsaStackedRecord { n, s, em }];

    let layout = build_rsa_stacked_layout(records.len());
    // n_trace must accommodate the layout's row schedule; for one
    // record at 2046 bits, ~2080 active rows.  Round up to power-of-2.
    let n_trace_active = 2080usize;
    let n_trace = n_trace_active.next_power_of_two();

    let mut trace: Vec<Vec<F>> = (0..layout.width)
        .map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_stacked(&mut trace, &layout, n_trace, &records);

    let blowup: usize = std::env::var("BENCH_BLOWUP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(32);
    let r: usize = std::env::var("BENCH_QUERIES")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(54);

    let kk = rsa_stacked_constraints(&layout);
    eprintln!(
        "trace cols: {}, rows: {}, constraints: {}, blowup: {}, r: {}",
        layout.width, n_trace, kk, blowup, r
    );

    // ── Prove ──
    let n0 = n_trace * blowup;
    let domain = FriDomain::new_radix2(n0);
    let pi_hash: [u8; 32] = {
        use sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        h.update(b"deep_ali/rsa2048_bench/v1");
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
    let comb_coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
    let (c_eval, _info) = deep_ali_merge_rsa_stacked_streaming(
        &lde, &comb_coeffs, &layout, F::zero(), n_trace, blowup,
    );
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // ── Proof size ──
    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).expect("serialize");
    let proof_kib = buf.len() as f64 / 1024.0;

    // ── Verify (3 runs for median) ──
    let mut samples: Vec<f64> = Vec::with_capacity(3);
    for _ in 0..3 {
        let t0 = Instant::now();
        let ok = deep_fri_verify::<Ext>(&params, &proof);
        samples.push(t0.elapsed().as_secs_f64() * 1000.0);
        assert!(ok, "RSA-2048 verify rejected — bench is broken");
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let verify_ms = samples[1];

    println!(
        "rsa2048_bench n_trace={n_trace} blowup={blowup} r={r} \
         prove_ms={prove_ms:.0} verify_ms={verify_ms:.2} proof_kib={proof_kib:.1}"
    );
}
