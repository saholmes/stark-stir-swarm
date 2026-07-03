//! Soundness probe for the stacked RSA-2048 bench path.
//!
//! Runs the EXACT `rsa2048_bench` prove pipeline (stacked AIR, n_trace=4096,
//! deep_ali_merge_rsa_stacked_streaming -> deep_fri_prove(c_eval)) twice:
//!   (1) honest record  (em = s^65537 mod n)   -> expect verify ACCEPT
//!   (2) tampered record (em = s^65537 + 1)     -> a SOUND proof must REJECT
//!
//! If (2) ACCEPTS, the bare `merge -> deep_fri_prove(c_eval)` path is
//! witness-non-binding (low-degree-only), confirming the gap is systemic
//! to the simple per-signature benches, not specific to the exp merge.
//!
//! Run:
//!   cargo run --release -p deep_ali --example rsa2048_stacked_soundness \
//!     --no-default-features --features sha3-256,mldsa-44,parallel

use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

use deep_ali::{
    deep_ali_merge_rsa_stacked_streaming,
    fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain},
    rsa2048_stacked_air::{
        build_rsa_stacked_layout, fill_rsa_stacked, rsa_stacked_constraints, RsaStackedRecord,
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
    if extra > 0 { buf[0] &= 0xFF >> extra; }
    BigUint::from_bytes_be(&buf)
}
fn gen_biguint_below(rng: &mut rand::rngs::StdRng, n: &BigUint) -> BigUint {
    let bits = n.bits() as u32;
    loop { let c = gen_biguint(rng, bits); if &c < n { return c; } }
}

fn run(label: &str, n: &BigUint, s: &BigUint, em: &BigUint) -> bool {
    let records = vec![RsaStackedRecord { n: n.clone(), s: s.clone(), em: em.clone() }];
    let layout = build_rsa_stacked_layout(records.len());
    let n_trace = 2080usize.next_power_of_two();
    let blowup = 32usize;
    let mut trace: Vec<Vec<F>> = (0..layout.width).map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_stacked(&mut trace, &layout, n_trace, &records);

    let kk = rsa_stacked_constraints(&layout);
    let n0 = n_trace * blowup;
    let domain = FriDomain::new_radix2(n0);
    let pi_hash: [u8; 32] = {
        use sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        h.update(b"deep_ali/rsa2048_stacked_soundness/v1");
        h.finalize().into()
    };
    let params = DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r: 55, seed_z: 0xDEEFu64, coeff_commit_final: true, d_final: 1,
        stir: true, s0: 55, public_inputs_hash: Some(pi_hash),
    };
    let t0 = Instant::now();
    let lde = lde_trace_columns(&trace, n_trace, blowup).expect("LDE");
    let comb_coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
    let (c_eval, _info) = deep_ali_merge_rsa_stacked_streaming(
        &lde, &comb_coeffs, &layout, F::zero(), n_trace, blowup,
    );
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let ok = deep_fri_verify::<Ext>(&params, &proof);
    eprintln!("[{label}] prove+verify {:.1}s -> verify={}", t0.elapsed().as_secs_f64(), ok);
    ok
}

fn main() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xDEAD);
    let n = (gen_biguint(&mut rng, 2046) << 1) | BigUint::from(1u8);
    let s = gen_biguint_below(&mut rng, &n);
    let em = s.modpow(&BigUint::from(65_537u32), &n);
    let bogus = (&em + BigUint::from(1u8)) % &n;

    let honest_ok = run("honest", &n, &s, &em);
    let tampered_ok = run("tampered", &n, &s, &bogus);

    println!("STACKED-SOUNDNESS honest_verify={honest_ok} tampered_verify={tampered_ok}");
    if tampered_ok {
        println!("=> SYSTEMIC: stacked rsa2048_bench path is witness-NON-binding (tampered proof verifies)");
    } else {
        println!("=> stacked path REJECTS tampering (binding) — gap would be specific to the exp merge");
    }
}
