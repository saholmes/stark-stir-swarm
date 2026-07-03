//! END-TO-END WITNESS-BINDING + PUBLIC-INPUT-BINDING multi-row P256
//! ECDSA *verification*.
//!
//! Drives the narrow double-scalar-mult kernel (one step/row, K=256
//! rows) PLUS the verify tail (group_add + inverse-free cross-multiply
//! `R.X ≡ {r, r+n}·R.Z (mod p)` + final equality) at row K, and binds
//! the whole thing — TWO ways, both required — to the ACTUAL public
//! signature:
//!   1. `pi_hash = SHA256(r ‖ s ‖ Qx ‖ Qy ‖ digest)`  (Fiat–Shamir),
//!   2. in-circuit boundary pins: u1/u2 bits, the G and Q base columns,
//!      and the tail-row `r` column == the verifier's public values.
//!
//! DECISIVE SOUNDNESS TEST: the proof for signature A, re-verified under
//! signature B's pi_hash + B's pinned public constants, MUST REJECT —
//! proving the proof is bound to *this specific* public signature, not
//! merely an internally-consistent witness.
//!
//! Run: cargo run --release -p swarm-dns --example ecdsa_verify_multirow_bound_bench \
//!        --no-default-features --features sha3-256,mldsa-44,parallel

use std::time::Instant;

use ark_ff::{PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;
use sha2::{Digest as _, Sha256};

use p256::ecdsa::{signature::Signer, Signature as P256Signature, SigningKey, VerifyingKey};
use p256::elliptic_curve::sec1::ToEncodedPoint;

use deep_ali::{
    deep_ali_merge_ecdsa_verify_multirow_streaming,
    fri::DeepFriParams,
    p256_ecdsa::{
        reduce_digest_mod_n, verify as ecdsa_verify_native, PublicKey as EcdsaPublicKey,
        Signature as EcdsaSignature,
    },
    p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, ecdsa_verify_multirow_constraints,
        eval_ecdsa_verify_multirow_per_row, fill_ecdsa_verify_multirow,
        EcdsaVerifyMultirowLayout, EcdsaVerifyPublicInputs,
    },
    p256_field::{FieldElement, NUM_LIMBS},
    p256_group::GENERATOR as P256_GENERATOR,
    p256_scalar::ScalarElement,
    sub_air_with_trace::{prove_one_sub_air_with_trace, verify_one_sub_air_with_trace},
};

fn scalar_to_msb_bits_256(s: &ScalarElement) -> Vec<bool> {
    let bytes = s.to_be_bytes();
    let mut bits = Vec::with_capacity(256);
    for byte in bytes.iter() {
        for shift in (0..8).rev() {
            bits.push((byte >> shift) & 1 == 1);
        }
    }
    bits
}

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
        limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
    }
    FieldElement { limbs }
}

/// All derived data for one real signature: the in-circuit witness
/// inputs AND the verifier's public binding (pi_hash + pinned values).
struct SigCase {
    native_ok: bool,
    u1_bits: Vec<bool>,
    u2_bits: Vec<bool>,
    qx: FieldElement,
    qy: FieldElement,
    r_fe: FieldElement,
    pi_hash: [u8; 32],
    pub_inputs: EcdsaVerifyPublicInputs,
    // for the diagnostic native cross-check:
    u_1: ScalarElement,
    u_2: ScalarElement,
    sig_r: ScalarElement,
    qpoint: deep_ali::p256_group::AffinePoint,
}

fn derive_case(key_bytes: &[u8; 32], msg: &[u8], k: usize) -> SigCase {
    let sk = SigningKey::from_slice(key_bytes).expect("valid P256 key");
    let sig: P256Signature = sk.sign(msg);
    let vk = VerifyingKey::from(&sk);
    let ep = vk.to_encoded_point(false);
    let epb = ep.as_bytes();
    let mut qx = [0u8; 32]; qx.copy_from_slice(&epb[1..33]);
    let mut qy = [0u8; 32]; qy.copy_from_slice(&epb[33..65]);
    let sb = sig.to_bytes();
    let mut rbytes = [0u8; 32]; rbytes.copy_from_slice(&sb[0..32]);
    let mut sbytes = [0u8; 32]; sbytes.copy_from_slice(&sb[32..64]);
    let digest: [u8; 32] = Sha256::digest(msg).into();

    let pk = EcdsaPublicKey::from_be_bytes(&qx, &qy).expect("pk parse");
    let signature = EcdsaSignature::from_be_bytes(&rbytes, &sbytes).expect("sig parse");
    let native_ok = ecdsa_verify_native(&digest, &pk, &signature);

    // Verifier-side scalar prep (cheap, native).
    let e = reduce_digest_mod_n(&digest);
    let w = signature.s.invert();
    let u_1 = e.mul(&w);
    let u_2 = signature.r.mul(&w);
    let u1_bits = scalar_to_msb_bits_256(&u_1);
    let u2_bits = scalar_to_msb_bits_256(&u_2);
    assert_eq!(u1_bits.len(), k);

    let r_fe = FieldElement::from_be_bytes(&rbytes);
    let g = *P256_GENERATOR;
    let pub_inputs = EcdsaVerifyPublicInputs::new(
        &u1_bits, &u2_bits, &g.x, &g.y, &pk.point.x, &pk.point.y, &r_fe,
    );

    // pi_hash = SHA256(r ‖ s ‖ Qx ‖ Qy ‖ digest).
    let mut hasher = Sha256::new();
    hasher.update(rbytes);
    hasher.update(sbytes);
    hasher.update(qx);
    hasher.update(qy);
    hasher.update(digest);
    let pi_hash: [u8; 32] = hasher.finalize().into();

    SigCase {
        native_ok, u1_bits, u2_bits,
        qx: pk.point.x, qy: pk.point.y, r_fe, pi_hash, pub_inputs,
        u_1, u_2, sig_r: signature.r, qpoint: pk.point,
    }
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    // r MUST track the blowup via the slack-Johnson bound: 55/81/108 is the
    // b=32 floor and is UNSOUND at b=4 (~51 bits).  num_queries_for_blowup
    // gives the sound count at THIS blowup (≈143/214/284 at b=4 for L1/L3/L5).
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup);
    let k = std::env::var("KSTEPS").ok().and_then(|s| s.parse().ok()).unwrap_or(256usize);
    let n_trace = (k + 1).next_power_of_two();
    eprintln!("=== ecdsa_verify_multirow_bound_bench: END-TO-END + PUBLIC-INPUT-BOUND P256 ECDSA verify, \
               K={k}, n_trace={n_trace}, NIST L{level}, Fp{ext_deg}, r={r}, blowup={blowup} ===");

    // ── Two distinct real signatures (different keys + messages). ──
    let case_a = derive_case(&[0x42u8; 32], b"STARK-DNS public-input-bound ECDSA verify: message A", k);
    let case_b = derive_case(&[0x17u8; 32], b"STARK-DNS public-input-bound ECDSA verify: message B", k);
    eprintln!("[native] ecdsa_verify(A) = {}, ecdsa_verify(B) = {}", case_a.native_ok, case_b.native_ok);
    assert!(case_a.native_ok && case_b.native_ok, "both signatures must natively verify");
    assert_ne!(case_a.pi_hash, case_b.pi_hash, "distinct signatures must have distinct pi_hash");

    let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
    let kk = ecdsa_verify_multirow_constraints(&layout);
    eprintln!("    per-row width = {total} cells, constraints = {kk}");

    let g = *P256_GENERATOR;
    let z_one = { let mut t = FieldElement::zero(); t.limbs[0] = 1; t };
    let id_x = FieldElement::zero();
    let id_y = { let mut t = FieldElement::zero(); t.limbs[0] = 1; t };
    let id_z = FieldElement::zero();

    let build_trace = |c: &SigCase| -> Vec<Vec<F>> {
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&id_x, &id_y, &id_z), (&g.x, &g.y, &z_one), &c.u1_bits,
            (&id_x, &id_y, &id_z), (&c.qx, &c.qy, &z_one), &c.u2_bits,
            &c.r_fe,
        );
        trace
    };

    // ── Diagnostic: in-circuit R.x == native R.x for A. ──
    {
        let trace = build_trace(&case_a);
        let r_x3 = read_fe(&trace, layout.group_add.result_x3_limbs_base, k);
        let r_z3 = read_fe(&trace, layout.group_add.result_z3_limbs_base, k);
        let mut x1 = r_x3.mul(&r_z3.invert());
        x1.freeze();
        let r_native = g.scalar_mul(&case_a.u_1).add(&case_a.qpoint.scalar_mul(&case_a.u_2));
        let mut rx_native = r_native.x;
        rx_native.freeze();
        eprintln!("[diag] in-circuit R.x == native R.x (A): {}", x1.ct_eq(&rx_native));
        let x1_mod_n = ScalarElement::from_be_bytes(&x1.to_be_bytes());
        eprintln!("[diag] (R.x mod n) == sig.r (A): {}", x1_mod_n.ct_eq(&case_a.sig_r));
        assert!(x1.ct_eq(&rx_native), "in-circuit R.x must equal native R.x");
    }

    let prove = |trace: &[Vec<F>], c: &SigCase, layout: &EcdsaVerifyMultirowLayout| {
        prove_one_sub_air_with_trace(
            trace, n_trace, blowup, c.pi_hash, b"ecdsa_verify_multirow", kk,
            |lde, nt, bw, cc| deep_ali_merge_ecdsa_verify_multirow_streaming(lde, cc, layout, &c.pub_inputs, nt, bw).0,
            |n0, ph| mk_params(n0, r, use_stir, ph),
        )
    };
    let verify = |proof: &deep_ali::sub_air_with_trace::SubAirProofWithTrace, c: &SigCase, layout: &EcdsaVerifyMultirowLayout| -> bool {
        verify_one_sub_air_with_trace(
            proof, n_trace, blowup, c.pi_hash, b"ecdsa_verify_multirow", total, kk,
            |cur, nxt, row| eval_ecdsa_verify_multirow_per_row(cur, nxt, row, n_trace, layout, &c.pub_inputs),
            |n0, ph| mk_params(n0, r, use_stir, ph),
        ).is_ok()
    };

    // ── Honest A: prove under A, verify under A → ACCEPT. ──
    let trace_a = build_trace(&case_a);
    let t = Instant::now();
    let proof_a = prove(&trace_a, &case_a, &layout);
    let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let fri_b = proof_a.fri_proof_bytes.len();
    // COMPLETE sound proof = full serialized SubAirProofWithTrace (LDT + openings + paths).
    let full_mib = deep_ali::sub_air_with_trace::serialize_proof(&proof_a).len() as f64 / 1048576.0;
    let t = Instant::now();
    let honest_a = verify(&proof_a, &case_a, &layout);
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    eprintln!("[honest A]  prove {prove_ms:.1} ms, verify {verify_ms:.2} ms, fri {} KiB, FULL sound proof {full_mib:.2} MiB -> verify={honest_a}", fri_b / 1024);
    assert!(honest_a, "BINDING BROKEN: honest A must accept under A's public inputs");

    // ── CROSS: A's proof, verified under B's pi_hash + B's pins → REJECT. ──
    let cross_a_under_b = verify(&proof_a, &case_b, &layout);
    eprintln!("[cross]     A's proof under B's public inputs -> verify={cross_a_under_b}");

    // ── Symmetric: B's proof under A → REJECT (prove B once). ──
    let trace_b = build_trace(&case_b);
    let proof_b = prove(&trace_b, &case_b, &layout);
    let honest_b = verify(&proof_b, &case_b, &layout);
    let cross_b_under_a = verify(&proof_b, &case_a, &layout);
    eprintln!("[cross]     honest_B={honest_b}, B's proof under A -> verify={cross_b_under_a}");

    // ── Internal tamper: perturb r[0] at the tail row → REJECT. ──
    let mut bad = trace_a.clone();
    bad[layout.r_base][k] += F::from(1u64);
    let proof_bad = prove(&bad, &case_a, &layout);
    let internal_tamper = verify(&proof_bad, &case_a, &layout);
    eprintln!("[tampered]  perturb r[0] -> verify={internal_tamper}");

    println!(
        "ecdsa_verify_multirow_pub K={k} n_trace={n_trace} per_row_width={total} r={r} blowup={blowup} \
         prove_ms={prove_ms:.1} verify_ms={verify_ms:.2} fri_kib={} proof_mib={full_mib:.2} native={} \
         honest_A={honest_a} honest_B={honest_b} cross_A_under_B={cross_a_under_b} \
         cross_B_under_A={cross_b_under_a} internal_tamper={internal_tamper}",
        fri_b / 1024, case_a.native_ok
    );
    let pass = case_a.native_ok && honest_a && honest_b
        && !cross_a_under_b && !cross_b_under_a && !internal_tamper;
    if pass {
        println!("=> PUBLIC-INPUT BINDING WORKS: honest accepts; cross-signature + internal tamper REJECT; native agrees");
    } else {
        println!("=> FAILED: native={} honest_A={honest_a} honest_B={honest_b} \
                  cross_A_under_B={cross_a_under_b} cross_B_under_A={cross_b_under_a} internal_tamper={internal_tamper}",
                 case_a.native_ok);
    }
}
