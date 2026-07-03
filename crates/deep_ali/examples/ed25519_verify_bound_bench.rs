//! WITNESS-BINDING Ed25519 signature-verification STARK.
//!
//! Routes the end-to-end Ed25519 verify-air **v16** (RFC 8032 §5.1.7
//! cofactored verify: SHA-512 → k = H(R‖A‖M) mod ℓ, [s]·B and [k]·A
//! ladders, residual chain, cofactor multiply, final verdict) through
//! `sub_air_with_trace::{prove,verify}_one_sub_air_with_trace`, which
//! Merkle-commits the trace LDE (folded into the FS pi_hash), opens
//! trace cells (cur+nxt) at every FRI query position, and re-checks
//! `c_eval(x)·Z_H(x) = Σ αⱼ Φⱼ(trace[x])` there.  A tampered witness
//! leaves a non-zero `poly_div_zh` remainder that fails at the random
//! query points → verify REJECTS.
//!
//! DECISIVE TEST: honest signature ACCEPTS; flipping the dbl_1 input
//! cell (the v16 residual_2 → dbl_input binding) REJECTS.
//!
//! The v16 layout-capturing merge `deep_ali_merge_ed25519_verify`
//! carries the per-call public inputs (R/A coords, s/k scalar bits,
//! k_scalar) that the static AirType registry cannot express.  At the
//! deployed k_scalar=256 it is identical to the stark-stir-security
//! `deep_ali_merge_ed25519_v16_streaming` (verdict gating is off at 256).
//!
//! Run (per level): cargo run --release -p deep_ali \
//!   --example ed25519_verify_bound_bench --no-default-features \
//!   --features sha3-256,parallel,mldsa-44
//!   (L3: sha3-384 ; L5: sha3-512,tower-octic ; BENCH_K_SCALAR=8 light)

use std::time::Instant;

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;
use rand::{Rng, SeedableRng};
use sha2::{Digest as _, Sha512};

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;

use deep_ali::{
    deep_ali_merge_ed25519_verify,
    ed25519_scalar::reduce_mod_l_wide,
    ed25519_verify_air::{
        eval_verify_air_v16_per_row, fill_verify_air_v16, r_thread_bits_for_kA,
        verify_v16_per_row_constraints,
    },
    fri::DeepFriParams,
    sub_air_with_trace::{prove_one_sub_air_with_trace, verify_one_sub_air_with_trace},
};

const PI_HASH: [u8; 32] = [0x55; 32]; // domain constant; trace_root binds the witness

fn rand_scalar(rng: &mut rand::rngs::StdRng) -> Scalar {
    let mut b = [0u8; 32];
    rng.fill(&mut b[..]);
    Scalar::from_bytes_mod_order(b)
}

fn build_verify_sha512_input(r: &[u8; 32], a: &[u8; 32], m: &[u8]) -> Vec<u8> {
    let mut input = Vec::with_capacity(64 + m.len());
    input.extend_from_slice(r);
    input.extend_from_slice(a);
    input.extend_from_slice(m);
    input
}

fn sha512_native(input: &[u8]) -> [u8; 64] {
    let mut h = Sha512::new();
    h.update(input);
    h.finalize().into()
}

fn mk_params(n0: usize, r: usize, use_stir: bool, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64, coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r, public_inputs_hash: Some(ph),
    }
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(2usize);
    // r MUST track the blowup via the slack-Johnson bound: the b=32 floor
    // (55/81/108) is UNSOUND at lower blowup (~24 bits at b=2, ~51 at b=4).
    // num_queries_for_blowup gives the sound query count for the active NIST
    // level at THIS blowup (e.g. 308/461/615 at b=2 for L1/L3/L5).
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup);
    // DEFAULT k_scalar = 256: the real Ed25519 scalar width, at which the
    // cofactored VERDICT (s·B = R + k·A) is enforced and closes on a real
    // signature.  BENCH_K_SCALAR<256 is a light computation-only mode
    // (verdict gated; the truncated-scalar witness cannot close it).
    let k_scalar: usize = std::env::var("BENCH_K_SCALAR").ok().and_then(|s| s.parse().ok()).unwrap_or(256usize);

    // ── Build a REAL Ed25519 signature so the cofactored verdict
    //    (8·residual₂ ≡ 𝒪 / s·B = R + k·A) actually closes. ──
    //
    //   a       secret scalar,    A = a·B            (public key)
    //   r_n     nonce scalar,     R = r_n·B          (commitment)
    //   k       = SHA-512(R‖A‖M) mod ℓ  (the AIR's own in-circuit reduce)
    //   s       = r_n + k·a   mod ℓ
    //   ⇒ s·B = r_n·B + k·(a·B) = R + k·A           (verification holds)
    //
    // s_bits / k_bits are the FULL canonical 256-bit scalars in the
    // ladder's MSB-first convention (`r_thread_bits_for_kA`).  The
    // verdict only closes at k_scalar = 256 (truncation breaks s·B = R+k·A).
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xED_25519);
    let a = rand_scalar(&mut rng);
    let a_point = ED25519_BASEPOINT_POINT * a;
    let a_pub: [u8; 32] = a_point.compress().to_bytes();
    let r_n = rand_scalar(&mut rng);
    let r_point = ED25519_BASEPOINT_POINT * r_n;
    let r_pub: [u8; 32] = r_point.compress().to_bytes();
    let m: &[u8] = b"STIR ed25519 witness-binding bound bench";

    let sha_input = build_verify_sha512_input(&r_pub, &a_pub, m);
    let digest = sha512_native(&sha_input);
    let k_canonical = reduce_mod_l_wide(&digest);                 // 32-byte LE, < ℓ
    let k_dalek: Scalar = Option::from(Scalar::from_canonical_bytes(k_canonical))
        .expect("k_canonical is reduced mod ℓ");
    let s = r_n + k_dalek * a;                                    // s = r_n + k·a  (mod ℓ)
    let s_canonical: [u8; 32] = s.to_bytes();

    let s_bits = r_thread_bits_for_kA(&s_canonical, k_scalar);
    let k_bits = r_thread_bits_for_kA(&k_canonical, k_scalar);

    let (trace, layout, _k) = fill_verify_air_v16(&sha_input, &r_pub, &a_pub, &s_bits, &k_bits)
        .expect("v16 trace builder accepts the real (R, A) signature");

    let n_trace = layout.height.next_power_of_two();
    let kk = verify_v16_per_row_constraints(layout.k_scalar);
    eprintln!("=== ed25519_verify_bound_bench: WITNESS-BINDING Ed25519 verify-air v16, \
               k_scalar={k_scalar}, width={}, height={}, n_trace={n_trace}, NIST L{level}, \
               Fp{ext_deg}, r={r}, blowup={blowup} ===", layout.width, layout.height);
    eprintln!("    per-row width = {} cells, constraints = {kk}", layout.width);

    // Pad each column to power-of-two height.
    let pad = |trace: Vec<Vec<F>>| -> Vec<Vec<F>> {
        trace.into_iter().map(|mut col| { col.resize(n_trace, F::zero()); col }).collect()
    };
    let honest_trace = pad(trace);

    // ── Cheap verdict diagnostic (no FRI prove): which trace rows have
    //    non-zero constraints (natural nxt = row+1)?  At k_scalar=256 the
    //    result_row (verdict) MUST be zero on a real signature. ──
    if std::env::var("ED_DIAG").is_ok() {
        let mut nz_rows = Vec::new();
        for row in 0..n_trace - 1 {
            let cur: Vec<F> = (0..layout.width).map(|c| honest_trace[c][row]).collect();
            let nxt: Vec<F> = (0..layout.width).map(|c| honest_trace[c][row + 1]).collect();
            let cons = eval_verify_air_v16_per_row(&cur, &nxt, row, &layout);
            let nz = cons.iter().filter(|v| !v.is_zero()).count();
            if nz > 0 { nz_rows.push((row, nz)); }
        }
        let verdict_nz = {
            let row = layout.result_row;
            let cur: Vec<F> = (0..layout.width).map(|c| honest_trace[c][row]).collect();
            let nxt: Vec<F> = (0..layout.width).map(|c| honest_trace[c][row + 1]).collect();
            eval_verify_air_v16_per_row(&cur, &nxt, row, &layout).iter().filter(|v| !v.is_zero()).count()
        };
        eprintln!("[diag] k_scalar={k_scalar} result_row={} dbl_1_row={} n_trace={n_trace}",
            layout.result_row, layout.dbl_1_row);
        eprintln!("[diag] verdict (result_row) non-zero constraints = {verdict_nz}");
        eprintln!("[diag] all non-zero rows (natural nxt): {:?}", nz_rows);
        return;
    }

    let prove = |trace: &[Vec<F>]| {
        prove_one_sub_air_with_trace(
            trace, n_trace, blowup, PI_HASH, b"ed25519_v16_bound", kk,
            // STARK-DNS merge takes an (unused) omega arg; at k_scalar=256 this
            // is identical to the stir-security v16_streaming variant.
            |lde, nt, bw, cc| deep_ali_merge_ed25519_verify(lde, cc, &layout, F::zero(), nt, bw).0,
            |n0, ph| mk_params(n0, r, use_stir, ph),
        )
    };
    let verify = |proof: &deep_ali::sub_air_with_trace::SubAirProofWithTrace| -> bool {
        verify_one_sub_air_with_trace(
            proof, n_trace, blowup, PI_HASH, b"ed25519_v16_bound", layout.width, kk,
            // Gate the verdict identically to the merge: at reduced
            // scalar width the cofactored verdict (result_row) cannot
            // hold on a truncated-scalar witness, so it is excluded.
            |cur, nxt, row| {
                if layout.k_scalar < 256 && row == layout.result_row {
                    vec![F::zero(); kk]
                } else {
                    eval_verify_air_v16_per_row(cur, nxt, row, &layout)
                }
            },
            |n0, ph| mk_params(n0, r, use_stir, ph),
        ).is_ok()
    };

    // ── Honest: must ACCEPT. ──
    let t = Instant::now();
    let proof = prove(&honest_trace);
    let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let fri_kib = proof.fri_proof_bytes.len() as f64 / 1024.0;
    // COMPLETE sound proof = full serialized SubAirProofWithTrace (LDT + openings + paths).
    let full_mib = deep_ali::sub_air_with_trace::serialize_proof(&proof).len() as f64 / 1048576.0;
    let t = Instant::now();
    let honest_ok = verify(&proof);
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    eprintln!("[honest]   prove {prove_ms:.1} ms, verify {verify_ms:.2} ms, fri {fri_kib:.1} KiB, FULL sound proof {full_mib:.1} MiB -> verify={honest_ok}");
    assert!(honest_ok, "BINDING BROKEN: honest Ed25519 signature must verify");

    // ── Tampered: flip the dbl_1 input cell (v16 residual_2 → dbl_input
    //    binding) → must REJECT. ──
    let mut bad = honest_trace.clone();
    let cell = bad[layout.dbl_input_X_base][layout.dbl_1_row];
    bad[layout.dbl_input_X_base][layout.dbl_1_row] = cell + F::one();
    let proof_bad = prove(&bad);
    let tampered_ok = verify(&proof_bad);
    eprintln!("[tampered] flip dbl_1.input[X] @ dbl_1_row -> verify={tampered_ok}");

    println!(
        "ed25519_verify_bound level=L{level} field=Fp{ext_deg} k_scalar={k_scalar} \
         n_trace={n_trace} blowup={blowup} r={r} prove_ms={prove_ms:.1} verify_ms={verify_ms:.2} \
         fri_kib={fri_kib:.1} proof_mib={full_mib:.1} honest_verify={honest_ok} tampered_verify={tampered_ok}");
    if honest_ok && !tampered_ok {
        println!("=> WITNESS-BINDING WORKS: honest accepts, tampered REJECTS (sound in-circuit Ed25519)");
    } else {
        println!("=> FAILED: honest={honest_ok} tampered={tampered_ok}");
    }
}
