//! WITNESS-BINDING compact RSA-2048 exp-chain STARK (the soundness fix).
//!
//! Unlike `rsa2048_exp_bench` (which uses the non-binding
//! `merge -> deep_fri_prove(c_eval)` path and lets a tampered `em` verify),
//! this routes the SAME compact exp AIR through
//! `sub_air_with_trace::{prove,verify}_one_sub_air_with_trace`, which:
//!   - Merkle-commits the trace LDE (trace_root folded into the FS pi_hash),
//!   - opens trace cells (cur+nxt) at every FRI query position,
//!   - re-checks  c_eval(x)·Z_H(x) = Σ α_j Φ_j(trace[x])  at each opening.
//! A tampered witness makes the discarded poly_div_zh remainder non-zero, so
//! that equality fails at random query points -> verify REJECTS.
//!
//! DECISIVE TEST: honest record ACCEPTS, tampered em (s^65537+1) REJECTS.
//!
//! Run (per level): cargo run --release -p deep_ali --example rsa2048_exp_bound_bench \
//!   --no-default-features --features sha3-256,mldsa-44,parallel

use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

use deep_ali::{
    deep_ali_merge_per_row_no_layout,
    fri::DeepFriParams,
    rsa2048_exp_air::{
        build_rsa_exp_multirow_layout, eval_rsa_exp_multirow_per_row,
        fill_rsa_exp_multirow, rsa_exp_multirow_constraints, RsaExpMultirowLayout,
    },
    rsa2048_field_air::{biguint_to_limbs80, RSA_NUM_LIMBS},
    sub_air_with_trace::{prove_one_sub_air_with_trace, verify_one_sub_air_with_trace},
};

/// Public-input PIN targets: the 80-limb encodings of the modulus, signature,
/// and encoded message, pinned to the trace's `n_base`/`s_base`/`em_base`
/// input columns so the proof binds the committed trace to the PUBLIC
/// `(n, s, em)` — not an arbitrary `(s', n', em')` with `s'^e ≡ em' (mod n')`
/// that the prover chose.  Without these, the AIR proves only an internally
/// consistent exponentiation; the pins bind it to the verifier's public key
/// and signature.
fn rsa_public_pin_targets(n: &BigUint, s: &BigUint, em: &BigUint) -> (Vec<F>, Vec<F>, Vec<F>) {
    let f = |limbs: [i64; RSA_NUM_LIMBS]| limbs.iter().map(|&v| F::from(v as u64)).collect::<Vec<F>>();
    (f(biguint_to_limbs80(n)), f(biguint_to_limbs80(s)), f(biguint_to_limbs80(em)))
}

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

fn mk_params(n0: usize, r: usize, use_stir: bool, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64, coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r, public_inputs_hash: Some(ph),
    }
}

const PI_HASH: [u8; 32] = [0x11; 32]; // domain constant; trace_root binds the witness

/// Prove the compact exp AIR for (n,s,em) via the witness-binding path,
/// then verify. Returns (prove_ms, verify_ms, fri_kib, full_mib, opening_cells, verify_ok).
fn prove_then_verify(
    layout: &RsaExpMultirowLayout, width: usize, n: &BigUint, s: &BigUint, em: &BigUint,
    n_trace: usize, blowup: usize, r: usize, use_stir: bool,
) -> (f64, f64, f64, f64, usize, bool) {
    let kk_base = rsa_exp_multirow_constraints(layout);
    let kk = kk_base + 3 * RSA_NUM_LIMBS; // + public-input pins (n, s, em)
    let (want_n, want_s, want_em) = rsa_public_pin_targets(n, s, em);
    // Per-row eval = RSA exp constraints ++ pins binding the n/s/em input
    // columns to the PUBLIC values.  Shared verbatim by prover and verifier.
    let eval = |cur: &[F], nxt: &[F], row: usize| -> Vec<F> {
        let mut c = eval_rsa_exp_multirow_per_row(cur, nxt, row, n_trace, layout);
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.n_base + i]  - want_n[i]); }
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.s_base + i]  - want_s[i]); }
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.em_base + i] - want_em[i]); }
        c
    };
    let mut trace: Vec<Vec<F>> = (0..width).map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_exp_multirow(&mut trace, layout, n_trace, n, s, em);

    let t0 = Instant::now();
    let proof = prove_one_sub_air_with_trace(
        &trace, n_trace, blowup, PI_HASH, b"rsa_exp_bound", kk,
        |lde, nt, bw, cc| deep_ali_merge_per_row_no_layout(
            lde, cc, F::zero(), nt, bw, width, kk, &eval).0,
        |n0, ph| mk_params(n0, r, use_stir, ph),
    );
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let t0 = Instant::now();
    let res = verify_one_sub_air_with_trace(
        &proof, n_trace, blowup, PI_HASH, b"rsa_exp_bound", width, kk,
        &eval,
        |n0, ph| mk_params(n0, r, use_stir, ph),
    );
    let verify_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let fri_kib = proof.fri_proof_bytes.len() as f64 / 1024.0;
    // COMPLETE sound proof = full serialized SubAirProofWithTrace (LDT + openings + paths).
    let full_mib =
        deep_ali::sub_air_with_trace::serialize_proof(&proof).len() as f64 / 1048576.0;
    let opening_cells: usize = proof.openings_cur.iter().map(|o| o.cells.len()).sum::<usize>()
        + proof.openings_nxt.iter().map(|o| o.cells.len()).sum::<usize>();
    (prove_ms, verify_ms, fri_kib, full_mib, opening_cells, res.is_ok())
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let blowup = 32usize;
    // sound query count for THIS blowup (= 55/81/108 at b=32, the slack floor).
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup);
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let n_trace = 32usize;
    eprintln!("=== rsa2048_exp_bound_bench: WITNESS-BINDING compact RSA exp AIR, \
               NIST L{level}, Fp{ext_deg}, r={r}, ldt={} ===",
              if use_stir { "stir" } else { "fri" });

    let (layout, width) = build_rsa_exp_multirow_layout(0);

    let mut rng = rand::rngs::StdRng::seed_from_u64(0xDEAD);
    let n = (gen_biguint(&mut rng, 2046) << 1) | BigUint::from(1u8);
    let s = gen_biguint_below(&mut rng, &n);
    let em = s.modpow(&BigUint::from(65_537u32), &n);
    let bogus_em = (&em + BigUint::from(1u8)) % &n;

    // ── Honest: must ACCEPT ──
    let (p_ms, v_ms, fri_kib, full_mib, op_cells, ok) =
        prove_then_verify(&layout, width, &n, &s, &em, n_trace, blowup, r, use_stir);
    eprintln!("[honest]   prove {p_ms:.1} ms, verify {v_ms:.2} ms, fri {fri_kib:.1} KiB, \
               FULL sound proof {full_mib:.2} MiB ({op_cells} opening cells) -> verify={ok}");
    assert!(ok, "BINDING BROKEN: honest record must verify");

    // ── Tampered: must REJECT (this is the whole point) ──
    let (_, _, _, _, _, bad_ok) =
        prove_then_verify(&layout, width, &n, &s, &bogus_em, n_trace, blowup, r, use_stir);
    eprintln!("[tampered] em=s^65537+1 -> verify={bad_ok}");

    // ── Cross-signature: A's proof must NOT verify under B's public inputs ──
    //    (the public-input pins close signature substitution).
    let s2 = gen_biguint_below(&mut rng, &n);
    let em2 = s2.modpow(&BigUint::from(65_537u32), &n);
    let kk = rsa_exp_multirow_constraints(&layout) + 3 * RSA_NUM_LIMBS;
    let (an, as_, aem) = rsa_public_pin_targets(&n, &s, &em);
    let (bn, bs, bem) = rsa_public_pin_targets(&n, &s2, &em2);
    let eval_a = |cur: &[F], nxt: &[F], row: usize| -> Vec<F> {
        let mut c = eval_rsa_exp_multirow_per_row(cur, nxt, row, n_trace, &layout);
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.n_base + i]  - an[i]); }
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.s_base + i]  - as_[i]); }
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.em_base + i] - aem[i]); }
        c
    };
    let eval_b = |cur: &[F], nxt: &[F], row: usize| -> Vec<F> {
        let mut c = eval_rsa_exp_multirow_per_row(cur, nxt, row, n_trace, &layout);
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.n_base + i]  - bn[i]); }
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.s_base + i]  - bs[i]); }
        for i in 0..RSA_NUM_LIMBS { c.push(cur[layout.em_base + i] - bem[i]); }
        c
    };
    let mut trace_a: Vec<Vec<F>> = (0..width).map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_exp_multirow(&mut trace_a, &layout, n_trace, &n, &s, &em);
    let proof_a = prove_one_sub_air_with_trace(
        &trace_a, n_trace, blowup, PI_HASH, b"rsa_exp_bound", kk,
        |lde, nt, bw, cc| deep_ali_merge_per_row_no_layout(lde, cc, F::zero(), nt, bw, width, kk, &eval_a).0,
        |n0, ph| mk_params(n0, r, use_stir, ph),
    );
    let cross = verify_one_sub_air_with_trace(
        &proof_a, n_trace, blowup, PI_HASH, b"rsa_exp_bound", width, kk,
        &eval_b, |n0, ph| mk_params(n0, r, use_stir, ph),
    ).is_ok();
    eprintln!("[cross]    A's proof under B's public (s,em) -> verify={cross}");
    assert!(!cross, "PIN BROKEN: A's proof verified under a different public signature");

    println!("rsa2048_exp_bound level=L{level} field=Fp{ext_deg} n_trace={n_trace} blowup={blowup} \
              r={r} prove_ms={p_ms:.1} verify_ms={v_ms:.2} fri_kib={fri_kib:.1} proof_mib={full_mib:.2} \
              honest_verify={ok} tampered_verify={bad_ok}");
    if !bad_ok {
        println!("=> WITNESS-BINDING WORKS: honest accepts, tampered REJECTS (sound in-circuit RSA)");
    } else {
        println!("=> STILL NON-BINDING: tampered proof verified — binding insufficient");
    }
}
