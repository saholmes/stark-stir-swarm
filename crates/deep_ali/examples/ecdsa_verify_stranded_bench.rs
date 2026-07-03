//! LOW-MEMORY "stranded" PROVER PoC bench for the END-TO-END P256
//! ECDSA-verify AIR.
//!
//! Proves the SAME ~196k-col verify AIR as TWO column-group strands
//! (chain A = u1·G + r_a_proj seam; chain B + r_b_proj + TAIL + the
//! r_a_proj seam), each LDE'ing only its own columns, then splices them
//! with a single OOD seam on r_a_proj.  Goal: roughly halve the peak
//! prover RSS vs the single-strand bound bench (~5859 MiB @ blowup=4).
//!
//! Soundness gates checked here:
//!   (a) honest spliced proof VERIFIES (accept);
//!   (b) TAMPER-REJECT — flipping a chain-B witness cell rejects (strand
//!       B), and flipping r_a_proj in strand A rejects (seam + strand A
//!       binding).  This guards that the split dropped no constraint;
//!   (c) every strand uses num_queries_for_blowup(blowup);
//!   (d) per-strand column counts are reported (sum ≥ full width; the
//!       shared r_a_proj cols are counted in both).
//!
//! Run:
//!   BENCH_BLOWUP=4 /usr/bin/time -l \
//!     target/release/examples/ecdsa_verify_stranded_bench

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use sha2::{Digest as _, Sha256};

use p256::ecdsa::{signature::Signer, Signature as P256Signature, SigningKey, VerifyingKey};
use p256::elliptic_curve::sec1::ToEncodedPoint;

use deep_ali::{
    ecdsa_verify_stranded::{
        compute_strand_cut, extract_strand_trace, prove_strand_a, prove_strand_b,
        verify_stranded,
    },
    fri::DeepFriParams,
    p256_ecdsa::{
        reduce_digest_mod_n, verify as ecdsa_verify_native, PublicKey as EcdsaPublicKey,
        Signature as EcdsaSignature,
    },
    p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, ecdsa_verify_multirow_constraints,
        fill_ecdsa_verify_multirow, EcdsaVerifyPublicInputs,
    },
    p256_field::FieldElement,
    p256_group::GENERATOR as P256_GENERATOR,
    p256_scalar::ScalarElement,
};

/// Current process RSS in MiB (via `ps`, macOS/Linux).
fn rss_mib() -> f64 {
    let pid = std::process::id();
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output();
    match out {
        Ok(o) => String::from_utf8_lossy(&o.stdout)
            .trim()
            .parse::<f64>()
            .unwrap_or(0.0)
            / 1024.0,
        Err(_) => 0.0,
    }
}

/// Background sampler that tracks peak RSS (MiB) until stopped.
fn spawn_rss_sampler() -> (Arc<AtomicBool>, Arc<AtomicU64>, std::thread::JoinHandle<()>) {
    let stop = Arc::new(AtomicBool::new(false));
    let peak = Arc::new(AtomicU64::new(0));
    let s2 = stop.clone();
    let p2 = peak.clone();
    let h = std::thread::spawn(move || {
        while !s2.load(Ordering::Relaxed) {
            let cur = rss_mib() as u64;
            let mut prev = p2.load(Ordering::Relaxed);
            while cur > prev {
                match p2.compare_exchange(prev, cur, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => break,
                    Err(x) => prev = x,
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
    });
    (stop, peak, h)
}

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
        r,
        seed_z: 0xDEEFu64,
        coeff_commit_final: true,
        d_final: 1,
        stir: use_stir,
        s0: r,
        public_inputs_hash: Some(ph),
    }
}

struct SigCase {
    native_ok: bool,
    u1_bits: Vec<bool>,
    u2_bits: Vec<bool>,
    qx: FieldElement,
    qy: FieldElement,
    r_fe: FieldElement,
    pi_hash: [u8; 32],
    pub_inputs: EcdsaVerifyPublicInputs,
}

fn derive_case(key_bytes: &[u8; 32], msg: &[u8], k: usize) -> SigCase {
    let sk = SigningKey::from_slice(key_bytes).expect("valid P256 key");
    let sig: P256Signature = sk.sign(msg);
    let vk = VerifyingKey::from(&sk);
    let ep = vk.to_encoded_point(false);
    let epb = ep.as_bytes();
    let mut qx = [0u8; 32];
    qx.copy_from_slice(&epb[1..33]);
    let mut qy = [0u8; 32];
    qy.copy_from_slice(&epb[33..65]);
    let sb = sig.to_bytes();
    let mut rbytes = [0u8; 32];
    rbytes.copy_from_slice(&sb[0..32]);
    let mut sbytes = [0u8; 32];
    sbytes.copy_from_slice(&sb[32..64]);
    let digest: [u8; 32] = Sha256::digest(msg).into();

    let pk = EcdsaPublicKey::from_be_bytes(&qx, &qy).expect("pk parse");
    let signature = EcdsaSignature::from_be_bytes(&rbytes, &sbytes).expect("sig parse");
    let native_ok = ecdsa_verify_native(&digest, &pk, &signature);

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

    let mut hasher = Sha256::new();
    hasher.update(rbytes);
    hasher.update(sbytes);
    hasher.update(qx);
    hasher.update(qy);
    hasher.update(digest);
    let pi_hash: [u8; 32] = hasher.finalize().into();

    SigCase {
        native_ok,
        u1_bits,
        u2_bits,
        qx: pk.point.x,
        qy: pk.point.y,
        r_fe,
        pi_hash,
        pub_inputs,
    }
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let blowup = std::env::var("BENCH_BLOWUP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4usize);
    // Gate (c): r tracks the blowup via the slack-Johnson bound.
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup);
    let k = std::env::var("KSTEPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(256usize);
    let n_trace = (k + 1).next_power_of_two();

    eprintln!(
        "=== ecdsa_verify_stranded_bench: 2-STRAND low-mem prover, K={k}, n_trace={n_trace}, \
         NIST L{level}, Fp{ext_deg}, r={r}, blowup={blowup}, ldt={} ===",
        if use_stir { "STIR" } else { "FRI" }
    );

    let case = derive_case(
        &[0x42u8; 32],
        b"STARK-DNS low-mem stranded ECDSA verify: message A",
        k,
    );
    eprintln!("[native] ecdsa_verify(A) = {}", case.native_ok);
    assert!(case.native_ok, "signature must natively verify");

    let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
    let full_constraints = ecdsa_verify_multirow_constraints(&layout);
    eprintln!("    full AIR: per-row width = {total} cells, constraints = {full_constraints}");

    let cut = compute_strand_cut(&layout, k);
    eprintln!(
        "    [cut] strand A cols = {} (chain A + r_a_proj), num_constraints_a = {}",
        cut.width_a(),
        cut.num_constraints_a
    );
    eprintln!(
        "    [cut] strand B cols = {} (chain B + r_a_proj + r_b_proj + TAIL), num_constraints_b = {}",
        cut.width_b(),
        cut.num_constraints_b
    );
    let col_sum = cut.width_a() + cut.width_b();
    eprintln!(
        "    [cut] col sum = {} vs full width = {} (overlap = shared r_a_proj = {} cols)",
        col_sum,
        total,
        col_sum - total
    );
    assert!(
        col_sum >= total,
        "gate (d): strand cols must cover full width"
    );

    // ── Build the FULL trace once, extract both strand traces. ──
    let g = *P256_GENERATOR;
    let z_one = {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    };
    let id_x = FieldElement::zero();
    let id_y = {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    };
    let id_z = FieldElement::zero();

    let build_full = |c: &SigCase| -> Vec<Vec<F>> {
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace,
            &layout,
            n_trace,
            (&id_x, &id_y, &id_z),
            (&g.x, &g.y, &z_one),
            &c.u1_bits,
            (&id_x, &id_y, &id_z),
            (&c.qx, &c.qy, &z_one),
            &c.u2_bits,
            &c.r_fe,
        );
        trace
    };

    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, r, use_stir, ph);

    // ── Isolated single-strand mode (deployment model: each strand is
    //    proved in its OWN process/session, so allocator high-water does
    //    NOT accumulate across strands).  PROVE_STRAND=A|B builds+extracts
    //    +proves that one strand, reports its peak RSS, and exits.  The
    //    MAX of the two isolated peaks is the true low-mem prover
    //    footprint to compare against the monolith baseline. ──
    if let Ok(which) = std::env::var("PROVE_STRAND") {
        let (stop, peak, sampler) = spawn_rss_sampler();
        let t = Instant::now();
        let (cols, wcols) = if which == "A" {
            (&cut.cols_a, cut.width_a())
        } else {
            (&cut.cols_b, cut.width_b())
        };
        let strand = {
            let full = build_full(&case);
            extract_strand_trace(&full, cols)
        };
        if which == "A" {
            let _ = prove_strand_a(
                &strand, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            );
        } else {
            let _ = prove_strand_b(
                &strand, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            );
        }
        let ms = t.elapsed().as_secs_f64() * 1000.0;
        stop.store(true, Ordering::Relaxed);
        let _ = sampler.join();
        let pk = peak.load(Ordering::Relaxed);
        eprintln!(
            "    [rss] ISOLATED strand {which} (cols={wcols}): prove {ms:.1} ms, PEAK = {pk} MiB"
        );
        println!(
            "ISOLATED strand={which} cols={wcols} n_trace={n_trace} r={r} blowup={blowup} \
             prove_ms={ms:.1} peak_mib={pk}"
        );
        return;
    }

    // ── (a) Honest: prove strands SEQUENTIALLY.  For each strand, build
    //        the full trace, extract ONLY that strand's columns, drop the
    //        full trace, then prove — so at the peak we hold just ONE
    //        strand's trace + LDE (never both strands, never the full
    //        trace alongside an LDE). ──
    let (stop, peak, sampler) = spawn_rss_sampler();
    eprintln!("    [rss] start: cur={:.0} MiB", rss_mib());
    let t = Instant::now();

    let (proof_a, seam_a) = {
        let sa = {
            let full = build_full(&case);
            extract_strand_trace(&full, &cut.cols_a)
        };
        let out = prove_strand_a(
            &sa, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
        );
        eprintln!(
            "    [rss] after prove strand A (cols={}): cur={:.0} MiB, peak-so-far={} MiB",
            cut.width_a(),
            rss_mib(),
            peak.load(Ordering::Relaxed)
        );
        out
    };

    let (proof_b, seam_b) = {
        let sb = {
            let full = build_full(&case);
            extract_strand_trace(&full, &cut.cols_b)
        };
        let out = prove_strand_b(
            &sb, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
        );
        eprintln!(
            "    [rss] after prove strand B (cols={}): cur={:.0} MiB, peak-so-far={} MiB",
            cut.width_b(),
            rss_mib(),
            peak.load(Ordering::Relaxed)
        );
        out
    };

    let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    stop.store(true, Ordering::Relaxed);
    let _ = sampler.join();
    eprintln!(
        "    [rss] HONEST-PROVE PEAK (sampler) = {} MiB",
        peak.load(Ordering::Relaxed)
    );

    let proof = deep_ali::ecdsa_verify_stranded::StrandedProof {
        proof_a,
        proof_b,
        seam_a,
        seam_b,
    };
    let fri_a = proof.proof_a.fri_proof_bytes.len();
    let fri_b = proof.proof_b.fri_proof_bytes.len();
    let seam_cols = proof.seam_a.len();

    let t = Instant::now();
    let honest = verify_stranded(
        &proof,
        &cut,
        &layout,
        &case.pub_inputs,
        n_trace,
        blowup,
        case.pi_hash,
        params,
    );
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let honest_ok = honest.is_ok();
    eprintln!(
        "[honest]  prove {prove_ms:.1} ms, verify {verify_ms:.2} ms, \
         fri_A {} KiB, fri_B {} KiB, seam limbs {seam_cols} -> verify={honest_ok} {:?}",
        fri_a / 1024,
        fri_b / 1024,
        honest.as_ref().err()
    );
    assert!(honest_ok, "GATE (a) FAILED: honest spliced proof must ACCEPT");

    // ── (b) TAMPER-REJECT.  Gated by BENCH_TAMPER (default on).  Set
    //        BENCH_TAMPER=0 to measure the CLEAN honest-prove peak RSS
    //        without the tamper re-proves stacking allocations. ──
    let tamper_enabled = std::env::var("BENCH_TAMPER").as_deref() != Ok("0");
    let (mut tamper_b_reject, mut tamper_a_reject) = (true, true);
    if tamper_enabled {
        // #1: flip a chain-B interior witness cell → strand B rejects.
        //     Rebuild the tampered strand trace fresh (avoids cloning
        //     while the honest proof is live).
        let tamper_b_ok = {
            let full = build_full(&case);
            let mut bad_b = extract_strand_trace(&full, &cut.cols_b);
            drop(full);
            bad_b[0][1] += F::from(1u64); // chain-B first acc limb, active row
            let (pb, sb) = prove_strand_b(
                &bad_b, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            );
            drop(bad_b);
            let spliced = deep_ali::ecdsa_verify_stranded::StrandedProof {
                proof_a: proof.proof_a.clone(),
                proof_b: pb,
                seam_a: proof.seam_a.clone(),
                seam_b: sb,
            };
            verify_stranded(
                &spliced, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            )
        };
        tamper_b_reject = tamper_b_ok.is_err();
        eprintln!(
            "[tamper]  flip chain-B cell -> verify_err={:?} (reject={tamper_b_reject})",
            tamper_b_ok.as_ref().err()
        );

        // #2: flip r_a_proj in strand A → breaks constancy + the seam.
        let tamper_a_ok = {
            let full = build_full(&case);
            let mut bad_a = extract_strand_trace(&full, &cut.cols_a);
            drop(full);
            let ra0 = cut.ra_local_in_a[0];
            bad_a[ra0][0] += F::from(1u64);
            let (pa, sa) = prove_strand_a(
                &bad_a, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            );
            drop(bad_a);
            let spliced = deep_ali::ecdsa_verify_stranded::StrandedProof {
                proof_a: pa,
                proof_b: proof.proof_b.clone(),
                seam_a: sa,
                seam_b: proof.seam_b.clone(),
            };
            verify_stranded(
                &spliced, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            )
        };
        tamper_a_reject = tamper_a_ok.is_err();
        eprintln!(
            "[tamper]  flip r_a_proj (strand A) -> verify_err={:?} (reject={tamper_a_reject})",
            tamper_a_ok.as_ref().err()
        );
    } else {
        eprintln!("[tamper]  SKIPPED (BENCH_TAMPER=0) — measuring clean honest-prove peak");
    }

    let pass = case.native_ok && honest_ok && tamper_b_reject && tamper_a_reject;
    println!(
        "ecdsa_verify_stranded K={k} n_trace={n_trace} full_width={total} \
         strand_A cols={} strand_B cols={} col_sum={col_sum} seam_limbs={seam_cols} \
         r={r} blowup={blowup} prove_ms={prove_ms:.1} verify_ms={verify_ms:.2} \
         fri_A_kib={} fri_B_kib={} native={} honest={honest_ok} \
         tamper_chainB_reject={tamper_b_reject} tamper_ra_proj_reject={tamper_a_reject}",
        cut.width_a(),
        cut.width_b(),
        fri_a / 1024,
        fri_b / 1024,
        case.native_ok,
    );
    println!(
        "strand=A cols={} n_trace={n_trace} r={r} blowup={blowup} (peak RSS from /usr/bin/time)",
        cut.width_a()
    );
    println!(
        "strand=B cols={} n_trace={n_trace} r={r} blowup={blowup} (peak RSS from /usr/bin/time)",
        cut.width_b()
    );
    if pass {
        println!(
            "=> STRANDED PROVER WORKS: honest accepts; chain-B + r_a_proj tampers REJECT; \
             2 strands @ ~half width each"
        );
    } else {
        println!(
            "=> FAILED: native={} honest={honest_ok} tamper_chainB_reject={tamper_b_reject} \
             tamper_ra_proj_reject={tamper_a_reject}",
            case.native_ok
        );
        std::process::exit(1);
    }
}
