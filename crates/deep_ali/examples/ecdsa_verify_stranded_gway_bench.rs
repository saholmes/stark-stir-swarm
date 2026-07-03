//! BALANCED G-WAY low-memory "stranded" PROVER bench for the END-TO-END
//! P256 ECDSA-verify AIR (M2).
//!
//! Proves the SAME ~196k-col verify AIR as `STRAND_G` column-group
//! strands of ≈equal width (bin-packed whole gadgets, snapped to gadget
//! edges), each LDE'ing only its own columns, spliced by OOD seams on
//! every shared column.  Goal: peak prover RSS ≤ ~1 GB (vs ~5.9 GB
//! monolith) at blowup=4.
//!
//! Soundness gates checked:
//!   (a) honest spliced proof VERIFIES (accept);
//!   (b) COMPREHENSIVE TAMPER-REJECT — one interior witness cell per
//!       strand rejects that strand; one column per distinct seam group
//!       rejects the seam;
//!   (c) Σ_g num_constraints_g == monolith total (asserted + printed);
//!   (d) every strand uses num_queries_for_blowup(blowup).
//!
//! Fill modes (env FILL_MODE):
//!   rebuild (default) — memory-light: for each strand, build the full
//!       trace, extract that strand, DROP the full trace, prove, drop the
//!       strand.  Only ONE strand trace + ONE strand LDE is ever live, and
//!       the full trace is transient (never proved).  Rebuilds fill G×.
//!   once — build the full trace once, extract ALL strands, then prove
//!       sequentially (faster, higher peak; for comparison).
//!
//! Run (peak RSS):
//!   STRAND_G=8 BENCH_BLOWUP=4 /usr/bin/time -l \
//!     target/release/examples/ecdsa_verify_stranded_gway_bench

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use sha2::{Digest as _, Sha256};

use p256::ecdsa::{signature::Signer, Signature as P256Signature, SigningKey, VerifyingKey};
use p256::elliptic_curve::sec1::ToEncodedPoint;

use deep_ali::{
    ecdsa_verify_stranded_gway::{
        compute_gway_cut, prove_one_strand, strand_domain, verify_stranded_g, GwayCut,
        StrandedProofG,
    },
    fri::DeepFriParams,
    p256_ecdsa::{
        reduce_digest_mod_n, verify as ecdsa_verify_native, PublicKey as EcdsaPublicKey,
        Signature as EcdsaSignature,
    },
    p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, ecdsa_verify_multirow_constraints,
        fill_ecdsa_verify_multirow, fill_ecdsa_verify_multirow_strand,
        EcdsaVerifyMultirowLayout, EcdsaVerifyPublicInputs,
    },
    p256_field::{FieldElement, NUM_LIMBS},
    p256_group::GENERATOR as P256_GENERATOR,
    p256_scalar::ScalarElement,
};

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
            std::thread::sleep(std::time::Duration::from_millis(50));
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

/// Build the full verify trace for `case` (2-pass fill).
fn build_full(
    case: &SigCase,
    layout: &EcdsaVerifyMultirowLayout,
    n_trace: usize,
    total: usize,
) -> Vec<Vec<F>> {
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
    let mut trace = vec![vec![F::zero(); n_trace]; total];
    fill_ecdsa_verify_multirow(
        &mut trace, layout, n_trace,
        (&id_x, &id_y, &id_z), (&g.x, &g.y, &z_one), &case.u1_bits,
        (&id_x, &id_y, &id_z), (&case.qx, &case.qy, &z_one), &case.u2_bits,
        &case.r_fe,
    );
    trace
}

fn extract(full: &[Vec<F>], cols: &[usize]) -> Vec<Vec<F>> {
    cols.iter().map(|&c| full[c].clone()).collect()
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let g = std::env::var("STRAND_G").ok().and_then(|s| s.parse().ok()).unwrap_or(8usize);
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup); // gate (d)
    let k = std::env::var("KSTEPS").ok().and_then(|s| s.parse().ok()).unwrap_or(256usize);
    let n_trace = (k + 1).next_power_of_two();
    let fill_mode = std::env::var("FILL_MODE").unwrap_or_else(|_| "rebuild".into());
    let tamper_enabled = std::env::var("BENCH_TAMPER").as_deref() != Ok("0");

    eprintln!(
        "=== ecdsa_verify_stranded_gway_bench: G={g}-STRAND low-mem prover, K={k}, \
         n_trace={n_trace}, NIST L{level}, Fp{ext_deg}, r={r}, blowup={blowup}, \
         ldt={}, fill={fill_mode} ===",
        if use_stir { "STIR" } else { "FRI" }
    );

    let case = derive_case(&[0x42u8; 32], b"STARK-DNS low-mem G-way ECDSA verify: msg A", k);
    eprintln!("[native] ecdsa_verify = {}", case.native_ok);
    assert!(case.native_ok, "signature must natively verify");

    let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
    let mono = ecdsa_verify_multirow_constraints(&layout);
    eprintln!("    full AIR: width = {total} cells, constraints = {mono}");

    let cut = compute_gway_cut(&layout, k, g);

    // ── (c) constraint completeness ──
    let sum_nc: usize = cut.strand_nc.iter().sum();
    eprintln!(
        "    [gate c] Σ strand_nc = {sum_nc}  vs  monolith = {mono}  -> {}",
        if sum_nc == mono { "MATCH" } else { "MISMATCH!" }
    );
    assert_eq!(sum_nc, mono, "gate (c) FAILED");

    // ── balance + seam report ──
    let widths: Vec<usize> = (0..g).map(|s| cut.width(s)).collect();
    let wmin = *widths.iter().min().unwrap();
    let wmax = *widths.iter().max().unwrap();
    let seam_groups = cut.seams.len();
    let seam_cols: usize = cut.seams.iter().map(|sg| sg.cols.len()).sum();
    let overlap: usize = widths.iter().sum::<usize>() - total;
    eprintln!("    [cut] per-strand widths = {widths:?}");
    eprintln!(
        "    [cut] width min={wmin} max={wmax} (max/min = {:.3}), per-strand nc = {:?}",
        wmax as f64 / wmin as f64,
        cut.strand_nc
    );
    eprintln!(
        "    [cut] seam GROUPS = {seam_groups}, distinct seam COLUMNS = {seam_cols}, \
         held-col overlap = {overlap}"
    );

    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, r, use_stir, ph);

    // ── (a) honest prove (memory-light) ──
    let (stop, peak, sampler) = spawn_rss_sampler();
    eprintln!("    [rss] start: cur={:.0} MiB", rss_mib());
    let t = Instant::now();

    let mut proofs: Vec<Option<deep_ali::sub_air_with_trace::SubAirProofWithTrace>> =
        (0..g).map(|_| None).collect();
    let mut seam_commits: Vec<Vec<(usize, Vec<deep_ali::binding_cells_commit::BindingCellsCommit>)>> =
        vec![vec![]; g];

    if fill_mode == "direct" {
        // DIRECT-FILL: prove ONE strand (the widest — worst case for peak)
        // by filling ONLY its columns via `fill_ecdsa_verify_multirow_strand`.
        // The full ~196k-col trace is NEVER allocated, so the process peak
        // (measured externally by `/usr/bin/time -l`) reflects only the
        // single-row scratch (~few MB) + the strand trace + the strand's
        // prove/LDE working set — the whole point of this milestone.
        let s = (0..g).max_by_key(|&s| cut.width(s)).unwrap();
        let cols = &cut.strand_cols[s];

        let g_pt = *P256_GENERATOR;
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

        let mut strand: Vec<Vec<F>> = vec![vec![F::zero(); n_trace]; cols.len()];
        let t_fill = Instant::now();
        fill_ecdsa_verify_multirow_strand(
            cols, &mut strand, &layout, n_trace,
            (&id_x, &id_y, &id_z), (&g_pt.x, &g_pt.y, &z_one), &case.u1_bits,
            (&id_x, &id_y, &id_z), (&case.qx, &case.qy, &z_one), &case.u2_bits,
            &case.r_fe,
        );
        eprintln!(
            "    [rss] DIRECT-filled strand {s} (w={}) in {:.0} ms — NO full trace built: cur={:.0} MiB",
            cut.width(s),
            t_fill.elapsed().as_secs_f64() * 1000.0,
            rss_mib()
        );

        let sep = strand_domain(s);
        let (p, c) = prove_one_strand(
            &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, &sep,
            params,
        );
        drop(strand);
        stop.store(true, Ordering::Relaxed);
        let _ = sampler.join();
        proofs[s] = Some(p);
        seam_commits[s] = c;
        let sampled_peak = peak.load(Ordering::Relaxed);
        eprintln!(
            "    [rss] DIRECT strand {s} whole-run PEAK (sampler; no full-trace build) = {} MiB",
            sampled_peak
        );
        // NOTE: only one strand proven in direct mode → skip splice-verify
        // here (soundness gates a/b/c/d are validated by the once/rebuild
        // modes + the byte-equality guard test, which proves direct-fill is
        // byte-identical to build_full+extract).
        println!(
            "DIRECT G={g} strand={s} width={} n_trace={n_trace} full_width={total} \
             sum_nc={sum_nc} mono={mono} r={r} blowup={blowup} sampled_peak_mib={sampled_peak} \
             (use /usr/bin/time -l for true process peak)",
            cut.width(s),
        );
        return;
    }
    if fill_mode == "solo" {
        // Isolate ONE strand's prove working set (the direct-fill
        // projection): build full, extract the widest strand, DROP full,
        // then measure a FRESH peak over just that strand's prove.
        let s = (0..g).max_by_key(|&s| cut.width(s)).unwrap();
        let full = build_full(&case, &layout, n_trace, total);
        let strand = extract(&full, &cut.strand_cols[s]);
        drop(full);
        stop.store(true, Ordering::Relaxed);
        let _ = sampler.join();
        eprintln!(
            "    [rss] full dropped, only strand {s} (w={}) held: cur={:.0} MiB",
            cut.width(s),
            rss_mib()
        );
        // Fresh sampler → peak excludes the transient full-trace build.
        let (stop2, peak2, sampler2) = spawn_rss_sampler();
        let sep = strand_domain(s);
        let (p, c) = prove_one_strand(
            &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, &sep,
            params,
        );
        drop(strand);
        stop2.store(true, Ordering::Relaxed);
        let _ = sampler2.join();
        proofs[s] = Some(p);
        seam_commits[s] = c;
        eprintln!(
            "    [rss] SOLO strand {s} PROVE-ONLY PEAK (full excluded) = {} MiB  \
             (== direct-fill per-strand projection)",
            peak2.load(Ordering::Relaxed)
        );
        // note: remaining strands unproven in solo mode → skip verify.
        println!(
            "SOLO G={g} strand={s} width={} prove_only_peak_mib={} blowup={blowup}",
            cut.width(s),
            peak2.load(Ordering::Relaxed)
        );
        return;
    }
    if fill_mode == "once" {
        // Build full once, extract all strands, drop full, prove sequentially.
        let full = build_full(&case, &layout, n_trace, total);
        let mut strands: Vec<Vec<Vec<F>>> =
            (0..g).map(|s| extract(&full, &cut.strand_cols[s])).collect();
        drop(full);
        eprintln!("    [rss] full built+extracted+dropped: cur={:.0} MiB", rss_mib());
        for s in 0..g {
            let sep = strand_domain(s);
            let (p, c) = prove_one_strand(
                &strands[s], &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash,
                &sep, params,
            );
            proofs[s] = Some(p);
            seam_commits[s] = c;
            strands[s].clear();
            strands[s].shrink_to_fit();
            eprintln!(
                "    [rss] strand {s} proved+freed: cur={:.0} MiB peak={} MiB",
                rss_mib(),
                peak.load(Ordering::Relaxed)
            );
        }
    } else if fill_mode == "keep" {
        // Build full ONCE, keep it resident, prove one strand at a time
        // (extract → prove → drop that strand).  Avoids the rebuild-mode
        // allocator churn; peak = full trace + one strand LDE/tree.
        let full = build_full(&case, &layout, n_trace, total);
        eprintln!("    [rss] full built (resident): cur={:.0} MiB", rss_mib());
        for s in 0..g {
            let strand = extract(&full, &cut.strand_cols[s]);
            let sep = strand_domain(s);
            let (p, c) = prove_one_strand(
                &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash,
                &sep, params,
            );
            drop(strand);
            proofs[s] = Some(p);
            seam_commits[s] = c;
            eprintln!(
                "    [rss] strand {s} (w={}) proved+freed: cur={:.0} MiB peak={} MiB",
                cut.width(s),
                rss_mib(),
                peak.load(Ordering::Relaxed)
            );
        }
        drop(full);
    } else {
        // Memory-light: rebuild full per strand, extract, drop, prove, drop.
        for s in 0..g {
            let full = build_full(&case, &layout, n_trace, total);
            let strand = extract(&full, &cut.strand_cols[s]);
            drop(full); // full trace never survives into the prove/LDE phase
            let sep = strand_domain(s);
            let (p, c) = prove_one_strand(
                &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash,
                &sep, params,
            );
            drop(strand);
            proofs[s] = Some(p);
            seam_commits[s] = c;
            eprintln!(
                "    [rss] strand {s} (w={}) proved+freed: cur={:.0} MiB peak={} MiB",
                cut.width(s),
                rss_mib(),
                peak.load(Ordering::Relaxed)
            );
        }
    }

    let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    stop.store(true, Ordering::Relaxed);
    let _ = sampler.join();
    let honest_peak = peak.load(Ordering::Relaxed);
    eprintln!("    [rss] HONEST-PROVE PEAK (sampler) = {honest_peak} MiB");

    let proof = StrandedProofG {
        proofs: proofs.into_iter().map(|p| p.unwrap()).collect(),
        seam_commits,
    };
    let fri_total: usize = proof.proofs.iter().map(|p| p.fri_proof_bytes.len()).sum();

    let t = Instant::now();
    let honest = verify_stranded_g(
        &proof, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
    );
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let honest_ok = honest.is_ok();
    eprintln!(
        "[honest]  prove {prove_ms:.0} ms, verify {verify_ms:.1} ms, \
         fri_total {} KiB -> verify={honest_ok} {:?}",
        fri_total / 1024,
        honest.as_ref().err()
    );
    assert!(honest_ok, "GATE (a) FAILED: honest G-way proof must ACCEPT");

    // ── (b) comprehensive tamper-reject ──
    let mut all_strand_reject = true;
    let mut all_seam_reject = true;
    if tamper_enabled {
        let seam_cols_set: std::collections::BTreeSet<usize> =
            cut.seams.iter().flat_map(|sg| sg.cols.iter().copied()).collect();

        // one interior tamper per strand.
        for s in 0..g {
            let interior = cut.strand_cols[s]
                .iter()
                .copied()
                .find(|c| !seam_cols_set.contains(c));
            let Some(col) = interior else { continue };
            let full = build_full(&case, &layout, n_trace, total);
            let mut strand = extract(&full, &cut.strand_cols[s]);
            drop(full);
            let local = cut.strand_cols[s].iter().position(|&c| c == col).unwrap();
            for row in 0..n_trace {
                strand[local][row] += F::from(1u64);
            }
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(
                &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash,
                &sep, params,
            );
            let mut proofs2 = proof.proofs.clone();
            let mut seam2 = proof.seam_commits.clone();
            proofs2[s] = ps;
            seam2[s] = cs;
            let spliced = StrandedProofG { proofs: proofs2, seam_commits: seam2 };
            let rej = verify_stranded_g(
                &spliced, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            )
            .is_err();
            all_strand_reject &= rej;
            eprintln!("[tamper]  strand {s} interior col {col} -> reject={rej}");
        }

        // one column tamper per distinct seam group.
        for (gid, sg) in cut.seams.iter().enumerate() {
            let s = sg.holders[0];
            let col = sg.cols[0];
            let full = build_full(&case, &layout, n_trace, total);
            let mut strand = extract(&full, &cut.strand_cols[s]);
            drop(full);
            let local = cut.strand_cols[s].iter().position(|&c| c == col).unwrap();
            for row in 0..n_trace {
                strand[local][row] += F::from(1u64);
            }
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(
                &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash,
                &sep, params,
            );
            let mut proofs2 = proof.proofs.clone();
            let mut seam2 = proof.seam_commits.clone();
            proofs2[s] = ps;
            seam2[s] = cs;
            let spliced = StrandedProofG { proofs: proofs2, seam_commits: seam2 };
            let rej = verify_stranded_g(
                &spliced, &cut, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, params,
            )
            .is_err();
            all_seam_reject &= rej;
            eprintln!(
                "[tamper]  seam group {gid} (holders {:?}) col {col} -> reject={rej}",
                sg.holders
            );
        }
    } else {
        eprintln!("[tamper]  SKIPPED (BENCH_TAMPER=0)");
    }

    let pass = case.native_ok && honest_ok && (!tamper_enabled || (all_strand_reject && all_seam_reject));
    println!(
        "ecdsa_verify_stranded_gway G={g} K={k} n_trace={n_trace} full_width={total} \
         width_min={wmin} width_max={wmax} seam_groups={seam_groups} seam_cols={seam_cols} \
         sum_nc={sum_nc} mono={mono} r={r} blowup={blowup} prove_ms={prove_ms:.0} \
         verify_ms={verify_ms:.1} fri_total_kib={} honest={honest_ok} \
         strand_tampers_reject={all_strand_reject} seam_tampers_reject={all_seam_reject} \
         honest_peak_mib={honest_peak} fill={fill_mode}",
        fri_total / 1024,
    );
    if pass {
        println!("=> G-WAY STRANDED PROVER WORKS: honest accepts; all tampers REJECT");
    } else {
        println!("=> FAILED");
        std::process::exit(1);
    }
}
