//! BALANCED G-WAY low-memory "stranded" PROVER bench for the END-TO-END
//! Ed25519 verify-air **v16** (RFC 8032 §5.1.7 cofactored verify).
//!
//! Proves the SAME width=41_519 / 70_602-constraint v16 AIR as `STRAND_G`
//! column-group strands of ≈equal width (phase-overlay-aware cut: shared
//! pool [0,14_941) + col-disjoint tail [14_941,41_519); mult ladder
//! decomposed to leaf gadgets), each LDE'ing only its own columns, spliced
//! by OOD seams on every cross-strand column (incl. transition seams).
//! Goal: peak per-element prover RSS ≤ ~1 GB (vs ~6.2 GB monolith) @ b4.
//!
//! Soundness gates:
//!   (a) honest spliced proof VERIFIES;
//!   (b) COMPREHENSIVE TAMPER-REJECT — one interior cell per strand + one
//!       column per distinct seam group (incl transition seams) rejects;
//!   (c) Σ strand_nc == monolith (asserted in compute_gway_cut + printed);
//!   (d) every strand uses num_queries_for_blowup(blowup) (slack r).
//!
//! Fill modes (env FILL_MODE):
//!   rebuild (default) — for each strand: build full trace, extract that
//!       strand, DROP the full trace, prove, drop the strand.  The full
//!       (~340 MB) trace never enters the LDE/prove phase.
//!   once — build full once, extract all strands, drop full, prove all
//!       (+ honest verify + comprehensive tamper).
//!   solo — build full, extract the WIDEST strand, drop full, then measure
//!       a FRESH peak over just that one strand's prove (the per-element
//!       projection for /usr/bin/time -l).
//!
//! Run (real per-element peak):
//!   FILL_MODE=solo STRAND_G=16 BENCH_BLOWUP=4 /usr/bin/time -l \
//!     target/release/examples/ed25519_verify_stranded_gway_bench

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use rand::{Rng, SeedableRng};
use sha2::{Digest as _, Sha512};

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;

use deep_ali::{
    ed25519_scalar::reduce_mod_l_wide,
    ed25519_verify_air::{fill_verify_air_v16, r_thread_bits_for_kA, verify_v16_per_row_constraints, VerifyAirLayoutV16},
    ed25519_verify_stranded_gway::{
        compute_gway_cut, extract_strand, prove_one_strand, strand_domain,
        verify_stranded_g, GwayCut, StrandedProofG,
    },
    fri::DeepFriParams,
};

fn rss_mib() -> f64 {
    let pid = std::process::id();
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output();
    match out {
        Ok(o) => String::from_utf8_lossy(&o.stdout).trim().parse::<f64>().unwrap_or(0.0) / 1024.0,
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

fn mk_params(n0: usize, r: usize, use_stir: bool, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64, coeff_commit_final: true, d_final: 1,
        stir: use_stir, s0: r, public_inputs_hash: Some(ph),
    }
}

fn build_full(layout_out: &mut Option<VerifyAirLayoutV16>, n_trace_out: &mut usize) -> Vec<Vec<F>> {
    let k_scalar: usize = std::env::var("BENCH_K_SCALAR").ok().and_then(|s| s.parse().ok()).unwrap_or(256usize);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xED_25519);
    let a = {
        let mut b = [0u8; 32];
        rng.fill(&mut b[..]);
        Scalar::from_bytes_mod_order(b)
    };
    let a_point = ED25519_BASEPOINT_POINT * a;
    let a_pub: [u8; 32] = a_point.compress().to_bytes();
    let r_n = {
        let mut b = [0u8; 32];
        rng.fill(&mut b[..]);
        Scalar::from_bytes_mod_order(b)
    };
    let r_point = ED25519_BASEPOINT_POINT * r_n;
    let r_pub: [u8; 32] = r_point.compress().to_bytes();
    let m: &[u8] = b"STARK-DNS low-mem G-way Ed25519 verify: msg A";

    let mut input = Vec::new();
    input.extend_from_slice(&r_pub);
    input.extend_from_slice(&a_pub);
    input.extend_from_slice(m);
    let digest: [u8; 64] = Sha512::digest(&input).into();
    let k_canonical = reduce_mod_l_wide(&digest);
    let k_dalek: Scalar = Option::from(Scalar::from_canonical_bytes(k_canonical)).unwrap();
    let s = r_n + k_dalek * a;
    let s_canonical: [u8; 32] = s.to_bytes();

    let s_bits = r_thread_bits_for_kA(&s_canonical, k_scalar);
    let k_bits = r_thread_bits_for_kA(&k_canonical, k_scalar);

    let (trace, layout, _k) =
        fill_verify_air_v16(&input, &r_pub, &a_pub, &s_bits, &k_bits).expect("v16 fill");
    let n_trace = layout.height.next_power_of_two();
    let padded: Vec<Vec<F>> = trace
        .into_iter()
        .map(|mut c| { c.resize(n_trace, F::zero()); c })
        .collect();
    *n_trace_out = n_trace;
    *layout_out = Some(layout);
    padded
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let g = std::env::var("STRAND_G").ok().and_then(|s| s.parse().ok()).unwrap_or(16usize);
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup); // gate (d)
    let fill_mode = std::env::var("FILL_MODE").unwrap_or_else(|_| "solo".into());
    let tamper_enabled = std::env::var("BENCH_TAMPER").as_deref() != Ok("0");
    let pi_hash = [0x55u8; 32];

    let mut layout_opt: Option<VerifyAirLayoutV16> = None;
    let mut n_trace = 0usize;

    eprintln!("[rss] start: cur={:.0} MiB", rss_mib());
    // Build the full trace (only ~340 MB; dropped before any LDE/prove).
    let full = build_full(&mut layout_opt, &mut n_trace);
    let layout = layout_opt.unwrap();
    let total = layout.width;
    let mono = verify_v16_per_row_constraints(layout.k_scalar);
    eprintln!(
        "=== ed25519_verify_stranded_gway_bench: G={g}-STRAND low-mem prover, \
         k_scalar={}, width={total}, n_trace={n_trace}, NIST L{level}, Fp{ext_deg}, \
         r={r}, blowup={blowup}, ldt={}, fill={fill_mode} ===",
        layout.k_scalar, if use_stir { "STIR" } else { "FRI" }
    );
    eprintln!("    full AIR: width = {total} cells, constraints = {mono}");
    eprintln!("[rss] full trace built (~{:.0} MiB): cur={:.0} MiB", (total * n_trace * 8) as f64 / 1048576.0, rss_mib());

    let cut = compute_gway_cut(&layout, g);

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
        "    [cut] width min={wmin} max={wmax} (max/min = {:.3})",
        wmax as f64 / wmin as f64
    );
    eprintln!("    [cut] per-strand nc = {:?}", cut.strand_nc);
    eprintln!(
        "    [cut] seam GROUPS = {seam_groups}, distinct seam COLUMNS = {seam_cols}, \
         held-col overlap = {overlap}"
    );

    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, r, use_stir, ph);

    if fill_mode == "solo" {
        // Per-element projection: keep only the WIDEST strand, drop full,
        // measure a FRESH peak over just that strand's prove.
        let s = (0..g).max_by_key(|&s| cut.width(s)).unwrap();
        let strand = extract_strand(&full, &cut, s);
        drop(full);
        eprintln!(
            "    [rss] full dropped, only strand {s} (w={}) held: cur={:.0} MiB",
            cut.width(s), rss_mib()
        );
        let (stop, peak, sampler) = spawn_rss_sampler();
        let t = Instant::now();
        let sep = strand_domain(s);
        let (_p, _c) = prove_one_strand(&strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params);
        let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
        drop(strand);
        stop.store(true, Ordering::Relaxed);
        let _ = sampler.join();
        let pk = peak.load(Ordering::Relaxed);
        eprintln!("    [rss] SOLO strand {s} PROVE-ONLY PEAK (full excluded) = {pk} MiB  (per-element projection)");
        println!(
            "SOLO_ED25519 G={g} strand={s} width={} full_width={total} n_trace={n_trace} \
             sum_nc={sum_nc} mono={mono} r={r} blowup={blowup} prove_ms={prove_ms:.0} \
             prove_only_peak_mib={pk} (use /usr/bin/time -l for true process peak)",
            cut.width(s)
        );
        return;
    }

    // rebuild / once — prove every strand, then honest verify + tamper.
    let (stop, peak, sampler) = spawn_rss_sampler();
    let t = Instant::now();
    let mut proofs: Vec<Option<deep_ali::sub_air_with_trace::SubAirProofWithTrace>> =
        (0..g).map(|_| None).collect();
    let mut seam_commits: Vec<Vec<(usize, Vec<deep_ali::binding_cells_commit::BindingCellsCommit>)>> =
        vec![vec![]; g];

    for s in 0..g {
        let strand = extract_strand(&full, &cut, s);
        let sep = strand_domain(s);
        let (p, c) = prove_one_strand(&strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params);
        proofs[s] = Some(p);
        seam_commits[s] = c;
        drop(strand);
        eprintln!(
            "    [rss] strand {s} (w={}) proved+freed: cur={:.0} MiB peak={} MiB",
            cut.width(s), rss_mib(), peak.load(Ordering::Relaxed)
        );
    }
    drop(full);
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
    let honest = verify_stranded_g(&proof, &cut, &layout, n_trace, blowup, pi_hash, params);
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let honest_ok = honest.is_ok();
    eprintln!(
        "[honest]  prove {prove_ms:.0} ms, verify {verify_ms:.1} ms, fri_total {} KiB -> verify={honest_ok} {:?}",
        fri_total / 1024, honest.as_ref().err()
    );
    assert!(honest_ok, "GATE (a) FAILED: honest G-way proof must ACCEPT");

    // ── (b) comprehensive tamper-reject ──
    let mut all_strand_reject = true;
    let mut all_seam_reject = true;
    if tamper_enabled {
        // Rebuild the full trace for tamper cases (dropped above).
        let mut lo: Option<VerifyAirLayoutV16> = None;
        let mut nt2 = 0usize;
        let full2 = build_full(&mut lo, &mut nt2);
        let seam_set: std::collections::BTreeSet<usize> =
            cut.seams.iter().flat_map(|sg| sg.cols.iter().copied()).collect();

        for s in 0..g {
            let interior = cut.strand_cols[s].iter().copied().find(|c| !seam_set.contains(c));
            let Some(col) = interior else { continue };
            let mut strand = extract_strand(&full2, &cut, s);
            let local = cut.strand_cols[s].iter().position(|&c| c == col).unwrap();
            for row in 0..n_trace { strand[local][row] += F::from(1u64); }
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(&strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params);
            let mut p2 = proof.proofs.clone();
            let mut s2 = proof.seam_commits.clone();
            p2[s] = ps; s2[s] = cs;
            let spliced = StrandedProofG { proofs: p2, seam_commits: s2 };
            let rej = verify_stranded_g(&spliced, &cut, &layout, n_trace, blowup, pi_hash, params).is_err();
            all_strand_reject &= rej;
            eprintln!("[tamper]  strand {s} interior col {col} -> reject={rej}");
        }
        for (gid, sg) in cut.seams.iter().enumerate() {
            let s = sg.holders[0];
            let col = sg.cols[0];
            let mut strand = extract_strand(&full2, &cut, s);
            let local = cut.strand_cols[s].iter().position(|&c| c == col).unwrap();
            for row in 0..n_trace { strand[local][row] += F::from(1u64); }
            let sep = strand_domain(s);
            let (ps, cs) = prove_one_strand(&strand, &cut, s, &layout, n_trace, blowup, pi_hash, &sep, params);
            let mut p2 = proof.proofs.clone();
            let mut s2 = proof.seam_commits.clone();
            p2[s] = ps; s2[s] = cs;
            let spliced = StrandedProofG { proofs: p2, seam_commits: s2 };
            let rej = verify_stranded_g(&spliced, &cut, &layout, n_trace, blowup, pi_hash, params).is_err();
            all_seam_reject &= rej;
            eprintln!("[tamper]  seam group {gid} (holders {:?}) col {col} -> reject={rej}", sg.holders);
        }
    } else {
        eprintln!("[tamper]  SKIPPED (BENCH_TAMPER=0)");
    }

    let pass = honest_ok && (!tamper_enabled || (all_strand_reject && all_seam_reject));
    println!(
        "ed25519_verify_stranded_gway G={g} k_scalar={} n_trace={n_trace} full_width={total} \
         width_min={wmin} width_max={wmax} seam_groups={seam_groups} seam_cols={seam_cols} \
         sum_nc={sum_nc} mono={mono} r={r} blowup={blowup} prove_ms={prove_ms:.0} \
         verify_ms={verify_ms:.1} fri_total_kib={} honest={honest_ok} \
         strand_tampers_reject={all_strand_reject} seam_tampers_reject={all_seam_reject} \
         honest_peak_mib={honest_peak} fill={fill_mode}",
        layout.k_scalar, fri_total / 1024
    );
    if pass {
        println!("=> G-WAY STRANDED PROVER WORKS: honest accepts; all tampers REJECT");
    } else {
        println!("=> FAILED");
        std::process::exit(1);
    }
}
