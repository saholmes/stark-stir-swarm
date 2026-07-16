//! seam_batch_bridge.rs — deep_ali-native aggregation of seam OOD checks.
//!
//! The measured reconstruction bottleneck (deep_ali/examples/gway_reconstruction:
//! ~36.5 s) is the ~2622 *per-column* seam OOD checks, each a full FRI verify of
//! a single-column `BindingCellsCommit`.  This bridge batches a seam GROUP's K
//! columns into ONE packed `BindingCellsCommit` (a path `commit_binding_cells`
//! already supports), so the coordinator runs ONE OOD verify per group instead
//! of one per column — cutting the dominant FRI-verify count by the per-group
//! column factor.
//!
//! Soundness (unchanged): the packing is deterministic; both strands' packed
//! commits share the SAME `pi_hash`-derived OOD point z0 (FS from the FRI
//! params, which carry `public_inputs_hash = pi_hash`); and
//! `f_a_packed(z0) = f_b_packed(z0)` implies the packed polynomials agree, hence
//! every column agrees, by Schwartz–Zippel (ε ≤ n/|F_ext|, F_ext = Fp⁶ ⇒ ~2⁻³⁷⁰).
//! A single differing column changes the packed value at z0 ⇒ reject.  The whole
//! check is bound to `pi_hash`: verifying under a different pi_hash re-derives
//! different FS challenges and the FRI verify rejects.
//!
//! Run:
//!   COLS=8 cargo run --release --features "parallel,sha3-256" -p deep_ali \
//!     --example seam_batch_bridge

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use std::time::Instant;

use deep_ali::binding_cells_commit::{commit_binding_cells, verify_ood_consistency};
use deep_ali::fri::DeepFriParams;

fn rss_mib() -> f64 {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output();
    match out {
        Ok(o) => String::from_utf8_lossy(&o.stdout).trim().parse::<f64>().unwrap_or(0.0) / 1024.0,
        Err(_) => 0.0,
    }
}

/// One low-degree LDE column: trace values from `pat`, ifft→coeffs→fft on the
/// blown-up domain (so it passes the FRI low-degree test).
fn make_col(pat: impl Fn(usize) -> u64, n_trace: usize, blowup: usize) -> Vec<F> {
    let lde_size = n_trace * blowup;
    let trace_dom = GeneralEvaluationDomain::<F>::new(n_trace).unwrap();
    let lde_dom = GeneralEvaluationDomain::<F>::new(lde_size).unwrap();
    let coeffs: Vec<F> = (0..n_trace).map(|r| F::from(pat(r))).collect();
    let mut poly = trace_dom.ifft(&coeffs);
    poly.resize(lde_size, F::zero());
    lde_dom.fft(&poly)
}

/// A strand's seam columns: K low-degree LDE columns.
fn seam_columns(k: usize, n_trace: usize, blowup: usize, salt: u64) -> Vec<Vec<F>> {
    (0..k).map(|c| make_col(move |r| (c as u64 * 257 + r as u64 * 31 + salt * 7919) % 1_000_003, n_trace, blowup)).collect()
}

fn params(n0: usize, pi_hash: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: vec![2usize; n0.trailing_zeros() as usize],
        r: 16,
        seed_z: 0xDEEF_BAAD,
        coeff_commit_final: true,
        d_final: 1,
        stir: false,
        s0: 16,
        public_inputs_hash: Some(pi_hash),
    }
}

fn main() {
    let n_trace: usize = std::env::var("NTRACE").ok().and_then(|s| s.parse().ok()).unwrap_or(512);
    let k: usize = std::env::var("COLS").ok().and_then(|s| s.parse().ok()).unwrap_or(8);
    assert!(k.is_power_of_two(), "COLS must be a power of two (packed LDE stays radix-2)");
    let blowup = 4usize;
    let pi = [0x42u8; 32];
    let cols: Vec<usize> = (0..k).collect();
    // MODE=baseline | batched | both(default).  Separate processes give clean
    // peak RSS per path under /usr/bin/time -l.
    let mode = std::env::var("MODE").unwrap_or_else(|_| "both".into());
    let run_base = mode == "baseline" || mode == "both";
    let run_batch = mode == "batched" || mode == "both";

    // Honest seam: strand A and strand B agree on all K shared columns.
    let lde_a = seam_columns(k, n_trace, blowup, 0);
    let lde_b = lde_a.clone();

    // ── BASELINE: one single-column commit per side per column, K OOD verifies ──
    let (mut base_ms, mut base_fri_verifies, mut base_rss) = (0.0f64, 0usize, 0.0f64);
    if run_base {
        let t = Instant::now();
        for &c in &cols {
            let (ca, _) = commit_binding_cells(&lde_a, &[c], n_trace, blowup, pi, b"seam", params);
            let (cb, _) = commit_binding_cells(&lde_b, &[c], n_trace, blowup, pi, b"seam", params);
            verify_ood_consistency(&ca, &cb, pi, params).expect("honest per-column seam must verify");
            base_fri_verifies += 2; // one FRI verify per commit
            base_rss = base_rss.max(rss_mib());
        }
        base_ms = t.elapsed().as_secs_f64() * 1000.0;
    }

    // ── BATCHED: one packed commit per side over ALL K columns, ONE OOD verify ──
    let (mut batch_ms, mut batch_rss) = (0.0f64, 0.0f64);
    let batch_fri_verifies = 2usize;
    if run_batch {
        let t = Instant::now();
        let (pa0, _) = commit_binding_cells(&lde_a, &cols, n_trace, blowup, pi, b"seam", params);
        let (pb0, _) = commit_binding_cells(&lde_b, &cols, n_trace, blowup, pi, b"seam", params);
        verify_ood_consistency(&pa0, &pb0, pi, params).expect("honest batched seam group must verify");
        batch_ms = t.elapsed().as_secs_f64() * 1000.0;
        batch_rss = rss_mib();
        assert_eq!(pa0.num_cols, k as u32, "packed commit must carry all K columns");
    }
    if mode != "both" {
        println!(
            "MODE={mode} K={k} n_trace={n_trace} fri_verifies={} wall_ms={:.1} peak_rss_mib={:.0}",
            if run_base { base_fri_verifies } else { batch_fri_verifies },
            if run_base { base_ms } else { batch_ms },
            if run_base { base_rss } else { batch_rss },
        );
        return;
    }
    let (pa, _) = commit_binding_cells(&lde_a, &cols, n_trace, blowup, pi, b"seam", params);
    let (pb, _) = commit_binding_cells(&lde_b, &cols, n_trace, blowup, pi, b"seam", params);

    // ── ADVERSARIAL 1: one column of strand B differs (still low-degree) ──
    let mut lde_b_bad = lde_a.clone();
    lde_b_bad[3] = make_col(|r| (99 * 257 + r as u64 * 31 + 5) % 1_000_003, n_trace, blowup);
    // baseline catches it at column 3:
    let (ca3, _) = commit_binding_cells(&lde_a, &[3], n_trace, blowup, pi, b"seam", params);
    let (cb3, _) = commit_binding_cells(&lde_b_bad, &[3], n_trace, blowup, pi, b"seam", params);
    let base_rej = verify_ood_consistency(&ca3, &cb3, pi, params).is_err();
    // batched catches it via the packed OOD value:
    let (pa2, _) = commit_binding_cells(&lde_a, &cols, n_trace, blowup, pi, b"seam", params);
    let (pb2, _) = commit_binding_cells(&lde_b_bad, &cols, n_trace, blowup, pi, b"seam", params);
    let batch_rej = verify_ood_consistency(&pa2, &pb2, pi, params).is_err();
    assert!(base_rej, "baseline must reject a tampered column");
    assert!(batch_rej, "BATCHED must reject a tampered column (packed OOD differs)");

    // ── ADVERSARIAL 2: pi-binding — verify the honest packed commits under a
    //    DIFFERENT pi_hash.  The FRI FS challenges re-derive from pi_hash ⇒ the
    //    proof made under `pi` fails verification under `pi2`. ──
    let pi2 = [0x99u8; 32];
    let wrong_pi_rej = verify_ood_consistency(&pa, &pb, pi2, params).is_err();
    assert!(wrong_pi_rej, "a seam proof bound to pi must be REJECTED under a different pi_hash");

    let factor = base_fri_verifies as f64 / batch_fri_verifies as f64;
    println!("\n═══ deep_ali seam-batch bridge (K={k} columns / group, n_trace={n_trace}, L1/Fp6) ═══");
    println!("  BASELINE  per-column : {base_fri_verifies} FRI verifies, {base_ms:.1} ms, peak {base_rss:.0} MiB  (K commits ×2, K OOD checks)");
    println!("  BATCHED   per-group  : {batch_fri_verifies} FRI verifies, {batch_ms:.1} ms, peak {batch_rss:.0} MiB  (1 packed commit ×2, 1 OOD check)");
    println!("  reduction            : {factor:.0}× fewer FRI verifies, {:.1}× wall, but {:.1}× MORE RSS (packed poly is K× larger)", base_ms / batch_ms, batch_rss / base_rss.max(1.0));
    println!("  ----------------------------------------------------------------");
    println!("  honest group verifies         : true");
    println!("  tampered column rejected      : baseline={base_rej}, batched={batch_rej}");
    println!("  wrong pi_hash rejected        : {wrong_pi_rej}  (pi-bound: FS challenges re-derive from pi_hash)");
    println!("  soundness                     : shared z0, Schwartz–Zippel ε ≤ n/|Fp6| ≈ 2⁻³⁷⁰ (κ_sys unchanged)\n");
    println!("HONEST: packing cuts the FRI-verify COUNT by K× but the WALL only ~{:.1}× — the", base_ms / batch_ms);
    println!("packed poly is K× larger, so one batched verify costs ~K× a single one; the folding");
    println!("work is unchanged and only per-proof fixed costs amortize.  For a real WALL win the");
    println!("aggregation must reduce total work: a random-linear-combination BATCH — R(x)=Σαⁱ·dᵢ(x)");
    println!("(pointwise over the SAME size-n domain, one low-degree test instead of K) — which needs");
    println!("an F_ext-valued FRI (deep_fri_prove is currently base-F only).  Today's practical");
    println!("seam-verify speed-up is parallelising the independent checks (measured 5.3× on 10 cores).\n");
}
