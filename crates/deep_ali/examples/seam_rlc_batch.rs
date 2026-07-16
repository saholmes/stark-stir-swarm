//! seam_rlc_batch.rs — deep_ali-native RLC seam batch via COMPONENT DECOMPOSITION.
//!
//! Goal: check that K seam columns of strand A agree with strand B using far
//! fewer than K FRI verifies, at F_ext (NIST-level) soundness, WITHOUT blowing
//! up RSS (unlike per-group packing, which is K× larger — see seam_batch_bridge).
//!
//! Mechanism.  Let dᵢ = aᵢ − bᵢ be the seam-column difference polynomials
//! (base-F, low-degree; honest ⇒ dᵢ ≡ 0).  Draw α ∈ F_ext (FS from pi_hash) and
//! form the random-linear-combination R(x) = Σᵢ αⁱ·dᵢ(x).  R ≡ 0 iff every dᵢ ≡ 0
//! (Schwartz–Zippel over α, ε ≤ K/|F_ext|); and R(z0) = 0 for the pi-derived OOD
//! point z0 iff R ≡ 0 (Schwartz–Zippel over z0, ε ≤ n/|F_ext|).  Both errors are
//! ≤ 2⁻³⁷⁰ at L1 (Fp⁶) — κ_sys unchanged.
//!
//! R is F_ext-valued, and deep_fri_prove is base-F only.  So decompose over the
//! F_ext basis {eⱼ}: since αⁱ = Σⱼ cᵢⱼ·eⱼ (cᵢⱼ = (αⁱ).to_fp_components()[j] ∈ F),
//!     R(x) = Σⱼ eⱼ · R⁽ʲ⁾(x),   R⁽ʲ⁾(x) = Σᵢ cᵢⱼ·dᵢ(x)   (base-F!).
//! Commit each of the d = EXT_DEGREE base-F codewords R⁽ʲ⁾ with the EXISTING,
//! tested base-F FRI, extract R⁽ʲ⁾(z0), and recombine R(z0) = Σⱼ eⱼ·R⁽ʲ⁾(z0).
//! ⇒ d = 6 (L1/L3) or 8 (L5) FRI verifies, each size-n (baseline RSS), replacing
//! the K per-column checks — with full F_ext soundness.
//!
//! Prototype scope (like accumulation.rs): the R⁽ʲ⁾ are formed from the real dᵢ
//! to demonstrate the reduction + soundness of the CONSISTENCY check.  Binding
//! R⁽ʲ⁾ to the individual aᵢ/bᵢ commitments (a per-FRI-query linear-combination
//! check = standard FRI batching) is the remaining production step.
//!
//! Run:
//!   COLS=32 cargo run --release --features "parallel,sha3-256" -p deep_ali \
//!     --example seam_rlc_batch

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use sha3::{Digest, Sha3_256};
use std::time::Instant;

use deep_ali::binding_cells_commit::{commit_binding_cells, verify_ood_consistency};
use deep_ali::fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain};
use deep_ali::permutation_argument::{ExtField, EXT_DEGREE};
use deep_ali::tower_field::TowerField;

fn rss_mib() -> f64 {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output();
    match out {
        Ok(o) => String::from_utf8_lossy(&o.stdout).trim().parse::<f64>().unwrap_or(0.0) / 1024.0,
        Err(_) => 0.0,
    }
}

fn make_col(pat: impl Fn(usize) -> u64, n_trace: usize, blowup: usize) -> Vec<F> {
    let lde_size = n_trace * blowup;
    let trace_dom = GeneralEvaluationDomain::<F>::new(n_trace).unwrap();
    let lde_dom = GeneralEvaluationDomain::<F>::new(lde_size).unwrap();
    let coeffs: Vec<F> = (0..n_trace).map(|r| F::from(pat(r))).collect();
    let mut poly = trace_dom.ifft(&coeffs);
    poly.resize(lde_size, F::zero());
    lde_dom.fft(&poly)
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

/// FS-derive α ∈ F_ext from pi_hash.
fn derive_alpha(pi_hash: &[u8; 32]) -> ExtField {
    let comps: Vec<F> = (0..EXT_DEGREE)
        .map(|j| {
            let mut h = Sha3_256::new();
            h.update(pi_hash);
            h.update(b"seam-rlc-alpha");
            h.update((j as u64).to_le_bytes());
            let d = h.finalize();
            let mut b = [0u8; 8];
            b.copy_from_slice(&d[..8]);
            F::from(u64::from_le_bytes(b))
        })
        .collect();
    ExtField::from_fp_components(&comps).expect("valid F_ext element")
}

fn main() {
    let n_trace: usize = std::env::var("NTRACE").ok().and_then(|s| s.parse().ok()).unwrap_or(2048);
    let k: usize = std::env::var("COLS").ok().and_then(|s| s.parse().ok()).unwrap_or(32);
    let blowup = 4usize;
    let n_lde = n_trace * blowup;
    let pi = [0x42u8; 32];
    let tamper = std::env::var("TAMPER").as_deref() == Ok("1");

    // Strand A columns; strand B = A (honest) except one column if TAMPER.
    let a: Vec<Vec<F>> = (0..k)
        .map(|c| make_col(move |r| (c as u64 * 257 + r as u64 * 31 + 11) % 1_000_003, n_trace, blowup))
        .collect();
    let mut b = a.clone();
    if tamper {
        b[k / 2] = make_col(|r| (99 * 257 + r as u64 * 31 + 5) % 1_000_003, n_trace, blowup);
    }

    // ── BASELINE: K per-column OOD checks (2K FRI verifies) ──
    let t = Instant::now();
    let mut base_ok = true;
    let mut base_rss = 0.0f64;
    for c in 0..k {
        let la = vec![a[c].clone()];
        let lb = vec![b[c].clone()];
        let (ca, _) = commit_binding_cells(&la, &[0], n_trace, blowup, pi, b"seam", params);
        let (cb, _) = commit_binding_cells(&lb, &[0], n_trace, blowup, pi, b"seam", params);
        base_ok &= verify_ood_consistency(&ca, &cb, pi, params).is_ok();
        base_rss = base_rss.max(rss_mib());
    }
    let base_ms = t.elapsed().as_secs_f64() * 1000.0;
    let base_fri = 2 * k;

    // ── RLC BATCH via component decomposition (d = EXT_DEGREE base-F FRIs) ──
    let t = Instant::now();
    // Difference polynomials dᵢ = aᵢ − bᵢ over the LDE domain.
    let diffs: Vec<Vec<F>> = (0..k)
        .map(|i| (0..n_lde).map(|x| a[i][x] - b[i][x]).collect())
        .collect();
    // αⁱ and their base-F components cᵢⱼ.
    let alpha = derive_alpha(&pi);
    let mut alpha_pows: Vec<ExtField> = Vec::with_capacity(k);
    let mut cur = ExtField::from_fp(F::from(1u64));
    for _ in 0..k {
        alpha_pows.push(cur);
        cur = cur * alpha;
    }
    let comps: Vec<Vec<F>> = alpha_pows.iter().map(|ai| ai.to_fp_components()).collect();

    // R⁽ʲ⁾(x) = Σᵢ cᵢⱼ·dᵢ(x), a base-F codeword; commit each with the base-F FRI.
    let domain = FriDomain::new_radix2(n_lde);
    let fri_params = params(n_lde, pi);
    let mut r_z0 = ExtField::zero();
    let mut rlc_ok = true;
    let mut rlc_rss = 0.0f64;
    for j in 0..EXT_DEGREE {
        let mut rj = vec![F::zero(); n_lde];
        for i in 0..k {
            let cij = comps[i][j];
            if cij.is_zero() {
                continue;
            }
            for x in 0..n_lde {
                rj[x] += cij * diffs[i][x];
            }
        }
        let proof = deep_fri_prove::<ExtField>(rj, domain.clone(), &fri_params);
        rlc_ok &= deep_fri_verify::<ExtField>(&fri_params, &proof);
        // R⁽ʲ⁾(z0) = proof.fz_per_layer[0]; e_j = basis vector j.
        let mut unit = vec![F::zero(); EXT_DEGREE];
        unit[j] = F::from(1u64);
        let e_j = ExtField::from_fp_components(&unit).unwrap();
        r_z0 += e_j * proof.fz_per_layer[0];
        rlc_rss = rlc_rss.max(rss_mib());
    }
    let rlc_ms = t.elapsed().as_secs_f64() * 1000.0;
    let rlc_fri = EXT_DEGREE;
    // Consistency accept ⇔ all seams agree ⇔ R(z0) = 0.
    let rlc_accept = rlc_ok && r_z0.is_zero();

    println!("\n═══ deep_ali seam RLC batch via component decomposition (K={k}, n_trace={n_trace}) ═══");
    println!("  F_ext = Fp{EXT_DEGREE}  (α ∈ F_ext, FS from pi_hash; z0 pi-derived)");
    println!("  TAMPER = {tamper}");
    println!("  ----------------------------------------------------------------");
    println!("  BASELINE per-column : {base_fri} FRI verifies, {base_ms:.1} ms, peak {base_rss:.0} MiB → all-agree={base_ok}");
    println!("  RLC BATCH (decomp)  : {rlc_fri} FRI verifies, {rlc_ms:.1} ms, peak {rlc_rss:.0} MiB → accept={rlc_accept}");
    println!("  ----------------------------------------------------------------");
    println!("  FRI-verify reduction: {:.1}× ({base_fri}→{rlc_fri}); RSS ratio {:.2}× (both size-n, no K× blow-up)", base_fri as f64 / rlc_fri as f64, rlc_rss / base_rss.max(1.0));
    if tamper {
        assert!(!base_ok, "baseline must detect the tampered column");
        assert!(!rlc_accept, "RLC batch must REJECT: R(z0) ≠ 0 for a tampered seam");
        println!("  ✓ tampered seam REJECTED by both (R(z0) ≠ 0)");
    } else {
        assert!(base_ok && rlc_accept, "honest seams must verify both ways");
        println!("  ✓ honest seams ACCEPTED by both (R(z0) = 0)");
    }
    println!("  soundness: α∈F_ext ⇒ ε ≤ (K+n)/|F_ext| ≈ 2⁻³⁷⁰ (L1); κ_sys unchanged.\n");
    println!("(prototype: R⁽ʲ⁾ formed from real dᵢ; per-query LC binding of R to the aᵢ/bᵢ");
    println!(" commitments = standard FRI batching, the remaining production step.)\n");
}
