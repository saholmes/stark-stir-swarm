//! Mixed-signature DNSSEC rollup demo — ML-DSA + RSA-2048 + Ed25519
//! aggregated into ONE outer rollup STARK.
//!
//! Models the STARK-DNS shape where a single zone holds RRSIGs across
//! multiple signature algorithms (DNSSEC alg. 8 = RSA-2048, alg. 15
//! = Ed25519, alg. 16/17 = ML-DSA when the PQ extension lands).  The
//! outer HashRollup AIR is signature-algorithm-oblivious — it only
//! commits to 32-byte pi_hashes — so a single epoch artefact covers
//! arbitrary mixes.
//!
//! In this branch:
//!
//!   - ML-DSA-44     : full v2 verify STARK via `prove_v2_real`
//!   - RSA-2048      : stacked-AIR verify STARK via the recipe in
//!                     `crates/deep_ali/examples/rsa2048_bench.rs`
//!   - Ed25519       : NATIVE pi_hash via `verify_zsk_ksk_native_v2`
//!                     (full STARK at `prove_zsk_ksk_binding_v2`
//!                     takes ~1.3 min/sig with streaming merge; we
//!                     use the native path here to keep the demo
//!                     runnable.  Upgrade to full STARK by replacing
//!                     the `make_ed25519_pi_hash` call with
//!                     `prove_zsk_ksk_binding_v2`.)
//!   - ECDSA-P256    : NOT WIRED in this branch (no `prove_ecdsa_*`
//!                     entry point exists yet — the `p256_*` AIRs
//!                     ship from a different branch).
//!
//! Run:
//!
//! ```bash
//! cargo run --release -p swarm-dns --example mixed_signature_rollup_demo
//! ```
//!
//! Environment overrides:
//!
//!   MIXED_N_MLDSA      — number of ML-DSA-44 records  (default 1)
//!   MIXED_N_RSA        — number of RSA-2048 records   (default 1)
//!   MIXED_N_ED25519    — number of Ed25519 records    (default 1)
//!   MIXED_BLOWUP       — inner FRI blowup factor      (default 4)
//!   MIXED_LDT          — `fri` (default) or `stir`    (outer LDT)

use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_serialize::{CanonicalSerialize, Compress};
use ed25519_dalek::Signer;
use num_bigint::BigUint;
use rand::{Rng, SeedableRng};

use deep_ali::{
    deep_ali_merge_rsa_stacked_streaming,
    fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain},
    ml_dsa::params::C_TILDE_BYTES,
    ml_dsa_transcript,
    ml_dsa_verify_air_v2_orchestration::{
        prove_v2_real, synthesize_demo_witness, verify_v2_real,
    },
    rsa2048_stacked_air::{
        build_rsa_stacked_layout, fill_rsa_stacked,
        rsa_stacked_constraints, RsaStackedRecord,
    },
    sextic_ext::SexticExt,
    trace_import::lde_trace_columns,
};
use swarm_dns::prover::{
    LdtMode, prove_outer_rollup, verify_zsk_ksk_native_v2,
};

type Ext = SexticExt;

fn parse_env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn fmt_kib(bytes: usize) -> String { format!("{:.1} KiB", bytes as f64 / 1024.0) }

// ─── ML-DSA leg ─────────────────────────────────────────────────────

struct LegOutput {
    pi_hash:        [u8; 32],
    prove_ms:       f64,
    verify_ms:      f64,
    size_bytes:     usize,
    label:          String,
}

fn prove_mldsa_record(sig_idx: u64, blowup: usize) -> LegOutput {
    let w = synthesize_demo_witness(sig_idx);
    let c_tilde: [u8; C_TILDE_BYTES] =
        ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

    let t = Instant::now();
    let proof = prove_v2_real(&w, &c_tilde, blowup);
    let prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    verify_v2_real(&w, &c_tilde, &proof, blowup)
        .expect("inner ML-DSA verify must accept honest proof");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;

    let size_bytes = proof.to_bytes().len();
    LegOutput {
        pi_hash: proof.pi_hash, prove_ms, verify_ms, size_bytes,
        label: format!("ML-DSA-44 #{sig_idx}"),
    }
}

// ─── RSA-2048 leg ───────────────────────────────────────────────────

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

fn prove_rsa2048_record(sig_idx: u64, blowup: usize) -> LegOutput {
    // Synthesise one honest RSA verification record (n odd, s < n,
    // em = s^65537 mod n).  Same recipe as rsa2048_bench.
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xDEAD_0000 + sig_idx);
    let n = (gen_biguint(&mut rng, 2046) << 1) | BigUint::from(1u8);
    let s = gen_biguint_below(&mut rng, &n);
    let em = s.modpow(&BigUint::from(65_537u32), &n);
    let records = vec![RsaStackedRecord { n, s, em }];

    let layout = build_rsa_stacked_layout(records.len());
    let n_trace_active = 2080usize;
    let n_trace = n_trace_active.next_power_of_two();

    let mut trace: Vec<Vec<F>> = (0..layout.width)
        .map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_stacked(&mut trace, &layout, n_trace, &records);

    let kk = rsa_stacked_constraints(&layout);
    let r: usize = 54;

    let n0 = n_trace * blowup;
    let domain = FriDomain::new_radix2(n0);
    let pi_hash: [u8; 32] = {
        use ::sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        Digest::update(&mut h, b"MIXED-ROLLUP-RSA2048-V1");
        Digest::update(&mut h, sig_idx.to_le_bytes());
        Digest::finalize(h).into()
    };
    let params = DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r, seed_z: 0xDEEFu64,
        coeff_commit_final: true, d_final: 1,
        stir: false, s0: r,
        public_inputs_hash: Some(pi_hash),
    };

    let t_prove = Instant::now();
    let lde = lde_trace_columns(&trace, n_trace, blowup).expect("rsa LDE");
    let comb_coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
    let (c_eval, _info) = deep_ali_merge_rsa_stacked_streaming(
        &lde, &comb_coeffs, &layout, F::zero(), n_trace, blowup,
    );
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;

    let t_verify = Instant::now();
    let ok = deep_fri_verify::<Ext>(&params, &proof);
    let verify_ms = t_verify.elapsed().as_secs_f64() * 1000.0;
    assert!(ok, "RSA-2048 self-verify must accept");

    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes)
        .expect("rsa proof serialise");
    let size_bytes = buf.len();

    LegOutput {
        pi_hash, prove_ms, verify_ms, size_bytes,
        label: format!("RSA-2048 #{sig_idx}"),
    }
}

// ─── Ed25519 native-only leg ────────────────────────────────────────

fn prove_ed25519_native(sig_idx: u64) -> LegOutput {
    use ed25519_dalek::{SigningKey, VerifyingKey};
    use rand::rngs::StdRng;

    let mut rng = StdRng::seed_from_u64(0xED25519_0000 + sig_idx);
    let mut sk_bytes = [0u8; 32];
    rng.fill(&mut sk_bytes);
    let sk = SigningKey::from_bytes(&sk_bytes);
    let vk: VerifyingKey = sk.verifying_key();

    let signed_data: Vec<u8> = format!("MIXED-ROLLUP-ED25519 record #{sig_idx}").into_bytes();
    let signature = sk.sign(&signed_data).to_bytes();
    let pubkey_bytes: [u8; 32] = vk.to_bytes();

    let fs_binding_32: [u8; 32] = [0xCA; 32];
    let merkle_root_32: [u8; 32] = [0xBB; 32];

    let t = Instant::now();
    let native = verify_zsk_ksk_native_v2(
        &pubkey_bytes, &signature, &signed_data, &fs_binding_32, &merkle_root_32,
    );
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    assert!(native.verified, "Ed25519 native verify must accept honest sig");

    LegOutput {
        pi_hash: native.pi_hash,
        prove_ms: 0.0,
        verify_ms,
        size_bytes: 0,
        label: format!("Ed25519 #{sig_idx} (NATIVE)"),
    }
}

// ─── Driver ─────────────────────────────────────────────────────────

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("MIXED-SIGNATURE DNSSEC ROLLUP DEMO");
    println!("═══════════════════════════════════════════════════════════════");
    println!();

    let n_mldsa = parse_env_usize("MIXED_N_MLDSA", 1);
    let n_rsa = parse_env_usize("MIXED_N_RSA", 1);
    let n_ed25519 = parse_env_usize("MIXED_N_ED25519", 1);
    let blowup = parse_env_usize("MIXED_BLOWUP", 4);
    let use_stir = std::env::var("MIXED_LDT").ok().as_deref() == Some("stir");
    let outer_ldt = if use_stir { LdtMode::Stir } else { LdtMode::Fri };

    println!("Configuration:");
    println!("  ML-DSA-44 records:    {n_mldsa}");
    println!("  RSA-2048 records:     {n_rsa}");
    println!("  Ed25519 records:      {n_ed25519} (NATIVE pi_hash; STARK path: prove_zsk_ksk_binding_v2)");
    println!("  ECDSA-P256:           NOT WIRED in this branch");
    println!("  Inner FRI blowup:     {blowup}");
    println!("  Outer LDT:            {}", if use_stir { "STIR" } else { "FRI" });
    println!();

    let total_legs = n_mldsa + n_rsa + n_ed25519;
    let mut all_legs: Vec<LegOutput> = Vec::with_capacity(total_legs);

    if total_legs == 0 {
        println!("No legs configured (all counts zero) — set MIXED_N_* env vars.");
        return;
    }

    // ─── ML-DSA legs ─────────────────────────────────────────────────
    if n_mldsa > 0 {
        println!("[ML-DSA-44] proving {n_mldsa} STARK verifications …");
        for i in 0..n_mldsa {
            let leg = prove_mldsa_record(i as u64, blowup);
            println!(
                "  {label}:  prove {prove:>7.1} ms   verify {verify:>6.2} ms   size {size:>9}",
                label = leg.label,
                prove = leg.prove_ms, verify = leg.verify_ms,
                size = fmt_kib(leg.size_bytes),
            );
            all_legs.push(leg);
        }
        println!();
    }

    // ─── RSA-2048 legs ───────────────────────────────────────────────
    if n_rsa > 0 {
        println!("[RSA-2048] proving {n_rsa} STARK verifications …");
        for i in 0..n_rsa {
            let leg = prove_rsa2048_record(i as u64, blowup);
            println!(
                "  {label}:  prove {prove:>7.1} ms   verify {verify:>6.2} ms   size {size:>9}",
                label = leg.label,
                prove = leg.prove_ms, verify = leg.verify_ms,
                size = fmt_kib(leg.size_bytes),
            );
            all_legs.push(leg);
        }
        println!();
    }

    // ─── Ed25519 legs (native) ──────────────────────────────────────
    if n_ed25519 > 0 {
        println!("[Ed25519] producing {n_ed25519} native pi_hashes …");
        for i in 0..n_ed25519 {
            let leg = prove_ed25519_native(i as u64);
            println!(
                "  {label}:  verify {verify:>6.2} ms   (no STARK proof in this run)",
                label = leg.label, verify = leg.verify_ms,
            );
            all_legs.push(leg);
        }
        println!();
    }

    // ─── Sub-totals per algorithm ────────────────────────────────────
    let totals = |legs: &[LegOutput]| -> (f64, f64, usize) {
        legs.iter().fold((0.0, 0.0, 0), |(p, v, s), l| {
            (p + l.prove_ms, v + l.verify_ms, s + l.size_bytes)
        })
    };
    let mldsa_legs:   Vec<&LegOutput> = all_legs.iter().filter(|l| l.label.contains("ML-DSA")).collect();
    let rsa_legs:     Vec<&LegOutput> = all_legs.iter().filter(|l| l.label.contains("RSA-2048")).collect();
    let ed_legs:      Vec<&LegOutput> = all_legs.iter().filter(|l| l.label.contains("Ed25519")).collect();

    // Outer rollup over ALL pi_hashes.
    let pi_hashes: Vec<[u8; 32]> = all_legs.iter().map(|l| l.pi_hash).collect();
    let outer_pk_hash: [u8; 32] = {
        use ::sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        Digest::update(&mut h, b"MIXED-SIGNATURE-ROLLUP-DEMO-V1");
        Digest::update(&mut h, (total_legs as u64).to_le_bytes());
        Digest::finalize(h).into()
    };

    println!("[OUTER] aggregating {total_legs} pi_hashes via HashRollup STARK …");
    let outer = prove_outer_rollup(&pi_hashes, &outer_pk_hash, outer_ldt);
    println!(
        "  outer:  prove {:>7.1} ms   verify {:>6.2} ms   size {:>9}   n_trace={}",
        outer.prove_ms, outer.local_verify_ms, fmt_kib(outer.proof_bytes), outer.n_trace,
    );
    println!();

    let inner_total_size: usize = all_legs.iter().map(|l| l.size_bytes).sum();
    let inner_total_prove: f64  = all_legs.iter().map(|l| l.prove_ms).sum();
    let inner_total_verify: f64 = all_legs.iter().map(|l| l.verify_ms).sum();
    let composite_size = inner_total_size + outer.proof_bytes;
    let composite_prove = inner_total_prove + outer.prove_ms;
    let composite_verify = inner_total_verify + outer.local_verify_ms;

    println!("═══════════════════════════════════════════════════════════════");
    println!("  MIXED-SIGNATURE COMPOSITE ({total_legs} legs → 1 outer rollup):");
    println!();
    if !mldsa_legs.is_empty() {
        let (p, v, s) = totals(&mldsa_legs.iter().map(|l| (*l).clone_for_sum()).collect::<Vec<_>>());
        println!("    ML-DSA-44   ×{:<2}:   prove {:>9.1} ms   verify {:>7.2} ms   size {:>10}",
            mldsa_legs.len(), p, v, fmt_kib(s));
    }
    if !rsa_legs.is_empty() {
        let (p, v, s) = totals(&rsa_legs.iter().map(|l| (*l).clone_for_sum()).collect::<Vec<_>>());
        println!("    RSA-2048    ×{:<2}:   prove {:>9.1} ms   verify {:>7.2} ms   size {:>10}",
            rsa_legs.len(), p, v, fmt_kib(s));
    }
    if !ed_legs.is_empty() {
        let (p, v, s) = totals(&ed_legs.iter().map(|l| (*l).clone_for_sum()).collect::<Vec<_>>());
        println!("    Ed25519 ×{:<2} (native):              verify {:>7.2} ms   size {:>10}",
            ed_legs.len(), v, fmt_kib(s));
        let _ = p;  // no prove time for native
    }
    println!();
    println!("    outer rollup:        prove {:>9.1} ms   verify {:>7.2} ms   size {:>10}",
        outer.prove_ms, outer.local_verify_ms, fmt_kib(outer.proof_bytes));
    println!("    ────────────────────────────────────────────────────────────────────");
    println!("    end-to-end:          prove {composite_prove:>9.1} ms   verify {composite_verify:>7.2} ms   size {:>10}",
        fmt_kib(composite_size));
    println!();
    println!("  Single outer FRI proof attests Merkle commitment over ALL {total_legs}");
    println!("  per-signature pi_hashes regardless of underlying algorithm.");
    println!();
    println!("  Note: Ed25519 pi_hash carries native-verify provenance only.  For full");
    println!("  STARK aggregation, swap `verify_zsk_ksk_native_v2` for");
    println!("  `prove_zsk_ksk_binding_v2` (≈ 1-2 min/sig at K=256 with streaming).");
    println!("  ECDSA-P256 legs require the `p256_ecdsa_double_multirow_air` wiring,");
    println!("  which ships from a sister branch — not present in this tree.");
    println!("═══════════════════════════════════════════════════════════════");
}

// Helper for sums (Vec<&LegOutput> can't fold with mutating values
// directly without ownership; the trivial clone here just for arithmetic).
trait CloneForSum { fn clone_for_sum(&self) -> LegOutput; }
impl CloneForSum for LegOutput {
    fn clone_for_sum(&self) -> LegOutput {
        LegOutput {
            pi_hash: self.pi_hash,
            prove_ms: self.prove_ms,
            verify_ms: self.verify_ms,
            size_bytes: self.size_bytes,
            label: self.label.clone(),
        }
    }
}
