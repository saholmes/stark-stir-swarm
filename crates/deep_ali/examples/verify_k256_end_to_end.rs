//! verify_k256_end_to_end.rs — measure the LogUp range-check argument for a
//! FULL K=256 ECDSA-P256 verify's worth of sub-limbs, proven end-to-end
//! through the real DEEP-FRI prover (commit trace -> merge -> prove ->
//! verify).  This is the dominant cost of the lookup-configuration verify
//! (range checking is ~90-98% of the trace); the per-gadget arithmetic
//! (sub-limb-pack + schoolbook/carry/borrow/mux) is single-row and measured
//! separately below.
//!
//! Run (macOS, wall + RSS):
//!   STEPS=196 /usr/bin/time -l cargo run --release \
//!     --features "parallel,sha3-256" -p deep_ali --example verify_k256_end_to_end
//!
//! STEPS=196 double-and-add iterations = 392 real point operations, the
//! MSM-optimised point-op count for a K=256 verify (fixed-base comb G +
//! windowed Q ~= 141 adds + 252 doubles).  Smaller STEPS extrapolate.

use ark_goldilocks::Goldilocks as F;
use deep_ali::group_op_lookup_prover_air::{group_add_sublimbs, group_double_sublimbs};
use deep_ali::p256_group::GENERATOR;
use deep_ali::permutation_argument::{ExtField, EXT_DEGREE};
use deep_ali::tower_field::TowerField;
use deep_ali::verify_lookup_fri_air::prove_verify_lookup;
use std::time::Instant;

fn main() {
    let steps: usize = std::env::var("STEPS").ok().and_then(|s| s.parse().ok()).unwrap_or(196);

    // (1) Generate a full K=256 verify's worth of sub-limbs by composing
    //     real point operations (double + add per step), and time the
    //     per-gadget fill + local range-check evidence generation.
    let t = Instant::now();
    let g = *GENERATOR;
    let mut acc = g;
    let mut vals: Vec<u64> = Vec::new();
    let mut n_ops = 0usize;
    let mut arithmetic_ok = true;
    for _ in 0..steps {
        let (dv, da) = group_double_sublimbs(&acc);
        vals.extend(dv);
        arithmetic_ok &= da;
        n_ops += 1;

        let two = acc.double();
        let (av, aa) = group_add_sublimbs(&two, &g);
        vals.extend(av);
        arithmetic_ok &= aa;
        n_ops += 1;

        acc = two.add(&g);
    }
    let gen_s = t.elapsed().as_secs_f64();
    assert!(arithmetic_ok, "all point-op arithmetic must be valid");

    // (2) Prove the LogUp range check over EVERY sub-limb through the full
    //     trace-committed DEEP-FRI prover, and time it.
    let comps: Vec<F> = (0..EXT_DEGREE).map(|i| F::from(0x0B00_0000u64 + 43 * i as u64 + 19)).collect();
    let alpha = ExtField::from_fp_components(&comps).expect("valid F_ext");

    let table_size = 1usize << 13;
    let n_trace = (table_size + vals.len() + 1).next_power_of_two();

    let t = Instant::now();
    let ok = prove_verify_lookup(&vals, alpha);
    let fri_s = t.elapsed().as_secs_f64();
    assert!(ok, "the full-verify range-check accumulator must FRI prove+verify");

    println!("\n═══ K=256 ECDSA-P256 verify, LogUp configuration (end-to-end) ═══");
    println!("  point operations       : {n_ops}  (STEPS={steps}; MSM-optimised K=256 ~= 393)");
    println!("  sub-limbs range-checked : {}", vals.len());
    println!("  accumulator trace rows  : {n_trace}  (x4 blow-up on LDE)");
    println!("  ----------------------------------------------------------------");
    println!("  gadget fill + sub-limbs : {gen_s:.2}s  (single-row arithmetic + evidence)");
    println!("  range-check DEEP-FRI     : {fri_s:.2}s  (commit -> merge -> prove -> verify)");
    println!("  TOTAL wall (1 core)      : {:.2}s", gen_s + fri_s);
    println!("  verified                : {ok}");
    println!("  (range checking dominates the lookup-config trace; the ~5 core-hour");
    println!("   projection was for the full arithmetic prove, embarrassingly parallel");
    println!("   across the {n_ops} independent point-op proofs.)\n");
}
