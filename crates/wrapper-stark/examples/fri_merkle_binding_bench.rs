//! Phase 6 bench — measures proof sizes + wall-clock times for the
//! FRI-Merkle binding pipeline (Phase 3 linear form + Phase 4b compact
//! form) at smoke L1 (blowup=4, r=54), then projects to L1 prod.
//!
//! Output written to stdout; pipe to `scripts/results/fri-merkle-binding-bench.log`
//! when running:
//!
//! ```bash
//! cargo run --release -p wrapper-stark \
//!     --features "sha3-256 mldsa-44 parallel" --no-default-features \
//!     --example fri_merkle_binding_bench \
//!     > scripts/results/fri-merkle-binding-bench.log 2>&1
//! ```

use std::time::Instant;

use ark_serialize::CanonicalSerialize;

use deep_ali::ml_dsa::params::C_TILDE_BYTES;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    prove_v2_real, synthesize_demo_witness,
};

use wrapper_stark::master_recursion_bridge::{
    aggregate_fri_merkle_bindings, extract_fri_merkle_openings,
    prove_master_recursive, verify_master_recursive,
};
use wrapper_stark::merkle_prover::{
    prove_batched_merkle_paths, verify_batched_merkle_paths,
};
use wrapper_stark::recursive_prover::verify_recursive_stark;
use wrapper_stark::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive;

fn fmt_kib(n: usize) -> String {
    format!("{} B  ({:.2} KiB)", n, n as f64 / 1024.0)
}

fn fmt_ms(ms: f64) -> String {
    if ms < 1000.0 {
        format!("{ms:.1} ms")
    } else {
        format!("{:.2} s", ms / 1000.0)
    }
}

fn proof_size<T: CanonicalSerialize>(p: &T) -> usize {
    let mut buf = Vec::new();
    p.serialize_compressed(&mut buf).unwrap();
    buf.len()
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════════");
    println!(" FRI-MERKLE BINDING BENCH — Phase 6 anchor");
    println!(" sha3-256 / NIST L1 / smoke blowup=4 r=54 / N=1 inner, B=10 subset");
    println!("═══════════════════════════════════════════════════════════════════");
    println!();

    let inner_blowup = 4usize;
    let master_blowup = 4usize;
    let master_r = 54usize;
    let binding_blowup = 4usize;
    let binding_r = 54usize;
    let aggregator_blowup = 4usize;
    let aggregator_r = 54usize;

    // ─── 1. Build 1 inner v2 + recursive STARK ────────────────────
    println!("[1/6] Build inner v2 + recursive STARK …");
    let t = Instant::now();
    let w = synthesize_demo_witness(900);
    let c_tilde: [u8; C_TILDE_BYTES] =
        ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
    let synth_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    let v2_proof = prove_v2_real(&w, &c_tilde, inner_blowup);
    let v2_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    let inner = prove_v2_all_subairs_composed_recursive(
        &v2_proof, &w, inner_blowup, master_blowup, master_r, /*stir=*/false,
    ).expect("recursive STARK wrap");
    let rec_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    assert!(verify_recursive_stark(&inner));
    let inner_size = proof_size(&inner.fri_proof);

    let l = inner.fri_proof.queries[0].per_layer_payloads.len();
    let r = inner.fri_proof.queries.len();
    let n_lde_inner = inner.n_trace * inner.blowup;

    println!("  v2 witness synth:           {}", fmt_ms(synth_ms));
    println!("  v2 inner prove:             {}", fmt_ms(v2_prove_ms));
    println!("  recursive wrap prove:       {}", fmt_ms(rec_prove_ms));
    println!("  inner.n_trace:              {}", inner.n_trace);
    println!("  n_lde_inner:                {}", n_lde_inner);
    println!("  L (FRI layers):             {l}");
    println!("  r (queries):                {r}");
    println!("  M_paths = r × L:            {}", r * l);
    println!("  inner.fri_proof size:       {}", fmt_kib(inner_size));
    println!();

    // ─── 2. Extract subset binding claim ─────────────────────────
    println!("[2/6] Extract FRI Merkle openings → B=10 subset binding claim …");
    let t = Instant::now();
    let mut full_claim = extract_fri_merkle_openings(&inner)
        .expect("extract must succeed");
    let extract_ms = t.elapsed().as_secs_f64() * 1000.0;
    let subset_indices: Vec<usize> = vec![
        0, 1, l - 1, l, l + 1, 2 * l, 3 * l, 10 * l, 20 * l, 30 * l - 1,
    ];
    full_claim.paths = subset_indices.iter()
        .map(|&i| full_claim.paths[i].clone()).collect();
    let subset_claim = full_claim;
    println!("  extract_fri_merkle_openings: {}", fmt_ms(extract_ms));
    println!("  subset.batch_size:           {}", subset_claim.batch_size());
    println!();

    // ─── 3. Phase 3 linear form: master + per-inner binding ──────
    println!("[3/6] Phase 3 linear form: master STARK + 1 binding bundle …");
    let inner_proofs = vec![inner];

    let t = Instant::now();
    let master = prove_master_recursive(
        &inner_proofs, master_blowup, master_r, /*stir=*/false,
    ).expect("master prove");
    let master_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    let binding = prove_batched_merkle_paths(
        &subset_claim, binding_blowup, binding_r, /*stir=*/false,
    ).expect("binding prove");
    let binding_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    assert!(verify_master_recursive(&master));
    assert!(verify_batched_merkle_paths(&binding));
    let phase3_verify_ms = t.elapsed().as_secs_f64() * 1000.0;

    let master_size = proof_size(&master.fri_proof);
    let binding_size = proof_size(&binding.fri_proof);
    let binding_publics_size =
        binding.public.paths.len() * (32 + 8 + 8) + 32; // root+leaf_idx+depth + pi_hash
    let phase3_l1_wire = master_size + binding_size;

    println!("  master prove:               {}", fmt_ms(master_prove_ms));
    println!("  binding (B=10) prove:       {}", fmt_ms(binding_prove_ms));
    println!("  master + binding verify:    {}", fmt_ms(phase3_verify_ms));
    println!("  master.fri_proof size:      {}", fmt_kib(master_size));
    println!("  binding.fri_proof size:     {}", fmt_kib(binding_size));
    println!("  binding publics (off-wire): {}", fmt_kib(binding_publics_size));
    println!("  ──────────────────────────────────────────────");
    println!("  Phase 3 L1 wire (master + binding):  {}", fmt_kib(phase3_l1_wire));
    println!();

    // ─── 4. Phase 4b compact form: master + aggregator + publics ─
    println!("[4/6] Phase 4b compact form: master + binding aggregator + publics …");
    let bindings = std::slice::from_ref(&binding);

    let t = Instant::now();
    let aggregator = aggregate_fri_merkle_bindings(
        bindings, aggregator_blowup, aggregator_r, /*stir=*/false,
    ).expect("aggregate must succeed");
    let aggregator_prove_ms = t.elapsed().as_secs_f64() * 1000.0;

    let t = Instant::now();
    assert!(verify_recursive_stark(&aggregator));
    let aggregator_verify_ms = t.elapsed().as_secs_f64() * 1000.0;

    let aggregator_size = proof_size(&aggregator.fri_proof);
    let phase4b_l1_wire = master_size + aggregator_size + binding_publics_size;

    println!("  aggregator prove:           {}", fmt_ms(aggregator_prove_ms));
    println!("  aggregator verify:          {}", fmt_ms(aggregator_verify_ms));
    println!("  aggregator.fri_proof size:  {}", fmt_kib(aggregator_size));
    println!("  ──────────────────────────────────────────────");
    println!("  Phase 4b L1 wire:           {}", fmt_kib(phase4b_l1_wire));
    println!("    = master + aggregator + binding_publics");
    println!();

    // ─── 5. Wire-cost comparison + L1 prod projection ────────────
    println!("[5/6] Wire-cost comparison + L1 prod projection …");
    println!();
    println!("  Smoke (blowup=4 r=54) at N=1 B=10:");
    println!("    Phase 3 (linear):       master {} + binding {} = {}",
        fmt_kib(master_size), fmt_kib(binding_size), fmt_kib(phase3_l1_wire));
    println!("    Phase 4b (compact):     master {} + aggregator {} + publics {} = {}",
        fmt_kib(master_size), fmt_kib(aggregator_size),
        fmt_kib(binding_publics_size), fmt_kib(phase4b_l1_wire));
    let savings_pct = 100.0 *
        (phase3_l1_wire as f64 - phase4b_l1_wire as f64) / phase3_l1_wire as f64;
    println!("    Compact saving at N=1:  {savings_pct:.1}%");
    println!();

    // L1 prod scaling: typical at blowup=32 r=54 the proof shrinks
    // ~5× (more queries cheaper to verify; smaller FRI; per
    // recursive-stark-bench-bw32.md anchored numbers).  Prove time
    // grows ~5-7×.
    let prod_scale_size = 5.0_f64;
    let prod_scale_prove = 6.0_f64;
    let master_prod = (master_size as f64 / prod_scale_size) as usize;
    let binding_prod = (binding_size as f64 / prod_scale_size) as usize;
    let aggregator_prod = (aggregator_size as f64 / prod_scale_size) as usize;
    let phase3_prod_wire = master_prod + binding_prod;
    let phase4b_prod_wire = master_prod + aggregator_prod + binding_publics_size;
    println!("  Projected L1 prod (blowup=32, r=54):");
    println!("    Phase 3 (linear):       {} ({}× smaller proof shape)",
        fmt_kib(phase3_prod_wire), prod_scale_size as usize);
    println!("    Phase 4b (compact):     {}", fmt_kib(phase4b_prod_wire));
    println!();

    // At larger N the compact form's advantage compounds.
    println!("  Compact L1 wire vs N (prod blowup=32, r=54, B=810 full per-inner):");
    println!("    N        Phase 3            Phase 4b      Saving");
    println!("    ───────────────────────────────────────────────────");
    let binding_full_smoke = binding_size * 81;  // B=10 → B=810 ≈ 81×
    let binding_full_prod = (binding_full_smoke as f64 / prod_scale_size) as usize;
    let binding_publics_full_prod = (binding_publics_size as f64) as usize * 81;
    for n in [1, 10, 100, 1000] {
        let p3 = master_prod + n * binding_full_prod;
        let p4b = master_prod + aggregator_prod
            + n * binding_publics_full_prod;
        let saving = 100.0 * (p3 as f64 - p4b as f64) / p3 as f64;
        let p3_mib = p3 as f64 / 1024.0 / 1024.0;
        let p4b_mib = p4b as f64 / 1024.0 / 1024.0;
        println!("    {n:>5}    {p3_mib:>10.2} MiB     {p4b_mib:>8.2} MiB    {saving:>5.1}%");
    }
    println!();

    // ─── 6. Sub-circuit 1a (Phase 5) constraint count anchor ─────
    println!("[6/6] Sub-circuit 1a constraint count (Phase 5):");
    let comp_constraints_phase3 = r * l * 6;          // DEEP-quotient × Ext degree
    let comp_constraints_phase5 = r * (2 * l - 1) * 6; // + fold residues
    println!("    Phase 3 (DEEP-quotient only): {comp_constraints_phase3} cons/inner");
    println!("    Phase 5 (+ fold relation):    {comp_constraints_phase5} cons/inner");
    let increase = comp_constraints_phase5 as f64 / comp_constraints_phase3 as f64;
    println!("    Constraint-count ratio:       {increase:.2}×");
    println!();
    println!("═══════════════════════════════════════════════════════════════════");
    println!(" Bench complete.  See scripts/results/fri-merkle-binding-bench.md");
    println!(" for narrative analysis + production calibration notes.");
    println!("═══════════════════════════════════════════════════════════════════");
}
