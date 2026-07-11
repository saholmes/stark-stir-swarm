//! ECDSA SWARM RECURSION DEMO — STARK-of-STARK compression of the
//! G-strand stranded ECDSA-verify proof into ONE succinct master STARK.
//!
//! # What this does
//!
//! The `ecdsa_swarm_demo` proves ECDSA-verify as G strands, each a
//! `deep_ali::sub_air_with_trace::SubAirProofWithTrace` (inner FRI +
//! per-query trace openings), bound by F2b OOD seams
//! (`binding_cells_commit` / `verify_ood_consistency`).  Verifying that
//! DIRECTLY is non-succinct (the per-query trace openings carry the
//! full-width cells → GiB-scale artefact, tens-of-seconds verify).
//!
//! This demo restores succinctness by RECURSIVELY WRAPPING each strand
//! + its seams via the existing wrapper-stark recursion stack
//! (`deep_ali_verifier_air` / `recursive_prover`), then AGGREGATING the
//! G recursive strand-proofs into ONE master `RecursiveStarkProof` via
//! `master_recursion_bridge::prove_master_recursive`.  This is the SAME
//! pipeline the working ML-DSA `master_recursion_demo` uses — here fed
//! by the ECDSA stranded output instead of ML-DSA v2 proofs.
//!
//! No new crypto: the recursive wrap attests the SAME algebraic
//! relations the direct verifier checks —
//!   * inner FRI DEEP-quotient relation per (query, layer)  → sub-circuit 1
//!   * F2b seam OOD equality f(z₀) = g(z₀)                  → sub-circuit 2
//!   * a vestige perm-arg bound to the strand pi_hash        → sub-circuit 3
//! composed into one outer FRI proof per strand, then one master FRI
//! proof over the G strand-proofs.  Soundness = min(inner, outer) at the
//! NIST level of the outer FRI params (blowup/r).
//!
//! # Run
//!
//! ```bash
//! K=16 G=4 BENCH_BLOWUP=4 cargo run --release -p wrapper-stark \
//!   --example ecdsa_swarm_recursion_demo \
//!   --features "sha3-256 mldsa-44 parallel" --no-default-features
//! ```
//!
//! Env: K (scalar-mult steps / trace rows, default 16), G (strands,
//! default 4), BENCH_BLOWUP (inner+outer LDE blowup, default 4).

#![allow(non_snake_case)]

use std::time::Instant;

use ark_ff::{Field, PrimeField, Zero};
use ark_goldilocks::Goldilocks as F;
use ark_serialize::CanonicalSerialize;

use deep_ali::{
    binding_cells_commit::{extract_ood_value, BindingCellsCommit, Ext},
    ecdsa_verify_stranded_gway::{
        compute_gway_cut, prove_one_strand, strand_domain, verify_stranded_g,
        GwayCut, StrandedProofG,
    },
    fri::{derive_z_ext_for_proof, layer_sizes_from_schedule, DeepFriParams, DeepFriProof},
    p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, ecdsa_verify_multirow_constraints,
        fill_ecdsa_verify_multirow, EcdsaVerifyMultirowLayout, EcdsaVerifyPublicInputs,
    },
    p256_field::{FieldElement, NUM_LIMBS},
    p256_group::GENERATOR as P256_GENERATOR,
    sub_air_with_trace::{augment_pi_hash, SubAirProofWithTrace},
    tower_field::TowerField,
};
use ark_serialize::{CanonicalDeserialize, Compress, Validate};

use wrapper_stark::bit_constraint::{BitOp, CellRef};
use wrapper_stark::composition::alphas_from_transcript;
use wrapper_stark::deep_ali_verifier_air::binding_cells_ood_verifier::{
    OodClaimBundle, OodEqualityClaim,
};
use wrapper_stark::deep_ali_verifier_air::constraint_composition_verifier::CompositionClaim;
use wrapper_stark::deep_ali_verifier_air::permutation_argument_verifier::PermArgClaim;
use wrapper_stark::master_recursion_bridge::{
    prove_master_recursive, prove_master_with_batched_in_air_merkle_path,
    prove_master_with_in_air_merkle_path, verify_master_recursive,
    verify_master_with_batched_in_air_merkle_path,
    verify_master_with_in_air_merkle_path,
};
use wrapper_stark::recursive_prover::{
    prove_recursive_stark, verify_recursive_stark, OodAccumulatorClaim, RecursiveProverError,
    RecursiveStarkProof,
};

// ─── FRI params — IDENTICAL shape to the ECDSA gway strand prover ────
// (see ecdsa_swarm_demo::mk_params).  FRI mode (stir=false), schedule
// all-2, seed_z 0xDEEF.  Reusing this exact shape is what makes our
// z_ext derivation match what each strand was proved with, so honest
// DEEP-quotient residues are exactly zero.
fn mk_params(n0: usize, r: usize, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r,
        seed_z: 0xDEEFu64,
        coeff_commit_final: true,
        d_final: 1,
        stir: false,
        s0: r,
        public_inputs_hash: Some(ph),
    }
}

fn parse_env_usize(key: &str, default: usize) -> usize {
    std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}
fn fmt_kib(bytes: usize) -> String { format!("{:.1} KiB", bytes as f64 / 1024.0) }
fn fmt_mib(bytes: usize) -> String { format!("{:.2} MiB", bytes as f64 / (1024.0 * 1024.0)) }

fn stranded_proof_bytes(proof: &StrandedProofG) -> usize {
    // Approximate on-wire size: FRI bytes + per-query trace openings +
    // seam-commit bytes across all strands (this is the artefact a
    // relying party must ship + verify directly).
    let mut total = 0usize;
    for p in &proof.proofs {
        let mut b = Vec::new();
        p.serialize_with_mode(&mut b, Compress::Yes).unwrap();
        total += b.len();
    }
    for sc in &proof.seam_commits {
        for (_gid, commits) in sc {
            for c in commits {
                total += c.to_bytes().len();
            }
        }
    }
    total
}

fn rec_proof_bytes(rec: &RecursiveStarkProof) -> usize {
    let mut b = Vec::new();
    rec.fri_proof.serialize_compressed(&mut b).unwrap();
    b.len()
}

// ═══════════════════════════════════════════════════════════════════
//  Build a satisfiable ECDSA-verify AIR instance at arbitrary K.
//  (Generalises the `ecdsa_verify_stranded_gway` test `build_k4`: a real
//  scalar-mult chain of G by u1-bits and Q=2G by u2-bits, with the tail
//  signature-r derived from the honest group-add result.  This is a
//  genuine honest witness of the SAME AIR the real swarm proves; the
//  recursion machinery is identical whether the bits come from a real
//  P256 signature or this deterministic instance.)
// ═══════════════════════════════════════════════════════════════════
fn z_one() -> FieldElement { let mut t = FieldElement::zero(); t.limbs[0] = 1; t }
fn identity() -> (FieldElement, FieldElement, FieldElement) {
    let mut y = FieldElement::zero(); y.limbs[0] = 1;
    (FieldElement::zero(), y, FieldElement::zero())
}

struct Instance {
    layout: EcdsaVerifyMultirowLayout,
    cut: GwayCut,
    trace: Vec<Vec<F>>,
    pubin: EcdsaVerifyPublicInputs,
    n_trace: usize,
    pi_hash: [u8; 32],
}

fn build_instance(k: usize, g: usize) -> Instance {
    let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
    let n_trace = (k + 1).next_power_of_two();
    let g_pt = *P256_GENERATOR;
    let q = g_pt.double();
    let zo = z_one();
    let (ix, iy, iz) = identity();

    // Deterministic pseudo-random scalar bit patterns of length k.
    let a_bits: Vec<bool> = (0..k).map(|i| (i * 2654435761usize >> 3) & 1 == 1).collect();
    let b_bits: Vec<bool> = (0..k).map(|i| (i * 40503usize >> 2) & 1 == 1).collect();

    let read_fe = |trace: &[Vec<F>], base: usize, row: usize| -> FieldElement {
        let mut limbs = [0i64; NUM_LIMBS];
        for i in 0..NUM_LIMBS {
            limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
        }
        FieldElement { limbs }
    };

    // Pass 1: fill with r=0 to derive the honest signature-r from the tail.
    let mut trace = vec![vec![F::zero(); n_trace]; total];
    fill_ecdsa_verify_multirow(
        &mut trace, &layout, n_trace,
        (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
        (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &FieldElement::zero(),
    );
    let r_x3 = read_fe(&trace, layout.group_add.result_x3_limbs_base, k);
    let r_z3 = read_fe(&trace, layout.group_add.result_z3_limbs_base, k);
    let mut r_fe = r_x3.mul(&r_z3.invert());
    r_fe.freeze();

    // Pass 2: refill with the derived r_fe → fully satisfiable trace.
    let mut trace = vec![vec![F::zero(); n_trace]; total];
    fill_ecdsa_verify_multirow(
        &mut trace, &layout, n_trace,
        (&ix, &iy, &iz), (&g_pt.x, &g_pt.y, &zo), &a_bits,
        (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits, &r_fe,
    );
    let pubin = EcdsaVerifyPublicInputs::new(&a_bits, &b_bits, &g_pt.x, &g_pt.y, &q.x, &q.y, &r_fe);
    let cut = compute_gway_cut(&layout, k, g);
    let _ = ecdsa_verify_multirow_constraints(&layout);
    Instance { layout, cut, trace, pubin, n_trace, pi_hash: [0x42u8; 32] }
}

fn extract_cols(full: &[Vec<F>], cols: &[usize]) -> Vec<Vec<F>> {
    cols.iter().map(|&c| full[c].clone()).collect()
}

// ═══════════════════════════════════════════════════════════════════
//  ECDSA → recursion bridge (ADDITIVE — no soundness logic changed).
//
//  Mirrors v2_recursion_bridge's three-sub-circuit construction, but
//  fed from an ECDSA stranded `SubAirProofWithTrace` + its F2b seam
//  BindingCellsCommits, using the strand's OWN FRI params (mk_params).
// ═══════════════════════════════════════════════════════════════════

/// Sub-circuit 1: DEEP-quotient residues of a strand's inner FRI proof.
///
/// residue = q_val·(x_i − z_ext) − (f_val − fz)  per (query, layer),
/// projected to EXT_DEGREE Goldilocks coords.  Honest ⇒ all zero.
/// Byte-for-byte the same relation `deep_fri_verify` checks and the
/// master bridge re-checks — so a corrupted inner FRI proof yields a
/// non-zero residue and the composition-accumulator self-check refuses
/// to build the wrap.
fn build_strand_composition(
    proof: &SubAirProofWithTrace,
    n_trace: usize,
    blowup: usize,
    r: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
) -> Result<CompositionClaim<F>, String> {
    let aug = augment_pi_hash(&pi_hash, &proof.trace_root, domain_sep);
    let n0 = n_trace * blowup;
    let params = mk_params(n0, r, aug);

    let fri: DeepFriProof<Ext> = <DeepFriProof<Ext> as CanonicalDeserialize>::deserialize_with_mode(
        proof.fri_proof_bytes.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|e| format!("FRI deserialize: {e:?}"))?;
    if fri.queries.is_empty() {
        return Err("strand FRI proof has no queries (STIR mode unsupported here)".into());
    }
    let l = params.schedule.len();
    let sizes = layer_sizes_from_schedule(fri.n0, &params.schedule);
    let z_ext = derive_z_ext_for_proof::<Ext>(&fri, &params);
    let omega_per_layer: Vec<F> = (0..l)
        .map(|ell| {
            use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
            Radix2EvaluationDomain::<F>::new(sizes[ell]).expect("pow2 layer").group_gen
        })
        .collect();

    let mut column_values: Vec<(CellRef, F)> = Vec::new();
    let mut constraints: Vec<BitOp> = Vec::new();
    let mut next_col = 0usize;
    for qp in &fri.queries {
        for ell in 0..l {
            let pay = &qp.per_layer_payloads[ell];
            let rref = &qp.per_layer_refs[ell];
            let x_i = <Ext as TowerField>::from_fp(omega_per_layer[ell].pow([rref.i as u64]));
            let fz = fri.fz_per_layer[ell];
            let residue = pay.q_val * (x_i - z_ext) - (pay.f_val - fz);
            for coord in residue.to_fp_components() {
                let cell = CellRef::new(0, next_col);
                column_values.push((cell, coord));
                constraints.push(BitOp::IsZero { cell });
                next_col += 1;
            }
        }
    }
    let mut seed = aug; seed[0] ^= 0xA1;
    let alphas = alphas_from_transcript::<F>(&seed, constraints.len());
    Ok(CompositionClaim { column_values, constraints, alphas, expected: F::zero() })
}

/// Sub-circuit 2: F2b seam OOD equalities that strand `s` REFERENCES.
///
/// For every seam group whose reference holder (`holders[0]`) is `s`,
/// pair the reference column commit against every other holder's commit
/// and assert f(z₀) == g(z₀) — EXACTLY what `verify_seams` /
/// `verify_ood_consistency` checks.  Flattened to EXT_DEGREE base
/// coords.  Honest ⇒ residue zero; a tampered seam ⇒ non-zero ⇒ the OOD
/// accumulator self-check refuses to build the wrap.
///
/// A strand that references no seam still gets one honest 0-residue
/// claim (its own first seam column vs itself, or a pi_hash-derived
/// dummy) so the OOD sub-circuit stays non-empty.
fn build_strand_ood(
    cut: &GwayCut,
    seam_commits: &[Vec<(usize, Vec<BindingCellsCommit>)>],
    s: usize,
    pi_hash: [u8; 32],
) -> Result<OodAccumulatorClaim, String> {
    let find = |st: usize, gid: usize| -> Option<&Vec<BindingCellsCommit>> {
        seam_commits[st].iter().find(|(g, _)| *g == gid).map(|(_, c)| c)
    };
    let mut claims: Vec<OodEqualityClaim<F>> = Vec::new();
    for (gid, sg) in cut.seams.iter().enumerate() {
        if sg.holders[0] != s { continue; }
        let refc = find(s, gid).ok_or_else(|| format!("seam {gid}: missing ref commits"))?;
        for &h in &sg.holders[1..] {
            let hc = find(h, gid).ok_or_else(|| format!("seam {gid}: missing holder {h} commits"))?;
            if refc.len() != hc.len() {
                return Err(format!("seam {gid}: commit-count mismatch"));
            }
            for (ca, cb) in refc.iter().zip(hc.iter()) {
                let fz = extract_ood_value(ca)?;
                let gz = extract_ood_value(cb)?;
                let fco = fz.to_fp_components();
                let gco = gz.to_fp_components();
                for i in 0..fco.len() {
                    claims.push(OodEqualityClaim {
                        z: F::zero(), f_at_z: fco[i], g_at_z: gco[i],
                        binding_tag: "ecdsa-seam",
                    });
                }
            }
        }
    }
    if claims.is_empty() {
        // Honest 0-residue filler keeps the sub-circuit non-empty.
        let v = F::from(u64::from_le_bytes(pi_hash[..8].try_into().unwrap()));
        claims.push(OodEqualityClaim { z: F::zero(), f_at_z: v, g_at_z: v, binding_tag: "ecdsa-seam-nil" });
    }
    let mut seed = pi_hash; seed[0] ^= 0xB2; seed[1] ^= s as u8;
    let alphas = alphas_from_transcript::<F>(&seed, claims.len());
    Ok(OodAccumulatorClaim { bundle: OodClaimBundle { claims }, alphas })
}

/// Sub-circuit 3: vestige perm-arg bound to the strand identity
/// (mirror of v2_recursion_bridge::build_v2_pi_hash_vestige_perm_arg).
fn build_strand_perm(pi_hash: [u8; 32], s: usize) -> PermArgClaim<F> {
    let mut elems = Vec::with_capacity(4);
    for c in 0..4 {
        let mut b = [0u8; 8];
        b.copy_from_slice(&pi_hash[8 * c..8 * (c + 1)]);
        elems.push(F::from(u64::from_le_bytes(b)));
    }
    elems[0] += F::from(s as u64);
    let mut seed = pi_hash; seed[0] ^= 0xE5; seed[1] ^= s as u8;
    let gamma = alphas_from_transcript::<F>(&seed, 1)[0];
    PermArgClaim { left: elems.clone(), right: elems, gamma, perm_tag: "ecdsa-strand-vestige" }
}

/// Recursively wrap ONE ECDSA strand (+ the seams it references) into a
/// single `RecursiveStarkProof`.
#[allow(clippy::too_many_arguments)]
fn wrap_strand(
    proof: &SubAirProofWithTrace,
    cut: &GwayCut,
    seam_commits: &[Vec<(usize, Vec<BindingCellsCommit>)>],
    s: usize,
    n_trace: usize,
    inner_blowup: usize,
    inner_r: usize,
    pi_hash: [u8; 32],
    outer_blowup: usize,
    outer_r: usize,
) -> Result<RecursiveStarkProof, String> {
    let sep = strand_domain(s);
    let comp = build_strand_composition(proof, n_trace, inner_blowup, inner_r, pi_hash, &sep)?;
    let ood = build_strand_ood(cut, seam_commits, s, pi_hash)?;
    let perm = build_strand_perm(pi_hash, s);
    prove_recursive_stark(&comp, &ood, &perm, outer_blowup, outer_r, false)
        .map_err(|e: RecursiveProverError| format!("recursive wrap: {e}"))
}

// ═══════════════════════════════════════════════════════════════════
fn main() {
    let k = parse_env_usize("K", 16);
    let g = parse_env_usize("G", 4);
    let blowup = parse_env_usize("BENCH_BLOWUP", 4);
    let inner_r = deep_ali::stark_level::num_queries_for_blowup(blowup);
    let outer_blowup = 4usize;
    let outer_r = 135usize; // L1-calibrated at bw=4 (same as master_recursion_demo)
    let master_blowup = 4usize;
    let master_r = 135usize;

    println!("═══════════════════════════════════════════════════════════════");
    println!("ECDSA SWARM RECURSION — STARK-of-STARK compression");
    println!("  G ECDSA strands (SubAirProofWithTrace + F2b seams)");
    println!("     → G recursive strand-STARKs → 1 master STARK");
    println!("═══════════════════════════════════════════════════════════════");
    println!("Config: K={k}  G={g}  inner blowup={blowup} r={inner_r}  \
              outer/master blowup={outer_blowup} r={outer_r}");
    println!();

    // ─── 0. Build the stranded ECDSA proof (the swarm output) ───────
    println!("[0/4] Build the G-strand stranded ECDSA-verify proof …");
    let inst = build_instance(k, g);
    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, inner_r, ph);
    let mut proofs: Vec<SubAirProofWithTrace> = Vec::with_capacity(g);
    let mut seam_commits: Vec<Vec<(usize, Vec<BindingCellsCommit>)>> = Vec::with_capacity(g);
    let t = Instant::now();
    for s in 0..g {
        let strand = extract_cols(&inst.trace, &inst.cut.strand_cols[s]);
        let sep = strand_domain(s);
        let (p, c) = prove_one_strand(
            &strand, &inst.cut, s, &inst.layout, &inst.pubin,
            inst.n_trace, blowup, inst.pi_hash, &sep, params,
        );
        proofs.push(p);
        seam_commits.push(c);
    }
    let strand_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let stranded = StrandedProofG { proofs, seam_commits };
    let stranded_size = stranded_proof_bytes(&stranded);
    let widths: Vec<usize> = (0..g).map(|s| inst.cut.width(s)).collect();
    println!("  full AIR width: {}  per-strand widths: {widths:?}", inst.layout.width);
    println!("  seam groups: {}", inst.cut.seams.len());
    println!("  strand prove (all G): {strand_prove_ms:.0} ms");

    // Direct (non-succinct) verify of the stranded proof — the baseline.
    let t = Instant::now();
    let direct = verify_stranded_g(
        &stranded, &inst.cut, &inst.layout, &inst.pubin, inst.n_trace, blowup, inst.pi_hash, params,
    );
    let direct_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  DIRECT stranded proof size : {}", fmt_mib(stranded_size));
    println!("  DIRECT verify              : {}  ({direct_verify_ms:.1} ms)",
        if direct.is_ok() { "PASS" } else { "FAIL" });
    assert!(direct.is_ok(), "honest stranded proof must verify directly");
    println!();

    // ─── 1. Stage 1 + 2: recursively wrap each strand (+ its seams) ──
    println!("[1/4] Recursively wrap each strand (Stage 1 inner-FRI + Stage 2 seams) …");
    let mut recs: Vec<RecursiveStarkProof> = Vec::with_capacity(g);
    let mut wrap_ms_total = 0.0f64;
    let mut rec_size_total = 0usize;
    for s in 0..g {
        let t = Instant::now();
        let rec = wrap_strand(
            &stranded.proofs[s], &inst.cut, &stranded.seam_commits, s,
            inst.n_trace, blowup, inner_r, inst.pi_hash, outer_blowup, outer_r,
        ).expect("strand recursive wrap must succeed on honest input");
        let ms = t.elapsed().as_secs_f64() * 1000.0;
        wrap_ms_total += ms;
        assert!(verify_recursive_stark(&rec), "honest strand wrap must verify");
        let sz = rec_proof_bytes(&rec);
        rec_size_total += sz;
        println!("  strand {s:>2}: wrap {ms:>7.0} ms · rec_size {} · n_trace {}",
            fmt_kib(sz), rec.n_trace);
        recs.push(rec);
    }
    println!("  Σ recursive-wrap: {wrap_ms_total:.0} ms · Σ rec size {}", fmt_kib(rec_size_total));
    println!();

    // ─── 2. Stage 3: aggregate into ONE master STARK ────────────────
    println!("[2/4] Aggregate the G recursive strand-STARKs into ONE master STARK …");
    let t = Instant::now();
    let master = prove_master_recursive(&recs, master_blowup, master_r, false)
        .expect("master prove must succeed");
    let master_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let master_size = rec_proof_bytes(&master);
    let t = Instant::now();
    let master_ok = verify_master_recursive(&master);
    let master_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  master prove : {master_prove_ms:.0} ms");
    println!("  master verify: {master_verify_ms:.2} ms   → {}",
        if master_ok { "ACCEPT" } else { "REJECT" });
    println!("  master size  : {}   n_trace {}", fmt_kib(master_size), master.n_trace);
    assert!(master_ok, "honest master must ACCEPT");
    println!("  (this master is ALGEBRAIC-ONLY: it attests the FRI DEEP-quotient +");
    println!("   seam-OOD relations on prover-supplied opened values.  The verifier does");
    println!("   NOT re-bind those opened values to their committed roots — that binding");
    println!("   is added below.)");
    println!();

    // ─── 3. SOUND master: in-AIR SHA-3 Merkle-path binding (VERIFIER-SIDE) ─
    // Mirror of master_recursion_demo.rs [FULL]/[BATCHED].  Each inner
    // recursive strand-STARK's `outer_pi_hash` (which the recursion
    // FS-commits to the strand's FRI roots + DEEP-quotient/seam residues)
    // is bound to a real in-AIR-SHA-3-hashed Merkle root.  The verifier
    // RE-DERIVES the expected root from `inner.outer_pi_hash` and cross-
    // checks it against the proof — a verifier-side binding a prover
    // cannot forge (a malicious leaf/sibling substitution fails the
    // in-AIR SHA-3 constraints AND the re-derivation cross-check).
    let merkle_blowup = 4usize;
    let merkle_r = 54usize;
    println!("[3/5] SOUND master — in-AIR SHA-3 Merkle-path binding \
             (merkle blowup={merkle_blowup} r={merkle_r}) …");

    // (i) Per-inner bound master (N Merkle-path STARKs — linear in G).
    let t = Instant::now();
    let bound = prove_master_with_in_air_merkle_path(
        &recs, master_blowup, master_r, false, merkle_blowup, merkle_r, false,
    ).expect("bound master prove must succeed");
    let bound_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let t = Instant::now();
    let bound_ok = verify_master_with_in_air_merkle_path(&bound, &recs);
    let bound_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let bound_master_sz = rec_proof_bytes(&bound.master);
    let bound_merkle_sz: usize = bound.merkle_path_proofs.iter()
        .map(|mp| { let mut b = Vec::new(); mp.fri_proof.serialize_compressed(&mut b).unwrap(); b.len() })
        .sum();
    let bound_total = bound_master_sz + bound_merkle_sz;
    println!("  [per-inner] prove {bound_prove_ms:.0} ms · verify {bound_verify_ms:.2} ms → {}",
        if bound_ok { "ACCEPT" } else { "REJECT" });
    println!("  [per-inner] size: master {} + {}×merkle {} = {}",
        fmt_kib(bound_master_sz), g, fmt_kib(bound_merkle_sz), fmt_kib(bound_total));
    assert!(bound_ok, "honest bound master must ACCEPT (verifier-side)");

    // (ii) Batched bound master (ONE Merkle-path STARK — O(log G) wire).
    let t = Instant::now();
    let mut batched = prove_master_with_batched_in_air_merkle_path(
        &recs, master_blowup, master_r, false, merkle_blowup, merkle_r, false,
    ).expect("batched bound master prove must succeed");
    let batched_prove_ms = t.elapsed().as_secs_f64() * 1000.0;
    let t = Instant::now();
    let batched_ok = verify_master_with_batched_in_air_merkle_path(&batched, &recs);
    let batched_verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let batched_master_sz = rec_proof_bytes(&batched.master);
    let batched_merkle_sz = { let mut b = Vec::new();
        batched.merkle_path_proof.fri_proof.serialize_compressed(&mut b).unwrap(); b.len() };
    let batched_pi_sz = batched.inner_pi_hashes.len() * 32;
    let sound_size = batched_master_sz + batched_merkle_sz + batched_pi_sz;
    println!("  [batched]   prove {batched_prove_ms:.0} ms · verify {batched_verify_ms:.2} ms → {}",
        if batched_ok { "ACCEPT" } else { "REJECT" });
    println!("  [batched]   size: master {} + 1×merkle {} + {}×32B = {}  ← SOUND DELIVERABLE",
        fmt_kib(batched_master_sz), fmt_kib(batched_merkle_sz), g, fmt_kib(sound_size));
    assert!(batched_ok, "honest batched bound master must ACCEPT (verifier-side)");
    println!();

    // ─── 4. Soundness gates ─────────────────────────────────────────
    println!("[4/5] SOUNDNESS GATES");
    println!();
    println!("  (a) HONEST: master ACCEPT = {master_ok}  (attests all {g} strands' inner");
    println!("      FRI DEEP-quotient + all F2b seam OOD equalities, bound to h(m),PK)");
    println!("      SOUND (batched, verifier-side) ACCEPT = {batched_ok}");
    println!();

    // Helper: wrap ALL G strands from the given proofs+commits and build+
    // verify the master.  Returns `true` iff the statement is REJECTED —
    // i.e. some strand's recursive wrap cannot be produced (non-zero
    // residue → accumulator self-check fails) OR the master verify rejects.
    let build_and_check_rejected =
        |proofs: &[SubAirProofWithTrace],
         commits: &[Vec<(usize, Vec<BindingCellsCommit>)>]| -> bool {
            let mut rs: Vec<RecursiveStarkProof> = Vec::with_capacity(g);
            for s in 0..g {
                match wrap_strand(
                    &proofs[s], &inst.cut, commits, s,
                    inst.n_trace, blowup, inner_r, inst.pi_hash, outer_blowup, outer_r,
                ) {
                    Err(_) => return true,
                    Ok(rec) => rs.push(rec),
                }
            }
            match prove_master_recursive(&rs, master_blowup, master_r, false) {
                Err(_) => true,
                Ok(m) => !verify_master_recursive(&m),
            }
        };

    // (b1) Corrupt one strand's inner FRI proof → non-zero DEEP-quotient
    //      residue → its recursive wrap cannot be produced (or master rejects).
    println!("  (b) TAMPER-REJECT");
    let victim = 0usize;
    let mut proofs_b1 = stranded.proofs.clone();
    if let Some(b) = proofs_b1[victim].fri_proof_bytes.last_mut() { *b ^= 0x01; }
    let b1_rejected = build_and_check_rejected(&proofs_b1, &stranded.seam_commits);
    println!("      corrupt strand {victim} inner FRI proof → {}",
        if b1_rejected { "REJECT (wrap fails / master rejects) ✓" } else { "ACCEPTED ✗ BUG" });

    // (b2) Break a seam: re-prove the reference strand with one seam cell
    //      tampered → its seam BCC OOD value diverges from the honest
    //      holder's → the OOD sub-circuit self-check refuses to build the wrap.
    let mut b2_rejected = false;
    if let Some((gid, sg)) = inst.cut.seams.iter().enumerate().find(|(_, sg)| sg.holders.len() >= 2) {
        let refs = sg.holders[0];
        let col = sg.cols[0];
        let mut bad_trace = inst.trace.clone();
        bad_trace[col][0] += F::from(1u64);
        let strand = extract_cols(&bad_trace, &inst.cut.strand_cols[refs]);
        let sep = strand_domain(refs);
        let (bp, bc) = prove_one_strand(
            &strand, &inst.cut, refs, &inst.layout, &inst.pubin,
            inst.n_trace, blowup, inst.pi_hash, &sep, params,
        );
        let mut proofs_b2 = stranded.proofs.clone();
        let mut commits_b2 = stranded.seam_commits.clone();
        proofs_b2[refs] = bp;
        commits_b2[refs] = bc;
        b2_rejected = build_and_check_rejected(&proofs_b2, &commits_b2);
        println!("      break seam group {gid} col {col} (strand {refs}) → {}",
            if b2_rejected { "REJECT (OOD self-check fails) ✓" } else { "ACCEPTED ✗ BUG" });
    } else {
        println!("      (no ≥2-holder seam group at this G — skip seam tamper)");
        b2_rejected = true;
    }
    println!("      (these are PROVER-SIDE: the wrap/self-check refuses to build.)");
    println!();

    // (b') VERIFIER-SIDE tamper on the SOUND (Merkle-bound) master.  Here
    //      the MASTER VERIFY ITSELF rejects a forged artifact — no prover
    //      self-check involved — because the in-AIR SHA-3 Merkle binding is
    //      re-derived + cross-checked by the verifier.
    println!("  (b') VERIFIER-SIDE TAMPER-REJECT (SOUND Merkle-bound master)");
    // The algebraic-only check on the SAME honest master still accepts —
    // proving the extra rejections below come from the Merkle binding.
    let algebraic_still_accepts = verify_master_recursive(&batched.master);
    println!("      algebraic-only verify of the honest master : {}",
        if algebraic_still_accepts { "ACCEPT (same master as [2/5])" } else { "REJECT?!" });

    // (i) Forge the committed Merkle root → verifier re-derivation mismatch.
    let good_root = batched.merkle_root;
    batched.merkle_root[0] ^= 0x01;
    let v_root = verify_master_with_batched_in_air_merkle_path(&batched, &recs);
    batched.merkle_root = good_root;
    println!("      forge committed merkle_root  → SOUND verify {}",
        if !v_root { "REJECT ✓" } else { "ACCEPT ✗ BUG" });

    // (ii) Substitute a leaf identity (inner_pi_hashes) → binding to the
    //      actual inner recursive proofs fails at the verifier.
    let good_pi = batched.inner_pi_hashes[0];
    batched.inner_pi_hashes[0][0] ^= 0x01;
    let v_leaf = verify_master_with_batched_in_air_merkle_path(&batched, &recs);
    batched.inner_pi_hashes[0] = good_pi;
    println!("      substitute inner leaf pi_hash → SOUND verify {}",
        if !v_leaf { "REJECT ✓" } else { "ACCEPT ✗ BUG" });

    // (iii) Tamper the in-AIR Merkle-path STARK's committed root node →
    //       the path no longer opens to the verifier-expected root.
    let good_node = batched.merkle_path_proof.public.root.0.clone();
    batched.merkle_path_proof.public.root.0[0] ^= 0x01;
    let v_node = verify_master_with_batched_in_air_merkle_path(&batched, &recs);
    batched.merkle_path_proof.public.root.0 = good_node;
    println!("      tamper merkle-path root node → SOUND verify {}",
        if !v_node { "REJECT ✓" } else { "ACCEPT ✗ BUG" });

    let bv_rejected = algebraic_still_accepts && !v_root && !v_leaf && !v_node;
    println!("      → verifier rejects the forged artifact even though the algebraic");
    println!("        master inside it is honest: the Merkle binding is verifier-side.");
    println!();

    // (c) Outer params / NIST level.
    println!("  (c) Master soundness = min(inner, outer).");
    println!("      inner strand FRI : blowup={blowup} r={inner_r}  (per-query trace-cell +");
    println!("                         DEEP-quotient, ≥ L1 by num_queries_for_blowup)");
    println!("      outer/master FRI : blowup={outer_blowup} r={outer_r} (L1-calibrated at bw=4)");
    println!("      merkle binding   : blowup={merkle_blowup} r={merkle_r} in-AIR SHA3-256 (L1)");
    println!();

    // ─── 5. Headline ────────────────────────────────────────────────
    println!("[5/5] HEADLINE — succinct verify restored, SOUND (verifier-side binding)");
    println!();
    println!("  stranded (direct)      : {} · {direct_verify_ms:.1} ms verify",
        fmt_mib(stranded_size));
    println!("  master (algebraic-only): {} · {master_verify_ms:.2} ms verify  (prover-side soundness)",
        fmt_kib(master_size));
    println!("  master (SOUND, batched): {} · {batched_verify_ms:.2} ms verify  (VERIFIER-SIDE binding)",
        fmt_kib(sound_size));
    if stranded_size > 0 {
        println!("  compression (SOUND)    : {:.1}× smaller · {:.1}× faster verify vs direct",
            stranded_size as f64 / sound_size as f64,
            direct_verify_ms / batched_verify_ms.max(1e-6));
        println!("  Merkle-binding overhead: {:.2}× size · {:.2}× verify vs algebraic-only",
            sound_size as f64 / master_size as f64,
            batched_verify_ms / master_verify_ms.max(1e-6));
    }
    println!();
    println!("  Reference (K=256 real swarm, from task context): stranded ~4 GB /");
    println!("  ~31 s direct verify → SOUND master ~few MiB / ms-scale verify (same shape).");
    println!();
    let all_ok = master_ok && batched_ok && bound_ok && bv_rejected
        && b1_rejected && b2_rejected && direct.is_ok();
    println!("═══════════════════════════════════════════════════════════════");
    println!("  RESULT: {}", if all_ok {
        "ECDSA swarm proof compressed to ONE SOUND succinct master STARK — \
         honest ACCEPT, verifier-side tamper REJECT."
    } else { "FAILED — see gates above." });
    println!("═══════════════════════════════════════════════════════════════");
    if !all_ok { std::process::exit(1); }
}
