//! seam_rlc_bound.rs — the per-query LINEAR-COMBINATION BINDING that makes the
//! RLC seam batch (seam_rlc_batch.rs) fully sound: it ties each committed
//! component codeword R⁽ʲ⁾ to the INDIVIDUAL strand columns aᵢ, bᵢ, so a prover
//! cannot commit R⁽ʲ⁾ = 0 to fake seam agreement.
//!
//! Standard FRI-batching soundness: commit aᵢ, bᵢ (Merkle roots); draw query
//! positions Q = FS(pi_hash ‖ all roots); at each q ∈ Q check
//!     R⁽ʲ⁾(q) == Σᵢ cᵢⱼ·(aᵢ(q) − bᵢ(q))       (cᵢⱼ = (αⁱ).to_fp_components()[j])
//! with a Merkle-path verification of every opened aᵢ(q), bᵢ(q), R⁽ʲ⁾(q) against
//! its committed root.  Given this binding + R⁽ʲ⁾ low-degree (its FRI, from
//! seam_rlc_batch) + a_i/b_i low-degree (the strand proofs), R⁽ʲ⁾ ≡ Σᵢ cᵢⱼ(aᵢ−bᵢ),
//! so the R(z0)=0 consistency check is bound to the REAL columns.
//!
//! Scenarios:
//!   1. honest      — aᵢ = bᵢ, R⁽ʲ⁾ = 0; binding holds (0 = Σc·0).
//!   2. tampered    — one aᵢ ≠ bᵢ, prover commits the HONEST R⁽ʲ⁾ = Σc·dᵢ;
//!                    binding holds (R is the true LC), and the R(z0)≠0
//!                    consistency check (seam_rlc_batch) catches the mismatch.
//!   3. ★ FORGERY   — one aᵢ ≠ bᵢ, prover LIES and commits R⁽ʲ⁾ = 0 to hide it;
//!                    the per-query LC binding REJECTS (R⁽ʲ⁾(q)=0 ≠ Σc(aᵢ(q)−bᵢ(q))).
//!   4. Merkle tamper — a corrupted opening fails verify_opening.
//!
//! Run:
//!   cargo run --release --features "parallel,sha3-256" -p deep_ali \
//!     --example seam_rlc_bound

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use sha3::{Digest, Sha3_256};

use merkle::{compute_leaf_hash, MerkleChannelCfg, MerkleOpening, MerkleTreeChannel};

use deep_ali::permutation_argument::{ExtField, EXT_DEGREE};
use deep_ali::tower_field::TowerField;

const TREE_LABEL: u64 = 0x5EA_B1D; // "seam bind"
const TRACE_HASH: [u8; 32] = [0u8; 32];

fn make_col(pat: impl Fn(usize) -> u64, n_trace: usize, blowup: usize) -> Vec<F> {
    let lde_size = n_trace * blowup;
    let trace_dom = GeneralEvaluationDomain::<F>::new(n_trace).unwrap();
    let lde_dom = GeneralEvaluationDomain::<F>::new(lde_size).unwrap();
    let coeffs: Vec<F> = (0..n_trace).map(|r| F::from(pat(r))).collect();
    let mut poly = trace_dom.ifft(&coeffs);
    poly.resize(lde_size, F::zero());
    lde_dom.fft(&poly)
}

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
    ExtField::from_fp_components(&comps).expect("valid F_ext")
}

/// A committed column: its values + Merkle root (leaves = one value each).
struct Committed {
    vals: Vec<Vec<F>>,
    root: [u8; 32],
}

fn commit_col(col: &[F], cfg: &MerkleChannelCfg) -> (Committed, MerkleTreeChannel) {
    let vals: Vec<Vec<F>> = col.iter().map(|&v| vec![v]).collect();
    let mut tree = MerkleTreeChannel::new(cfg.clone(), TRACE_HASH);
    let root = tree.commit_compact(&vals);
    (Committed { vals, root }, tree)
}

/// Verify that `claimed` is the committed value at `q` under `root`.
fn verify_value(cfg: &MerkleChannelCfg, root: [u8; 32], q: usize, claimed: F, op: &MerkleOpening) -> bool {
    compute_leaf_hash(cfg, q, &[claimed]) == op.leaf
        && MerkleTreeChannel::verify_opening(cfg, root, op, &TRACE_HASH)
}

/// FS-derive `r` query positions in `[0, n)` from pi_hash ‖ all roots.
fn derive_queries(pi_hash: &[u8; 32], roots: &[[u8; 32]], r: usize, n: usize) -> Vec<usize> {
    (0..r)
        .map(|k| {
            let mut h = Sha3_256::new();
            h.update(pi_hash);
            for rt in roots {
                h.update(rt);
            }
            h.update(b"seam-query");
            h.update((k as u64).to_le_bytes());
            let d = h.finalize();
            let mut b = [0u8; 8];
            b.copy_from_slice(&d[..8]);
            (u64::from_le_bytes(b) as usize) % n
        })
        .collect()
}

/// The per-query LC binding verifier.  `a`, `b` are the committed strand columns;
/// `rj[j]` is the committed j-th component codeword; `comps[i][j] = cᵢⱼ`.
/// Returns Ok(()) iff every opened value verifies against its root AND the LC
/// R⁽ʲ⁾(q) = Σᵢ cᵢⱼ(aᵢ(q) − bᵢ(q)) holds at every query, for every component.
#[allow(clippy::too_many_arguments)]
fn lc_bind_verify(
    cfg: &MerkleChannelCfg,
    a: &[Committed],
    b: &[Committed],
    rj: &[Committed],
    a_trees: &[MerkleTreeChannel],
    b_trees: &[MerkleTreeChannel],
    rj_trees: &[MerkleTreeChannel],
    comps: &[Vec<F>],
    queries: &[usize],
) -> Result<(), String> {
    let k = a.len();
    for &q in queries {
        // Open + verify every strand value at q.
        let mut av = vec![F::zero(); k];
        let mut bv = vec![F::zero(); k];
        for i in 0..k {
            let (va, vb) = (a[i].vals[q][0], b[i].vals[q][0]);
            let opa = a_trees[i].open_compact(q, &a[i].vals);
            let opb = b_trees[i].open_compact(q, &b[i].vals);
            if !verify_value(cfg, a[i].root, q, va, &opa) {
                return Err(format!("a[{i}]({q}) Merkle-open failed"));
            }
            if !verify_value(cfg, b[i].root, q, vb, &opb) {
                return Err(format!("b[{i}]({q}) Merkle-open failed"));
            }
            av[i] = va;
            bv[i] = vb;
        }
        // For each component j: R⁽ʲ⁾(q) must equal Σᵢ cᵢⱼ(aᵢ(q) − bᵢ(q)).
        for (j, rjc) in rj.iter().enumerate() {
            let vr = rjc.vals[q][0];
            let opr = rj_trees[j].open_compact(q, &rjc.vals);
            if !verify_value(cfg, rjc.root, q, vr, &opr) {
                return Err(format!("R[{j}]({q}) Merkle-open failed"));
            }
            let mut lc = F::zero();
            for i in 0..k {
                lc += comps[i][j] * (av[i] - bv[i]);
            }
            if vr != lc {
                return Err(format!(
                    "LC BINDING VIOLATED at q={q}, component j={j}: R⁽ʲ⁾(q) ≠ Σᵢ cᵢⱼ(aᵢ−bᵢ)"
                ));
            }
        }
    }
    Ok(())
}

fn main() {
    let n_trace = 256usize;
    let blowup = 4usize;
    let n_lde = n_trace * blowup;
    let k = 8usize;
    let r = 24usize; // query repetitions
    let pi = [0x42u8; 32];
    let cfg = MerkleChannelCfg::new(vec![2usize; n_lde.trailing_zeros() as usize], TREE_LABEL);

    // RLC coefficients cᵢⱼ from α = FS(pi_hash).
    let alpha = derive_alpha(&pi);
    let mut aps = Vec::with_capacity(k);
    let mut cur = ExtField::from_fp(F::from(1u64));
    for _ in 0..k {
        aps.push(cur);
        cur = cur * alpha;
    }
    let comps: Vec<Vec<F>> = aps.iter().map(|ai| ai.to_fp_components()).collect();

    // Build (a, b) columns; `honest_r` picks the committed R⁽ʲ⁾ (true LC or a lie).
    let run = |tamper: bool, forge_zero_r: bool| -> Result<(), String> {
        let a_cols: Vec<Vec<F>> = (0..k)
            .map(|c| make_col(move |x| (c as u64 * 257 + x as u64 * 31 + 11) % 1_000_003, n_trace, blowup))
            .collect();
        let mut b_cols = a_cols.clone();
        if tamper {
            b_cols[k / 2] = make_col(|x| (99 * 257 + x as u64 * 31 + 5) % 1_000_003, n_trace, blowup);
        }
        // Honest R⁽ʲ⁾ = Σᵢ cᵢⱼ(aᵢ − bᵢ); forged = all-zeros (the attack).
        let rj_cols: Vec<Vec<F>> = (0..EXT_DEGREE)
            .map(|j| {
                if forge_zero_r {
                    vec![F::zero(); n_lde]
                } else {
                    (0..n_lde)
                        .map(|x| (0..k).fold(F::zero(), |acc, i| acc + comps[i][j] * (a_cols[i][x] - b_cols[i][x])))
                        .collect()
                }
            })
            .collect();

        let (a, a_trees): (Vec<_>, Vec<_>) = a_cols.iter().map(|c| commit_col(c, &cfg)).unzip();
        let (b, b_trees): (Vec<_>, Vec<_>) = b_cols.iter().map(|c| commit_col(c, &cfg)).unzip();
        let (rj, rj_trees): (Vec<_>, Vec<_>) = rj_cols.iter().map(|c| commit_col(c, &cfg)).unzip();

        let mut roots: Vec<[u8; 32]> = Vec::new();
        roots.extend(a.iter().map(|c| c.root));
        roots.extend(b.iter().map(|c| c.root));
        roots.extend(rj.iter().map(|c| c.root));
        let queries = derive_queries(&pi, &roots, r, n_lde);

        lc_bind_verify(&cfg, &a, &b, &rj, &a_trees, &b_trees, &rj_trees, &comps, &queries)
    };

    // Scenario 1: honest — binding holds.
    assert!(run(false, false).is_ok(), "honest LC binding must hold");
    // Scenario 2: tampered, prover commits the TRUE LC — binding still holds
    // (the mismatch is caught by the separate R(z0)≠0 consistency check).
    assert!(run(true, false).is_ok(), "true-LC binding holds even when a seam differs");
    // Scenario 3 ★: tampered, prover FORGES R⁽ʲ⁾ = 0 to hide it — binding REJECTS.
    let forge = run(true, true);
    assert!(forge.is_err(), "forged R=0 must be caught by the LC binding");

    // Scenario 4: Merkle tamper — a corrupted opening fails verification.
    let col = make_col(|x| (x as u64 * 7 + 1) % 999_983, n_trace, blowup);
    let (c0, t0) = commit_col(&col, &cfg);
    let mut op = t0.open_compact(5, &c0.vals);
    let good = verify_value(&cfg, c0.root, 5, c0.vals[5][0], &op);
    op.leaf[0] ^= 0xFF; // corrupt the opened leaf
    let bad = verify_value(&cfg, c0.root, 5, c0.vals[5][0], &op);

    println!("\n═══ per-query LC binding for the RLC seam batch (K={k}, n_lde={n_lde}, Fp{EXT_DEGREE}, r={r}) ═══");
    println!("  1. honest (aᵢ=bᵢ, R=0)                : binding holds        = {}", run(false, false).is_ok());
    println!("  2. tampered + true R=Σc(aᵢ−bᵢ)        : binding holds        = {}", run(true, false).is_ok());
    println!("  3. ★ tampered + FORGED R=0            : binding REJECTS      = {}  ({})", forge.is_err(), forge.as_ref().err().map(|e| e.as_str()).unwrap_or(""));
    println!("  4. corrupted Merkle opening           : good={good}, corrupted-rejected={}", !bad);
    println!("  ----------------------------------------------------------------");
    println!("  ⇒ R⁽ʲ⁾ is BOUND to the individual aᵢ/bᵢ commitments: a prover cannot");
    println!("    commit R⁽ʲ⁾=0 to fake seam agreement. Combined with R⁽ʲ⁾ low-degree");
    println!("    (its FRI) + R(z0)=0 (seam_rlc_batch), the RLC batch is now SOUND end-to-end.");
    println!("  soundness: {r} random queries × per-query LC over α∈Fp{EXT_DEGREE}; κ_sys unchanged.\n");
}
