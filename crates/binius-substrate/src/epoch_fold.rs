// epoch_fold.rs — piece 2 (model A): commit the epoch's record leaves into one
// proof whose single public input is the zone Merkle root R*, verified by the
// resolver in ~ms FLAT IN N, with a per-query Merkle-path record opening.
// See docs/recursion-fold-epoch-integration.md.
//
// MODEL A (trusted-aggregation baseline, = shipped TM-1 trust model): each
// record's validity is verified NATIVELY by the aggregator before inclusion;
// this module attests "R* commits exactly this set of records" (position-bound).
//
// ARCHITECTURE — interleaved single-opening (replaces the earlier fold + O(N)
// fold-replay, which made verify_epoch O(N)).  The aggregator concatenates the
// record witnesses into one polynomial P (|P| = N·2^inner), and produces ONE
// FRI-Binius (committed_decider) opening of P at a single FS-derived point.
// The resolver verify is then ONE decider check (~ms, flat in N — MEASURED) +
// the R* commitment recompute; no fold chain, no O(N) replay.  The point is
// derived from pi_hash ‖ R* (R* fixes the records ⇒ fixes P, so the point is
// non-adaptive).  `verify_record` is a µs Merkle path.
//
// Model-A scope: the decider binds the opening to P's FRI commitment; binding
// that commitment to R* (so P provably IS the interleave of the R*-committed
// records) is the model-C upgrade (docs §5).
//
// Run: cargo test --release --lib epoch_fold

use sha3::{Digest, Sha3_256};

use binius_field::{underlier::WithUnderlier, BinaryField128b as F, Field};

use crate::accumulation::mle_eval;
use crate::decider::{decider_open_l1, decider_verify_l1, lift_b128_to_b256};
use crate::recursion::{merkle_path_verify, merkle_tree_sha3};

// ── transcript helpers ──────────────────────────────────────────────────────

fn f_bytes(x: F) -> [u8; 16] {
    u128::from(x.to_underlier()).to_le_bytes()
}
fn f_from(parts: &[&[u8]]) -> F {
    let mut h = Sha3_256::new();
    for p in parts {
        h.update(p);
    }
    let d = h.finalize();
    let mut b = [0u8; 8];
    b.copy_from_slice(&d[..8]);
    F::new(u64::from_le_bytes(b) as u128)
}
fn sha3_1(x: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(x);
    h.finalize().into()
}

/// Position-bound record commitment: SHA3(position ‖ record evals).
pub fn sub_root(pos: usize, record: &[F]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update((pos as u64).to_le_bytes());
    for &e in record {
        h.update(f_bytes(e));
    }
    h.finalize().into()
}

/// The epoch statement's public-input hash: H(zone ‖ epoch ‖ R*).
fn epoch_pi_hash(zone: &str, epoch: u64, rstar: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(zone.as_bytes());
    h.update(epoch.to_le_bytes());
    h.update(rstar);
    h.finalize().into()
}

/// FS-derive the single interleaved-opening point (`n_vars` field elements) from
/// pi_hash ‖ R*.  R* commits the records, so the point is fixed after the record
/// set is; the aggregator cannot adapt the (record-determined) P to it.
fn derive_open_point(pi_hash: &[u8; 32], rstar: &[u8; 32], n_vars: usize) -> Vec<F> {
    (0..n_vars)
        .map(|j| f_from(&[pi_hash, rstar, b"epoch-open", &(j as u64).to_le_bytes()]))
        .collect()
}

fn zone_root(sub_roots: &[[u8; 32]]) -> [u8; 32] {
    let leaves: Vec<[u8; 32]> = sub_roots.iter().map(sha3_1).collect();
    *merkle_tree_sha3(&leaves).last().unwrap().first().unwrap()
}

// ── surface ─────────────────────────────────────────────────────────────────

/// One epoch leaf: a validated record's witness (2^inner_vars B128 values).
/// Model A: validity already checked natively by the aggregator.
pub struct EpochLeaf {
    pub record: Vec<F>,
}

/// The epoch proof.  `decider_proof` is the SUCCINCT FRI-Binius opening of the
/// committed interleaved polynomial P (= all record witnesses concatenated) at
/// ONE FS-derived point — the resolver verifies it in ~ms **flat in N** (no P
/// shipped, no O(N) fold replay).
pub struct EpochProof {
    pub rstar: [u8; 32],
    pub sub_roots: Vec<[u8; 32]>,
    pub opening_value: F, // P(open_point), the value the decider opening attests
    pub decider_proof: Vec<u8>,
    pub n_vars: usize, // log2(|P|) = inner_vars + log2(N)
    pub epoch: u64,
}

/// A resolver's per-query record opening: the record + its Merkle path to R*.
pub struct RecordOpening {
    pub index: usize,
    pub record: Vec<F>,
    pub path: Vec<[u8; 32]>,
}

/// Interleave the leaf records into one polynomial P (block-concatenation:
/// P at [i·2^inner .. (i+1)·2^inner) = record i).  |P| = N · 2^inner = 2^n_vars.
fn interleave_records(leaves: &[EpochLeaf]) -> Vec<F> {
    let mut p = Vec::with_capacity(leaves.len() * leaves[0].record.len());
    for l in leaves {
        p.extend_from_slice(&l.record);
    }
    p
}

/// AGGREGATOR (once/epoch): commit the interleaved record polynomial and open it
/// ONCE at an FS-derived point — the interleaved single-opening.  No fold: the
/// resolver verify is one decider check, flat in N.
pub fn fold_epoch(leaves: &[EpochLeaf], zone: &str, epoch: u64) -> EpochProof {
    let n = leaves.len();
    assert!(n.is_power_of_two() && n >= 2, "leaf count must be a power of two ≥ 2");
    let inner_len = leaves[0].record.len();
    assert!(inner_len.is_power_of_two(), "record length must be a power of two");
    assert!(leaves.iter().all(|l| l.record.len() == inner_len), "records must share length");

    let sub_roots: Vec<[u8; 32]> = leaves.iter().enumerate().map(|(i, l)| sub_root(i, &l.record)).collect();
    let rstar = zone_root(&sub_roots);
    let pi_hash = epoch_pi_hash(zone, epoch, &rstar);

    let p = interleave_records(leaves);
    let n_vars = p.len().trailing_zeros() as usize;
    let open_point = derive_open_point(&pi_hash, &rstar, n_vars);
    let opening_value = mle_eval(&p, &open_point);

    // One succinct FRI-Binius opening of P at open_point (lifted to B256).
    let (decider_proof, value_b256, _n_vars) = decider_open_l1(&p, &open_point);
    debug_assert_eq!(value_b256, lift_b128_to_b256(opening_value), "lift must preserve eval");

    EpochProof { rstar, sub_roots, opening_value, decider_proof, n_vars, epoch }
}

/// RESOLVER (once/epoch): verify the epoch proof against `zone` — one decider
/// opening + the R* commitment check.  Cost is flat in N (~ms).
pub fn verify_epoch(proof: &EpochProof, zone: &str) -> Result<(), String> {
    let n = proof.sub_roots.len();
    if !n.is_power_of_two() || n < 2 {
        return Err("epoch: malformed proof".into());
    }
    // (1) R* commits exactly the presented sub-roots.
    if zone_root(&proof.sub_roots) != proof.rstar {
        return Err("epoch: R* does not commit the sub-roots".into());
    }
    // (2) recompute the FS opening point (pi ‖ R*) and verify the ONE decider
    //     opening: the committed interleaved P evaluates to opening_value there.
    let pi_hash = epoch_pi_hash(zone, proof.epoch, &proof.rstar);
    let open_point = derive_open_point(&pi_hash, &proof.rstar, proof.n_vars);
    let value_b256 = lift_b128_to_b256(proof.opening_value);
    if !decider_verify_l1(proof.decider_proof.clone(), &open_point, value_b256, proof.n_vars) {
        return Err("epoch: decider opening rejected".into());
    }
    Ok(())
}

/// RESOLVER (per query): verify a record is committed under the epoch's R*.
pub fn verify_record(proof: &EpochProof, opening: &RecordOpening) -> Result<(), String> {
    let sr = sub_root(opening.index, &opening.record);
    let leaf = sha3_1(&sr);
    if !merkle_path_verify(leaf, opening.index, &opening.path, proof.rstar) {
        return Err("record: Merkle path to R* invalid".into());
    }
    Ok(())
}

/// Build a resolver opening for record `index` from the epoch's leaves.
pub fn open_record(leaves: &[EpochLeaf], index: usize) -> RecordOpening {
    use crate::recursion::merkle_auth_path;
    let sub_roots: Vec<[u8; 32]> = leaves.iter().enumerate().map(|(i, l)| sub_root(i, &l.record)).collect();
    let zone_leaves: Vec<[u8; 32]> = sub_roots.iter().map(sha3_1).collect();
    let tree = merkle_tree_sha3(&zone_leaves);
    RecordOpening { index, record: leaves[index].record.clone(), path: merkle_auth_path(&tree, index) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, RngCore, SeedableRng};

    fn rand_f(rng: &mut StdRng) -> F {
        F::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128)
    }
    fn leaves(n: usize, inner_vars: usize, seed: u8) -> Vec<EpochLeaf> {
        let mut rng = StdRng::from_seed([seed; 32]);
        (0..n)
            .map(|_| EpochLeaf { record: (0..(1usize << inner_vars)).map(|_| rand_f(&mut rng)).collect() })
            .collect()
    }

    const ZONE: &str = "example.se";
    const EPOCH: u64 = 42;

    /// GATE: honest epoch verifies, and every record opens under R*.
    #[test]
    fn honest_epoch_and_records() {
        for &(n, iv) in &[(8usize, 5usize), (16, 6), (64, 4)] {
            let ls = leaves(n, iv, 1);
            let proof = fold_epoch(&ls, ZONE, EPOCH);
            assert_eq!(verify_epoch(&proof, ZONE), Ok(()), "honest epoch must verify (n={n})");
            for i in 0..n {
                assert_eq!(verify_record(&proof, &open_record(&ls, i)), Ok(()), "record {i} must open");
            }
        }
        println!("GATE epoch-fold: honest epoch verifies + all records open under R*");
    }

    /// MEASURE: the resolver-facing cost — succinct verify_epoch (once/epoch) +
    /// per-query verify_record (Merkle path).
    #[test]
    fn succinct_epoch_resolver_cost() {
        use std::time::Instant;
        let (n, iv) = (16usize, 6usize);
        let ls = leaves(n, iv, 9);
        let proof = fold_epoch(&ls, ZONE, EPOCH);
        let t = Instant::now();
        assert!(verify_epoch(&proof, ZONE).is_ok());
        let ve = t.elapsed().as_secs_f64() * 1e3;
        let op = open_record(&ls, 7);
        let t = Instant::now();
        assert!(verify_record(&proof, &op).is_ok());
        let vr = t.elapsed().as_secs_f64() * 1e6;
        println!(
            "[epoch-resolver] N={n} n_vars={} | verify_epoch {ve:.2} ms (decider {} KiB) | \
             verify_record {vr:.1} µs (Merkle path {} hashes)",
            proof.n_vars,
            proof.decider_proof.len() / 1024,
            op.path.len()
        );
    }

    /// `.se`-SCALE SWEEP: the succinct resolver verify stays ~ms as the zone
    /// grows (polylog), with a µs per-query membership check.  Ignored by
    /// default (fold_epoch is O(N) aggregator work; run with --ignored).
    #[test]
    #[ignore = "sweep/measurement (decider prove per N); run with --ignored"]
    fn se_scale_resolver_sweep() {
        use std::time::Instant;
        let inner_vars = 4usize; // small record witness (model A membership leaf)
        println!("\n=== epoch-fold .se-scale resolver cost (interleaved single-opening, inner_vars={inner_vars}, L1) ===");
        println!("| N records | n_vars | aggregator open ms | RESOLVER verify_epoch ms | proof KiB | verify_record µs |");
        for &logn in &[8usize, 10, 12, 14] {
            let n = 1usize << logn;
            let ls = leaves(n, inner_vars, 3);
            let t = Instant::now();
            let proof = fold_epoch(&ls, "se", EPOCH);
            let agg_ms = t.elapsed().as_secs_f64() * 1e3;
            let t = Instant::now();
            assert!(verify_epoch(&proof, "se").is_ok());
            let ve = t.elapsed().as_secs_f64() * 1e3;
            let op = open_record(&ls, n / 3);
            let t = Instant::now();
            assert!(verify_record(&proof, &op).is_ok());
            let vr = t.elapsed().as_secs_f64() * 1e6;
            println!(
                "| {n} | {} | {agg_ms:.0} | {ve:.2} | {} | {vr:.1} |",
                proof.n_vars,
                proof.decider_proof.len() / 1024,
            );
        }
        println!("(verify_epoch is once/epoch; verify_record is per DNS query.)");
    }

    /// ADVERSARIAL: wrong zone ⇒ pi_hash differs ⇒ FS open-point differs ⇒ decider rejects.
    #[test]
    fn wrong_zone_rejected() {
        let ls = leaves(16, 6, 2);
        let proof = fold_epoch(&ls, ZONE, EPOCH);
        assert_eq!(verify_epoch(&proof, ZONE), Ok(()));
        assert!(verify_epoch(&proof, "evil.se").is_err(), "epoch bound to a zone must reject another zone");
        let mut ep2 = fold_epoch(&ls, ZONE, EPOCH);
        ep2.epoch = EPOCH + 1; // wrong epoch (pi_hash mismatch)
        assert!(verify_epoch(&ep2, ZONE).is_err(), "wrong epoch must reject");
        println!("GATE epoch-fold: wrong zone/epoch rejected (pi-bound)");
    }

    /// ADVERSARIAL: tampered sub-root breaks R*; lying opening value fails the decider.
    #[test]
    fn tamper_rejected() {
        let ls = leaves(16, 6, 3);
        let mut proof = fold_epoch(&ls, ZONE, EPOCH);
        // (a) tamper a sub-root ⇒ R* no longer commits them.
        let mut p_a = fold_epoch(&ls, ZONE, EPOCH);
        p_a.sub_roots[5][0] ^= 0xFF;
        assert!(verify_epoch(&p_a, ZONE).is_err(), "tampered sub-root must break R*");
        // (b) lying leaf value ⇒ fold replay inconsistent / acc mismatch.
        proof.opening_value += F::ONE;
        assert!(verify_epoch(&proof, ZONE).is_err(), "lying leaf value must reject");
        println!("GATE epoch-fold: tampered sub-root + lying opening value rejected");
    }

    /// ADVERSARIAL: a record not under R* (wrong record bytes) fails to open.
    #[test]
    fn forged_record_rejected() {
        let ls = leaves(16, 6, 4);
        let proof = fold_epoch(&ls, ZONE, EPOCH);
        let mut op = open_record(&ls, 9);
        op.record[0] += F::ONE; // record not the committed one
        assert!(verify_record(&proof, &op).is_err(), "a record not under R* must fail to open");
        // right record, wrong index
        let mut op2 = open_record(&ls, 9);
        op2.index = 10;
        assert!(verify_record(&proof, &op2).is_err(), "wrong-index opening must fail");
        println!("GATE epoch-fold: forged / mis-indexed record opening rejected");
    }

    /// Position binding: permuting two records yields a DIFFERENT R*.
    #[test]
    fn permutation_changes_rstar() {
        let ls = leaves(16, 6, 5);
        let r1 = fold_epoch(&ls, ZONE, EPOCH).rstar;
        let mut ls2 = leaves(16, 6, 5);
        ls2.swap(3, 11);
        let r2 = fold_epoch(&ls2, ZONE, EPOCH).rstar;
        assert_ne!(r1, r2, "permuted records must yield a different R* (position-bound)");
        println!("GATE epoch-fold: record permutation changes R* (position-bound)");
    }
}
