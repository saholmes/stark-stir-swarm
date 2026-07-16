// epoch_fold.rs — piece 2 (model A): fold the epoch's record leaves into one
// proof whose single public input is the zone Merkle root R*, with a resolver
// Merkle-path record opening.  See docs/recursion-fold-epoch-integration.md.
//
// MODEL A (trusted-aggregation baseline, = shipped TM-1 trust model): each
// record's validity is verified NATIVELY by the aggregator before inclusion;
// this module attests "R* commits exactly this set of records" (position-bound)
// and folds them into one accumulated claim.  The RESOLVER checks (i) the epoch
// proof once and (ii) a Merkle path per query.
//
// v1 DECIDER: the accumulated claim is discharged by a NATIVE mle_eval of the
// interleaved polynomial P (shipped in the proof).  This validates the fold +
// membership + pi-binding + adversarial rejects, but is NOT succinct (P is
// large) and does NOT bind P to R*.  The SUCCINCT resolver verify (~8-10 ms,
// ~400 KiB, no P shipped, P bound to R*) is the committed_decider piop opening
// (committed_decider.rs, MEASURED) — the documented follow-on that replaces the
// native decider here.  `verify_record` is already succinct (µs).
//
// Binding lesson carried from seam_aggregation.rs: the fold is sound for ANY
// challenge, so the anchor is (a) R* in pi_hash + (b) pi-DERIVED leaf points +
// (c) the acc_claim equality check; fold challenges are FS-derived too.
//
// Run: cargo test --release --lib epoch_fold

use sha3::{Digest, Sha3_256};

use binius_field::{underlier::WithUnderlier, BinaryField128b as F, Field};

use crate::accumulation::{accumulate, accumulate_verify, mle_eval, EvalClaim, FoldProof, Record};
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

/// FS-derive record i's OOD point (nvars field elements) from pi_hash.
fn derive_point(pi_hash: &[u8; 32], i: usize, nvars: usize) -> Vec<F> {
    (0..nvars)
        .map(|j| f_from(&[pi_hash, b"epoch-pt", &(i as u64).to_le_bytes(), &(j as u64).to_le_bytes()]))
        .collect()
}
/// FS-derive the k-th fold challenge from pi_hash ‖ R* ‖ k.
fn derive_challenge(pi_hash: &[u8; 32], rstar: &[u8; 32], k: usize) -> F {
    f_from(&[pi_hash, rstar, b"epoch-fold", &(k as u64).to_le_bytes()])
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

/// The epoch proof.  `interleaved_p` is the v1 native-decider witness; it is
/// replaced by a committed_decider opening in the succinct follow-on.
pub struct EpochProof {
    pub rstar: [u8; 32],
    pub sub_roots: Vec<[u8; 32]>,
    pub leaf_values: Vec<F>,
    pub acc_claim: EvalClaim,
    pub fold_proofs: Vec<FoldProof>,
    pub interleaved_p: Vec<F>, // v1 native decider only (NOT shipped in the succinct version)
    pub inner_vars: usize,
    pub epoch: u64,
}

/// A resolver's per-query record opening: the record + its Merkle path to R*.
pub struct RecordOpening {
    pub index: usize,
    pub record: Vec<F>,
    pub path: Vec<[u8; 32]>,
}

/// AGGREGATOR (once/epoch): fold the validated leaves into one epoch proof
/// bound to the zone Merkle root R*.
pub fn fold_epoch(leaves: &[EpochLeaf], zone: &str, epoch: u64) -> EpochProof {
    let n = leaves.len();
    assert!(n.is_power_of_two() && n >= 2, "leaf count must be a power of two ≥ 2");
    let inner_vars = leaves[0].record.len().trailing_zeros() as usize;
    assert!(leaves.iter().all(|l| l.record.len() == 1 << inner_vars), "records must share 2^inner_vars length");

    let sub_roots: Vec<[u8; 32]> = leaves.iter().enumerate().map(|(i, l)| sub_root(i, &l.record)).collect();
    let rstar = zone_root(&sub_roots);
    let pi_hash = epoch_pi_hash(zone, epoch, &rstar);

    let records: Vec<Record> = leaves
        .iter()
        .enumerate()
        .map(|(i, l)| {
            let point = derive_point(&pi_hash, i, inner_vars);
            let value = mle_eval(&l.record, &point);
            Record { evals: l.record.clone(), claim: EvalClaim { point, value } }
        })
        .collect();
    let leaf_values: Vec<F> = records.iter().map(|r| r.claim.value).collect();
    let challenges: Vec<F> = (0..n - 1).map(|k| derive_challenge(&pi_hash, &rstar, k)).collect();
    let (interleaved_p, acc_claim, fold_proofs) = accumulate(&records, &challenges);

    EpochProof { rstar, sub_roots, leaf_values, acc_claim, fold_proofs, interleaved_p, inner_vars, epoch }
}

/// RESOLVER (once/epoch): verify the epoch proof against `zone`.
pub fn verify_epoch(proof: &EpochProof, zone: &str) -> Result<(), String> {
    let n = proof.sub_roots.len();
    if !n.is_power_of_two() || n < 2 || proof.leaf_values.len() != n {
        return Err("epoch: malformed proof".into());
    }
    let m = n.trailing_zeros() as usize;
    // (1) R* commits exactly the presented sub-roots.
    if zone_root(&proof.sub_roots) != proof.rstar {
        return Err("epoch: R* does not commit the sub-roots".into());
    }
    let pi_hash = epoch_pi_hash(zone, proof.epoch, &proof.rstar);
    // (2) reconstruct the lifted leaf claims (pi-derived points + committed values).
    let claims: Vec<EvalClaim> = (0..n)
        .map(|i| {
            let mut point = derive_point(&pi_hash, i, proof.inner_vars);
            for b in 0..m {
                point.push(if (i >> b) & 1 == 1 { F::ONE } else { F::ZERO });
            }
            EvalClaim { point, value: proof.leaf_values[i] }
        })
        .collect();
    // (3) replay the fold with pi‖R*-bound challenges; must reproduce acc_claim.
    let challenges: Vec<F> = (0..n - 1).map(|k| derive_challenge(&pi_hash, &proof.rstar, k)).collect();
    let acc = accumulate_verify(&claims, &proof.fold_proofs, &challenges)
        .ok_or("epoch: fold replay inconsistent")?;
    if acc.point != proof.acc_claim.point || acc.value != proof.acc_claim.value {
        return Err("epoch: replayed root ≠ asserted acc_claim (pi/leaf binding)".into());
    }
    // (4) DECIDER (v1 native): the accumulated claim holds on the interleaved P.
    //     Follow-on: committed_decider piop opening (succinct; binds P to R*).
    if mle_eval(&proof.interleaved_p, &proof.acc_claim.point) != proof.acc_claim.value {
        return Err("epoch: decider — acc_claim false on P".into());
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

    /// ADVERSARIAL: wrong zone ⇒ pi_hash differs ⇒ fold replay ≠ acc_claim ⇒ reject.
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

    /// ADVERSARIAL: tampered sub-root breaks R*; lying leaf value breaks the fold.
    #[test]
    fn tamper_rejected() {
        let ls = leaves(16, 6, 3);
        let mut proof = fold_epoch(&ls, ZONE, EPOCH);
        // (a) tamper a sub-root ⇒ R* no longer commits them.
        let mut p_a = fold_epoch(&ls, ZONE, EPOCH);
        p_a.sub_roots[5][0] ^= 0xFF;
        assert!(verify_epoch(&p_a, ZONE).is_err(), "tampered sub-root must break R*");
        // (b) lying leaf value ⇒ fold replay inconsistent / acc mismatch.
        proof.leaf_values[7] += F::ONE;
        assert!(verify_epoch(&proof, ZONE).is_err(), "lying leaf value must reject");
        println!("GATE epoch-fold: tampered sub-root + lying leaf value rejected");
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
