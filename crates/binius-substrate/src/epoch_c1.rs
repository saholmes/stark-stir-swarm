// epoch_c1.rs — model C, C1: TRUSTLESS P↔R* binding via per-record FRI commitments.
//
// Model A (epoch_fold) commits the interleaved P with the decider's own root, so
// the resolver trusts P = interleave(R*'s records).  C1 removes that trust: each
// record P_i is FRI-committed to its OWN root R*_i; the zone tree R* is the
// Merkle parent over {R*_i}; and the epoch is verified as N per-record rooted
// openings at a shared point a.  So every committed P_i provably underlies R*_i,
// and R* commits exactly them — no aggregator trust for P↔R*.
//
// This is the decomposition P(a,b) = Σ_i eq(b,i)·P_i(a) made explicit: the
// R*-committed opening IS the set of batch-local openings P_i(a) against R*_i.
// COST: N per-record FRI verifies ⇒ ~seconds/epoch (the honest ~9–13 s at scale),
// vs model A's ~ms — the trust↔cost tradeoff (docs/model-c-trustless-epoch.md §1).
//
// SCOPE (first C1 step): this wires + measures the epoch-level P↔R* binding.  The
// remaining C1 sub-problem is CHEAP per-query record↔R*_i binding: R*_i is a FRI
// commitment, so binding a record to it at µs cost (not recommitting ~ms/query)
// needs a batched record-position opening — noted, not yet built.
//
// Run: cargo test --release --lib epoch_c1 -- --ignored

use sha3::{Digest, Sha3_256};

use binius_field::BinaryField128b as F;

use crate::b256_field::B256;
use crate::decider::{decider_commit_open_l1, decider_verify_rooted_l1, lift_b128_to_b256};
use crate::epoch_fold::EpochLeaf;
use crate::recursion::{merkle_auth_path, merkle_path_verify, merkle_tree_sha3};

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

/// FS opening point `a` (inner_vars dims) from zone ‖ epoch.  (Prototype: bound
/// to the public statement; the production point is FS from R* via a commit-only
/// pass so it follows the commitments.)
fn derive_point_a(zone: &str, epoch: u64, inner_vars: usize) -> Vec<F> {
    (0..inner_vars)
        .map(|j| f_from(&[zone.as_bytes(), &epoch.to_le_bytes(), b"c1-a", &(j as u64).to_le_bytes()]))
        .collect()
}

/// The zone tree R* = SHA3-Merkle parent over the per-record commitments {R*_i}.
fn zone_root(roots: &[[u8; 32]]) -> [u8; 32] {
    *merkle_tree_sha3(roots).last().unwrap().first().unwrap()
}

/// The trustless (C1) epoch proof: per-record FRI commitments + openings.
pub struct EpochProofC1 {
    pub rstar: [u8; 32],
    pub roots: Vec<[u8; 32]>,   // R*_i per record
    pub proofs: Vec<Vec<u8>>,   // per-record rooted opening
    pub values: Vec<B256>,      // P_i(a)
    pub inner_vars: usize,
    pub epoch: u64,
}

/// Per-query membership opening: the record's commitment R*_i + Merkle path to R*.
pub struct RecordOpeningC1 {
    pub index: usize,
    pub root: [u8; 32],
    pub path: Vec<[u8; 32]>,
}

/// AGGREGATOR (once/epoch): FRI-commit each record and open at the shared point a.
pub fn fold_epoch_c1(leaves: &[EpochLeaf], zone: &str, epoch: u64) -> EpochProofC1 {
    let n = leaves.len();
    assert!(n.is_power_of_two() && n >= 2, "leaf count must be a power of two ≥ 2");
    let inner_len = leaves[0].record.len();
    assert!(inner_len.is_power_of_two(), "record length must be a power of two");
    let inner_vars = inner_len.trailing_zeros() as usize;
    let a = derive_point_a(zone, epoch, inner_vars);

    let mut roots = Vec::with_capacity(n);
    let mut proofs = Vec::with_capacity(n);
    let mut values = Vec::with_capacity(n);
    for l in leaves {
        let (root, proof, v, _nv) = decider_commit_open_l1(&l.record, &a);
        roots.push(root);
        proofs.push(proof);
        values.push(v);
    }
    let rstar = zone_root(&roots);
    EpochProofC1 { rstar, roots, proofs, values, inner_vars, epoch }
}

/// RESOLVER (once/epoch): TRUSTLESS verify — R* commits exactly {R*_i}, and each
/// R*_i is a valid FRI commitment opening to P_i(a).  N per-record verifies.
pub fn verify_epoch_c1(proof: &EpochProofC1, zone: &str) -> Result<(), String> {
    let n = proof.roots.len();
    if !n.is_power_of_two() || n < 2 || proof.proofs.len() != n || proof.values.len() != n {
        return Err("epoch-c1: malformed proof".into());
    }
    if zone_root(&proof.roots) != proof.rstar {
        return Err("epoch-c1: R* does not commit the per-record roots".into());
    }
    let a = derive_point_a(zone, proof.epoch, proof.inner_vars);
    for i in 0..n {
        if !decider_verify_rooted_l1(proof.roots[i], proof.proofs[i].clone(), &a, proof.values[i], proof.inner_vars) {
            return Err(format!("epoch-c1: record {i} opening/root check failed"));
        }
    }
    Ok(())
}

/// RESOLVER (per query): the record's commitment R*_i is under R*.  (See the SCOPE
/// note: binding R*_i to the record's bytes at µs cost is the remaining C1 piece.)
pub fn verify_record_c1(proof: &EpochProofC1, opening: &RecordOpeningC1) -> Result<(), String> {
    if !merkle_path_verify(opening.root, opening.index, &opening.path, proof.rstar) {
        return Err("record-c1: Merkle path to R* invalid".into());
    }
    if proof.roots.get(opening.index) != Some(&opening.root) {
        return Err("record-c1: root ≠ epoch's committed R*_i".into());
    }
    Ok(())
}

pub fn open_record_c1(proof: &EpochProofC1, index: usize) -> RecordOpeningC1 {
    let tree = merkle_tree_sha3(&proof.roots);
    RecordOpeningC1 { index, root: proof.roots[index], path: merkle_auth_path(&tree, index) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use binius_field::Field;
    use rand::{rngs::StdRng, RngCore, SeedableRng};
    use std::time::Instant;

    fn leaves(n: usize, inner_vars: usize, seed: u8) -> Vec<EpochLeaf> {
        let mut rng = StdRng::from_seed([seed; 32]);
        (0..n)
            .map(|_| EpochLeaf {
                record: (0..(1usize << inner_vars))
                    .map(|_| F::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128))
                    .collect(),
            })
            .collect()
    }

    /// GATE + MEASURE: the trustless C1 epoch verifies (N per-record FRI openings
    /// bound to R*); a tampered record breaks it; cost is O(N) (the ~seconds
    /// trust↔cost tradeoff vs model A's ~ms).
    #[test]
    #[ignore = "C1 trustless epoch (N per-record FRI commit+verify, O(N)); run with --ignored"]
    fn c1_trustless_epoch() {
        println!("\n=== C1 trustless epoch: per-record FRI commitments bound to R* (L1) ===");
        println!("| N records | inner_vars | aggregator ms | RESOLVER verify_epoch ms | verify_record µs |");
        for &(n, iv) in &[(4usize, 5usize), (8, 5), (16, 5)] {
            let ls = leaves(n, iv, 7);
            let t = Instant::now();
            let proof = fold_epoch_c1(&ls, "se", 100);
            let agg = t.elapsed().as_secs_f64() * 1e3;
            let t = Instant::now();
            assert!(verify_epoch_c1(&proof, "se").is_ok(), "honest C1 epoch must verify (N={n})");
            let ve = t.elapsed().as_secs_f64() * 1e3;
            let op = open_record_c1(&proof, n / 2);
            let t = Instant::now();
            assert!(verify_record_c1(&proof, &op).is_ok(), "record must open");
            let vr = t.elapsed().as_secs_f64() * 1e6;
            // a tampered record commits to a different R*_i ⇒ R* recompute / opening fails.
            let mut bad_leaves = leaves(n, iv, 7);
            bad_leaves[1].record[0] += F::ONE;
            let bad = fold_epoch_c1(&bad_leaves, "se", 100);
            assert_ne!(bad.rstar, proof.rstar, "a tampered record must change R*");
            // and swapping a proof's root vs a foreign one breaks the rooted opening.
            let mut forged = fold_epoch_c1(&ls, "se", 100);
            forged.roots[1] = bad.roots[1];
            assert!(verify_epoch_c1(&forged, "se").is_err(), "a substituted R*_i must be rejected");
            println!("| {n} | {iv} | {agg:.0} | {ve:.1} | {vr:.1} |");
        }
        println!("(N per-record FRI verifies ⇒ O(N) resolver verify — the trustless cost. Model A is ~ms.)");
    }
}
