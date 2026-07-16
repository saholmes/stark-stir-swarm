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
// Per-query record↔R*_i binding (trustless, µs): sub_root_i = SHA3(R*_i ‖ record_i)
// is under R* (Merkle path), AND the epoch's opened value v_i at point a equals the
// record's own MLE at a — so R*_i's committed P_i = record's MLE (Schwartz–Zippel),
// i.e. R*_i commits EXACTLY that record.  No recommit; ~40 µs/query.
//
// SOUNDNESS (both prior caveats tightened): the opening point a = FS(R*) via a
// COMMIT-ONLY pass 1 — so a follows the commitments (the aggregator cannot craft
// P_i to agree with a record only at a) — and a is over F_ext (B256), so the
// record-binding Schwartz–Zippel error is ε ≤ inner/2²⁵⁶ (full L1).
//
// Run: cargo test --release --lib epoch_c1 -- --ignored

use sha3::{Digest, Sha3_256};

use binius_field::BinaryField128b as F;

use binius_field::BinaryField128b as B128;

use crate::b256_field::B256;
use crate::b512_field::B512;
use crate::decider::{
    decider_commit_root_l1, decider_commit_root_l5, decider_open_at_ext_l1, decider_open_at_ext_l5,
    decider_verify_rooted_ext_l1, decider_verify_rooted_ext_l5, mle_eval_ext, mle_eval_ext_l5,
};
use crate::epoch_fold::EpochLeaf;
use crate::recursion::{merkle_auth_path, merkle_path_verify, merkle_tree_sha3};

fn f_bytes_of(root: &[u8; 32], record: &[F]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(root);
    for &e in record {
        h.update(u128::from(binius_field::underlier::WithUnderlier::to_underlier(e)).to_le_bytes());
    }
    h.finalize().into()
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

/// FS opening point `a` (inner_vars dims) over F_ext (B256), derived from R* —
/// so it FOLLOWS the record commitments (non-adaptive: the aggregator cannot
/// craft P_i to agree with a record only at `a`) — and over B256 the record
/// binding's Schwartz–Zippel error is ε ≤ inner/2²⁵⁶ (full L1).
fn derive_point_a(rstar: &[u8; 32], zone: &str, epoch: u64, inner_vars: usize) -> Vec<B256> {
    (0..inner_vars)
        .map(|j| {
            let lo = f_from(&[rstar, zone.as_bytes(), &epoch.to_le_bytes(), b"c1-a-lo", &(j as u64).to_le_bytes()]);
            let hi = f_from(&[rstar, zone.as_bytes(), &epoch.to_le_bytes(), b"c1-a-hi", &(j as u64).to_le_bytes()]);
            B256::from_halves(lo, hi)
        })
        .collect()
}

/// The zone tree R* = SHA3-Merkle parent over the per-record commitments {R*_i}.
fn zone_root(roots: &[[u8; 32]]) -> [u8; 32] {
    *merkle_tree_sha3(roots).last().unwrap().first().unwrap()
}

/// The trustless (C1) epoch proof: per-record FRI commitments + openings.
/// `sub_roots[i] = SHA3(R*_i ‖ record_i)` binds each record to its commitment;
/// R* is the Merkle parent over {sub_roots}.
pub struct EpochProofC1 {
    pub rstar: [u8; 32],
    pub sub_roots: Vec<[u8; 32]>, // SHA3(R*_i ‖ record_i)
    pub roots: Vec<[u8; 32]>,     // R*_i per record (FRI commitment)
    pub proofs: Vec<Vec<u8>>,     // per-record rooted opening
    pub values: Vec<B256>,        // P_i(a)
    pub inner_vars: usize,
    pub epoch: u64,
    /// FRI target soundness: 128 = NIST L1, 192 = NIST L3 (both over B256; the
    /// higher level just draws more FRI queries — the field/FS carry ≥ 256 bits).
    pub security_bits: usize,
}

/// Per-query membership opening: the record + its commitment R*_i + Merkle path.
pub struct RecordOpeningC1 {
    pub index: usize,
    pub record: Vec<F>,
    pub root: [u8; 32],
    pub path: Vec<[u8; 32]>,
}

/// AGGREGATOR (once/epoch), NIST L1: FRI-commit each record and open at `a`.
pub fn fold_epoch_c1(leaves: &[EpochLeaf], zone: &str, epoch: u64) -> EpochProofC1 {
    fold_epoch_c1_lvl(leaves, zone, epoch, 128)
}

/// AGGREGATOR at a chosen NIST level: `security_bits` = 128 (L1) or 192 (L3).
/// Both commit over B256 — the level only changes the FRI query count.
pub fn fold_epoch_c1_lvl(leaves: &[EpochLeaf], zone: &str, epoch: u64, security_bits: usize) -> EpochProofC1 {
    let n = leaves.len();
    assert!(n.is_power_of_two() && n >= 2, "leaf count must be a power of two ≥ 2");
    let inner_len = leaves[0].record.len();
    assert!(inner_len.is_power_of_two(), "record length must be a power of two");
    let inner_vars = inner_len.trailing_zeros() as usize;

    // PASS 1 (commit only): per-record roots R*_i → sub_roots → R*.  R* must
    // exist before the opening point so `a` follows the commitments.
    let roots: Vec<[u8; 32]> = leaves.iter().map(|l| decider_commit_root_l1(&l.record, security_bits)).collect();
    let sub_roots: Vec<[u8; 32]> =
        leaves.iter().zip(&roots).map(|(l, r)| f_bytes_of(r, &l.record)).collect();
    let rstar = zone_root(&sub_roots);

    // PASS 2 (open at the R*-bound F_ext point a): per-record openings at `a`.
    let a = derive_point_a(&rstar, zone, epoch, inner_vars);
    let mut proofs = Vec::with_capacity(n);
    let mut values = Vec::with_capacity(n);
    for (l, &root) in leaves.iter().zip(&roots) {
        let (root2, proof, v, _nv) = decider_open_at_ext_l1(&l.record, &a, security_bits);
        debug_assert_eq!(root2, root, "commit is deterministic across passes");
        proofs.push(proof);
        values.push(v);
    }
    EpochProofC1 { rstar, sub_roots, roots, proofs, values, inner_vars, epoch, security_bits }
}

/// RESOLVER (once/epoch): TRUSTLESS verify — R* commits exactly {R*_i}, and each
/// R*_i is a valid FRI commitment opening to P_i(a).  N per-record verifies.
pub fn verify_epoch_c1(proof: &EpochProofC1, zone: &str) -> Result<(), String> {
    let n = proof.roots.len();
    if !n.is_power_of_two() || n < 2 || proof.proofs.len() != n || proof.values.len() != n || proof.sub_roots.len() != n {
        return Err("epoch-c1: malformed proof".into());
    }
    if zone_root(&proof.sub_roots) != proof.rstar {
        return Err("epoch-c1: R* does not commit the sub-roots".into());
    }
    let a = derive_point_a(&proof.rstar, zone, proof.epoch, proof.inner_vars);
    for i in 0..n {
        if !decider_verify_rooted_ext_l1(proof.roots[i], proof.proofs[i].clone(), &a, proof.values[i], proof.inner_vars, proof.security_bits) {
            return Err(format!("epoch-c1: record {i} opening/root check failed"));
        }
    }
    Ok(())
}

/// RESOLVER (per query): TRUSTLESS membership — the record is committed under R*
/// AND R*_i (the epoch-verified FRI commitment) commits THIS record's bytes.
/// (1) sub_root = SHA3(R*_i ‖ record) is under R* (Merkle path); (2) the epoch's
/// opened value at `a` equals the record's own MLE at `a` — so R*_i's committed
/// P_i = record's MLE (Schwartz–Zippel), i.e. R*_i commits exactly this record.
pub fn verify_record_c1(proof: &EpochProofC1, opening: &RecordOpeningC1, zone: &str) -> Result<(), String> {
    let i = opening.index;
    if proof.roots.get(i) != Some(&opening.root) {
        return Err("record-c1: R*_i ≠ epoch's committed root".into());
    }
    let sub_root = f_bytes_of(&opening.root, &opening.record);
    if proof.sub_roots.get(i) != Some(&sub_root) {
        return Err("record-c1: SHA3(R*_i ‖ record) ≠ epoch's sub-root".into());
    }
    if !merkle_path_verify(sub_root, i, &opening.path, proof.rstar) {
        return Err("record-c1: Merkle path to R* invalid".into());
    }
    // Byte binding: R*_i's committed poly agrees with this record's MLE at the
    // R*-derived F_ext point a (ε ≤ inner/2²⁵⁶).
    let a = derive_point_a(&proof.rstar, zone, proof.epoch, proof.inner_vars);
    if mle_eval_ext(&opening.record, &a) != proof.values[i] {
        return Err("record-c1: record's MLE(a) ≠ R*_i's opened value — R*_i does not commit this record".into());
    }
    Ok(())
}

pub fn open_record_c1(proof: &EpochProofC1, index: usize, record: &[F]) -> RecordOpeningC1 {
    let tree = merkle_tree_sha3(&proof.sub_roots);
    RecordOpeningC1 {
        index,
        record: record.to_vec(),
        root: proof.roots[index],
        path: merkle_auth_path(&tree, index),
    }
}

// ============================================================================
// L5 (B512 @ 256-bit): the trustless C1 epoch over the B512 tower field.  Same
// construction as above — per-record FRI commitment R*_i, zone tree R*, N rooted
// openings at a shared point a — but every field-valued step (commitment, the
// opening point, the record-binding MLE eval) is over B512 (F5).  The R*/Merkle
// scaffolding (sub_roots, zone_root, f_bytes_of, paths) is field-agnostic and
// reused verbatim, as is `RecordOpeningC1`.  ε_bind ≤ inner/2⁵¹² (past L5's 256).
// ============================================================================

/// FS opening point `a` over B512 — four hash-derived B128 limbs per dimension
/// (B512 = (B256,B256), B256 = (B128,B128)), derived from R* so it follows the
/// commitments (non-adaptive), same as the B256 `derive_point_a`.
fn derive_point_a_l5(rstar: &[u8; 32], zone: &str, epoch: u64, inner_vars: usize) -> Vec<B512> {
    (0..inner_vars)
        .map(|j| {
            let jb = (j as u64).to_le_bytes();
            let z = zone.as_bytes();
            let e = epoch.to_le_bytes();
            let ll = f_from(&[rstar, z, &e, b"c1l5-a-ll", &jb]);
            let lh = f_from(&[rstar, z, &e, b"c1l5-a-lh", &jb]);
            let hl = f_from(&[rstar, z, &e, b"c1l5-a-hl", &jb]);
            let hh = f_from(&[rstar, z, &e, b"c1l5-a-hh", &jb]);
            B512::from_halves(B256::from_halves(ll, lh), B256::from_halves(hl, hh))
        })
        .collect()
}

/// The trustless (C1) epoch proof at L5 — per-record B512 FRI commitments + openings.
pub struct EpochProofC1L5 {
    pub rstar: [u8; 32],
    pub sub_roots: Vec<[u8; 32]>,
    pub roots: Vec<[u8; 32]>,
    pub proofs: Vec<Vec<u8>>,
    pub values: Vec<B512>, // P_i(a) over B512
    pub inner_vars: usize,
    pub epoch: u64,
    pub security_bits: usize, // 256 (NIST L5)
}

/// AGGREGATOR (once/epoch), NIST L5: B512 FRI-commit each record and open at `a`.
pub fn fold_epoch_c1_l5(leaves: &[EpochLeaf], zone: &str, epoch: u64) -> EpochProofC1L5 {
    let security_bits = 256usize;
    let n = leaves.len();
    assert!(n.is_power_of_two() && n >= 2, "leaf count must be a power of two ≥ 2");
    let inner_len = leaves[0].record.len();
    assert!(inner_len.is_power_of_two(), "record length must be a power of two");
    let inner_vars = inner_len.trailing_zeros() as usize;

    let roots: Vec<[u8; 32]> = leaves.iter().map(|l| decider_commit_root_l5(&l.record, security_bits)).collect();
    let sub_roots: Vec<[u8; 32]> =
        leaves.iter().zip(&roots).map(|(l, r)| f_bytes_of(r, &l.record)).collect();
    let rstar = zone_root(&sub_roots);

    let a = derive_point_a_l5(&rstar, zone, epoch, inner_vars);
    let mut proofs = Vec::with_capacity(n);
    let mut values = Vec::with_capacity(n);
    for (l, &root) in leaves.iter().zip(&roots) {
        let (root2, proof, v, _nv) = decider_open_at_ext_l5(&l.record, &a, security_bits);
        debug_assert_eq!(root2, root, "commit is deterministic across passes");
        proofs.push(proof);
        values.push(v);
    }
    EpochProofC1L5 { rstar, sub_roots, roots, proofs, values, inner_vars, epoch, security_bits }
}

/// RESOLVER (once/epoch), L5: TRUSTLESS verify — N per-record B512 FRI openings.
pub fn verify_epoch_c1_l5(proof: &EpochProofC1L5, zone: &str) -> Result<(), String> {
    let n = proof.roots.len();
    if !n.is_power_of_two() || n < 2 || proof.proofs.len() != n || proof.values.len() != n || proof.sub_roots.len() != n {
        return Err("epoch-c1-l5: malformed proof".into());
    }
    if zone_root(&proof.sub_roots) != proof.rstar {
        return Err("epoch-c1-l5: R* does not commit the sub-roots".into());
    }
    let a = derive_point_a_l5(&proof.rstar, zone, proof.epoch, proof.inner_vars);
    for i in 0..n {
        if !decider_verify_rooted_ext_l5(proof.roots[i], proof.proofs[i].clone(), &a, proof.values[i], proof.inner_vars, proof.security_bits) {
            return Err(format!("epoch-c1-l5: record {i} opening/root check failed"));
        }
    }
    Ok(())
}

/// RESOLVER (per query), L5: TRUSTLESS membership + record↔R*_i byte binding over B512.
pub fn verify_record_c1_l5(proof: &EpochProofC1L5, opening: &RecordOpeningC1, zone: &str) -> Result<(), String> {
    let i = opening.index;
    if proof.roots.get(i) != Some(&opening.root) {
        return Err("record-c1-l5: R*_i ≠ epoch's committed root".into());
    }
    let sub_root = f_bytes_of(&opening.root, &opening.record);
    if proof.sub_roots.get(i) != Some(&sub_root) {
        return Err("record-c1-l5: SHA3(R*_i ‖ record) ≠ epoch's sub-root".into());
    }
    if !merkle_path_verify(sub_root, i, &opening.path, proof.rstar) {
        return Err("record-c1-l5: Merkle path to R* invalid".into());
    }
    let a = derive_point_a_l5(&proof.rstar, zone, proof.epoch, proof.inner_vars);
    if mle_eval_ext_l5(&opening.record, &a) != proof.values[i] {
        return Err("record-c1-l5: record's MLE(a) ≠ R*_i's opened value — R*_i does not commit this record".into());
    }
    Ok(())
}

pub fn open_record_c1_l5(proof: &EpochProofC1L5, index: usize, record: &[F]) -> RecordOpeningC1 {
    let tree = merkle_tree_sha3(&proof.sub_roots);
    RecordOpeningC1 {
        index,
        record: record.to_vec(),
        root: proof.roots[index],
        path: merkle_auth_path(&tree, index),
    }
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
            let op = open_record_c1(&proof, n / 2, &ls[n / 2].record);
            let t = Instant::now();
            assert!(verify_record_c1(&proof, &op, "se").is_ok(), "record must open");
            let vr = t.elapsed().as_secs_f64() * 1e6;
            // ★ record↔R*_i BYTE binding: claim a DIFFERENT record for the same slot ⇒
            //   sub_root mismatch AND MLE(a) ≠ opened value ⇒ rejected.
            let mut lying = open_record_c1(&proof, n / 2, &ls[n / 2].record);
            lying.record[0] += F::ONE;
            assert!(verify_record_c1(&proof, &lying, "se").is_err(), "a record not committed by R*_i must be rejected");
            // a tampered record commits to a different R*_i ⇒ different R*.
            let mut bad_leaves = leaves(n, iv, 7);
            bad_leaves[1].record[0] += F::ONE;
            let bad = fold_epoch_c1(&bad_leaves, "se", 100);
            assert_ne!(bad.rstar, proof.rstar, "a tampered record must change R*");
            // substituting a foreign R*_i breaks the rooted opening.
            let mut forged = fold_epoch_c1(&ls, "se", 100);
            forged.roots[1] = bad.roots[1];
            assert!(verify_epoch_c1(&forged, "se").is_err(), "a substituted R*_i must be rejected");
            println!("| {n} | {iv} | {agg:.0} | {ve:.1} | {vr:.1} |");
        }
        println!("(N per-record FRI verifies ⇒ O(N) resolver verify — the trustless cost. Model A is ~ms.)");
    }

    /// GATE + MEASURE: the trustless C1 epoch at NIST L1 (128-bit) vs L3 (192-bit).
    /// Both commit over B256; L3 draws more FRI queries, so the proof is larger and
    /// verify slower — the security↔cost curve, on the same trustless construction.
    #[test]
    #[ignore = "C1 trustless epoch at L1 vs L3 (per-record FRI); run with --ignored"]
    fn c1_trustless_epoch_l1_vs_l3() {
        println!("\n=== C1 trustless epoch: NIST L1 (128) vs L3 (192), same B256 construction ===");
        println!("| level | bits | N | aggregator ms | verify_epoch ms | verify_record µs | proof bytes |");
        // inner_vars=10 (1024-eval record) is wide enough that the FRI folds and runs a
        // real query phase, so the 128- vs 192-bit query counts (309 vs 463) actually
        // diverge.  (At iv=5 the MLE fully folds with no query phase, so security_bits is
        // moot — a small-instance artifact, not the deployment width.)
        let n = 8usize;
        let iv = 10usize;
        let ls = leaves(n, iv, 11);
        for &(name, bits) in &[("L1", 128usize), ("L3", 192usize)] {
            let t = Instant::now();
            let proof = fold_epoch_c1_lvl(&ls, "se", 200, bits);
            let agg = t.elapsed().as_secs_f64() * 1e3;
            assert_eq!(proof.security_bits, bits);
            let t = Instant::now();
            assert!(verify_epoch_c1(&proof, "se").is_ok(), "honest {name} epoch must verify");
            let ve = t.elapsed().as_secs_f64() * 1e3;
            let op = open_record_c1(&proof, n / 2, &ls[n / 2].record);
            let t = Instant::now();
            assert!(verify_record_c1(&proof, &op, "se").is_ok(), "{name} record must open");
            let vr = t.elapsed().as_secs_f64() * 1e6;
            let bytes: usize = proof.proofs.iter().map(|p| p.len()).sum();
            // a tampered record still breaks R* at L3 (soundness preserved).
            let mut bad = leaves(n, iv, 11);
            bad[1].record[0] += F::ONE;
            let badp = fold_epoch_c1_lvl(&bad, "se", 200, bits);
            assert_ne!(badp.rstar, proof.rstar, "{name}: tampered record must change R*");
            println!("| {name} | {bits} | {n} | {agg:.0} | {ve:.1} | {vr:.1} | {bytes} |");
        }
        println!("(Same trustless C1 construction over B256; L3's extra FRI queries buy 192-bit soundness.)");
    }

    /// GATE + MEASURE: the trustless C1 epoch at NIST L5 (256-bit) over B512.
    /// Same construction as L1/L3 but every field-valued step is over the B512
    /// tower field.  Soundness preserved: a tampered record still breaks R*, and
    /// a foreign R*_i / lying record are rejected — now at the 256-bit level.
    #[test]
    #[ignore = "C1 trustless epoch at L5 over B512 (per-record FRI); run with --ignored"]
    fn c1_trustless_epoch_l5() {
        println!("\n=== C1 trustless epoch: NIST L5 (256) over B512 ===");
        println!("| level | field | bits | N | aggregator ms | verify_epoch ms | verify_record µs | proof bytes |");
        let n = 8usize;
        let iv = 10usize; // wide enough that the FRI folds + runs a real query phase
        let ls = leaves(n, iv, 13);
        let t = Instant::now();
        let proof = fold_epoch_c1_l5(&ls, "se", 300);
        let agg = t.elapsed().as_secs_f64() * 1e3;
        assert_eq!(proof.security_bits, 256);
        let t = Instant::now();
        assert!(verify_epoch_c1_l5(&proof, "se").is_ok(), "honest L5 epoch must verify");
        let ve = t.elapsed().as_secs_f64() * 1e3;
        let op = open_record_c1_l5(&proof, n / 2, &ls[n / 2].record);
        let t = Instant::now();
        assert!(verify_record_c1_l5(&proof, &op, "se").is_ok(), "L5 record must open");
        let vr = t.elapsed().as_secs_f64() * 1e6;
        let bytes: usize = proof.proofs.iter().map(|p| p.len()).sum();
        println!("| L5 | B512 | 256 | {n} | {agg:.0} | {ve:.1} | {vr:.1} | {bytes} |");

        // ★ soundness at L5: a lying record for the same slot is rejected
        //   (sub_root mismatch AND MLE(a) ≠ opened value over B512).
        let mut lying = open_record_c1_l5(&proof, n / 2, &ls[n / 2].record);
        lying.record[0] += F::ONE;
        assert!(verify_record_c1_l5(&proof, &lying, "se").is_err(), "a record not committed by R*_i must be rejected");
        // a tampered record changes R*; a substituted R*_i breaks the rooted opening.
        let mut bad = leaves(n, iv, 13);
        bad[1].record[0] += F::ONE;
        let badp = fold_epoch_c1_l5(&bad, "se", 300);
        assert_ne!(badp.rstar, proof.rstar, "a tampered record must change R* at L5");
        let mut forged = fold_epoch_c1_l5(&ls, "se", 300);
        forged.roots[1] = badp.roots[1];
        assert!(verify_epoch_c1_l5(&forged, "se").is_err(), "a substituted R*_i must be rejected at L5");
        println!("(Trustless C1 over B512: commitment + membership at NIST L5, soundness preserved. ε_bind ≤ inner/2⁵¹².)");
    }
}
