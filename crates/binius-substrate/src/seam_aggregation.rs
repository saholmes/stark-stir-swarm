// seam_aggregation.rs — PUBLIC-INPUT-BOUND aggregation of seam OOD eval claims
// via the accumulation fold-tree (Towers-of-Hanoi), with the Fiat–Shamir
// binding to `pi_hash` that makes the aggregated proof NON-SUBSTITUTABLE.
//
// ## What this is
// The direct streaming reconstruction of a G-way stranded proof verifies each
// seam column's OOD consistency with its own FRI opening (~2622 checks,
// ~36.5 s — the measured bottleneck, deep_ali/examples/gway_reconstruction).
// Each such check is an evaluation claim `f(z0) = v`.  This module aggregates
// N such claims into ONE via a balanced binary fold tree (accumulation.rs):
// N−1 width-independent folds → one accumulated claim, discharged by a single
// committed-decider opening (committed_decider.rs).  The verifier replays the
// folds (µs each) instead of running N FRI openings.
//
// ## The soundness anchor (why `pi_hash` must be in the transcript)
// The fold-replay is a PRE-VERIFICATION reduction; on its own it is sound for
// ANY challenges (the line-restriction fold holds for every t), so binding the
// challenges alone does NOT reject a substituted proof — a wrong-`pi` replay
// still lands on a claim true on the SAME committed polynomial.  The binding
// therefore lives in the CLAIMS, exactly as in the real STARK: the seam OOD
// evaluation point `z0` is Fiat–Shamir-derived from `pi_hash`.  So here every
// leaf claim sits at a `pi`-derived point; the verifier re-derives the expected
// points from ITS `pi_hash` and REJECTS if the proof's leaf points differ.
// Defense-in-depth: (a) each record's sub-root binds `pi_hash ‖ position ‖
// evals`; (b) the canonical root R* is a CR commitment to exactly those
// sub-roots; (c) the fold challenges derive from `H(pi_hash ‖ R* ‖ k)`.
//
// Substitute a proof built for `pi_A` into a `pi_B` verifier ⇒ the leaf points
// no longer match `derive_point(pi_B, ·)` ⇒ reject.  This is the identical
// `pi_hash`-in-`F_ext` discipline used by `verify_ood_consistency` and the
// perm-arg challenges elsewhere in the stack.
//
// Native model (like accumulation.rs): the decider is the direct O(|P|) claim
// check here; in production it is the `committed_decider` FRI opening against
// the R*-committed polynomial.  Run under `cargo test --lib seam_aggregation`.

use sha3::{Digest, Sha3_256};

use binius_field::{underlier::WithUnderlier, BinaryField128b as F, Field};

use crate::accumulation::{
    fold_prove, fold_verify, interleave, lifted_claim, mle_eval, EvalClaim, FoldProof, Record,
};

// ── transcript helpers ────────────────────────────────────────────────────

fn f_bytes(x: F) -> [u8; 16] {
    u128::from(x.to_underlier()).to_le_bytes()
}

/// Squeeze a field element out of a SHA3-256 transcript tag (low 16 bytes).
fn f_from_tag(parts: &[&[u8]]) -> F {
    let mut h = Sha3_256::new();
    for p in parts {
        h.update(p);
    }
    let d = h.finalize();
    let mut b = [0u8; 16];
    b.copy_from_slice(&d[..16]);
    F::new(u128::from_le_bytes(b))
}

/// FS-derive record `i`'s OOD evaluation point (`nvars` field elements) from
/// `pi_hash` — the multilinear analogue of the STARK's `z0 = H(pi_hash, …)`.
pub fn derive_point(pi_hash: &[u8; 32], i: usize, nvars: usize) -> Vec<F> {
    (0..nvars)
        .map(|j| {
            f_from_tag(&[
                pi_hash,
                b"seam-pt",
                &(i as u64).to_le_bytes(),
                &(j as u64).to_le_bytes(),
            ])
        })
        .collect()
}

/// Sub-root binding `pi_hash ‖ position i ‖ the record's evals` (CR commitment).
pub fn subroot(pi_hash: &[u8; 32], i: usize, evals: &[F]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(pi_hash);
    h.update((i as u64).to_le_bytes());
    for &e in evals {
        h.update(f_bytes(e));
    }
    h.finalize().into()
}

/// Canonical interleaved root: SHA3 balanced tree over the sub-roots.
pub fn canonical_root(subroots: &[[u8; 32]]) -> [u8; 32] {
    assert!(subroots.len().is_power_of_two() && !subroots.is_empty());
    let mut level: Vec<[u8; 32]> = subroots.to_vec();
    while level.len() > 1 {
        level = level
            .chunks(2)
            .map(|pair| {
                let mut h = Sha3_256::new();
                h.update(pair[0]);
                h.update(pair[1]);
                h.finalize().into()
            })
            .collect();
    }
    level[0]
}

/// FS-derive the `k`-th fold challenge from `pi_hash ‖ R* ‖ k`.
pub fn derive_challenge(pi_hash: &[u8; 32], rstar: &[u8; 32], k: usize) -> F {
    f_from_tag(&[pi_hash, rstar, b"seam-fold", &(k as u64).to_le_bytes()])
}

// ── proof object ──────────────────────────────────────────────────────────

/// A `pi`-bound aggregated seam proof: the canonical root, the per-record
/// sub-roots, the (lifted) leaf OOD claims, the balanced-tree fold messages,
/// and the accumulated root claim discharged by the decider.
pub struct SeamAggProof {
    pub rstar: [u8; 32],
    pub subroots: Vec<[u8; 32]>,
    pub leaves: Vec<EvalClaim>,
    pub fold_proofs: Vec<FoldProof>,
    pub root: EvalClaim,
}

/// PROVER: aggregate N seam records (a power of two) into one `pi`-bound proof.
/// Each record's OOD claim is re-pointed to its `pi`-derived evaluation point,
/// so the whole proof is anchored to `pi_hash`.  Returns the proof and the
/// interleaved polynomial `P` (the decider's committed object).
pub fn aggregate(pi_hash: &[u8; 32], mut records: Vec<Record>) -> (SeamAggProof, Vec<F>) {
    let nrec = records.len();
    assert!(nrec.is_power_of_two() && nrec >= 2, "record count must be a power of two ≥ 2");
    let nvars = records[0].claim.point.len();

    // (a) pi-bind each record's OOD claim: point = derive_point(pi_hash, i).
    for (i, r) in records.iter_mut().enumerate() {
        let pt = derive_point(pi_hash, i, nvars);
        let v = mle_eval(&r.evals, &pt);
        r.claim = EvalClaim { point: pt, value: v };
    }
    // (b) sub-roots (pi ‖ pos ‖ evals) and the canonical root R*.
    let subroots: Vec<[u8; 32]> =
        records.iter().enumerate().map(|(i, r)| subroot(pi_hash, i, &r.evals)).collect();
    let rstar = canonical_root(&subroots);

    // (c) interleave + lift, then balanced fold tree with pi‖R*-bound challenges.
    let m = nrec.trailing_zeros() as usize;
    let p = interleave(&records);
    let leaves: Vec<EvalClaim> =
        records.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();

    let mut level = leaves.clone();
    let mut fold_proofs: Vec<FoldProof> = Vec::new();
    let mut k = 0usize;
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        let mut i = 0;
        while i < level.len() {
            let t = derive_challenge(pi_hash, &rstar, k);
            k += 1;
            let (g, folded) = fold_prove(&p, &level[i], &level[i + 1], t);
            fold_proofs.push(g);
            next.push(folded);
            i += 2;
        }
        level = next;
    }
    let root = level.pop().unwrap();
    (SeamAggProof { rstar, subroots, leaves, fold_proofs, root }, p)
}

/// Why a `verify_aggregate` call rejected — one variant per binding check.
#[derive(Debug, PartialEq, Eq)]
pub enum AggReject {
    /// A leaf claim is not at the `pi`-derived point ⇒ proof is for another `pi`.
    PiPointMismatch,
    /// The canonical root does not commit the presented sub-roots.
    RstarMismatch,
    /// A fold message is inconsistent with its two child claims.
    FoldInconsistent,
    /// The replayed fold tree did not reproduce the asserted root.
    RootMismatch,
    /// The accumulated claim is false on the committed polynomial (decider).
    DeciderFalse,
}

/// VERIFIER: accept iff the aggregation is bound to `pi_hash` and valid.
/// `p_committed` models the decider's committed polynomial (in production, the
/// R*-committed poly opened by `committed_decider`; here the native check).
pub fn verify_aggregate(
    pi_hash: &[u8; 32],
    proof: &SeamAggProof,
    p_committed: &[F],
) -> Result<(), AggReject> {
    let nrec = proof.subroots.len();
    assert!(nrec.is_power_of_two() && proof.leaves.len() == nrec);
    let m = nrec.trailing_zeros() as usize;
    let nvars = proof.leaves[0].point.len() - m;

    // (1) PUBLIC-INPUT BINDING: every leaf claim must sit at the pi-derived OOD
    //     point (lifted with its position bits).  Wrong pi_hash ⇒ mismatch.
    for i in 0..nrec {
        let mut expect = derive_point(pi_hash, i, nvars);
        for b in 0..m {
            expect.push(if (i >> b) & 1 == 1 { F::ONE } else { F::ZERO });
        }
        if proof.leaves[i].point != expect {
            return Err(AggReject::PiPointMismatch);
        }
    }
    // (2) RECORD BINDING: R* must commit exactly the presented sub-roots.
    if canonical_root(&proof.subroots) != proof.rstar {
        return Err(AggReject::RstarMismatch);
    }
    // (3) FOLD REPLAY with pi‖R*-bound challenges; must reproduce the root.
    let mut level = proof.leaves.clone();
    let (mut fi, mut k) = (0usize, 0usize);
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        let mut i = 0;
        while i < level.len() {
            let t = derive_challenge(pi_hash, &proof.rstar, k);
            k += 1;
            let folded = fold_verify(&level[i], &level[i + 1], &proof.fold_proofs[fi], t)
                .ok_or(AggReject::FoldInconsistent)?;
            fi += 1;
            next.push(folded);
            i += 2;
        }
        level = next;
    }
    let replayed = level.pop().unwrap();
    if replayed.point != proof.root.point || replayed.value != proof.root.value {
        return Err(AggReject::RootMismatch);
    }
    // (4) DECIDER: the accumulated claim holds on the committed polynomial.
    if mle_eval(p_committed, &proof.root.point) != proof.root.value {
        return Err(AggReject::DeciderFalse);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, RngCore, SeedableRng};

    fn rand_f(rng: &mut StdRng) -> F {
        F::new(((rng.next_u64() as u128) << 64) | rng.next_u64() as u128)
    }
    /// N seam records, each a small committed column; claim points are OVERWRITTEN
    /// by `aggregate` to the pi-derived OOD points, so the input points are dummy.
    fn seam_records(nrec: usize, nvars: usize, seed: u8) -> Vec<Record> {
        let mut rng = StdRng::from_seed([seed; 32]);
        (0..nrec)
            .map(|_| {
                let evals: Vec<F> = (0..(1usize << nvars)).map(|_| rand_f(&mut rng)).collect();
                let point: Vec<F> = (0..nvars).map(|_| rand_f(&mut rng)).collect();
                let value = mle_eval(&evals, &point);
                Record { evals, claim: EvalClaim { point, value } }
            })
            .collect()
    }

    const PI_A: [u8; 32] = [0xA1; 32];
    const PI_B: [u8; 32] = [0xB2; 32];

    /// GATE: honest pi-bound aggregation VERIFIES under the same pi_hash.
    #[test]
    fn honest_aggregation_verifies() {
        for &(nrec, nvars) in &[(8usize, 5usize), (16, 6), (64, 4)] {
            let (proof, p) = aggregate(&PI_A, seam_records(nrec, nvars, 1));
            assert_eq!(
                verify_aggregate(&PI_A, &proof, &p),
                Ok(()),
                "honest aggregation must verify (N={nrec})"
            );
        }
        println!("GATE seam-agg: honest pi-bound aggregation verifies (fold tree + decider)");
    }

    /// ★ ADVERSARIAL: a proof built for PI_A is REJECTED by a PI_B verifier —
    /// the public-input substitution the whole binding exists to stop.
    #[test]
    fn wrong_pi_rejected() {
        let (proof, p) = aggregate(&PI_A, seam_records(16, 6, 2));
        // Sanity: it DOES verify under its own pi.
        assert_eq!(verify_aggregate(&PI_A, &proof, &p), Ok(()));
        // Substituted public input ⇒ leaf points no longer match ⇒ reject.
        assert_eq!(
            verify_aggregate(&PI_B, &proof, &p),
            Err(AggReject::PiPointMismatch),
            "a proof for PI_A must be REJECTED under PI_B"
        );
        // Even a single-bit flip of pi_hash is caught.
        let mut pi_flip = PI_A;
        pi_flip[0] ^= 1;
        assert_eq!(
            verify_aggregate(&pi_flip, &proof, &p),
            Err(AggReject::PiPointMismatch),
            "one-bit pi_hash change must reject"
        );
        println!("GATE seam-agg ★: proof bound to PI_A is REJECTED under PI_B / flipped pi (non-substitutable)");
    }

    /// ADVERSARIAL: tampering a leaf claim value is caught at its fold.
    #[test]
    fn tampered_leaf_value_rejected() {
        let (mut proof, p) = aggregate(&PI_A, seam_records(16, 6, 3));
        proof.leaves[7].value += F::ONE;
        assert_eq!(
            verify_aggregate(&PI_A, &proof, &p),
            Err(AggReject::FoldInconsistent),
            "a tampered seam value must be rejected at its fold"
        );
        println!("GATE seam-agg: tampered leaf value rejected at its fold");
    }

    /// ADVERSARIAL: tampering a sub-root (substituting a record's commitment)
    /// breaks the canonical-root binding.
    #[test]
    fn substituted_subroot_rejected() {
        let (mut proof, p) = aggregate(&PI_A, seam_records(16, 6, 4));
        proof.subroots[5][0] ^= 0xFF;
        assert_eq!(
            verify_aggregate(&PI_A, &proof, &p),
            Err(AggReject::RstarMismatch),
            "a substituted sub-root must break R*"
        );
        println!("GATE seam-agg: substituted record sub-root rejected (R* mismatch)");
    }

    /// ADVERSARIAL: tampering a fold message breaks the replay.
    #[test]
    fn tampered_fold_proof_rejected() {
        let (mut proof, p) = aggregate(&PI_A, seam_records(16, 6, 5));
        proof.fold_proofs[3][1] += F::ONE;
        let res = verify_aggregate(&PI_A, &proof, &p);
        assert!(
            matches!(res, Err(AggReject::FoldInconsistent) | Err(AggReject::RootMismatch)),
            "a tampered fold message must be rejected, got {res:?}"
        );
        println!("GATE seam-agg: tampered fold message rejected");
    }
}
