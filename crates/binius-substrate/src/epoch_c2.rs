// epoch_c2.rs — model C, C2: attest record VALIDITY in the epoch (not trusted).
//
// C1 (epoch_c1) makes the commitment + membership TRUSTLESS: R*_i is each record's
// FRI commitment, R* commits them, and per query the record is provably the thing
// R*_i commits.  C2 adds VALIDITY: the epoch attests that each committed record is
// a validly-signed statement (pk, message), so the resolver need not trust that
// the aggregator native-verified the signatures.
//
// LEAF = the STATEMENT (pk_hash ‖ msg_hash), committed trustlessly via C1.  The
// VALIDITY attestation is a PLUGGABLE slot:
//   * `NativeVerified` — the aggregator native-verified the signatures (hybrid /
//     model-A validity; the deployable path today, e.g. .se ECDSA-P256 RRSIGs).
//   * `InCircuitBatch` — a proof that the in-circuit signature-verify AIR ACCEPTs
//     every statement (mldsa_verify.rs S1d / ec_verify.rs).  TRUSTLESS validity —
//     NOT yet wired: the full in-circuit ML-DSA verify (`prove_verify_mldsa_b256`)
//     is design-only, and the full ECDSA verify assembly is partial.  This slot is
//     where it plugs in; the ACCEPT-claim batch binds to R* via
//     `mldsa_statement_hash` / `mldsa_batch_root`.
//
// So statement COMMITMENT + MEMBERSHIP are trustless (C1); statement VALIDITY is
// native today and becomes trustless when the in-circuit sig-verify AIR lands.
// See docs/model-c-trustless-epoch.md §3.
//
// Run: cargo test --release --lib epoch_c2 -- --ignored

use binius_field::BinaryField128b as F;

use crate::epoch_c1::{fold_epoch_c1, open_record_c1, verify_epoch_c1, verify_record_c1, EpochProofC1, RecordOpeningC1};
use crate::epoch_fold::EpochLeaf;

/// The signed statement an epoch leaf attests: a (public key, message) pair,
/// identified by their hashes (as in `mldsa_statement_hash`).
#[derive(Clone)]
pub struct Statement {
    pub pk_hash: [u8; 32],
    pub msg_hash: [u8; 32],
}

impl Statement {
    /// The 64 statement bytes (pk_hash ‖ msg_hash).
    pub fn bytes(&self) -> [u8; 64] {
        let mut b = [0u8; 64];
        b[..32].copy_from_slice(&self.pk_hash);
        b[32..].copy_from_slice(&self.msg_hash);
        b
    }
    /// The epoch-fold leaf committing this statement: its 64 bytes as 4 B128
    /// values, zero-padded to 2^5 = 32 (the FRI needs a poly wider than the
    /// 4-value statement; the padding is deterministic and public).
    pub fn leaf(&self) -> EpochLeaf {
        let b = self.bytes();
        let mut record: Vec<F> = b
            .chunks(16)
            .map(|c| {
                let mut x = [0u8; 16];
                x.copy_from_slice(c);
                F::new(u128::from_le_bytes(x))
            })
            .collect();
        record.resize(32, F::new(0u128)); // inner_vars = 5
        EpochLeaf { record }
    }
}

/// How the epoch attests each statement's signature is valid.
pub enum ValidityAttestation {
    /// The aggregator native-verified the signatures (hybrid; validity trusted).
    NativeVerified,
    /// A proof that the in-circuit sig-verify AIR ACCEPTs every statement, bound
    /// to R* (trustless validity).  NOT yet wired — the slot for the in-circuit
    /// ML-DSA/ECDSA verify batch (mldsa_verify S1d / ec_verify).
    InCircuitBatch(Vec<u8>),
}

/// The C2 epoch proof: the trustless C1 statement commitment + the validity slot.
pub struct EpochProofC2 {
    pub c1: EpochProofC1,
    pub statements: Vec<Statement>,
    pub validity: ValidityAttestation,
}

/// AGGREGATOR: commit the statements trustlessly (C1) and attach the validity
/// attestation.  `validity` is produced by native verification (hybrid) or, once
/// wired, the in-circuit sig-verify batch.
pub fn fold_epoch_c2(statements: Vec<Statement>, validity: ValidityAttestation, zone: &str, epoch: u64) -> EpochProofC2 {
    let leaves: Vec<EpochLeaf> = statements.iter().map(|s| s.leaf()).collect();
    let c1 = fold_epoch_c1(&leaves, zone, epoch);
    EpochProofC2 { c1, statements, validity }
}

/// RESOLVER: verify the trustless statement commitment (C1) AND the validity
/// attestation.  With `InCircuitBatch` the validity is trustless (once wired);
/// with `NativeVerified` the resolver accepts the aggregator's native check
/// (hybrid) — the statements are still trustlessly committed and member-checkable.
pub fn verify_epoch_c2(proof: &EpochProofC2, zone: &str) -> Result<(), String> {
    verify_epoch_c1(&proof.c1, zone)?;
    match &proof.validity {
        ValidityAttestation::NativeVerified => Ok(()),
        ValidityAttestation::InCircuitBatch(_batch) => {
            // Trustless-validity slot: verify the in-circuit sig-verify batch proof
            // ACCEPTs every statement and binds to R* (mldsa_batch_root).  Requires
            // the in-circuit sig-verify AIR (mldsa_verify S1d / ec_verify) — pending.
            Err("model C2 (trustless validity): in-circuit sig-verify batch not yet wired — see docs/model-c-trustless-epoch.md §3".into())
        }
    }
}

/// RESOLVER (per query): the statement is trustlessly committed under R*, and
/// its bytes are revealed (membership + the C1 byte binding).
pub fn verify_record_c2(proof: &EpochProofC2, opening: &RecordOpeningC1, statement: &Statement, zone: &str) -> Result<(), String> {
    verify_record_c1(&proof.c1, opening, zone)?;
    if statement.leaf().record != opening.record {
        return Err("record-c2: statement bytes ≠ the committed leaf".into());
    }
    Ok(())
}

pub fn open_statement_c2(proof: &EpochProofC2, index: usize) -> RecordOpeningC1 {
    open_record_c1(&proof.c1, index, &proof.statements[index].leaf().record)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha3::{Digest, Sha3_256};

    fn statement(i: usize) -> Statement {
        Statement {
            pk_hash: Sha3_256::digest(format!("pk-{i}").as_bytes()).into(),
            msg_hash: Sha3_256::digest(format!("msg-{i}").as_bytes()).into(),
        }
    }

    /// C2 structure: statements committed TRUSTLESSLY (C1) + a validity slot.
    /// Native validity accepts (hybrid); the in-circuit slot reports pending.
    #[test]
    #[ignore = "C2 statement-commitment epoch (per-record FRI); run with --ignored"]
    fn c2_statement_epoch() {
        let n = 8usize;
        let statements: Vec<Statement> = (0..n).map(statement).collect();

        // NATIVE validity (hybrid, deployable): statements trustlessly committed.
        let proof = fold_epoch_c2(statements.clone(), ValidityAttestation::NativeVerified, "se", 100);
        assert_eq!(verify_epoch_c2(&proof, "se"), Ok(()), "hybrid C2 epoch must verify");

        // trustless membership: a real statement opens; a forged one is rejected.
        let op = open_statement_c2(&proof, 3);
        assert_eq!(verify_record_c2(&proof, &op, &statements[3], "se"), Ok(()), "statement 3 must open");
        assert!(
            verify_record_c2(&proof, &op, &statement(999), "se").is_err(),
            "a statement not committed under R* must be rejected"
        );

        // trustless-validity slot: the in-circuit batch path is the C2 target.
        let pending = fold_epoch_c2(statements, ValidityAttestation::InCircuitBatch(vec![]), "se", 100);
        assert!(verify_epoch_c2(&pending, "se").is_err(), "in-circuit validity is the pending C2 target");

        println!("GATE epoch-c2: statements committed trustlessly (C1) + membership; native validity verifies (hybrid), in-circuit validity slot pending (S1d).");
    }
}
