// standalone_record.rs — Outcome 1: a registrant-authorized DNS record update,
// signed with ML-DSA (FIPS 204, post-quantum), submitted to the registry, and
// folded into the epoch (epoch_fold, piece 2) at the next epoch.
//
// Flow:
//   registrant : ML-DSA keygen; sign canonical(record) with the secret key
//   registry   : native ML-DSA verify the submission (model A), then commit the
//                record as an epoch_fold leaf (SHA3-256 of the canonical bytes)
//   next epoch : fold_epoch commits all verified leaves under R*
//   resolver   : verify_epoch once (~ms), verify_record per query (~µs)
//
// Model A trust: the registry native-verifies the ML-DSA signature before
// inclusion. The model-C upgrade proves the ML-DSA verify in-circuit
// (mldsa_verify.rs AIR) so the leaf carries an ACCEPT claim — no registry trust.

use sha3::{Digest, Sha3_256};

use binius_field::{BinaryField128b as F, Field};

use crate::epoch_fold::EpochLeaf;

/// A registrant's ML-DSA-signed record update.  `registrant_pk` / `mldsa_sig`
/// are the FIPS 204 public key and signature bytes (ML-DSA-44: 1312 / 2420 B).
pub struct StandaloneRecord {
    pub name: String,
    pub rr_type: u16,
    pub rdata: Vec<u8>,
    pub epoch: u64,
    pub registrant_pk: Vec<u8>,
    pub mldsa_sig: Vec<u8>,
}

impl StandaloneRecord {
    /// Canonical bytes the ML-DSA signature covers: name ‖ type ‖ rdata ‖ epoch ‖ pk.
    /// Binding the epoch + registrant pk prevents cross-epoch / cross-key replay.
    pub fn signing_bytes(name: &str, rr_type: u16, rdata: &[u8], epoch: u64, pk: &[u8]) -> Vec<u8> {
        let mut v = Vec::with_capacity(name.len() + rdata.len() + pk.len() + 16);
        v.extend_from_slice(name.as_bytes());
        v.push(0);
        v.extend_from_slice(&rr_type.to_be_bytes());
        v.extend_from_slice(&(rdata.len() as u32).to_be_bytes());
        v.extend_from_slice(rdata);
        v.extend_from_slice(&epoch.to_le_bytes());
        v.extend_from_slice(pk);
        v
    }

    pub fn canonical(&self) -> Vec<u8> {
        Self::signing_bytes(&self.name, self.rr_type, &self.rdata, self.epoch, &self.registrant_pk)
    }

    /// The FIPS commitment leaf for the epoch: SHA3-256(canonical) as B128 values.
    pub fn epoch_leaf(&self) -> EpochLeaf {
        commit_leaf(&self.canonical())
    }
}

/// SHA3-256(bytes) packed into a power-of-two vector of B128 field values.
pub fn commit_leaf(bytes: &[u8]) -> EpochLeaf {
    let d: [u8; 32] = Sha3_256::digest(bytes).into();
    let mut r: Vec<F> = d
        .chunks(16)
        .map(|c| {
            let mut b = [0u8; 16];
            b.copy_from_slice(c);
            F::new(u128::from_le_bytes(b))
        })
        .collect();
    while !r.len().is_power_of_two() {
        r.push(F::ZERO);
    }
    EpochLeaf { record: r }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::epoch_fold::{fold_epoch, open_record, verify_epoch, verify_record};
    use fips204::ml_dsa_44;
    use fips204::traits::{SerDes, Signer, Verifier};
    use std::time::Instant;

    const PK_LEN: usize = 1312;
    const SIG_LEN: usize = 2420;

    /// Reconstruct the public key from submitted bytes and native-verify the sig.
    fn registry_verify(rec: &StandaloneRecord) -> bool {
        let pk_arr: [u8; PK_LEN] = match rec.registrant_pk.clone().try_into() {
            Ok(a) => a,
            Err(_) => return false,
        };
        let sig_arr: [u8; SIG_LEN] = match rec.mldsa_sig.clone().try_into() {
            Ok(a) => a,
            Err(_) => return false,
        };
        match ml_dsa_44::PublicKey::try_from_bytes(pk_arr) {
            Ok(pk) => pk.verify(&rec.canonical(), &sig_arr, b""),
            Err(_) => false,
        }
    }

    /// ★ END-TO-END: N registrants ML-DSA-sign record updates; the registry
    /// native-verifies and folds them into the epoch; a resolver verifies the
    /// epoch once and answers membership per query.
    #[test]
    #[ignore = "ML-DSA standalone records -> epoch (fips204 keygen/sign/verify); run with --ignored"]
    fn mldsa_records_to_epoch_e2e() {
        let n = 256usize; // power-of-two registrants

        // (1) REGISTRANTS: ML-DSA keygen + sign a record update.
        let t = Instant::now();
        let records: Vec<StandaloneRecord> = (0..n)
            .map(|i| {
                let (pk, sk) = ml_dsa_44::try_keygen().expect("ml-dsa keygen");
                let pk_bytes = pk.into_bytes().to_vec();
                let name = format!("update-{i}.example.");
                let rdata = format!("v=spf1 include:_spf{i}.example ~all").into_bytes();
                let signing = StandaloneRecord::signing_bytes(&name, 16, &rdata, 100, &pk_bytes);
                let sig = sk.try_sign(&signing, b"").expect("ml-dsa sign").to_vec();
                StandaloneRecord { name, rr_type: 16, rdata, epoch: 100, registrant_pk: pk_bytes, mldsa_sig: sig }
            })
            .collect();
        let sign_ms = t.elapsed().as_secs_f64() * 1e3;

        // (2) REGISTRY: native ML-DSA verify each submission.
        let t = Instant::now();
        let all_ok = records.iter().all(registry_verify);
        let verify_ms = t.elapsed().as_secs_f64() * 1e3;
        assert!(all_ok, "all ML-DSA-signed record submissions must verify");

        // a tampered submission (flip a signature byte) must be rejected.
        let mut bad = StandaloneRecord {
            name: records[0].name.clone(),
            rr_type: records[0].rr_type,
            rdata: records[0].rdata.clone(),
            epoch: records[0].epoch,
            registrant_pk: records[0].registrant_pk.clone(),
            mldsa_sig: records[0].mldsa_sig.clone(),
        };
        bad.mldsa_sig[200] ^= 1;
        assert!(!registry_verify(&bad), "a tampered ML-DSA submission must be rejected");

        // (3) REGISTRY: fold the verified records into the epoch.
        let leaves: Vec<EpochLeaf> = records.iter().map(|r| r.epoch_leaf()).collect();
        let t = Instant::now();
        let proof = fold_epoch(&leaves, "example", 100);
        let agg_ms = t.elapsed().as_secs_f64() * 1e3;

        // (4) RESOLVER: verify the epoch once + membership per query.
        let t = Instant::now();
        assert!(verify_epoch(&proof, "example").is_ok(), "epoch of ML-DSA records must verify");
        let ve_ms = t.elapsed().as_secs_f64() * 1e3;
        let op = open_record(&leaves, n / 3);
        let t = Instant::now();
        assert!(verify_record(&proof, &op).is_ok(), "an included record must open");
        let vr_us = t.elapsed().as_secs_f64() * 1e6;
        // a record not in the epoch fails to open.
        let mut fake = open_record(&leaves, n / 3);
        fake.record = commit_leaf(b"never-submitted.example.").record;
        assert!(verify_record(&proof, &fake).is_err(), "a record not under R* must fail to open");

        println!("\n=== Standalone ML-DSA record updates → epoch (Outcome 1 → Outcome 2, L1) ===");
        println!("  registrants (ML-DSA-44 / FIPS 204, PQ)  : {n}");
        println!("  REGISTRANT: keygen + sign               : {:.1} µs/record", sign_ms * 1e3 / n as f64);
        println!("  REGISTRY:");
        println!("    native ML-DSA verify                  : {verify_ms:.1} ms total ({:.1} µs/sig)", verify_ms * 1e3 / n as f64);
        println!("    tampered submission rejected          : ✓");
        println!("    interleave + decider open             : {agg_ms:.0} ms");
        println!("  RESOLVER:");
        println!(
            "    verify_epoch (once per epoch)         : {ve_ms:.2} ms   (n_vars={}, proof {} KiB)",
            proof.n_vars,
            proof.decider_proof.len() / 1024
        );
        println!("    verify_record (per DNS query)         : {vr_us:.1} µs");
        println!("    record NOT in epoch rejected          : ✓");
        println!("  ⇒ a PQ-signed (ML-DSA) record update, native-verified by the registry, is folded");
        println!("    into the epoch and served to resolvers at DNS cost (~{ve_ms:.0} ms/epoch + µs/query).");
    }
}
