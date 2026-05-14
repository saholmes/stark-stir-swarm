//! .se HNPL Phase 2 epoch-package format — paper §IV-B.
//!
//! Self-contained binary artefact that an edge resolver consumes to
//! serve DNS queries OFFLINE against a STARK-attested, ML-DSA-signed
//! corpus.  Contains:
//!
//!   1. ML-DSA-65 (FIPS 204) authority public key + signature
//!   2. Inner shard STARK π_inner (HashRollup AIR over verified records)
//!   3. Outer rollup STARK π_outer (commits inner pi_hash to epoch root)
//!   4. Merkle tree levels (for offline inclusion proofs at query time)
//!   5. Record metadata (domain, type, algorithm, leaf data)
//!
//! The ML-DSA signature covers a single binding hash
//!
//!     H = SHA3-256(outer.root_f0 ‖ inner.pi_hash ‖ merkle_root ‖
//!                  epoch_t ‖ epoch_seq ‖ epoch_prev)
//!
//! that ties every component of the package together (paper Def. 1).
//!
//! # Usage
//!
//!   - **Phase 1 prover** (e.g. `se_zone_demo` example) builds a
//!     `SeEpochPackage` after running native-verify + STARK-prove +
//!     ML-DSA-sign, then writes it to disk via [`save_to_file`].
//!   - **Phase 3 edge** (e.g. `se_offline_resolver` example) reads it
//!     via [`load_from_file`], verifies via [`verify`], and answers
//!     queries via [`resolve`] — NO network access required after
//!     the one-time epoch package load.

use std::path::Path;

use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

use crate::dns::{DnsRecord, merkle_verify, merkle_path};

/// Current epoch-package format version.  Increment on breaking changes.
pub const PACKAGE_VERSION: u32 = 1;

/// Domain-separation tag fed into ML-DSA-65 sign/verify.
pub const ML_DSA_CTX: &[u8] = b"STARK-DNS-EPOCH-V1";

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EpochRecord {
    pub domain:        String,
    pub record_type:   u16,
    /// DNSSEC algorithm code (5=RSASHA1, 8=RSASHA256, 13=ECDSAP256SHA256,
    /// 14=ECDSAP384SHA384, 15=Ed25519, etc.).  Per RFC 8624.
    pub algorithm:     u8,
    /// Canonical leaf rdata (hash bytes for DNSKEY+RRSIG attestation
    /// records; A-record octets for resolvable address records).
    pub rdata:         Vec<u8>,
    /// Original DNS TTL (preserved from the wire capture).
    pub ttl:           u32,
}

impl EpochRecord {
    /// Convert to the `DnsRecord` shape `merkle_build`/`leaf_hash` use.
    pub fn to_dns_record(&self) -> DnsRecord {
        DnsRecord {
            domain:      self.domain.clone(),
            record_type: self.record_type,
            ttl:         self.ttl,
            rdata:       self.rdata.clone(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SeEpochPackage {
    /// Format-version tag.
    pub version: u32,

    /// Epoch metadata.
    pub epoch_t:    u64,
    pub epoch_seq:  u64,
    pub epoch_prev: [u8; 32],

    /// ML-DSA-65 (FIPS 204) authority public key (1 952 B).
    pub authority_pk:  Vec<u8>,
    /// ML-DSA-65 signature covering `binding_hash()` (3 309 B).
    pub authority_sig: Vec<u8>,

    /// Inner shard STARK (HashRollup AIR over verified records).
    pub inner_pi_hash:     [u8; 32],
    pub inner_merkle_root: [u8; 32],
    pub inner_n_trace:     usize,
    pub inner_stark_proof: Vec<u8>,
    pub inner_root_f0:     Vec<u8>,

    /// Outer rollup STARK (commits inner pi_hash to epoch root).
    pub outer_n_trace:     usize,
    pub outer_stark_proof: Vec<u8>,
    pub outer_root_f0:     Vec<u8>,

    /// Local Merkle tree (for offline inclusion proofs at query time).
    /// `merkle_levels[0]` is the leaf level; `merkle_levels.last()` is
    /// the root level (single entry).
    pub merkle_root:   [u8; 32],
    pub merkle_levels: Vec<Vec<[u8; 32]>>,
    pub merkle_salt:   [u8; 16],

    /// Records (ordered; index `i` corresponds to leaf-index `i`).
    pub records: Vec<EpochRecord>,
}

impl SeEpochPackage {
    /// Binding hash the ML-DSA signature covers (paper Def. 1).
    pub fn binding_hash(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(&self.outer_root_f0);
        h.update(self.inner_pi_hash);
        h.update(self.merkle_root);
        h.update(self.epoch_t.to_le_bytes());
        h.update(self.epoch_seq.to_le_bytes());
        h.update(self.epoch_prev);
        h.finalize().into()
    }

    /// Total serialised size in bytes (sum of all variable components +
    /// fixed overhead).  Used for reporting.
    pub fn size_estimate(&self) -> usize {
        self.authority_pk.len()
            + self.authority_sig.len()
            + self.inner_stark_proof.len()
            + self.inner_root_f0.len()
            + self.outer_stark_proof.len()
            + self.outer_root_f0.len()
            + self.merkle_levels.iter().map(|lvl| lvl.len() * 32).sum::<usize>()
            + 16  // merkle_salt
            + 32  // merkle_root
            + 32  // inner_pi_hash
            + 32  // inner_merkle_root
            + 32  // epoch_prev
            + 24  // epoch_t / seq / version
            + self.records.iter()
                .map(|r| r.domain.len() + r.rdata.len() + 7)
                .sum::<usize>()
    }
}

/// Persist the package to disk via bincode 1.3.
pub fn save_to_file(
    package: &SeEpochPackage, path: &Path,
) -> Result<usize, Box<dyn std::error::Error>> {
    let bytes = bincode::serialize(package)?;
    std::fs::write(path, &bytes)?;
    Ok(bytes.len())
}

/// Read the package from disk via bincode 1.3.
pub fn load_from_file(
    path: &Path,
) -> Result<SeEpochPackage, Box<dyn std::error::Error>> {
    let bytes = std::fs::read(path)?;
    let package: SeEpochPackage = bincode::deserialize(&bytes)?;
    Ok(package)
}

// ─── Edge-resolver helpers ───────────────────────────────────────────

/// Inclusion result returned by [`resolve`].  Carries everything the
/// caller needs to independently re-verify the answer:
///   - the matched record
///   - the leaf hash that was Merkle-committed
///   - the leaf index in the tree
///   - the authentication path (siblings up to the root)
#[derive(Clone, Debug)]
pub struct InclusionResult<'a> {
    pub record:     &'a EpochRecord,
    pub leaf_hash:  [u8; 32],
    pub leaf_index: usize,
    pub merkle_path: Vec<[u8; 32]>,
}

/// Offline lookup against the package's committed records.  Returns
/// `Some(InclusionResult)` if a matching `(domain, record_type)` exists
/// AND its Merkle inclusion path reconstructs the package's root.
///
/// Re-verifying inclusion at query time is paranoid but cheap (~1 µs)
/// and catches any in-memory tampering of `package.records` between
/// load and query.
pub fn resolve<'a>(
    package: &'a SeEpochPackage,
    domain: &str,
    record_type: u16,
) -> Option<InclusionResult<'a>> {
    let idx = package.records.iter().position(|r| {
        r.domain == domain && r.record_type == record_type
    })?;
    let leaf_hash = package.records[idx].to_dns_record()
        .leaf_hash(&package.merkle_salt);
    let path = merkle_path(&package.merkle_levels, idx);
    if !merkle_verify(leaf_hash, idx, &path, package.merkle_root) {
        return None;
    }
    Some(InclusionResult {
        record: &package.records[idx],
        leaf_hash,
        leaf_index: idx,
        merkle_path: path,
    })
}
