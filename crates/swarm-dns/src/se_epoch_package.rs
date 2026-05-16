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

    /// RRSIG `sig_inception` (RFC 4034 §3.1.5, Unix seconds, u32).
    /// Optional for backwards-compat with packages built before priority-6
    /// wiring; `None` means the producer did not stamp a validity window
    /// for this record (e.g. legacy demo data).  When present, the offline
    /// resolver enforces `now ≥ sig_inception` at query time.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sig_inception: Option<u32>,
    /// RRSIG `sig_expiration` (RFC 4034 §3.1.5, Unix seconds, u32).
    /// Optional for the same backwards-compat reason as `sig_inception`.
    /// When present, the resolver enforces `now ≤ sig_expiration` at
    /// query time and REJECTs replay of a long-since-expired RRSIG.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sig_expiration: Option<u32>,
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

    // ─── Optional Phase 4 — NSEC3 chain-completeness commitment ────
    //
    // Closes the paper's biggest acknowledged gap (authenticated
    // denial-of-existence) by binding a STARK proof of NSEC3 chain
    // closure into the same epoch package.  Optional because:
    //   * a producer may not yet have wired NSEC3 capture (legacy
    //     packages built before priority-4 lift have these fields
    //     unset; bincode treats `Option<T> = None` as backwards-compat)
    //   * zones not signed with NSEC3 (e.g. pure NSEC or unsigned)
    //     have nothing to commit here
    //
    // When present, the offline resolver's NXDOMAIN-proof path can
    // answer "this name is provably NOT in the corpus" by:
    //   1. verifying the NSEC3 STARK chain-closure proof
    //   2. hashing the queried name with the zone's NSEC3 params
    //   3. finding the covering NSEC3 record by `owner_hash < q < next_hash`
    /// SHA3-256 chain root = SHA3-256("DNS-NSEC3-CHAIN-ROOT-V1" || salt
    ///                                || count(LE) || record0 || … || recordN).
    /// Bound into `binding_hash` via the field below when present.
    pub nsec3_chain_root: Option<[u8; 32]>,
    /// Record count committed in the NSEC3 chain.
    pub nsec3_record_count: Option<usize>,
    /// NSEC3 chain STARK proof (ark-serialise compressed).  Produced
    /// by `swarm_dns::prover::prove_nsec3_completeness`.
    pub nsec3_stark_proof: Option<Vec<u8>>,
    /// NSEC3 chain STARK's n_trace (needed to reconstruct FRI params).
    pub nsec3_n_trace: Option<usize>,
    /// NSEC3 chain STARK's root_f0 (FRI commitment).
    pub nsec3_root_f0: Option<Vec<u8>>,
    /// The committed (owner_hash, next_hash) pairs in chain order;
    /// the resolver uses these to locate the covering record for
    /// NXDOMAIN proofs.
    pub nsec3_chain: Option<Vec<(Vec<u8>, Vec<u8>)>>,

    // ─── Optional Phase 5 — DS → DNSKEY hash-chain bindings ────────
    //
    // RFC 4034 §5.1.4: the parent zone's DS record commits to the
    // child zone's DNSKEY via SHA-256(owner_name || dnskey_rdata).
    // Each `DsKskBinding` is a STARK proof produced by
    // `swarm_dns::prover::prove_ds_ksk_binding` for one
    // (parent_zone, child_zone, DNSKEY) triple in the captured chain.
    //
    // Together these prove the multi-level chain
    //   root_KSK → root_DS_for_.se → .se_KSK → .se_DS_for_2LD → 2LD_KSK
    // is cryptographically anchored: a malicious resolver cannot
    // substitute a different DNSKEY at any level and still match the
    // parent's published DS hash.
    pub ds_ksk_bindings: Option<Vec<DsKskBinding>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DsKskBinding {
    /// Owner name in canonical text form (e.g. "iis.se.").
    pub owner_name: String,
    /// SHA-256 the STARK asserts == SHA-256(owner_name||dnskey_rdata).
    pub asserted_digest: [u8; 32],
    /// Parent zone's published DS record digest (must equal `asserted_digest`).
    pub parent_ds_digest: [u8; 32],
    /// FIPS 4034 digest_type (we only support 2 = SHA-256 in-circuit today).
    pub digest_type: u8,
    /// STARK n_trace (needed to reconstruct FRI params).
    pub n_trace: usize,
    /// FRI proof blob (ark-serialise compressed).
    pub stark_proof: Vec<u8>,
    /// FRI proof's root_f0.
    pub root_f0: Vec<u8>,
}

impl SeEpochPackage {
    /// Binding hash the ML-DSA signature covers (paper Def. 1).
    /// When `nsec3_chain_root` is present, it is mixed into the
    /// binding so the authority's signature commits to the NSEC3
    /// chain-completeness claim AS WELL AS the positive records.
    pub fn binding_hash(&self) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(&self.outer_root_f0);
        h.update(self.inner_pi_hash);
        h.update(self.merkle_root);
        h.update(self.epoch_t.to_le_bytes());
        h.update(self.epoch_seq.to_le_bytes());
        h.update(self.epoch_prev);
        if let Some(root) = &self.nsec3_chain_root {
            h.update(b"NSEC3-CHAIN-V1");
            h.update(root);
        }
        if let Some(bindings) = &self.ds_ksk_bindings {
            h.update(b"DS-KSK-CHAIN-V1");
            h.update((bindings.len() as u64).to_le_bytes());
            for b in bindings {
                h.update(b.owner_name.as_bytes());
                h.update(b.asserted_digest);
                h.update(b.parent_ds_digest);
                h.update([b.digest_type]);
                h.update(&b.root_f0);
            }
        }
        // RRSIG validity windows: mix per-record (inception, expiration)
        // bounds into the binding so the ML-DSA signature commits to
        // them.  A tampered window (e.g. extending an expired record's
        // expiration) is caught at signature verify.  Only mixed when
        // at least one record has a bound — keeps backwards compatibility
        // with pre-priority-6 packages.
        let has_any_validity = self.records.iter().any(|r|
            r.sig_inception.is_some() || r.sig_expiration.is_some());
        if has_any_validity {
            h.update(b"RRSIG-VALIDITY-V1");
            h.update((self.records.len() as u64).to_le_bytes());
            for r in &self.records {
                // present-flag(1) || inception(4) || present-flag(1) || expiration(4)
                let inc_flag = r.sig_inception.is_some() as u8;
                h.update([inc_flag]);
                h.update(r.sig_inception.unwrap_or(0).to_le_bytes());
                let exp_flag = r.sig_expiration.is_some() as u8;
                h.update([exp_flag]);
                h.update(r.sig_expiration.unwrap_or(0).to_le_bytes());
            }
        }
        h.finalize().into()
    }

    /// Zone-wide validity window: the intersection of every record's
    /// `[sig_inception, sig_expiration]` window.  Returns
    /// `(max_inception, min_expiration)` over records that HAVE both
    /// bounds.  Returns `None` if no record has any bound (legacy
    /// pre-priority-6 packages) or if the intersection is empty
    /// (`max_inception > min_expiration` — i.e. records can't all be
    /// simultaneously fresh, which signals a misbuilt package).
    pub fn zone_validity_window(&self) -> Option<(u32, u32)> {
        let mut max_inc: Option<u32> = None;
        let mut min_exp: Option<u32> = None;
        for r in &self.records {
            if let Some(inc) = r.sig_inception {
                max_inc = Some(max_inc.map_or(inc, |x| x.max(inc)));
            }
            if let Some(exp) = r.sig_expiration {
                min_exp = Some(min_exp.map_or(exp, |x| x.min(exp)));
            }
        }
        match (max_inc, min_exp) {
            (Some(i), Some(e)) if i <= e => Some((i, e)),
            _ => None,
        }
    }

    /// Per-record freshness verdict given a wall-clock `now` (Unix
    /// seconds).  Records without bounds return `Fresh` (the package
    /// predates priority-6 — caller can decide whether to reject
    /// unbound records at policy level).
    pub fn record_freshness(&self, record: &EpochRecord, now: u32)
        -> RrsigFreshness
    {
        let _ = self;
        if let Some(inc) = record.sig_inception {
            if now < inc { return RrsigFreshness::NotYetValid { inception: inc, now }; }
        }
        if let Some(exp) = record.sig_expiration {
            if now > exp { return RrsigFreshness::Expired { expiration: exp, now }; }
        }
        RrsigFreshness::Fresh
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

/// Three-way freshness verdict for an `EpochRecord` against a wall clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RrsigFreshness {
    /// Record's RRSIG window covers `now` — safe to serve.
    Fresh,
    /// `now < sig_inception` — replay of a future-dated signature.
    NotYetValid { inception: u32, now: u32 },
    /// `now > sig_expiration` — replay of a long-since-expired signature.
    Expired { expiration: u32, now: u32 },
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
