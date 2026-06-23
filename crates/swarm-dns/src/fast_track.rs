//! F4 — sub-TTL fast-track lane (paper §VII Future Work F4).
//!
//! A full epoch package commits a zone snapshot for a duration ΔT.  Records
//! whose DNS TTL is shorter than ΔT cannot be faithfully re-served from that
//! snapshot once their TTL elapses within the epoch: the cached answer is
//! "stale" in the DNS-caching sense, even though the STARK + ML-DSA binding
//! is still cryptographically valid.  The two blunt options are to shorten
//! ΔT globally (linear prover-cost increase) or to fail open to standard
//! DNSSEC for the expired record.
//!
//! The fast-track lane is the third option: re-prove ONLY the sub-TTL
//! records intra-epoch, producing a small [`SubTtlUpdate`] — a signed,
//! STARK-attested delta anchored to the parent epoch by its binding hash —
//! so the edge can keep serving TTL-faithful answers without globally
//! shrinking ΔT.  Cost is proportional to the sub-TTL record count, not the
//! zone size.
//!
//! Soundness model.  A `SubTtlUpdate` reuses the same inner-shard STARK
//! (`prove_inner_shard`, HashRollup AIR over the refreshed leaves) and
//! ML-DSA authority signature as the main package.  Its binding hash
//! carries the parent epoch's binding hash, so an update cannot be detached
//! from the epoch it refreshes or replayed against a different epoch; the
//! update's own `(seq, refresh_t)` order it within the epoch.  The edge
//! verifies each update ONCE on receipt (signature + STARK + Merkle), then
//! [`resolve_ttl_faithful`] answers queries against the verified set.

use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

use crate::dns::{merkle_build, merkle_path, merkle_root, merkle_verify};
use crate::dns_authority::AuthorityKeypair;
use crate::prover::{build_params, prove_inner_shard, Ext, LdtMode, BLOWUP};
use crate::se_epoch_package::{EpochRecord, InclusionResult, SeEpochPackage};

/// Domain-separation tag mixed into the fast-track binding hash.  Keeps a
/// fast-track signature from being confused with an epoch-package signature
/// (which is signed over a `binding_hash()` with no such tag).
pub const FASTTRACK_TAG: &[u8] = b"STARK-DNS-FASTTRACK-V1";

/// Is `record` a sub-TTL record relative to the epoch duration ΔT?
///
/// A record is sub-TTL iff its DNS TTL is shorter than ΔT, meaning its
/// cache lifetime can elapse within a single epoch.  TTL 0 (do-not-cache)
/// is treated as sub-TTL.
#[inline]
pub fn is_sub_ttl(record: &EpochRecord, epoch_duration_secs: u32) -> bool {
    record.ttl < epoch_duration_secs
}

/// The sub-TTL subset of a record set (cloned), in input order.
pub fn select_sub_ttl(records: &[EpochRecord], epoch_duration_secs: u32) -> Vec<EpochRecord> {
    records.iter()
        .filter(|r| is_sub_ttl(r, epoch_duration_secs))
        .cloned()
        .collect()
}

/// An intra-epoch refresh of a set of sub-TTL records, anchored to a parent
/// epoch package.  Self-contained: carries the refreshed records, their
/// Merkle commitment, an inner-shard STARK over them, and the authority's
/// ML-DSA signature over the fast-track binding hash.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubTtlUpdate {
    /// `epoch_seq` of the full epoch package this update refreshes.
    pub parent_epoch_seq:  u64,
    /// `binding_hash()` of the parent epoch package — anchors the update so
    /// it cannot be replayed against a different epoch.
    pub parent_binding_hash: [u8; 32],
    /// Monotonic sequence within the epoch (0, 1, 2, …).
    pub update_seq:        u64,
    /// Unix seconds at which this refresh snapshot was captured.  The edge
    /// serves a refreshed record only while `now - refresh_t <= ttl`.
    pub refresh_t:         u64,

    /// The refreshed sub-TTL records (leaf index `i` ↔ `records[i]`).
    pub records:           Vec<EpochRecord>,

    /// Merkle commitment over the refreshed leaves.
    pub merkle_root:       [u8; 32],
    pub merkle_levels:     Vec<Vec<[u8; 32]>>,
    pub merkle_salt:       [u8; 16],

    /// Inner-shard STARK (HashRollup AIR) over the refreshed leaves.
    pub inner_pi_hash:     [u8; 32],
    pub inner_n_trace:     usize,
    pub inner_stark_proof: Vec<u8>,
    pub inner_root_f0:     Vec<u8>,

    /// ML-DSA authority public key + signature over [`sub_ttl_binding_hash`].
    pub authority_pk:      Vec<u8>,
    pub authority_sig:     Vec<u8>,
}

/// The hash the authority signs for a fast-track update.  Binds the update
/// to its parent epoch, its position in the epoch, the refresh time, and
/// the refreshed records' Merkle root + inner-STARK commitment.
pub fn sub_ttl_binding_hash(
    parent_binding_hash: &[u8; 32],
    parent_epoch_seq:    u64,
    update_seq:          u64,
    refresh_t:           u64,
    merkle_root:         &[u8; 32],
    inner_pi_hash:       &[u8; 32],
    inner_root_f0:       &[u8],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(FASTTRACK_TAG);
    h.update(parent_binding_hash);
    h.update(parent_epoch_seq.to_le_bytes());
    h.update(update_seq.to_le_bytes());
    h.update(refresh_t.to_le_bytes());
    h.update(merkle_root);
    h.update(inner_pi_hash);
    h.update(inner_root_f0);
    h.finalize().into()
}

/// Verify an ML-DSA signature from raw public-key bytes (level inferred from
/// the key length), with the empty context used by [`AuthorityKeypair::sign`].
fn ml_dsa_verify_pk_bytes(pk_bytes: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    use fips204::traits::{SerDes, Verifier};
    use fips204::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
    match pk_bytes.len() {
        ml_dsa_44::PK_LEN => {
            let Ok(pk_arr): Result<[u8; ml_dsa_44::PK_LEN], _> = pk_bytes.try_into() else { return false };
            let Ok(pk) = ml_dsa_44::PublicKey::try_from_bytes(pk_arr) else { return false };
            let Ok(sig_arr): Result<[u8; ml_dsa_44::SIG_LEN], _> = sig.try_into() else { return false };
            pk.verify(msg, &sig_arr, b"")
        }
        ml_dsa_65::PK_LEN => {
            let Ok(pk_arr): Result<[u8; ml_dsa_65::PK_LEN], _> = pk_bytes.try_into() else { return false };
            let Ok(pk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else { return false };
            let Ok(sig_arr): Result<[u8; ml_dsa_65::SIG_LEN], _> = sig.try_into() else { return false };
            pk.verify(msg, &sig_arr, b"")
        }
        ml_dsa_87::PK_LEN => {
            let Ok(pk_arr): Result<[u8; ml_dsa_87::PK_LEN], _> = pk_bytes.try_into() else { return false };
            let Ok(pk) = ml_dsa_87::PublicKey::try_from_bytes(pk_arr) else { return false };
            let Ok(sig_arr): Result<[u8; ml_dsa_87::SIG_LEN], _> = sig.try_into() else { return false };
            pk.verify(msg, &sig_arr, b"")
        }
        _ => false,
    }
}

/// Build a fast-track update over `refreshed` records, anchored to `parent`.
///
/// Reuses [`prove_inner_shard`] (HashRollup AIR) with the parent epoch's
/// binding hash as the Fiat–Shamir tag, so the inner proof is itself bound
/// to the parent epoch.  `authority` signs the resulting fast-track binding
/// hash with the empty ML-DSA context (domain separation lives in the
/// [`FASTTRACK_TAG`]-prefixed message).
///
/// Panics only on internal invariant failure (the inner prover self-verifies).
pub fn build_sub_ttl_update(
    parent:    &SeEpochPackage,
    authority: &AuthorityKeypair,
    refreshed: &[EpochRecord],
    update_seq: u64,
    refresh_t:  u64,
    salt:      [u8; 16],
    ldt:       LdtMode,
) -> SubTtlUpdate {
    assert!(!refreshed.is_empty(), "fast-track update must refresh ≥1 record");

    let parent_binding = parent.binding_hash();

    // Inner-shard STARK over the refreshed leaves, FS-bound to the parent.
    let dns_records: Vec<_> = refreshed.iter().map(|r| r.to_dns_record()).collect();
    let inner = prove_inner_shard(&salt, &dns_records, &parent_binding, ldt);

    // Local Merkle tree over the same leaves (for offline inclusion proofs).
    let leaf_hashes: Vec<[u8; 32]> =
        dns_records.iter().map(|r| r.leaf_hash(&salt)).collect();
    let levels = merkle_build(&leaf_hashes);
    let mk_root = merkle_root(&levels);
    debug_assert_eq!(mk_root, inner.merkle_root,
        "fast-track Merkle root must match the inner shard's");

    let inner_root_f0 = inner.root_f0.to_vec();
    let binding = sub_ttl_binding_hash(
        &parent_binding, parent.epoch_seq, update_seq, refresh_t,
        &mk_root, &inner.pi_hash, &inner_root_f0,
    );
    let sig = authority.sign(&binding);

    SubTtlUpdate {
        parent_epoch_seq: parent.epoch_seq,
        parent_binding_hash: parent_binding,
        update_seq, refresh_t,
        records: refreshed.to_vec(),
        merkle_root: mk_root,
        merkle_levels: levels,
        merkle_salt: salt,
        inner_pi_hash: inner.pi_hash,
        inner_n_trace: inner.n_trace,
        inner_stark_proof: inner.proof_blob,
        inner_root_f0,
        authority_pk: authority.pk_bytes(),
        authority_sig: sig,
    }
}

/// Reasons a fast-track update fails verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FastTrackError {
    /// The update's parent anchor does not match the epoch being served.
    ParentMismatch,
    /// The ML-DSA authority signature did not verify.
    SignatureInvalid,
    /// The Merkle root does not commit the carried records.
    MerkleMismatch,
    /// The carried `inner_root_f0` does not match the proof's commitment.
    ProofMismatch,
    /// The inner-shard STARK failed `deep_fri_verify`.
    StarkInvalid,
}

/// Verify a fast-track update against the parent epoch's binding hash, the
/// way an edge does on receipt.  Checks (in order): parent anchor, ML-DSA
/// signature, Merkle commitment over the carried records, proof-commitment
/// consistency, and the inner-shard STARK.
pub fn verify_sub_ttl_update(
    update:                &SubTtlUpdate,
    expected_parent_binding_hash: &[u8; 32],
    ldt:                   LdtMode,
) -> Result<(), FastTrackError> {
    use ark_serialize::{CanonicalDeserialize, Compress, Validate};

    if &update.parent_binding_hash != expected_parent_binding_hash {
        return Err(FastTrackError::ParentMismatch);
    }

    let binding = sub_ttl_binding_hash(
        &update.parent_binding_hash, update.parent_epoch_seq, update.update_seq,
        update.refresh_t, &update.merkle_root, &update.inner_pi_hash,
        &update.inner_root_f0,
    );
    if !ml_dsa_verify_pk_bytes(&update.authority_pk, &binding, &update.authority_sig) {
        return Err(FastTrackError::SignatureInvalid);
    }

    // Rebuild the Merkle root from the carried records.
    let leaf_hashes: Vec<[u8; 32]> = update.records.iter()
        .map(|r| r.to_dns_record().leaf_hash(&update.merkle_salt))
        .collect();
    let rebuilt = merkle_root(&merkle_build(&leaf_hashes));
    if rebuilt != update.merkle_root {
        return Err(FastTrackError::MerkleMismatch);
    }

    // Inner-shard STARK, FS-bound to the parent epoch.
    let proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        update.inner_stark_proof.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|_| FastTrackError::StarkInvalid)?;
    if proof.root_f0.as_slice() != update.inner_root_f0.as_slice() {
        return Err(FastTrackError::ProofMismatch);
    }
    let n0 = update.inner_n_trace * BLOWUP;
    let params = build_params(n0, &update.parent_binding_hash, ldt);
    if !deep_ali::fri::deep_fri_verify::<Ext>(&params, &proof) {
        return Err(FastTrackError::StarkInvalid);
    }
    Ok(())
}

/// Locate `(domain, record_type)` in an update and re-verify its Merkle
/// inclusion (cheap tamper check at query time, mirroring `resolve`).
fn find_in_update<'a>(
    update: &'a SubTtlUpdate, domain: &str, record_type: u16,
) -> Option<(usize, &'a EpochRecord, Vec<[u8; 32]>)> {
    let idx = update.records.iter()
        .position(|r| r.domain == domain && r.record_type == record_type)?;
    let leaf = update.records[idx].to_dns_record().leaf_hash(&update.merkle_salt);
    let path = merkle_path(&update.merkle_levels, idx);
    if !merkle_verify(leaf, idx, &path, update.merkle_root) {
        return None;
    }
    Some((idx, &update.records[idx], path))
}

/// Verdict from [`resolve_ttl_faithful`].
#[derive(Clone, Debug)]
pub enum TtlServeDecision<'a> {
    /// The committed epoch snapshot is still within the record's TTL window.
    EpochFresh(InclusionResult<'a>),
    /// The epoch snapshot is TTL-stale, but a fast-track update refreshed the
    /// record within its TTL.  Served from that update.
    FastTrackFresh {
        record:      &'a EpochRecord,
        update_seq:  u64,
        refresh_t:   u64,
        leaf_index:  usize,
        merkle_path: Vec<[u8; 32]>,
    },
    /// The record exists but its TTL has elapsed and no fast-track update
    /// refreshes it within TTL — the caller applies its fail-open /
    /// fail-closed policy.
    StaleNeedsRefresh { ttl: u64, age: u64 },
    /// No matching `(domain, record_type)` in the epoch package.
    NotFound,
}

/// TTL-faithful offline resolution.  Serves a record from the committed
/// epoch snapshot while it is within its TTL window (measured from
/// `epoch_t`); once the snapshot is TTL-stale, serves from the newest
/// fast-track update that refreshed the record within its TTL, or reports
/// `StaleNeedsRefresh`.
///
/// `updates` MUST be pre-verified via [`verify_sub_ttl_update`]; this
/// function performs only freshness selection and Merkle inclusion
/// (re-running `deep_fri_verify` per query would defeat the offline model).
pub fn resolve_ttl_faithful<'a>(
    package:  &'a SeEpochPackage,
    updates:  &'a [SubTtlUpdate],
    domain:   &str,
    record_type: u16,
    now:      u64,
) -> TtlServeDecision<'a> {
    let incl = match crate::se_epoch_package::resolve(package, domain, record_type) {
        Some(i) => i,
        None => return TtlServeDecision::NotFound,
    };
    let ttl = incl.record.ttl as u64;
    let age = now.saturating_sub(package.epoch_t);

    // Within the first TTL window from epoch start → committed snapshot is
    // still cache-valid.  TTL 0 (do-not-cache) always needs a fast-track.
    if ttl > 0 && age <= ttl {
        return TtlServeDecision::EpochFresh(incl);
    }

    // Stale: find the newest update that refreshed this record within TTL.
    let best = updates.iter()
        .filter(|u| u.parent_epoch_seq == package.epoch_seq)
        .filter(|u| now >= u.refresh_t && now - u.refresh_t <= ttl.max(1))
        .filter_map(|u| find_in_update(u, domain, record_type).map(|f| (u, f)))
        .max_by_key(|(u, _)| u.refresh_t);

    match best {
        Some((u, (idx, rec, path))) => TtlServeDecision::FastTrackFresh {
            record: rec,
            update_seq: u.update_seq,
            refresh_t: u.refresh_t,
            leaf_index: idx,
            merkle_path: path,
        },
        None => TtlServeDecision::StaleNeedsRefresh { ttl, age },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dns_authority::NistLevel;

    const SALT: [u8; 16] = *b"fast-track-salt0";

    fn rec(domain: &str, rtype: u16, ttl: u32) -> EpochRecord {
        EpochRecord {
            domain: domain.to_string(),
            record_type: rtype,
            algorithm: 8,
            rdata: format!("{domain}:{rtype}").into_bytes(),
            ttl,
            sig_inception: None,
            sig_expiration: None,
        }
    }

    fn minimal_package(records: Vec<EpochRecord>, epoch_t: u64, epoch_seq: u64) -> SeEpochPackage {
        let leaves: Vec<[u8; 32]> =
            records.iter().map(|r| r.to_dns_record().leaf_hash(&SALT)).collect();
        let levels = merkle_build(&leaves);
        let root = merkle_root(&levels);
        SeEpochPackage {
            version: 1, epoch_t, epoch_seq, epoch_prev: [0u8; 32],
            authority_pk: vec![], authority_sig: vec![],
            inner_pi_hash: [0u8; 32], inner_merkle_root: root, inner_n_trace: 0,
            inner_stark_proof: vec![], inner_root_f0: vec![],
            outer_n_trace: 0, outer_stark_proof: vec![], outer_root_f0: vec![],
            merkle_root: root, merkle_levels: levels, merkle_salt: SALT,
            records,
            nsec3_chain_root: None, nsec3_record_count: None, nsec3_stark_proof: None,
            nsec3_n_trace: None, nsec3_root_f0: None, nsec3_chain: None,
            ds_ksk_bindings: None,
        }
    }

    /// A hand-built update with a valid Merkle commitment but a dummy STARK
    /// blob — sufficient for `resolve_ttl_faithful` (which checks Merkle +
    /// freshness only, not the STARK).
    fn minimal_update(
        parent: &SeEpochPackage, records: Vec<EpochRecord>,
        update_seq: u64, refresh_t: u64,
    ) -> SubTtlUpdate {
        let leaves: Vec<[u8; 32]> =
            records.iter().map(|r| r.to_dns_record().leaf_hash(&SALT)).collect();
        let levels = merkle_build(&leaves);
        let root = merkle_root(&levels);
        SubTtlUpdate {
            parent_epoch_seq: parent.epoch_seq,
            parent_binding_hash: parent.binding_hash(),
            update_seq, refresh_t,
            records,
            merkle_root: root, merkle_levels: levels, merkle_salt: SALT,
            inner_pi_hash: [0u8; 32], inner_n_trace: 0,
            inner_stark_proof: vec![], inner_root_f0: vec![],
            authority_pk: vec![], authority_sig: vec![],
        }
    }

    #[test]
    fn sub_ttl_selection() {
        let records = vec![rec("a.se.", 1, 300), rec("b.se.", 1, 86_400), rec("c.se.", 1, 0)];
        let sel = select_sub_ttl(&records, 3600);
        // a (300<3600) and c (0<3600) are sub-TTL; b (86400) is not.
        assert_eq!(sel.len(), 2);
        assert!(sel.iter().any(|r| r.domain == "a.se."));
        assert!(sel.iter().any(|r| r.domain == "c.se."));
        assert!(is_sub_ttl(&rec("x", 1, 0), 3600));
        assert!(!is_sub_ttl(&rec("x", 1, 3600), 3600));
    }

    #[test]
    fn serves_epoch_within_ttl() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 3600)], 1000, 7);
        // age = 2000 - 1000 = 1000 <= 3600 → epoch-fresh
        match resolve_ttl_faithful(&pkg, &[], "a.se.", 1, 2000) {
            TtlServeDecision::EpochFresh(i) => assert_eq!(i.record.domain, "a.se."),
            other => panic!("expected EpochFresh, got {other:?}"),
        }
    }

    #[test]
    fn stale_without_update_needs_refresh() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 300)], 1000, 7);
        // age = 1000 > ttl 300, no updates
        match resolve_ttl_faithful(&pkg, &[], "a.se.", 1, 2000) {
            TtlServeDecision::StaleNeedsRefresh { ttl, age } => {
                assert_eq!(ttl, 300); assert_eq!(age, 1000);
            }
            other => panic!("expected StaleNeedsRefresh, got {other:?}"),
        }
    }

    #[test]
    fn fast_track_serves_when_fresh() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 300)], 1000, 7);
        // refreshed at 1900; now 2000 → 100 <= 300 → fast-track fresh
        let upd = minimal_update(&pkg, vec![rec("a.se.", 1, 300)], 0, 1900);
        match resolve_ttl_faithful(&pkg, std::slice::from_ref(&upd), "a.se.", 1, 2000) {
            TtlServeDecision::FastTrackFresh { record, refresh_t, .. } => {
                assert_eq!(record.domain, "a.se."); assert_eq!(refresh_t, 1900);
            }
            other => panic!("expected FastTrackFresh, got {other:?}"),
        }
    }

    #[test]
    fn fast_track_picks_newest() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 300)], 1000, 7);
        let u1 = minimal_update(&pkg, vec![rec("a.se.", 1, 300)], 0, 1800);
        let u2 = minimal_update(&pkg, vec![rec("a.se.", 1, 300)], 1, 1950);
        let updates = vec![u1, u2];
        match resolve_ttl_faithful(&pkg, &updates, "a.se.", 1, 2000) {
            TtlServeDecision::FastTrackFresh { refresh_t, update_seq, .. } => {
                assert_eq!(refresh_t, 1950); assert_eq!(update_seq, 1);
            }
            other => panic!("expected newest FastTrackFresh, got {other:?}"),
        }
    }

    #[test]
    fn stale_update_is_ignored() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 300)], 1000, 7);
        // refreshed at 1000; now 2000 → 1000 > 300 → too old, ignored
        let upd = minimal_update(&pkg, vec![rec("a.se.", 1, 300)], 0, 1000);
        match resolve_ttl_faithful(&pkg, std::slice::from_ref(&upd), "a.se.", 1, 2000) {
            TtlServeDecision::StaleNeedsRefresh { .. } => {}
            other => panic!("expected StaleNeedsRefresh, got {other:?}"),
        }
    }

    #[test]
    fn update_for_wrong_epoch_is_ignored() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 300)], 1000, 7);
        let mut upd = minimal_update(&pkg, vec![rec("a.se.", 1, 300)], 0, 1950);
        upd.parent_epoch_seq = 999; // wrong epoch
        match resolve_ttl_faithful(&pkg, std::slice::from_ref(&upd), "a.se.", 1, 2000) {
            TtlServeDecision::StaleNeedsRefresh { .. } => {}
            other => panic!("expected StaleNeedsRefresh, got {other:?}"),
        }
    }

    #[test]
    fn missing_record_is_not_found() {
        let pkg = minimal_package(vec![rec("a.se.", 1, 300)], 1000, 7);
        match resolve_ttl_faithful(&pkg, &[], "absent.se.", 1, 2000) {
            TtlServeDecision::NotFound => {}
            other => panic!("expected NotFound, got {other:?}"),
        }
    }

    // ── Build + verify roundtrip (real STARK + ML-DSA): release-only. ──
    // The inner-shard prover hits the ark-ff 0.4.2 debug-assert in debug
    // builds (debug-only invariant, not a soundness bug — see memory note).
    // Run: cargo test --release -p swarm-dns --lib -- --ignored fast_track

    #[test]
    #[ignore = "build path runs prove_inner_shard; run --release --ignored"]
    fn build_verify_roundtrip() {
        let pkg = minimal_package(
            vec![rec("a.se.", 1, 86_400), rec("b.se.", 1, 300), rec("c.se.", 1, 60)],
            1000, 7);
        let auth = AuthorityKeypair::keygen(NistLevel::L1, [9u8; 32]);
        let refreshed = select_sub_ttl(&pkg.records, 3600); // b, c
        assert_eq!(refreshed.len(), 2);
        let upd = build_sub_ttl_update(&pkg, &auth, &refreshed, 0, 1900, SALT, LdtMode::Stir);
        verify_sub_ttl_update(&upd, &pkg.binding_hash(), LdtMode::Stir)
            .expect("honest fast-track update must verify");
        // And it serves a TTL-stale sub-record from the fast-track.
        match resolve_ttl_faithful(&pkg, std::slice::from_ref(&upd), "b.se.", 1, 2000) {
            TtlServeDecision::FastTrackFresh { record, .. } => assert_eq!(record.domain, "b.se."),
            other => panic!("expected FastTrackFresh, got {other:?}"),
        }
    }

    #[test]
    #[ignore = "build path runs prove_inner_shard; run --release --ignored"]
    fn verify_rejects_wrong_parent() {
        let pkg = minimal_package(vec![rec("b.se.", 1, 300)], 1000, 7);
        let auth = AuthorityKeypair::keygen(NistLevel::L1, [9u8; 32]);
        let upd = build_sub_ttl_update(&pkg, &auth, &[rec("b.se.", 1, 300)], 0, 1900, SALT, LdtMode::Stir);
        let err = verify_sub_ttl_update(&upd, &[0xABu8; 32], LdtMode::Stir).unwrap_err();
        assert_eq!(err, FastTrackError::ParentMismatch);
    }

    #[test]
    #[ignore = "build path runs prove_inner_shard; run --release --ignored"]
    fn verify_rejects_tampered_record() {
        let pkg = minimal_package(vec![rec("b.se.", 1, 300)], 1000, 7);
        let auth = AuthorityKeypair::keygen(NistLevel::L1, [9u8; 32]);
        let mut upd = build_sub_ttl_update(&pkg, &auth, &[rec("b.se.", 1, 300)], 0, 1900, SALT, LdtMode::Stir);
        upd.records[0].rdata = b"forged".to_vec(); // breaks the Merkle commitment
        let err = verify_sub_ttl_update(&upd, &pkg.binding_hash(), LdtMode::Stir).unwrap_err();
        assert_eq!(err, FastTrackError::MerkleMismatch);
    }

    #[test]
    #[ignore = "build path runs prove_inner_shard; run --release --ignored"]
    fn verify_rejects_tampered_signature() {
        let pkg = minimal_package(vec![rec("b.se.", 1, 300)], 1000, 7);
        let auth = AuthorityKeypair::keygen(NistLevel::L1, [9u8; 32]);
        let mut upd = build_sub_ttl_update(&pkg, &auth, &[rec("b.se.", 1, 300)], 0, 1900, SALT, LdtMode::Stir);
        let n = upd.authority_sig.len();
        upd.authority_sig[n / 2] ^= 0xFF;
        let err = verify_sub_ttl_update(&upd, &pkg.binding_hash(), LdtMode::Stir).unwrap_err();
        assert_eq!(err, FastTrackError::SignatureInvalid);
    }
}
