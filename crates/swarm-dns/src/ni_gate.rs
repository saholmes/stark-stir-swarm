//! NI-gated DNS record updates: post-quantum, source-authenticated update
//! authorization.
//!
//! A registrar/resolver accepts a record update only if it carries a STARK
//! proof **bound to the owner's registered ML-DSA public key** plus the
//! owner's ML-DSA signature.  This closes the capture-window MitM that the
//! central-epoch prover cannot: a forged update has no valid proof or
//! signature under a key registered for the name, so it is rejected at
//! ingress rather than faithfully proved later.
//!
//! ## Triple binding (substitution-proof)
//!  1. **name ↔ pk** — the owner registers `H(pk)` for the name (trust root,
//!     [`NameKeyRegistry`]).
//!  2. **proof ↔ pk** — the owner's pk is folded into the STARK's
//!     Fiat–Shamir public input ([`ni_fs_binding`] → `prove_inner_shard`'s
//!     `fs_binding_32`), so the proof verifies *only* for that key; a proof
//!     lifted onto another key fails `deep_fri_verify`.
//!  3. **sig ↔ pk** — the owner ML-DSA-signs the same binding.
//!
//! ## Separation of compute from trust
//! Proof *generation* can be delegated to an untrusted public swarm — a STARK
//! is publicly verifiable and sound regardless of who produced it — while the
//! owner retains the trust anchor by *verifying then signing* the proof.
//!
//! Built by reusing [`prove_inner_shard`] (the same inner-shard HashRollup AIR
//! as the fast-track lane), so the per-update cost is the measured inner-shard
//! cost plus one ML-DSA signature.

use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

use crate::dns::{merkle_build, merkle_root, DnsRecord};
use crate::dns_authority::{pk_binding_hash, AuthorityKeypair};
use crate::prover::{build_params, prove_inner_shard, Ext, LdtMode, BLOWUP};

/// The registrar's name→key registry: the one-time-enrolment trust root.
/// Maps a DNS name to `H(owner_pk)`; enrolment is the analogue of publishing
/// a DNSKEY, and is the single point where the owner key's authenticity must
/// be bootstrapped.
#[derive(Default, Clone)]
pub struct NameKeyRegistry {
    map: std::collections::HashMap<String, [u8; 32]>,
}

impl NameKeyRegistry {
    pub fn new() -> Self {
        Self::default()
    }
    /// One-time enrolment: bind `name` to the owner's ML-DSA public key.
    pub fn register(&mut self, name: &str, owner_pk: &[u8]) {
        self.map.insert(name.to_string(), pk_binding_hash(owner_pk));
    }
    pub fn registered_pk_hash(&self, name: &str) -> Option<[u8; 32]> {
        self.map.get(name).copied()
    }
}

/// NI binding: the Fiat–Shamir public input that anchors the STARK proof to
/// `(owner_pk, name, record-commitment, serial)`, and the exact message the
/// owner ML-DSA-signs.  Folding `owner_pk` here is what enforces *proof ↔ pk*.
pub fn ni_fs_binding(
    owner_pk: &[u8],
    name: &str,
    mk_root: &[u8; 32],
    serial: u64,
    created_at: u64,
    prev_hash: &[u8; 32],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    Digest::update(&mut h, b"stark-dns/ni-gate/v2");
    Digest::update(&mut h, owner_pk); // proof <-> pk
    Digest::update(&mut h, name.as_bytes());
    Digest::update(&mut h, mk_root);
    Digest::update(&mut h, serial.to_le_bytes());
    Digest::update(&mut h, created_at.to_le_bytes()); // temporal: pre-CRQC gate
    Digest::update(&mut h, prev_hash); // anchored chain: anti-backdating
    h.finalize().into()
}

/// An NI-gated, owner-authorized record update.
#[derive(Clone, Serialize, Deserialize)]
pub struct NiUpdate {
    pub name: String,
    pub records: Vec<DnsRecord>,
    /// Monotonic per-name freshness counter (anti-replay).
    pub serial: u64,
    pub merkle_root: [u8; 32],
    pub merkle_salt: [u8; 16],
    pub inner_n_trace: usize,
    pub inner_root_f0: Vec<u8>,
    pub inner_stark_proof: Vec<u8>,
    /// Owner ML-DSA public key (the key registered for `name`).
    pub owner_pk: Vec<u8>,
    /// Owner ML-DSA signature over [`ni_fs_binding`].
    pub owner_sig: Vec<u8>,
    /// Unix-seconds creation timestamp, bound into the proof.  A proof is only
    /// trustworthy if provably created before the CRQC cutoff (after which a
    /// classical signature it attests could be a Shor forgery).
    pub created_at: u64,
    /// Hash of the previous accepted update for this name (genesis = [0;32]),
    /// forming an append-only chain that, anchored to an external public log,
    /// prevents backdating.
    pub prev_proof_hash: [u8; 32],
    /// Proof of time: a trusted time authority's signature over
    /// `(attested_time ‖ proof_hash)`, making `created_at` authority-attested
    /// rather than owner-claimed (empty `time_sig` = unattested).
    pub attested_time: u64,
    pub time_authority_pk: Vec<u8>,
    pub time_sig: Vec<u8>,
}

/// The message a time authority signs to attest a proof's existence at a time.
/// Using the proof hash as the time-server \emph{nonce} means the signature
/// proves the proof existed at/before `attested_time` (one cannot sign over a
/// nonce that does not yet exist).
pub fn time_attest_msg(attested_time: u64, proof_hash: &[u8; 32]) -> Vec<u8> {
    let mut m = Vec::with_capacity(24 + 8 + 32);
    m.extend_from_slice(b"stark-dns/time-attest/v1");
    m.extend_from_slice(&attested_time.to_le_bytes());
    m.extend_from_slice(proof_hash);
    m
}

impl NiUpdate {
    /// Wire size of the carried proof + signature (bytes).
    pub fn proof_sig_bytes(&self) -> usize {
        self.inner_stark_proof.len() + self.owner_sig.len() + self.owner_pk.len()
    }
    /// This update's chain identity = its (deterministic) FS binding, used as
    /// the `prev_proof_hash` of the next update for the same name.
    pub fn proof_hash(&self) -> [u8; 32] {
        ni_fs_binding(
            &self.owner_pk, &self.name, &self.merkle_root, self.serial,
            self.created_at, &self.prev_proof_hash,
        )
    }

    /// Attach a proof of time: a trusted time service `authority` signs
    /// `(attested_time ‖ proof_hash)`.  In deployment `attested_time` is the
    /// authority's observed clock; the signature is an ML-DSA (or, for a
    /// Roughtime/RFC-3161 service, Ed25519/RSA/ECDSA) signature verifiable
    /// in-circuit by the same signature AIR used for DNSSEC RRSIGs.
    pub fn attach_time_attestation(&mut self, authority: &AuthorityKeypair) {
        let t = self.created_at;
        self.attested_time = t;
        self.time_authority_pk = authority.pk_bytes();
        self.time_sig = authority.sign(&time_attest_msg(t, &self.proof_hash()));
    }
}

/// Per-name chain state held by the registrar: the head of the append-only
/// proof chain, its timestamp, and the last serial.  In deployment the head is
/// periodically committed to an external append-only log / timestamp authority,
/// so the chain's position at a wall-clock time is publicly witnessed — which
/// is what makes the `created_at` unforgeable (a proof chaining from a
/// publicly-anchored head cannot have been created before that anchor).
#[derive(Clone, Copy)]
pub struct NiChainState {
    pub head_hash: [u8; 32],
    pub head_created_at: u64,
    pub last_serial: u64,
}
impl NiChainState {
    /// Genesis state for a freshly enrolled name.
    pub fn genesis() -> Self {
        Self { head_hash: [0u8; 32], head_created_at: 0, last_serial: 0 }
    }
    /// Advance the chain after accepting `update`.
    pub fn advance(&mut self, update: &NiUpdate) {
        self.head_hash = update.proof_hash();
        self.head_created_at = update.created_at;
        self.last_serial = update.serial;
    }
}

/// Build an NI-gated update.  In Tier-1 the `owner` runs this (or delegates
/// the `prove_inner_shard` step to a public swarm and signs the result).
pub fn build_ni_update(
    owner: &AuthorityKeypair,
    name: &str,
    records: &[DnsRecord],
    serial: u64,
    created_at: u64,
    prev_hash: [u8; 32],
    salt: [u8; 16],
    ldt: LdtMode,
) -> NiUpdate {
    let owner_pk = owner.pk_bytes();

    let leaf_hashes: Vec<[u8; 32]> = records.iter().map(|r| r.leaf_hash(&salt)).collect();
    let mk_root = merkle_root(&merkle_build(&leaf_hashes));

    // FS anchor folds owner pk (proof<->pk), creation date (temporal gate),
    // and the previous proof hash (anchored chain).
    let fs = ni_fs_binding(&owner_pk, name, &mk_root, serial, created_at, &prev_hash);
    let inner = prove_inner_shard(&salt, records, &fs, ldt);
    debug_assert_eq!(inner.merkle_root, mk_root);

    // Owner signs the same binding → sig <-> pk binding.
    let owner_sig = owner.sign(&fs);

    NiUpdate {
        name: name.to_string(),
        records: records.to_vec(),
        serial,
        merkle_root: mk_root,
        merkle_salt: salt,
        inner_n_trace: inner.n_trace,
        inner_root_f0: inner.root_f0.to_vec(),
        inner_stark_proof: inner.proof_blob,
        owner_pk,
        owner_sig,
        created_at,
        prev_proof_hash: prev_hash,
        attested_time: 0,
        time_authority_pk: Vec::new(),
        time_sig: Vec::new(),
    }
}

/// Why a registrar rejected an NI-gated update.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NiReject {
    /// No owner key is registered for this name (trust root absent).
    Unregistered,
    /// The carried owner pk does not match the name's registered key.
    PkBindingMismatch,
    /// The owner ML-DSA signature did not verify.
    SignatureInvalid,
    /// The Merkle root does not commit the carried records.
    MerkleMismatch,
    /// The carried `inner_root_f0` does not match the proof's commitment.
    ProofMismatch,
    /// The inner STARK failed verification (e.g. proof bound to a different key).
    StarkInvalid,
    /// The update's serial is not newer than the last accepted one (replay).
    StaleSerial,
    /// The proof was created at/after the configured CRQC cutoff date — a
    /// classical signature it attests could be a post-quantum forgery.
    PastCutoff,
    /// `prev_proof_hash` does not match the registrar's current chain head
    /// (reordering / backdating attempt).
    BadChainLink,
    /// The creation timestamp predates the chain head (time ran backwards).
    Backdated,
    /// A trusted time authority is required but the proof carries no valid
    /// time attestation (self-claimed / manipulated timestamp).
    TimeUnattested,
}

/// Registrar acceptance: enforces the triple binding + freshness.  Returns
/// `Ok(())` iff the update is a fresh, owner-authorized, key-bound proof for a
/// registered name.
pub fn accept_ni_update(
    registry: &NameKeyRegistry,
    chain: &NiChainState,
    crqc_cutoff: u64,
    trusted_time_authority_pk: Option<&[u8]>,
    update: &NiUpdate,
    ldt: LdtMode,
) -> Result<(), NiReject> {
    use ark_serialize::{CanonicalDeserialize, Compress, Validate};

    // (1) name <-> pk: owner key registered for this name?
    let want = registry
        .registered_pk_hash(&update.name)
        .ok_or(NiReject::Unregistered)?;
    if pk_binding_hash(&update.owner_pk) != want {
        return Err(NiReject::PkBindingMismatch);
    }

    // Anchored chain: the update must extend the current head (anti-backdating).
    if update.prev_proof_hash != chain.head_hash {
        return Err(NiReject::BadChainLink);
    }
    // Time moves forward along the chain (cannot chain an earlier-dated proof).
    if update.created_at < chain.head_created_at {
        return Err(NiReject::Backdated);
    }
    // Temporal gate: trustworthy only if provably created before the CRQC era.
    if update.created_at >= crqc_cutoff {
        return Err(NiReject::PastCutoff);
    }
    // Freshness (anti-replay).
    if update.serial <= chain.last_serial {
        return Err(NiReject::StaleSerial);
    }

    // Recompute the FS anchor (owner pk + date + prev-hash) from carried fields.
    let fs = ni_fs_binding(
        &update.owner_pk, &update.name, &update.merkle_root, update.serial,
        update.created_at, &update.prev_proof_hash,
    );

    // (3) sig <-> pk: ML-DSA over the binding under the owner key.
    if !ml_dsa_verify_pk_bytes(&update.owner_pk, &fs, &update.owner_sig) {
        return Err(NiReject::SignatureInvalid);
    }

    // Merkle commits exactly the carried records.
    let leaf_hashes: Vec<[u8; 32]> =
        update.records.iter().map(|r| r.leaf_hash(&update.merkle_salt)).collect();
    if merkle_root(&merkle_build(&leaf_hashes)) != update.merkle_root {
        return Err(NiReject::MerkleMismatch);
    }

    // (2) proof <-> pk: the inner STARK must be FS-bound to `fs` (owner pk).
    // build_params feeds `fs` into the verifier's public-input hash, so a
    // proof generated under a different key's binding fails deep_fri_verify.
    let proof = deep_ali::fri::DeepFriProof::<Ext>::deserialize_with_mode(
        update.inner_stark_proof.as_slice(),
        Compress::Yes,
        Validate::Yes,
    )
    .map_err(|_| NiReject::StarkInvalid)?;
    if proof.root_f0.as_slice() != update.inner_root_f0.as_slice() {
        return Err(NiReject::ProofMismatch);
    }
    let n0 = update.inner_n_trace * BLOWUP;
    let params = build_params(n0, &fs, ldt);
    if !deep_ali::fri::deep_fri_verify::<Ext>(&params, &proof) {
        return Err(NiReject::StarkInvalid);
    }

    // Proof of time: when a trusted time authority is configured, the creation
    // time must be authority-attested (not self-claimed).  The attestation is
    // the authority's signature over (attested_time ‖ proof_hash); a deployed
    // verifier checks it in-circuit via the same ML-DSA signature AIR.
    if let Some(ta_pk) = trusted_time_authority_pk {
        if update.attested_time != update.created_at
            || update.time_authority_pk.as_slice() != ta_pk
            || !ml_dsa_verify_pk_bytes(
                &update.time_authority_pk,
                &time_attest_msg(update.attested_time, &update.proof_hash()),
                &update.time_sig,
            )
        {
            return Err(NiReject::TimeUnattested);
        }
    }

    Ok(())
}

/// Verify an ML-DSA signature from raw public-key bytes (level inferred from
/// key length, empty context — matching [`AuthorityKeypair::sign`]).
fn ml_dsa_verify_pk_bytes(pk_bytes: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    use fips204::traits::{SerDes, Verifier};
    use fips204::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
    match pk_bytes.len() {
        ml_dsa_44::PK_LEN => {
            let Ok(pk_arr): Result<[u8; ml_dsa_44::PK_LEN], _> = pk_bytes.try_into() else {
                return false;
            };
            let Ok(pk) = ml_dsa_44::PublicKey::try_from_bytes(pk_arr) else { return false };
            let Ok(sig_arr): Result<[u8; ml_dsa_44::SIG_LEN], _> = sig.try_into() else {
                return false;
            };
            pk.verify(msg, &sig_arr, b"")
        }
        ml_dsa_65::PK_LEN => {
            let Ok(pk_arr): Result<[u8; ml_dsa_65::PK_LEN], _> = pk_bytes.try_into() else {
                return false;
            };
            let Ok(pk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else { return false };
            let Ok(sig_arr): Result<[u8; ml_dsa_65::SIG_LEN], _> = sig.try_into() else {
                return false;
            };
            pk.verify(msg, &sig_arr, b"")
        }
        ml_dsa_87::PK_LEN => {
            let Ok(pk_arr): Result<[u8; ml_dsa_87::PK_LEN], _> = pk_bytes.try_into() else {
                return false;
            };
            let Ok(pk) = ml_dsa_87::PublicKey::try_from_bytes(pk_arr) else { return false };
            let Ok(sig_arr): Result<[u8; ml_dsa_87::SIG_LEN], _> = sig.try_into() else {
                return false;
            };
            pk.verify(msg, &sig_arr, b"")
        }
        _ => false,
    }
}
