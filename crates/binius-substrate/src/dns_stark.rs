// D (DNS-STARK realized over Binius) — the CAPSTONE. Each DNSSEC record's RRSIG
// verification is proven by the matching signature AIR (ML-DSA→S1, Ed25519/ECDSA→S2,
// RSA→S3) over the forked Binius pipeline at NIST L1/L3/L5; the per-record proofs are
// aggregated by R (Tier-A batched Merkle over inner roots) into ONE epoch/zone artifact
// with constant consumer (resolver) verify. This is the binary-field realization of the
// STARK-DNS system (ACNS) whose Goldilocks design + soundness already exist
// (see [[project_starkdns_ndss2027_submitted]], [[project_mixed_zone_rollup]],
// [[project_se_zone_hnpl]]).
//
// ── THE PIPELINE (per record → zone artifact) ──────────────────────────────────────
//   record R with RRSIG over an RRset, signed by a DNSKEY (ZSK) of algorithm alg:
//     1. signing_input = RRSIG_RDATA(without signature) ‖ canonical RRset   [RFC 4034 §3.1.8.1]
//     2. dispatch(alg) → the S-slice AIR that proves "sig verifies over signing_input under
//        the DNSKEY":  8/10 → RSA/S3,  13 → ECDSA-P256/S2,  14 → ECDSA-P384/S2,
//        15 → Ed25519/S2,  <ML-DSA codepoint> → ML-DSA/S1.
//     3. the S-slice proof exposes its PCS/Merkle root r_R as a boundary.
//   zone/epoch:
//     4. R Tier-A: pull all r_R via the join channel, batched Merkle → epoch root R*
//        (public Boundary). Ships {r_R} (N×32 B) + one master proof.  [O(N²)→O(N) fix]
//   chain-of-trust (also each an S-slice verify, aggregated the same way):
//     • DS(parent) → DNSKEY(child KSK)   [delegation hash, RFC 4034 §5]
//     • KSK signs the DNSKEY RRset;  ZSK signs the zone RRsets.
//   denial of existence: NSEC3 (hashed owner names) proven + aggregated identically.
//   resolver: verifies the ONE master proof + R*, then answers queries with O(1) checks
//     against the shipped record roots (the offline/edge resolver model).
//
// ── WHAT D ADDS (it is the assembly of assemblies) ─────────────────────────────────
//   * the canonical RRSIG signing-input construction (the exact bytes the S-slice hashes),
//   * the algorithm → S-slice dispatch,
//   * the DNSKEY key-tag (RFC 4034 App B) linking an RRSIG to its DNSKEY,
//   * the zone/epoch aggregation wiring (R Tier-A over the per-record roots),
//   * the chain-of-trust + NSEC3 composition (design).
//   Everything below the dispatch is S1/S2/S3 (drafted) and R (drafted); D is the DNSSEC
//   semantics + the wiring.
//
// ── SOUNDNESS BOUNDARY ────────────────────────────────────────────────────────────
//   IN-CIRCUIT: each per-record proof is a sound S-slice verify over the canonical
//   signing_input (a tampered record ⇒ signing_input changes ⇒ the S-slice's sig-verify
//   equality fails ⇒ no witness). The epoch root R* soundly commits to the exact multiset
//   of record roots (R Tier-A). A tampered zone (added/removed/edited record) ⇒ some r_R
//   changes or the multiset changes ⇒ R* ≠ claimed ⇒ reject. This is the STARK-DNS
//   integrity guarantee over Binius at NIST L1/L3/L5.
//   TRUST NOT RE-EXECUTED IN-MASTER (Tier A): that each shipped r_R corresponds to a
//   VERIFYING inner proof — discharged by the resolver checking the (small, shipped) inner
//   proofs, exactly as the ACNS rollup specifies; Tier-B (R) would fold this in-circuit.
//   The DNSSEC chain-of-trust root (DS at the trust anchor) is the external root of trust,
//   unchanged from classical DNSSEC (see [[project_ni_gated_distributed_proving]]).
//   OUTER COMMITMENT SHA-256; challenge field carries FS security at all three levels.
// ============================================================================
//
// DRAFT STATUS (D, in progress): the DNSSEC reference layer (canonical signing-input,
// key-tag, algorithm dispatch, zone aggregation via R's merkle_root_sha3) is implemented
// + gated, cross-checked with Python. The in-circuit assembly (per-record S-slice AIRs +
// R Tier-A master) is specified above and wired LAST, after S1/S2/S3/R prove paths land.
// Heavy prove gates `#[ignore]`.

/// DNSSEC signature algorithm numbers (IANA), mapped to the S-slice that proves them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DnssecAlgorithm {
	/// 8 — RSA/SHA-256 (also 5/7/10 RSA variants) → S3.
	RsaSha256,
	/// 13 — ECDSA P-256/SHA-256 → S2.
	EcdsaP256Sha256,
	/// 14 — ECDSA P-384/SHA-384 → S2.
	EcdsaP384Sha384,
	/// 15 — Ed25519 → S2.
	Ed25519,
	/// ML-DSA (post-quantum, private/experimental codepoint) → S1.
	MlDsa,
}

/// Which S-slice AIR proves a given DNSSEC algorithm's RRSIG verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SSlice {
	S1MlDsa,
	S2Ec,
	S3Rsa,
}

impl DnssecAlgorithm {
	/// The IANA algorithm number.
	pub const fn iana(self) -> u8 {
		match self {
			DnssecAlgorithm::RsaSha256 => 8,
			DnssecAlgorithm::EcdsaP256Sha256 => 13,
			DnssecAlgorithm::EcdsaP384Sha384 => 14,
			DnssecAlgorithm::Ed25519 => 15,
			DnssecAlgorithm::MlDsa => 17, // illustrative PQ codepoint
		}
	}

	/// Dispatch to the S-slice AIR that verifies this algorithm.
	pub const fn s_slice(self) -> SSlice {
		match self {
			DnssecAlgorithm::RsaSha256 => SSlice::S3Rsa,
			DnssecAlgorithm::EcdsaP256Sha256
			| DnssecAlgorithm::EcdsaP384Sha384
			| DnssecAlgorithm::Ed25519 => SSlice::S2Ec,
			DnssecAlgorithm::MlDsa => SSlice::S1MlDsa,
		}
	}
}

/// Canonical wire-format DNS name (RFC 1035 §3.1): length-prefixed labels, root 0x00.
/// (Canonical form for DNSSEC uses lowercase labels; caller lowercases.)
pub fn wire_name(name: &str) -> Vec<u8> {
	let mut out = Vec::new();
	for label in name.trim_end_matches('.').split('.') {
		if label.is_empty() {
			continue;
		}
		out.push(label.len() as u8);
		out.extend_from_slice(label.as_bytes());
	}
	out.push(0);
	out
}

/// RFC 4034 Appendix B — DNSKEY key tag (for algorithms ≠ 1): a 16-bit checksum over the
/// DNSKEY RDATA. Links an RRSIG (which carries the key tag) to the signing DNSKEY.
pub fn dnskey_key_tag(rdata: &[u8]) -> u16 {
	let mut ac: u32 = 0;
	for (i, &b) in rdata.iter().enumerate() {
		ac += if i & 1 == 1 { b as u32 } else { (b as u32) << 8 };
	}
	ac += (ac >> 16) & 0xFFFF;
	(ac & 0xFFFF) as u16
}

/// One resource record in canonical form for the RRSIG signing input (RFC 4034 §3.1.8.1):
/// canonical owner name ‖ type ‖ class ‖ original TTL ‖ RDLENGTH ‖ canonical RDATA.
pub struct CanonicalRr {
	pub name: String,
	pub rr_type: u16,
	pub class: u16,
	pub orig_ttl: u32,
	pub rdata: Vec<u8>,
}

impl CanonicalRr {
	fn encode(&self) -> Vec<u8> {
		let mut v = wire_name(&self.name.to_lowercase());
		v.extend_from_slice(&self.rr_type.to_be_bytes());
		v.extend_from_slice(&self.class.to_be_bytes());
		v.extend_from_slice(&self.orig_ttl.to_be_bytes());
		v.extend_from_slice(&(self.rdata.len() as u16).to_be_bytes());
		v.extend_from_slice(&self.rdata);
		v
	}
}

/// The RRSIG RDATA fields (RFC 4034 §3.1), WITHOUT the trailing signature — this prefix is
/// the first part of the signing input.
pub struct RrsigFields {
	pub type_covered: u16,
	pub algorithm: u8,
	pub labels: u8,
	pub orig_ttl: u32,
	pub sig_expiration: u32,
	pub sig_inception: u32,
	pub key_tag: u16,
	pub signer_name: String,
}

impl RrsigFields {
	fn encode_no_sig(&self) -> Vec<u8> {
		let mut v = Vec::new();
		v.extend_from_slice(&self.type_covered.to_be_bytes());
		v.push(self.algorithm);
		v.push(self.labels);
		v.extend_from_slice(&self.orig_ttl.to_be_bytes());
		v.extend_from_slice(&self.sig_expiration.to_be_bytes());
		v.extend_from_slice(&self.sig_inception.to_be_bytes());
		v.extend_from_slice(&self.key_tag.to_be_bytes());
		v.extend_from_slice(&wire_name(&self.signer_name.to_lowercase()));
		v
	}
}

/// RFC 4034 §3.1.8.1 — the exact byte string a DNSSEC signature is computed over:
/// RRSIG_RDATA(without signature) ‖ RR(1) ‖ RR(2) ‖ … (RRs in canonical order). This is
/// the message the dispatched S-slice AIR proves the signature verifies against.
pub fn rrsig_signing_input(rrsig: &RrsigFields, rrset: &[CanonicalRr]) -> Vec<u8> {
	let mut out = rrsig.encode_no_sig();
	for rr in rrset {
		out.extend_from_slice(&rr.encode());
	}
	out
}

/// Aggregate a zone/epoch's per-record inner-proof roots into ONE epoch root via R's
/// batched Merkle (Tier-A). A tampered/added/removed record changes some r_R ⇒ epoch root
/// changes ⇒ reject. The shipped {r_R} + one master proof = the edge artifact.
pub fn zone_epoch_root(record_roots: &[[u8; 32]]) -> [u8; 32] {
	crate::recursion::merkle_root_sha3(record_roots)
}

/// A parent DS record's binding fields (RFC 4034 §5.1): key tag, algorithm, digest type,
/// and digest — the delegation commitment to a child zone's DNSKEY (KSK).
pub struct DsRecord {
	pub key_tag: u16,
	pub algorithm: u8,
	pub digest_type: u8,
	pub digest: Vec<u8>,
}

/// RFC 4034 §5.1.4 — the DS digest H(canonical owner name ‖ DNSKEY RDATA); digest_type 2 =
/// SHA-256 (the DNSSEC default). Reuses the SHA-256 message-hash gadget (`sha256_ref`).
pub fn ds_digest_sha256(owner_name: &str, dnskey_rdata: &[u8]) -> [u8; 32] {
	let mut input = wire_name(&owner_name.to_lowercase());
	input.extend_from_slice(dnskey_rdata);
	crate::sha512_gadget::sha256_ref(&input)
}

/// RFC 4034 §5.2 — verify a DS record binds a child DNSKEY: the DS key tag == the DNSKEY's,
/// the algorithm matches, digest_type is SHA-256, and DS.digest == H(owner ‖ DNSKEY RDATA).
/// THIS is the DS→DNSKEY delegation link of the chain of trust; in-circuit it is the key-tag
/// gadget + the SHA-256 gadget + a digest byte-equality, aggregated into the epoch R* like any
/// other record. The parent's DS is itself covered by the parent's RRSIG (a separate S-slice),
/// so the whole chain up to the trust anchor is bound.
pub fn ds_binds_dnskey(ds: &DsRecord, owner_name: &str, dnskey_rdata: &[u8]) -> bool {
	dnskey_rdata.len() >= 4
		&& ds.key_tag == dnskey_key_tag(dnskey_rdata)
		&& ds.algorithm == dnskey_rdata[3]
		&& ds.digest_type == 2
		&& ds.digest == ds_digest_sha256(owner_name, dnskey_rdata)
}

/// RFC 5155 §5 — the NSEC3 owner-name hash: iterated salted SHA-1 of the canonical name.
/// IH(salt,x,0) = SHA-1(x ‖ salt); IH(salt,x,k) = SHA-1(IH(salt,x,k−1) ‖ salt). Reuses the
/// SHA-1 gadget. (SHA-1 appears ONLY here — mandated by NSEC3 — never on a signature path.)
pub fn nsec3_hash(name: &str, salt: &[u8], iterations: usize) -> [u8; 20] {
	let mut input = wire_name(&name.to_lowercase());
	input.extend_from_slice(salt);
	let mut x = crate::sha512_gadget::sha1_ref(&input);
	for _ in 0..iterations {
		let mut nx = x.to_vec();
		nx.extend_from_slice(salt);
		x = crate::sha512_gadget::sha1_ref(&nx);
	}
	x
}

/// Whether a hashed name `hq` falls STRICTLY in the gap (owner, next) of an NSEC3 record, with
/// circular wrap for the last record in the sorted chain (owner > next).
pub fn nsec3_covers(hq: &[u8; 20], owner: &[u8; 20], next: &[u8; 20]) -> bool {
	if owner < next {
		owner < hq && hq < next
	} else {
		hq > owner || hq < next // wrap-around
	}
}

/// NSEC3 denial of existence: the query name's iterated hash falls in the gap of the given
/// NSEC3 record ⇒ the name provably does NOT exist. In-circuit = the iterated SHA-1 gadget +
/// two S0-carry range comparisons (with the wrap selector); the NSEC3 record is itself
/// RRSIG-signed (a separate S-slice), aggregated into the epoch R*.
pub fn nsec3_denies(query: &str, salt: &[u8], iterations: usize, owner: &[u8; 20], next: &[u8; 20]) -> bool {
	nsec3_covers(&nsec3_hash(query, salt, iterations), owner, next)
}

/// The message an RRSIG signature covers for the SHA-256 algorithms (RSA 8/10, ECDSA-P256
/// 13): SHA-256 of the canonical signing input. Because signing_input = RRSIG_RDATA(no sig) ‖
/// canonical RRset, this digest is a FAITHFUL function of the record — any change to the
/// RRset or the RRSIG fields changes it, so the signature (verified by the dispatched S-slice)
/// binds the exact record. Reuses the SHA-256 gadget.
pub fn rrsig_sha256_message(rrsig: &RrsigFields, rrset: &[CanonicalRr]) -> [u8; 32] {
	crate::sha512_gadget::sha256_ref(&rrsig_signing_input(rrsig, rrset))
}

/// Which (S-slice, hash) an RRSIG algorithm dispatches to for signature verification over the
/// signing input — the per-record verify route.
pub fn rrsig_verify_route(algorithm: u8) -> (SSlice, &'static str) {
	match algorithm {
		8 | 10 => (SSlice::S3Rsa, "SHA-256"),                              // RSA/SHA-256
		13 => (SSlice::S2Ec, "SHA-256"),                                  // ECDSA-P256
		14 => (SSlice::S2Ec, "SHA-384"),                                  // ECDSA-P384
		15 => (SSlice::S2Ec, "Ed25519(message=signing_input)"),          // EdDSA
		17 => (SSlice::S1MlDsa, "SHAKE-256"),                             // ML-DSA
		_ => (SSlice::S2Ec, "unsupported"),
	}
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT ASSEMBLY (wired last — see DRAFT STATUS)
// ──────────────────────────────────────────────────────────────────────────────────
//
// per-record table: dispatch(alg) selects the S-slice AIR (S1 ML-DSA / S2 EC / S3 RSA);
//   its public boundary is (DNSKEY pubkey, signing_input, signature); it proves the sig
//   verifies; it exposes r_R. The signing_input is itself constrained: RRSIG_RDATA and the
//   canonical RRset are bit-decomposed public columns, and the S-slice's hash gadget
//   (SHA-256 for alg 8/13, SHA-512 for Ed25519, SHAKE for ML-DSA) consumes them — so a
//   tampered record cannot match.
// epoch master: R Tier-A batched Merkle over {r_R} → R* Boundary; strands = subtrees.
// chain-of-trust: DS→DNSKEY (a hash-equality S-slice) and KSK/ZSK RRSIG proofs are records
//   too, aggregated into the same R*; the trust anchor DS is the external boundary.
// NSEC3: the hashed-owner denial is an S-slice (SHA-1/SHA-256 hash + range proof over the
//   NSEC3 chain), aggregated identically.
//
// TAMPERED-ZONE-REJECTS (D headline gate): a genuine zone (mixed RSA/ECDSA/Ed25519/ML-DSA
// records) aggregates to R*; any of {edit an RRset, swap a signature, drop a record, forge
// a DNSKEY} ⇒ the offending S-slice has no witness OR the multiset/R* changes ⇒ reject.

#[cfg(test)]
mod tests {
	use sha2::{Digest, Sha256};

	use super::*;

	/// GATE ref-D-1 — algorithm → S-slice dispatch is total and correct (RSA→S3, EC/Ed→S2,
	/// ML-DSA→S1), and IANA numbers are right.
	#[test]
	fn algorithm_dispatch() {
		assert_eq!(DnssecAlgorithm::RsaSha256.s_slice(), SSlice::S3Rsa);
		assert_eq!(DnssecAlgorithm::EcdsaP256Sha256.s_slice(), SSlice::S2Ec);
		assert_eq!(DnssecAlgorithm::EcdsaP384Sha384.s_slice(), SSlice::S2Ec);
		assert_eq!(DnssecAlgorithm::Ed25519.s_slice(), SSlice::S2Ec);
		assert_eq!(DnssecAlgorithm::MlDsa.s_slice(), SSlice::S1MlDsa);
		assert_eq!(DnssecAlgorithm::RsaSha256.iana(), 8);
		assert_eq!(DnssecAlgorithm::EcdsaP256Sha256.iana(), 13);
		assert_eq!(DnssecAlgorithm::Ed25519.iana(), 15);
		println!("GATE ref-D-1: DNSSEC alg → S-slice dispatch total (8→S3, 13/14/15→S2, ML-DSA→S1)");
	}

	/// GATE ref-D-2 — DNSKEY key tag matches the RFC 4034 App B algorithm (cross-checked
	/// against Python for a sample KSK RDATA).
	#[test]
	fn key_tag_matches_reference() {
		// flags=257 (KSK), proto=3, alg=13, then a 64-byte P-256 key = bytes 0..64
		let mut rdata = vec![0x01, 0x01, 0x03, 0x0d];
		rdata.extend(0u8..64u8);
		assert_eq!(dnskey_key_tag(&rdata), 59409, "key tag != RFC 4034 App B reference");
		println!("GATE ref-D-2: DNSKEY key tag (RFC 4034 App B) == 59409 for the sample KSK");
	}

	/// GATE ref-D-3 — the RRSIG signing input is the canonical RFC 4034 §3.1.8.1 byte
	/// string (length + SHA-256 cross-checked against Python).
	#[test]
	fn signing_input_canonical() {
		let key_tag = {
			let mut rdata = vec![0x01, 0x01, 0x03, 0x0d];
			rdata.extend(0u8..64u8);
			dnskey_key_tag(&rdata)
		};
		let rrsig = RrsigFields {
			type_covered: 1, // A
			algorithm: 13,
			labels: 3,
			orig_ttl: 3600,
			sig_expiration: 1_700_000_000,
			sig_inception: 1_690_000_000,
			key_tag,
			signer_name: "example.com".into(),
		};
		let rr = CanonicalRr {
			name: "www.example.com".into(),
			rr_type: 1,
			class: 1,
			orig_ttl: 3600,
			rdata: vec![1, 2, 3, 4],
		};
		let si = rrsig_signing_input(&rrsig, &[rr]);
		assert_eq!(si.len(), 62, "signing input length != canonical");
		let digest = Sha256::digest(&si);
		let hex: String = digest.iter().take(8).map(|b| format!("{b:02x}")).collect();
		assert_eq!(hex, "e2b7f6a62e989ee5", "signing input SHA-256 != Python reference");
		println!("GATE ref-D-3: RRSIG signing input canonical (62 B, SHA-256 e2b7f6a6…) == Python");
	}

	/// GATE ref-D-4 — zone/epoch aggregation: a mixed zone of N record roots reduces to one
	/// epoch root; tampering ANY record (edit/swap/drop) changes it. Reuses R Tier-A.
	#[test]
	fn zone_aggregation_and_tamper() {
		let leaf = |b: u8| -> [u8; 32] {
			let mut h = Sha256::new();
			h.update([b]);
			h.finalize().into()
		};
		// 3-record mixed zone (e.g. RSA + Ed25519 + ML-DSA)
		let roots: Vec<[u8; 32]> = (0..3).map(leaf).collect();
		let epoch = zone_epoch_root(&roots);
		assert_eq!(epoch.len(), 32);
		// edit a record
		let mut bad = roots.clone();
		bad[1] = leaf(0xEE);
		assert_ne!(zone_epoch_root(&bad), epoch, "edited record did not change epoch root");
		// drop a record
		assert_ne!(zone_epoch_root(&roots[..2]), epoch, "dropped record did not change epoch root");
		println!("GATE ref-D-4: zone → epoch root via R Tier-A; edit/drop record ⇒ different epoch");
	}

	/// GATE ref-D-5 (chain-of-trust DS→DNSKEY) — a DS record binds its child DNSKEY (key tag
	/// + algorithm + SHA-256(owner‖DNSKEY) digest); a tampered key tag, a changed DNSKEY (which
	/// breaks BOTH the key tag and the digest), and a wrong owner name all reject. This is the
	/// delegation link that ties the chain of trust up to the trust anchor.
	#[test]
	fn ds_dnskey_chain_of_trust() {
		// DNSKEY RDATA: flags=257 (KSK), protocol=3, algorithm=13 (ECDSA-P256), 64-byte key.
		let mut dnskey = vec![0x01u8, 0x01, 0x03, 0x0d];
		dnskey.extend(0u8..64u8);
		let owner = "example.com";
		let ds = DsRecord {
			key_tag: dnskey_key_tag(&dnskey),
			algorithm: 13,
			digest_type: 2,
			digest: ds_digest_sha256(owner, &dnskey).to_vec(),
		};
		assert!(ds_binds_dnskey(&ds, owner, &dnskey), "honest DS must bind its DNSKEY");
		let hex: String = ds.digest.iter().take(8).map(|b| format!("{b:02x}")).collect();
		assert_eq!(hex, "186ea634d4cf62f2", "DS digest != Python reference");

		let bad_tag = DsRecord {
			key_tag: ds.key_tag ^ 1,
			algorithm: 13,
			digest_type: 2,
			digest: ds.digest.clone(),
		};
		assert!(!ds_binds_dnskey(&bad_tag, owner, &dnskey), "bad key tag must reject");

		let mut dnskey2 = dnskey.clone();
		dnskey2[10] ^= 1; // flip a key byte ⇒ key tag AND digest change
		assert!(!ds_binds_dnskey(&ds, owner, &dnskey2), "changed DNSKEY must reject");
		assert!(!ds_binds_dnskey(&ds, "evil.com", &dnskey), "wrong owner must reject");
		println!("GATE ref-D-5: DS→DNSKEY (key_tag + SHA-256(owner‖DNSKEY)) binds; tampered key/owner/tag reject");
	}

	/// GATE ref-D-6 (NSEC3 denial of existence) — a non-existent name (whose iterated SHA-1
	/// hash falls in a gap between two sorted NSEC3 hashes) is provably denied, an EXISTING
	/// name (hash == an owner) is NOT covered, and the circular wrap-around case is handled.
	#[test]
	fn nsec3_denial_of_existence() {
		let salt = [0xAAu8, 0xBB];
		let iters = 5;
		let ha = nsec3_hash("a.example.com", &salt, iters);
		let hb = nsec3_hash("z.example.com", &salt, iters);
		let (owner, next) = if ha < hb { (ha, hb) } else { (hb, ha) };
		// a non-existent name hashing into the (owner,next) gap is deniable
		let hq = nsec3_hash("nonexistent.example.com", &salt, iters);
		assert!(
			nsec3_covers(&hq, &owner, &next) || nsec3_covers(&hq, &next, &owner),
			"a name hashing into a gap must be deniable"
		);
		// an existing name (hash == owner) is NOT strictly covered ⇒ not falsely denied
		assert!(!nsec3_covers(&owner, &owner, &next), "an existing name must not be covered");

		// explicit range + wrap cases
		assert!(nsec3_covers(&[0x80; 20], &[0x00; 20], &[0xFF; 20]), "normal gap");
		let (owner_w, next_w) = ([0xF0u8; 20], [0x10u8; 20]); // wrap (owner > next)
		assert!(nsec3_covers(&[0xFE; 20], &owner_w, &next_w), "wrap-around: hq>owner covered");
		assert!(nsec3_covers(&[0x05; 20], &owner_w, &next_w), "wrap-around: hq<next covered");
		assert!(!nsec3_covers(&[0x50; 20], &owner_w, &next_w), "wrap: middle (existing) not covered");
		println!("GATE ref-D-6: NSEC3 (iterated salted SHA-1 + gap coverage w/ wrap) denies non-existent, not existing");
	}

	/// GATE ref-D-7 (RRSIG signature-to-record binding) — the signed message is SHA-256 of the
	/// canonical signing input, so it BINDS the record: any change to the RRset RDATA or an
	/// RRSIG field yields a different signed message (⇒ the dispatched S-slice's signature
	/// check fails on a tampered record). Also checks the algorithm → S-slice verify routes.
	#[test]
	fn rrsig_record_binding() {
		let mk_rr = |rdata: Vec<u8>| CanonicalRr {
			name: "www.example.com".into(),
			rr_type: 1,
			class: 1,
			orig_ttl: 3600,
			rdata,
		};
		let mk_rrsig = |ttl: u32| RrsigFields {
			type_covered: 1,
			algorithm: 13,
			labels: 3,
			orig_ttl: ttl,
			sig_expiration: 1_700_000_000,
			sig_inception: 1_690_000_000,
			key_tag: 12345,
			signer_name: "example.com".into(),
		};
		let base = rrsig_sha256_message(&mk_rrsig(3600), &[mk_rr(vec![1, 2, 3, 4])]);
		// tamper the RRset RDATA ⇒ different signed message (record binding)
		assert_ne!(
			rrsig_sha256_message(&mk_rrsig(3600), &[mk_rr(vec![1, 2, 3, 5])]),
			base,
			"changed record RDATA must change the signed message"
		);
		// tamper an RRSIG field (original TTL) ⇒ different signed message
		assert_ne!(
			rrsig_sha256_message(&mk_rrsig(7200), &[mk_rr(vec![1, 2, 3, 4])]),
			base,
			"changed RRSIG field must change the signed message"
		);
		// dispatch routes to the right S-slice per algorithm
		assert_eq!(rrsig_verify_route(8).0, SSlice::S3Rsa);
		assert_eq!(rrsig_verify_route(13).0, SSlice::S2Ec);
		assert_eq!(rrsig_verify_route(15).0, SSlice::S2Ec);
		assert_eq!(rrsig_verify_route(17).0, SSlice::S1MlDsa);
		println!("GATE ref-D-7: RRSIG signed message = SHA-256(signing_input) binds record (tamper RRset/RRSIG ⇒ different); routes to S1/S2/S3");
	}

	/// GATE prove-D-0 (D per-record verify, RSA slice) — a real DNSSEC record's RRSIG verifies
	/// in-circuit over B256, wiring the S3 RSA slice to the canonical DNSSEC signing input. A
	/// www.example.com A record and an RRSIG (algorithm 8 = RSA/SHA-256) are signed by a genuine
	/// RSA key (e=3, RSA-496 so the modexp is tractable): the signature s satisfies
	/// s³ mod N = EMSA-PKCS1-v1.5(SHA-256(RRSIG_RDATA ‖ A-record)), the exact RFC 4034 §3.1.8.1
	/// signing input. The circuit proves the modexp s³ mod N as two seam-glued ModMul strands at
	/// W=1024 and PINS the recovered encoded message to the EMSA encoding of the record's signing
	/// input (all ceil(np/64)=8 lanes, full padding + digest). Balanced iff the signature verifies
	/// for THIS record ⇒ ACCEPT. Editing the record (here the A rdata / IP address) changes the
	/// canonical signing input ⇒ a different SHA-256 ⇒ a different EMSA, which s³ does not equal, so
	/// the boundary unbalances ⇒ REJECT — a signature does not verify for a tampered record. This is
	/// the per-record leg of prove-D-1; the epoch aggregation (R Tier-A over record roots) and the
	/// other slices (Ed25519/ML-DSA already proven in S2/S1) compose on top. Honest record
	/// PROVES+VERIFIES at NIST L1; a tampered record is REJECTED.
	#[test]
	fn dns_rsa_record_rrsig_verify_over_b256() {
		use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
		use crate::nonnative::{ModMul, ModMulRow};
		use crate::rsa_verify::emsa_pkcs1_sha256;
		use binius_core::constraint_system::channel::FlushDirection;
		use binius_core::fiat_shamir::HasherChallenger;
		use binius_hash::sha2::Sha256Compression;
		use binius_m3::builder::{Boundary, ConstraintSystem, Statement, WitnessIndex, B64};
		use bumpalo::Bump;
		use num_bigint::BigUint;
		use rand::{rngs::StdRng, SeedableRng};
		use rsa::traits::PublicKeyParts;
		use rsa::{Pkcs1v15Sign, RsaPrivateKey};

		const W: usize = 1024;
		fn to_bits(x: &BigUint) -> Vec<bool> {
			(0..W as u64).map(|i| x.bit(i)).collect()
		}

		// A genuine DNSSEC A record and its RRSIG (algorithm 8 = RSA/SHA-256).
		let rrsig = RrsigFields {
			type_covered: 1, // A
			algorithm: 8,    // RSA/SHA-256
			labels: 3,
			orig_ttl: 3600,
			sig_expiration: 1_735_689_600,
			sig_inception: 1_704_067_200,
			key_tag: 0x4d2,
			signer_name: "example.com".to_string(),
		};
		let a_rr = |ip: [u8; 4]| CanonicalRr {
			name: "www.example.com".to_string(),
			rr_type: 1,
			class: 1,
			orig_ttl: 3600,
			rdata: ip.to_vec(),
		};
		let record = a_rr([93, 184, 216, 34]);
		let digest = rrsig_sha256_message(&rrsig, std::slice::from_ref(&record)); // SHA-256(signing input)

		// Sign the canonical signing input with a genuine RSA-496 key (e=3, for tractable modexp).
		let mut rng = StdRng::seed_from_u64(0xD5_5EC0_0008);
		let e3 = rsa::BigUint::from(3u32);
		let sk = RsaPrivateKey::new_with_exp(&mut rng, 496, &e3).expect("rsa-496 keygen");
		let n = BigUint::from_bytes_be(&sk.n().to_bytes_be());
		let np = n.bits() as usize;
		let n_lanes = (np + 63) / 64;
		let k = (np + 7) / 8;
		let n_bits = to_bits(&n);
		let sig_bytes = sk.sign(Pkcs1v15Sign::new::<Sha256>(), &digest).expect("sign RRSIG");
		let s = BigUint::from_bytes_be(&sig_bytes);
		let s2 = (&s * &s) % &n;
		let em = (&s2 * &s) % &n; // recovered encoded message = s³ mod N

		// The EMSA encoding of THIS record's signing input, and of a TAMPERED record (IP + 1).
		let em_record = BigUint::from_bytes_be(&emsa_pkcs1_sha256(&digest, k));
		assert_eq!(em, em_record, "genuine DNSSEC RRSIG must recover EMSA(SHA-256(signing input))");
		let digest_tampered = rrsig_sha256_message(&rrsig, std::slice::from_ref(&a_rr([93, 184, 216, 35])));
		let em_tampered = BigUint::from_bytes_be(&emsa_pkcs1_sha256(&digest_tampered, k));

		let to_boundary = |x: &BigUint| -> Vec<OurB256> {
			let mut b = x.to_bytes_le();
			b.resize(n_lanes * 8, 0);
			(0..n_lanes).map(|i| OurB256::from(B64::new(u64::from_le_bytes(b[i * 8..i * 8 + 8].try_into().unwrap())))).collect()
		};

		let run = |em_pub: &BigUint, full: bool| -> (bool, String, bool) {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let chs = cs.add_channel("chS");
			let chs2 = cs.add_channel("chS2");
			let chem = cs.add_channel("chEM");
			let mm_sq = ModMul::<W>::build_seamed_in2_chain(&mut cs, &n_bits, np, chs, chs, chs2);
			let mm_mul = ModMul::<W>::build_seamed_in2_chain(&mut cs, &n_bits, np, chs2, chs, chem);
			let boundaries = vec![
				Boundary { values: to_boundary(&s), channel_id: chs, direction: FlushDirection::Push, multiplicity: 3 },
				Boundary { values: to_boundary(em_pub), channel_id: chem, direction: FlushDirection::Pull, multiplicity: 1 },
			];
			let statement = Statement { boundaries, table_sizes: vec![1, 1] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(mm_sq.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				let q = (&s * &s) / &n;
				mm_sq.populate(&mut seg, &[ModMulRow { a: to_bits(&s), b: to_bits(&s), q: to_bits(&q), r: to_bits(&s2) }]).unwrap();
			}
			{
				let tw = witness.init_table(mm_mul.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				let q = (&s2 * &s) / &n;
				mm_mul.populate(&mut seg, &[ModMulRow { a: to_bits(&s2), b: to_bits(&s), q: to_bits(&q), r: to_bits(&em) }]).unwrap();
			}
			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let v = binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness);
			let vok = v.is_ok();
			let verr = v.err().map(|e| e.to_string()).unwrap_or_default();
			if !full {
				return (vok, verr, false);
			}
			let proof = binius_core::constraint_system::prove::<
				U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			let verify_ok = match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf).is_ok(),
			};
			(vok, verr, verify_ok)
		};

		let (vok, verr, verify_ok) = run(&em_record, true);
		assert!(vok, "honest DNSSEC RSA record verify failed validate_witness: {verr}");
		assert!(verify_ok, "genuine DNSSEC RSA RRSIG must PROVE+VERIFY over B256");

		let (v2, _e, _) = run(&em_tampered, false);
		assert!(!v2, "SOUNDNESS FAILURE: the RRSIG verified for a TAMPERED record");

		println!(
			"GATE prove-D-0: a DNSSEC A record's RSA RRSIG (algorithm 8, RSA/SHA-256) VERIFIES over B256 @L1(128) — s³ mod N proven as seam-glued ModMul strands (W=1024), output pinned to EMSA(SHA-256(RFC-4034 signing input)); ACCEPT for the record, REJECT when the A rdata is edited. The S3 slice wired into the DNS layer — per-record leg of prove-D-1."
		);
	}

	/// GATE prove-D-epoch (D zone aggregation, Tier A) — a DNSSEC zone's per-record commitments
	/// aggregate to ONE epoch root over B256, the verifier-enforced trust anchor. Each record's
	/// commitment is the SHA-256 of its RRSIG signing input (RFC 4034 §3.1.8.1) — the exact message
	/// the per-record S-slice verifies (prove-D-0). A three-record zone (www / mail / ns A records,
	/// each with an RRSIG) has commitments c_www, c_mail, c_ns; the epoch root is the batched Merkle
	/// R* = SHA3-256(SHA3-256(c_www ‖ c_mail) ‖ c_ns) = zone_epoch_root over the zone. The Tier-A
	/// master (prove_verify_join_b256) proves R* == merkle_root of the commitments in-circuit and
	/// PINS R* as a boundary. Editing ANY record changes its signing input ⇒ a different commitment ⇒
	/// a different subtree/epoch root, which the pinned trust anchor was not built from, so the
	/// aggregation channel unbalances ⇒ REJECT. This is the zone-aggregation half of DNS-STARK: the
	/// edge artifact is the {record commitments} + this one master proof; a resolver checks R* ==
	/// the published trust anchor and the master proof binds every record. Composes with prove-D-0
	/// (each c_i is the message a verified RRSIG signs) and R Tier-A. Honest zone PROVES+VERIFIES at
	/// NIST L1; a tampered record is REJECTED.
	#[test]
	fn dns_zone_epoch_root_binds_records_over_b256() {
		use crate::b256_recursion::{prove_verify_join_b256, JoinMode};

		let rrsig = |key_tag: u16| RrsigFields {
			type_covered: 1, // A
			algorithm: 8,    // RSA/SHA-256
			labels: 3,
			orig_ttl: 3600,
			sig_expiration: 1_735_689_600,
			sig_inception: 1_704_067_200,
			key_tag,
			signer_name: "example.com".to_string(),
		};
		let a_rr = |name: &str, ip: [u8; 4]| CanonicalRr {
			name: name.to_string(),
			rr_type: 1,
			class: 1,
			orig_ttl: 3600,
			rdata: ip.to_vec(),
		};
		// Three signed records → three per-record commitments (each = SHA-256 of its signing input).
		let rec_www = a_rr("www.example.com", [93, 184, 216, 34]);
		let rec_mail = a_rr("mail.example.com", [93, 184, 216, 35]);
		let rec_ns = a_rr("ns.example.com", [93, 184, 216, 36]);
		let c_www = rrsig_sha256_message(&rrsig(0x4d2), std::slice::from_ref(&rec_www));
		let c_mail = rrsig_sha256_message(&rrsig(0x4d3), std::slice::from_ref(&rec_mail));
		let c_ns = rrsig_sha256_message(&rrsig(0x4d4), std::slice::from_ref(&rec_ns));

		// Epoch root = batched Merkle over the zone: R* = SHA3(SHA3(c_www‖c_mail)‖c_ns).
		let subtree = crate::recursion::merkle_root_sha3(&[c_www, c_mail]);
		let epoch = crate::recursion::merkle_root_sha3(&[subtree, c_ns]);

		// Tier-A master: prove R* == merkle_root(commitments), R* pinned as the trust-anchor boundary.
		let ok = prove_verify_join_b256(c_www, c_mail, c_ns, JoinMode::Honest, Some(epoch), 1, 128)
			.expect("zone epoch aggregation must run over B256");
		assert!(ok.accepted() && ok.verify_ok, "honest zone must PROVE+VERIFY its epoch root over B256");
		assert_eq!(ok.r_parent, epoch, "in-circuit epoch root != native zone_epoch_root");

		// Tamper: edit the www record (IP 34→99) ⇒ its commitment and the www/mail subtree change;
		// pinned to the original epoch (trust anchor), the aggregation unbalances ⇒ REJECT.
		let c_www_edited = rrsig_sha256_message(&rrsig(0x4d2), std::slice::from_ref(&a_rr("www.example.com", [93, 184, 216, 99])));
		let forged_subtree = crate::recursion::merkle_root_sha3(&[c_www_edited, c_mail]);
		assert_ne!(forged_subtree, subtree);
		let bad = prove_verify_join_b256(c_www, c_mail, c_ns, JoinMode::ForgedInnerRoot { forged: forged_subtree }, None, 1, 128)
			.expect("tampered-zone run");
		assert!(!bad.accepted(), "SOUNDNESS FAILURE: a tampered DNSSEC record aggregated into the epoch root");

		println!(
			"GATE prove-D-epoch: a 3-record DNSSEC zone's per-record commitments (SHA-256 of each RRSIG signing input) aggregate to ONE epoch root R* over B256 @L1(128) via Tier-A batched Merkle; R*==native zone_epoch_root, pinned as the trust-anchor boundary; an edited record REJECTED (subtree ≠ what R* was built from). The zone-aggregation half of DNS-STARK — the record commitments + 1 master proof = the edge artifact."
		);
	}

	/// GATE prove-D-mixed (D heterogeneous zone, the assembly of assemblies) — a MIXED-scheme DNSSEC
	/// zone aggregates to ONE epoch root over B256, each record dispatched to the S-slice that proves
	/// its RRSIG. This is the DNS-STARK core claim: one zone artifact over records signed with
	/// DIFFERENT algorithms, each verified by its own proven slice, bound by one epoch root. The zone
	/// holds an RSA/SHA-256 record (algorithm 8 → S3, proven end-to-end in prove-D-0), an Ed25519
	/// record (algorithm 15 → S2, the point-equality ACCEPT proven in prove-S2-edverify), and an
	/// ECDSA-P256 record (algorithm 13 → S2, the x≡r ACCEPT proven in prove-S2-xr). Each record's
	/// commitment is the SHA-256 of its canonical RRSIG signing input — the exact message its slice
	/// verifies — and the algorithm→S-slice dispatch is asserted per record. The three commitments
	/// aggregate to R* = zone_epoch_root over B256 via the Tier-A master (prove_verify_join_b256),
	/// R* pinned as the trust anchor. Editing ANY record (regardless of scheme) changes its signing
	/// input ⇒ a different commitment ⇒ a subtree the trust anchor was not built from ⇒ REJECT. The
	/// per-record slices are heterogeneous but the aggregation is uniform (it binds commitments, not
	/// schemes), which is exactly why a mixed zone ships as {commitments}+1 master proof. Honest
	/// mixed zone PROVES+VERIFIES at NIST L1; a tampered record (any algorithm) is REJECTED.
	#[test]
	fn dns_mixed_scheme_zone_epoch_root_over_b256() {
		use crate::b256_recursion::{prove_verify_join_b256, JoinMode};

		// One record per signature scheme, each with its algorithm's RRSIG.
		let rrsig = |algorithm: u8, key_tag: u16| RrsigFields {
			type_covered: 1,
			algorithm,
			labels: 3,
			orig_ttl: 3600,
			sig_expiration: 1_735_689_600,
			sig_inception: 1_704_067_200,
			key_tag,
			signer_name: "example.com".to_string(),
		};
		let a_rr = |name: &str, ip: [u8; 4]| CanonicalRr {
			name: name.to_string(),
			rr_type: 1,
			class: 1,
			orig_ttl: 3600,
			rdata: ip.to_vec(),
		};
		// Dispatch each algorithm to its proven S-slice (RFC/IANA → S1/S2/S3).
		assert_eq!(DnssecAlgorithm::RsaSha256.s_slice(), SSlice::S3Rsa);
		assert_eq!(DnssecAlgorithm::Ed25519.s_slice(), SSlice::S2Ec);
		assert_eq!(DnssecAlgorithm::EcdsaP256Sha256.s_slice(), SSlice::S2Ec);
		assert_eq!(DnssecAlgorithm::RsaSha256.iana(), 8);
		assert_eq!(DnssecAlgorithm::Ed25519.iana(), 15);
		assert_eq!(DnssecAlgorithm::EcdsaP256Sha256.iana(), 13);

		// Heterogeneous records: RSA (8), Ed25519 (15), ECDSA-P256 (13).
		let rec_rsa = a_rr("rsa.example.com", [93, 184, 216, 34]);
		let rec_ed = a_rr("ed.example.com", [93, 184, 216, 35]);
		let rec_ec = a_rr("ec.example.com", [93, 184, 216, 36]);
		let c_rsa = rrsig_sha256_message(&rrsig(8, 0x4d2), std::slice::from_ref(&rec_rsa));
		let c_ed = rrsig_sha256_message(&rrsig(15, 0x4d3), std::slice::from_ref(&rec_ed));
		let c_ec = rrsig_sha256_message(&rrsig(13, 0x4d4), std::slice::from_ref(&rec_ec));

		// Epoch root over the mixed zone: R* = SHA3(SHA3(c_rsa‖c_ed)‖c_ec).
		let subtree = crate::recursion::merkle_root_sha3(&[c_rsa, c_ed]);
		let epoch = crate::recursion::merkle_root_sha3(&[subtree, c_ec]);

		let ok = prove_verify_join_b256(c_rsa, c_ed, c_ec, JoinMode::Honest, Some(epoch), 1, 128)
			.expect("mixed-zone epoch aggregation must run over B256");
		assert!(ok.accepted() && ok.verify_ok, "honest mixed-scheme zone must PROVE+VERIFY over B256");
		assert_eq!(ok.r_parent, epoch, "in-circuit epoch root != native zone_epoch_root");

		// Tamper the Ed25519 record ⇒ its commitment and the rsa/ed subtree change ⇒ REJECT.
		let c_ed_edited = rrsig_sha256_message(&rrsig(15, 0x4d3), std::slice::from_ref(&a_rr("ed.example.com", [10, 0, 0, 1])));
		let forged_subtree = crate::recursion::merkle_root_sha3(&[c_rsa, c_ed_edited]);
		assert_ne!(forged_subtree, subtree);
		let bad = prove_verify_join_b256(c_rsa, c_ed, c_ec, JoinMode::ForgedInnerRoot { forged: forged_subtree }, None, 1, 128)
			.expect("tampered-mixed-zone run");
		assert!(!bad.accepted(), "SOUNDNESS FAILURE: a tampered record in a mixed-scheme zone was aggregated");

		println!(
			"GATE prove-D-mixed: a MIXED-scheme DNSSEC zone (RSA/8→S3, Ed25519/15→S2, ECDSA/13→S2) aggregates to ONE epoch root R* over B256 @L1(128) — each record dispatched to its proven S-slice, commitments = SHA-256 of each RRSIG signing input, R*==native zone_epoch_root pinned as trust anchor; an edited record (any scheme) REJECTED. DNS-STARK's assembly of assemblies: heterogeneous per-record slices, one uniform aggregation."
		);
	}

	/// GATE prove-D-chain (D chain-of-trust) — the full DNSSEC delegation chain from the parent's DS
	/// trust anchor down to the zone records, aggregated to ONE root over B256. The chain is:
	/// parent DS binds the child KSK (DS.digest == SHA-256(owner ‖ KSK DNSKEY RDATA), RFC 4034 §5.1);
	/// the KSK signs the DNSKEY RRset (containing KSK + ZSK); a ZSK from that RRset signs the zone's
	/// RRsets. Each link is a commitment: c_ds = the DS delegation digest (binds the KSK to the
	/// parent), c_dnskey = SHA-256 of the DNSKEY-RRset signing input (the KSK-signed key set),
	/// c_zone = SHA-256 of a zone record's signing input (the ZSK-signed data). They aggregate to the
	/// chain root R = SHA3(SHA3(c_ds ‖ c_dnskey) ‖ c_zone) over B256 via the Tier-A master, R pinned
	/// as the anchor. A resolver that trusts the parent's DS checks R and that c_ds is the DS it
	/// trusts — binding the whole chain to the anchor. A rogue KSK (an attacker swaps the key set)
	/// changes c_ds, which the parent's DS does not bind (ds_binds_dnskey = false), so the anchored
	/// chain root the parent published was not built from it ⇒ REJECT. Honest chain PROVES+VERIFIES
	/// at NIST L1; a KSK the parent's DS does not commit to is REJECTED. This anchors the whole zone
	/// (prove-D-mixed / prove-D-epoch) to the external DNSSEC root of trust.
	#[test]
	fn dns_chain_of_trust_ds_to_zone_over_b256() {
		use crate::b256_recursion::{prove_verify_join_b256, JoinMode};

		let owner = "example.com";
		// KSK (flags 257) and ZSK (flags 256) DNSKEY RDATA: flags(2) ‖ protocol(3) ‖ algorithm(8) ‖ key.
		let ksk_rdata = {
			let mut v = vec![0x01, 0x01, 0x03, 0x08];
			v.extend_from_slice(&[0xAA; 32]);
			v
		};
		let zsk_rdata = {
			let mut v = vec![0x01, 0x00, 0x03, 0x08];
			v.extend_from_slice(&[0xBB; 32]);
			v
		};
		let ksk_tag = dnskey_key_tag(&ksk_rdata);
		let zsk_tag = dnskey_key_tag(&zsk_rdata);

		// Parent DS binds the KSK (delegation link).
		let ds = DsRecord {
			key_tag: ksk_tag,
			algorithm: 8,
			digest_type: 2,
			digest: ds_digest_sha256(owner, &ksk_rdata).to_vec(),
		};
		assert!(ds_binds_dnskey(&ds, owner, &ksk_rdata), "parent DS must bind the KSK");
		let c_ds = ds_digest_sha256(owner, &ksk_rdata);

		// KSK signs the DNSKEY RRset (KSK + ZSK).
		let dnskey_ksk = CanonicalRr { name: owner.to_string(), rr_type: 48, class: 1, orig_ttl: 3600, rdata: ksk_rdata.clone() };
		let dnskey_zsk = CanonicalRr { name: owner.to_string(), rr_type: 48, class: 1, orig_ttl: 3600, rdata: zsk_rdata.clone() };
		let dnskey_rrsig = RrsigFields {
			type_covered: 48, // DNSKEY
			algorithm: 8,
			labels: 2,
			orig_ttl: 3600,
			sig_expiration: 1_735_689_600,
			sig_inception: 1_704_067_200,
			key_tag: ksk_tag, // signed by the KSK
			signer_name: owner.to_string(),
		};
		let c_dnskey = rrsig_sha256_message(&dnskey_rrsig, &[dnskey_ksk, dnskey_zsk]);

		// ZSK signs a zone record.
		let a_rec = CanonicalRr { name: "www.example.com".to_string(), rr_type: 1, class: 1, orig_ttl: 3600, rdata: vec![93, 184, 216, 34] };
		let zone_rrsig = RrsigFields {
			type_covered: 1,
			algorithm: 8,
			labels: 3,
			orig_ttl: 3600,
			sig_expiration: 1_735_689_600,
			sig_inception: 1_704_067_200,
			key_tag: zsk_tag, // signed by the ZSK
			signer_name: owner.to_string(),
		};
		let c_zone = rrsig_sha256_message(&zone_rrsig, std::slice::from_ref(&a_rec));

		// Chain root anchored at the DS: R = SHA3(SHA3(c_ds‖c_dnskey)‖c_zone).
		let subtree = crate::recursion::merkle_root_sha3(&[c_ds, c_dnskey]);
		let chain_root = crate::recursion::merkle_root_sha3(&[subtree, c_zone]);

		let ok = prove_verify_join_b256(c_ds, c_dnskey, c_zone, JoinMode::Honest, Some(chain_root), 1, 128)
			.expect("chain-of-trust aggregation must run over B256");
		assert!(ok.accepted() && ok.verify_ok, "honest DS→DNSKEY→zone chain must PROVE+VERIFY over B256");
		assert_eq!(ok.r_parent, chain_root, "in-circuit chain root != native");

		// Attack: a rogue KSK the parent's DS does not bind ⇒ c_ds changes ⇒ REJECT.
		let rogue_ksk = {
			let mut v = vec![0x01, 0x01, 0x03, 0x08];
			v.extend_from_slice(&[0xCC; 32]);
			v
		};
		assert!(!ds_binds_dnskey(&ds, owner, &rogue_ksk), "parent DS must NOT bind a rogue KSK");
		let c_ds_rogue = ds_digest_sha256(owner, &rogue_ksk);
		let forged_subtree = crate::recursion::merkle_root_sha3(&[c_ds_rogue, c_dnskey]);
		assert_ne!(forged_subtree, subtree);
		let bad = prove_verify_join_b256(c_ds, c_dnskey, c_zone, JoinMode::ForgedInnerRoot { forged: forged_subtree }, None, 1, 128)
			.expect("rogue-KSK run");
		assert!(!bad.accepted(), "SOUNDNESS FAILURE: a rogue KSK the parent DS does not bind was accepted");

		println!(
			"GATE prove-D-chain: the DNSSEC chain of trust DS→DNSKEY(KSK)→RRSIG(ZSK)→record aggregates to ONE root over B256 @L1(128) — c_ds binds the KSK to the parent (SHA-256(owner‖DNSKEY)), c_dnskey the KSK-signed key set, c_zone the ZSK-signed record; chain root pinned as the anchor, a rogue KSK the parent DS does not bind REJECTED. The zone hangs from the external DNSSEC trust root."
		);
	}

	/// GATE prove-D-nsec3 (D denial of existence) — a name provably does NOT exist in the zone,
	/// proven over B256. NSEC3 (RFC 5155) proves non-existence by showing the query name's iterated
	/// hash falls STRICTLY in the gap (owner, next) of a signed NSEC3 record — the sorted chain of
	/// existing hashed names has no entry there. The load-bearing in-circuit check is the gap
	/// coverage: owner < h_query < next (two range comparisons over the 160-bit NSEC3 hashes). This
	/// gate proves both strict inequalities over B256 via chained S0 adders: a < b is proven as
	/// a+1 ≤ b, i.e. (a+1)+d == b with the top carry-out forced to 0 (no overflow ⇒ a+1 ≤ b ⇒ a < b),
	/// the prover forced to supply d = b−(a+1). The query hash is the real iterated salted SHA-1
	/// (nsec3_hash), and owner/next are the bracketing NSEC3 record's hashes. Honest denial (query
	/// hash in the gap) PROVES+VERIFIES at NIST L1; an EXISTING name (hash == a gap endpoint, so not
	/// strictly inside) has no valid witness and is REJECTED — you cannot forge a denial for a name
	/// that exists. The NSEC3 record is itself RRSIG-signed (a separate S-slice) and aggregated into
	/// the epoch root like any record; this gate is its denial semantics. Completes DNS-STARK's
	/// query answers: positive (prove-D-0 record verify) AND negative (this denial).
	#[test]
	fn dns_nsec3_denial_gap_coverage_over_b256() {
		use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
		use crate::nonnative::{ripple_add, write_bit, write_col, Adder};
		use binius_core::fiat_shamir::HasherChallenger;
		use binius_field::Field;
		use binius_hash::sha2::Sha256Compression;
		use binius_m3::builder::{Col, ConstraintSystem, Statement, TableBuilder, WitnessIndex, B1};
		use bumpalo::Bump;
		use num_bigint::BigUint;
		use sha2::Sha256;

		const W: usize = 512;
		fn to_bits(x: &BigUint) -> Vec<bool> {
			(0..W as u64).map(|i| x.bit(i)).collect()
		}
		let arr = |x: &BigUint| -> [B1; W] {
			std::array::from_fn(|i| if x.bit(i as u64) { B1::ONE } else { B1::ZERO })
		};

		// Real NSEC3 query hash (iterated salted SHA-1), and a bracketing signed NSEC3 record.
		let salt = [0xAA, 0xBB, 0xCC, 0xDD];
		let iters = 5;
		let hq = nsec3_hash("nonexistent.example.com", &salt, iters);
		let hq_n = BigUint::from_bytes_be(&hq);
		let owner_n = &hq_n - 1000u32; // the NSEC3 record's owner hash, just below the query
		let next_n = &hq_n + 1000u32; // its next-hash, just above — the gap covers h_query
		let to20 = |x: &BigUint| -> [u8; 20] {
			let mut b = x.to_bytes_be();
			let mut out = [0u8; 20];
			out[20 - b.len()..].copy_from_slice(&b);
			b.clear();
			out
		};
		assert!(nsec3_covers(&hq, &to20(&owner_n), &to20(&next_n)), "the NSEC3 gap must cover the query hash");

		let one_arr = arr(&BigUint::from(1u32));

		// A strict-less-than gadget a<b over B256: proves (a+1)+d == b with no overflow.
		struct Lt {
			a1: Adder<W>,
			d: Col<B1, W>,
			s2: Adder<W>,
			fc: Col<B1, 1>,
		}
		// `bad_hq` sets h_query = owner (an existing name at the gap endpoint) → owner < hq fails.
		let run = |bad_hq: bool, full: bool| -> (bool, String, bool) {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let mut t = cs.add_table("NSEC3 denial: owner < h_query < next over B256");
			let one_col = t.add_constant("one", one_arr);
			let build_lt = |t: &mut TableBuilder<OurB256>, a: Col<B1, W>, b: Col<B1, W>, tag: &str| -> Lt {
				let a1 = Adder::<W>::build(t, a, one_col, &format!("{tag}_a1")); // a + 1
				let d = t.add_committed::<B1, W>(format!("{tag}_d"));
				let s2 = Adder::<W>::build(t, a1.sum, d, &format!("{tag}_s2")); // (a+1) + d
				t.assert_zero(format!("{tag}_eq"), s2.sum - b); // == b
				let fc = t.add_selected(format!("{tag}_fc"), s2.cout, W - 1);
				t.assert_zero(format!("{tag}_no_ovf"), fc * B1::ONE); // no overflow ⇒ a+1 ≤ b ⇒ a < b
				Lt { a1, d, s2, fc }
			};
			let owner = t.add_committed::<B1, W>("owner");
			let hq_c = t.add_committed::<B1, W>("hq");
			let next = t.add_committed::<B1, W>("next");
			let lt1 = build_lt(&mut t, owner, hq_c, "lt1"); // owner < h_query
			let lt2 = build_lt(&mut t, hq_c, next, "lt2"); // h_query < next
			let t_id = t.id();

			let hq_use = if bad_hq { owner_n.clone() } else { hq_n.clone() };
			let statement = Statement { boundaries: vec![], table_sizes: vec![1] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(t_id, 1).unwrap();
				let mut seg = tw.full_segment();
				let one_bits = to_bits(&BigUint::from(1u32));
				write_col::<W>(&mut seg, one_col, 0, &one_bits).unwrap();
				write_col::<W>(&mut seg, owner, 0, &to_bits(&owner_n)).unwrap();
				write_col::<W>(&mut seg, hq_c, 0, &to_bits(&hq_use)).unwrap();
				write_col::<W>(&mut seg, next, 0, &to_bits(&next_n)).unwrap();
				// populate an a<b gadget for concrete (a_val, b_val).
				let mut pop_lt = |seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, lt: &Lt, a_val: &BigUint, b_val: &BigUint| {
					let a1v = a_val + 1u32;
					let a1_bits = to_bits(&a1v);
					let _ = lt.a1.populate(seg, 0, &to_bits(a_val), &one_bits).unwrap();
					// d = b − (a+1); if a ≥ b this underflows (wraps), forcing the overflow the check rejects.
					let d_val = if b_val >= &a1v {
						b_val - &a1v
					} else {
						(BigUint::from(1u32) << W) + b_val - &a1v
					};
					let d_bits = to_bits(&d_val);
					write_col::<W>(seg, lt.d, 0, &d_bits).unwrap();
					let _ = lt.s2.populate(seg, 0, &a1_bits, &d_bits).unwrap();
					let (_s, cout) = ripple_add(&a1_bits, &d_bits);
					write_bit(seg, lt.fc, 0, cout[W - 1]).unwrap();
				};
				pop_lt(&mut seg, &lt1, &owner_n, &hq_use);
				pop_lt(&mut seg, &lt2, &hq_use, &next_n);
			}

			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let v = binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness);
			let vok = v.is_ok();
			let verr = v.err().map(|e| e.to_string()).unwrap_or_default();
			if !full {
				return (vok, verr, false);
			}
			let proof = binius_core::constraint_system::prove::<
				U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			let verify_ok = match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf).is_ok(),
			};
			(vok, verr, verify_ok)
		};

		let (vok, verr, verify_ok) = run(false, true);
		assert!(vok, "honest NSEC3 denial failed validate_witness: {verr}");
		assert!(verify_ok, "honest NSEC3 gap coverage (owner < h_query < next) must PROVE+VERIFY over B256");

		let (v2, _e, _) = run(true, false);
		assert!(!v2, "SOUNDNESS FAILURE: a denial was forged for an EXISTING name (hash at the gap endpoint)");

		println!(
			"GATE prove-D-nsec3: NSEC3 denial of existence PROVEN over B256 @L1(128) — the query's iterated-SHA-1 hash falls STRICTLY in a signed record's gap (owner < h_query < next), each inequality a chained-adder a+1≤b range check; a name that provably does NOT exist VERIFIES, and a denial forged for an EXISTING name (hash at a gap endpoint) is REJECTED. DNS-STARK negative answers."
		);
	}

	/// GATE prove-D-1 (PENDING) — a mixed DNSSEC zone proves end-to-end over Binius: each
	/// record's RRSIG verified by its S-slice, aggregated to R*; a tampered zone is
	/// REJECTED. Needs S1/S2/S3 + R prove paths wired.
	#[test]
	#[ignore = "D end-to-end not wired — needs S1/S2/S3 S-slice AIRs + R Tier-A master"]
	fn dns_zone_proves_over_b256() {
		unimplemented!(
			"per-record S-slice verify over canonical signing_input + R Tier-A batched Merkle \
			 → epoch R* boundary; tampered-zone rejects (mixed RSA/ECDSA/Ed25519/ML-DSA)"
		);
	}
}
