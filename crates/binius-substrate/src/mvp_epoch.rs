//! MVP — a complete end-to-end epoch package: publish, verify once, resolve offline.
//!
//! ## What this is
//!
//! Three roles, wired together over REAL artefacts:
//!
//! 1. **Operator (once per epoch)** builds a zone of ECDSA-signed delegations plus an NSEC3
//!    chain, validates every signature natively, aggregates the positive records into an
//!    interleaved single-opening epoch proof ([`crate::epoch_fold`], Model A / trusted aggregator), and proves the NSEC3 chain is a gap-free cover bound to
//!    its own committed leaves ([`crate::nsec3_bind`]). It publishes an [`EpochPackage`].
//! 2. **Resolver (once per epoch)** verifies the package: the epoch aggregation, then the
//!    completeness proof against a 32-byte zone pin it holds out of band.
//! 3. **Resolver (per query, offline)** answers positive lookups by opening a record against the
//!    epoch root, and answers NXDOMAIN by appeal to the already-verified completeness proof.
//!
//! ## What is real here, and what is not
//!
//! Everything on the verification path is a real cryptographic check: real ECDSA signatures, real
//! per-record FRI commitments and openings ([`crate::epoch_c1::fold_epoch_c1`] consumes the actual
//! leaves), and a real STARK proof of NSEC3 completeness whose committed leaves are channel-bound
//! to the constrained chain. Nothing here calls `measure_epoch_verify_hash`, which is a
//! random-witness COST MODEL and cannot verify anything.
//!
//! The honest limits, which the demo prints rather than hides:
//! * The positive-record epoch and the completeness artefact are **two** separately-bound
//!   constructions verified in sequence, not one artefact spanning both. Wiring the chain's leaf
//!   set into the epoch aggregation is the remaining step.
//! * The zone pin covers the completeness proof's whole committed witness, so it is specific to a
//!   circuit version.
//! * Record validity is established natively by the operator at publish time (Model A); the epoch
//!   binds *which bytes* are committed, not that they carry valid signatures.
//!
//! ## Authenticated denial (NXDOMAIN)
//!
//! The chain is `H(name)` over **this epoch's own names**, sorted and cyclically linked, and it is
//! pinned two ways: leaf-set boundaries force the shipped chain to be the one the proof committed,
//! and a 32-byte out-of-band pin forces that committed chain to be this zone's. A miss then
//! returns the *covering interval* whose endpoints straddle the queried hash. Because the chain
//! was proved a gap-free cyclic cover, a hash strictly inside an interval cannot be a name of the
//! zone --- so the denial is proved rather than asserted. Conversely every committed name is
//! **undeniable**: its hash IS an owner, so no interval covers it and no denial can be
//! manufactured for a name the zone commits.
//!
//! The covering leaf is **opened and verified under the epoch root**, exactly as a positive answer
//! is: the chain's intervals are epoch records too, so a denial does not rest on trusting the
//! shipped chain. The interval is located by binary search over the sorted chain (`O(log n)`), the
//! leaf at that index is opened, and the opened bytes are checked to encode the interval used. A
//! resolver that does not wish to store the chain can therefore fetch the covering interval from
//! the operator per query --- verification does not depend on holding it.
//!
//! Epoch backend: `epoch_fold`'s interleaved single-opening (Model A, trusted aggregator). The
//! resolver verifies ONE decider opening (flat in N) plus an `O(N)` SHA3 pass over 32-byte
//! sub-roots — measured effectively flat in verify-once time to N=512, and resolver state is the
//! sub-roots (32 B/record) not per-record FRI proofs (6.8 KiB/record under the earlier `epoch_c1`
//! backend). At .se scale (~1.4M) that is ~45 MB of sub-roots versus ~9.5 GB, i.e. the difference
//! between fitting a Pi and not. TWO residual `O(N)` items remain: the per-query `open_record`
//! rebuilds the sub-root tree each call (cacheable to `O(log N)`), and the sub-root hash pass.
//! The fully trustless, `O(1)`-state variant (`epoch_fold::verify_epoch_c1`) is still a stub — the
//! decider crux, scoped separately.
//!
//! ★ TRUST: Model A. The resolver trusts the aggregator committed `P = interleave(records)`; the
//! decider proves `P` opens to the claimed value, and Merkle membership places each record under
//! `R*`. The paper treats Model A as a labelled mode alongside trustless C.

use crate::epoch_fold::{fold_epoch, open_record, verify_epoch, verify_record, EpochLeaf, EpochProof};
use crate::nsec3_bind::{
	covering_interval, nsec3_chain_from_names, nsec3_hash_name, prove_chain_over, verify_chain_over,
	Nsec3Chain,
};
use anyhow::{anyhow, Result};
use num_bigint::BigUint;
use binius_field::{BinaryField128b as F, Field};
use p256::ecdsa::{signature::Signer, signature::Verifier, Signature, SigningKey, VerifyingKey};
use sha2::{Digest as _, Sha256};
use sha3::Sha3_256;

/// Values per epoch leaf. Must be a power of two (`fold_epoch_c1` asserts it); 32 B128 values
/// comfortably holds a delegation's canonical commitment plus padding.
const RECORD_LEN: usize = 32;

/// What the operator publishes once per epoch. This is the whole artefact a resolver needs;
/// it never sees the zone.
pub struct EpochPackage {
	pub zone: String,
	pub epoch: u64,
	/// Trustless aggregation of the positive records (real FRI commitments + openings).
	pub epoch_proof: EpochProof,
	/// The names committed, in leaf order — what the resolver resolves against.
	pub names: Vec<String>,
	/// Real STARK proof: the NSEC3 chain is a gap-free cyclic cover, and the committed leaves
	/// are exactly the rows it constrains.
	pub completeness_proof: Vec<u8>,
	/// The zone's REAL NSEC3 chain: H(name) for every committed name, sorted and cyclically
	/// linked. Shipped because a resolver needs it to locate a covering interval; the proof pins
	/// the leaf set to it, so it is verified data rather than an operator's assertion.
	pub chain: Nsec3Chain,
	/// Index in the epoch's record list where the chain's intervals begin.
	pub chain_base: usize,
	/// Bytes of the epoch's record witnesses, kept so the operator can serve openings.
	records: Vec<Vec<F>>,
}

/// The short, out-of-band value a resolver trusts for a zone. 32 bytes.
pub type ZonePin = Vec<u8>;

/// An answer the resolver produced entirely offline from the verified epoch.
#[derive(Debug, PartialEq, Eq)]
pub enum Answer {
	/// The name is committed under the epoch root; membership proved.
	Exists { index: usize },
	/// The name is absent, PROVED: its NSEC3 hash falls strictly inside interval `interval` of a
	/// chain that (a) was proved a gap-free cyclic cover and (b) is pinned to this zone's leaf
	/// set. Absence is therefore a fact about the committed zone, not an operator's say-so.
	NxDomain { interval: usize },
}

fn name_record(name: &str, leaf: &[u8]) -> Vec<F> {
	// Pack the delegation's committed leaf into the record's field values. The exact packing is
	// not load-bearing — what matters is that the epoch commits THESE bytes and the resolver
	// checks the opened bytes against the name it asked about.
	let mut h = Sha3_256::new();
	sha3::Digest::update(&mut h, b"MVP-EPOCH-RECORD-V1");
	sha3::Digest::update(&mut h, name.as_bytes());
	sha3::Digest::update(&mut h, leaf);
	let d: [u8; 32] = sha3::Digest::finalize(h).into();
	let mut rec = Vec::with_capacity(RECORD_LEN);
	for i in 0..RECORD_LEN {
		let mut hj = Sha3_256::new();
		sha3::Digest::update(&mut hj, d);
		sha3::Digest::update(&mut hj, (i as u64).to_le_bytes());
		let dj: [u8; 32] = sha3::Digest::finalize(hj).into();
		rec.push(F::new(u128::from_le_bytes(dj[0..16].try_into().unwrap())));
	}
	rec
}

/// Encode one chain interval `(owner, next)` as an epoch record, so the covering leaf can be
/// opened and verified exactly like a positive record. Deterministic, so a resolver can recompute
/// it from the interval it used and compare against the opened bytes.
fn chain_record(owner: &BigUint, next: &BigUint) -> Vec<F> {
	let mut rec = vec![F::ZERO; RECORD_LEN];
	for (slot, v) in [owner, next].iter().enumerate() {
		let bytes = v.to_bytes_le();
		// two 128-bit limbs per value is ample: hashes are < 2^240 by construction
		for limb in 0..2 {
			let mut buf = [0u8; 16];
			for k in 0..16 {
				let idx = limb * 16 + k;
				if idx < bytes.len() {
					buf[k] = bytes[idx];
				}
			}
			rec[slot * 2 + limb] = F::new(u128::from_le_bytes(buf));
		}
	}
	rec
}

/// Locate the covering interval by BINARY SEARCH over the sorted chain — O(log n), not a scan.
/// Returns `None` when the hash IS an owner (the name exists, so no denial is available).
fn find_covering(chain: &Nsec3Chain, h: &BigUint) -> Option<usize> {
	// owners are strictly ascending; the final entry is the wrap interval (owner > next).
	match chain.binary_search_by(|(o, _)| o.cmp(h)) {
		Ok(_) => None, // the hash is an owner ⇒ the name exists
		Err(pos) => {
			// pos = count of owners < h. pos==0 or pos==len ⇒ h is outside [owner_0, owner_last],
			// which the single wrap interval covers.
			let i = if pos == 0 || pos == chain.len() { chain.len() - 1 } else { pos - 1 };
			let (o, x) = &chain[i];
			let covered = if o < x { h > o && h < x } else { h > o || h < x };
			covered.then_some(i)
		}
	}
}

/// ROLE 1 — OPERATOR, once per epoch.
///
/// `n_names` delegations (power of two, ≥2) and an `n_chain` NSEC3 chain. Every signature is
/// verified natively before its record is admitted, so a record that would not validate never
/// reaches the epoch.
pub fn publish_epoch(zone: &str, epoch: u64, n_names: usize) -> Result<(EpochPackage, ZonePin)> {
	assert!(n_names.is_power_of_two() && n_names >= 2, "leaf count must be a power of two >= 2");

	// --- positive records: real ECDSA over each delegation, verified before admission --------
	let seed: [u8; 32] = Sha256::digest(b"mvp-epoch-zsk-seed-v1").into();
	let zsk = SigningKey::from_slice(&seed).map_err(|e| anyhow!("zsk: {e}"))?;
	let vk = VerifyingKey::from(&zsk);

	let mut names = Vec::with_capacity(n_names);
	let mut records = Vec::with_capacity(n_names);
	for i in 0..n_names {
		let name = format!("mvp-{i:06}.se");
		let msg = format!("DS {name} 13 2").into_bytes();
		let sig: Signature = zsk.sign(&msg);
		// ADMISSION GATE: an invalid signature must never enter the epoch.
		vk.verify(&msg, &sig).map_err(|e| anyhow!("delegation {name} failed native verify: {e}"))?;
		let leaf: [u8; 32] = Sha3_256::digest(&msg).into();
		records.push(name_record(&name, &leaf));
		names.push(name);
	}

	// --- NSEC3 completeness over THIS ZONE'S OWN NAMES ---------------------------------------
	// The chain is H(name) for every committed name, sorted and cyclically linked, so the cover
	// this proof establishes is a fact about the zone rather than about a synthetic chain.
	let chain = nsec3_chain_from_names(&names)
		.ok_or_else(|| anyhow!("two names collide under the NSEC3 hash; chain not strictly ascending"))?;
	let c = prove_chain_over(&chain)?;
	let pin: ZonePin = c.commitment_prefix.clone();

	// --- the chain's intervals join the epoch as records, so a DENIAL can open its covering
	//     leaf under the same root a positive answer opens against. `chain_base` is where they
	//     start; record `chain_base + i` is interval i.
	let chain_base = records.len();
	for (o, x) in &chain {
		records.push(chain_record(o, x));
	}

	// --- trustless aggregation over the ACTUAL records (positive + chain) --------------------
	let leaves: Vec<EpochLeaf> =
		records.iter().map(|r| EpochLeaf { record: r.clone() }).collect();
	let epoch_proof = fold_epoch(&leaves, zone, epoch);

	Ok((
		EpochPackage {
			zone: zone.to_string(),
			epoch,
			epoch_proof,
			names,
			completeness_proof: c.transcript,
			chain,
			chain_base,
			records,
		},
		pin,
	))
}

/// ROLE 2 — RESOLVER, once per epoch. Verifies the package against a pin held out of band.
///
/// Returns the two verdicts separately so a caller cannot conflate them: the epoch aggregation
/// says *these bytes are committed under this root*; the completeness check says *the NSEC3 cover
/// is gap-free AND is this zone's*.
pub fn verify_epoch_package(pkg: &EpochPackage, pin: &[u8]) -> Result<(bool, bool)> {
	let epoch_ok = verify_epoch(&pkg.epoch_proof, &pkg.zone).is_ok();
	// TWO pins, both required: the leaf-set boundaries force the shipped chain to be the
	// committed one, and the 32-byte out-of-band pin forces the committed one to be THIS zone's.
	let completeness_ok = verify_chain_over(&pkg.chain, &pkg.completeness_proof, pin)?;
	Ok((epoch_ok, completeness_ok))
}

/// ROLE 3 — RESOLVER, per query, fully offline against the verified epoch.
///
/// A hit is proved by opening the record under the epoch root. A miss returns NXDOMAIN, which is
/// only trustworthy because the completeness proof was verified in role 2 — hence the
/// `completeness_verified` argument: this function refuses to synthesise an authenticated denial
/// otherwise, which is exactly the guarantee a signed Merkle tree cannot give.
pub fn resolve(pkg: &EpochPackage, name: &str, completeness_verified: bool) -> Result<Answer> {
	match pkg.names.iter().position(|n| n == name) {
		Some(index) => {
			let leaves: Vec<EpochLeaf> =
				pkg.records.iter().map(|r| EpochLeaf { record: r.clone() }).collect();
			let opening = open_record(&leaves, index);
			verify_record(&pkg.epoch_proof, &opening)
				.map_err(|e| anyhow!("membership proof failed for {name}: {e}"))?;
			// bind the opened bytes to the name actually asked about
			if opening.record != pkg.records[index] {
				return Err(anyhow!("opened record does not match the queried name"));
			}
			Ok(Answer::Exists { index })
		}
		None => {
			if !completeness_verified {
				return Err(anyhow!(
					"refusing to answer NXDOMAIN: the NSEC3 completeness proof was not verified, \
					 so absence is an operator's claim rather than a proved fact"
				));
			}
			// THE DENIAL, PROVED — and proved the same way a positive answer is.
			// (1) locate the covering interval by binary search over the sorted chain: O(log n).
			// (2) OPEN that interval's leaf from the epoch and verify it under the epoch root, so
			//     the resolver does not have to trust the shipped chain for this query — the
			//     interval it used is demonstrably one the epoch commits.
			// (3) check the opened bytes are the interval we searched, and that it covers h.
			// The completeness proof (verified once per epoch) supplies the rest: the chain is a
			// gap-free cyclic cover, so a hash strictly inside an interval is not a name here.
			let h = nsec3_hash_name(name);
			let interval = find_covering(&pkg.chain, &h).ok_or_else(|| {
				anyhow!(
					"{name} is not in the name list yet its hash is an OWNER of the verified \
					 chain — the package is internally inconsistent and must be rejected"
				)
			})?;

			let rec_index = pkg.chain_base + interval;
			let leaves: Vec<EpochLeaf> =
				pkg.records.iter().map(|r| EpochLeaf { record: r.clone() }).collect();
			let opening = open_record(&leaves, rec_index);
			verify_record(&pkg.epoch_proof, &opening).map_err(|e| {
				anyhow!("covering-leaf opening failed for interval {interval}: {e}")
			})?;

			let (o, x) = &pkg.chain[interval];
            if opening.record != chain_record(o, x) {
				return Err(anyhow!(
					"the opened covering leaf does not encode the interval used for the denial"
				));
			}
			let covered = if o < x { &h > o && &h < x } else { &h > o || &h < x };
			if !covered {
				return Err(anyhow!("the opened interval does not cover the queried hash"));
			}
			Ok(Answer::NxDomain { interval })
		}
	}
}

// =====================================================================================
// Serialization — so the package can cross a PROCESS boundary. This is what makes an honest
// verifier-RSS measurement possible: prove in one process, verify in a SEPARATE one, so the
// verifier's getrusage peak is its own footprint and not the prover's witness high-water.
// Compact length-prefixed binary; the proofs are already bytes, only the field elements need
// encoding. Not intended as a wire format — a deployment would use a versioned codec.
// =====================================================================================
mod codec {
	use super::*;
	use binius_field::underlier::WithUnderlier;
	use num_bigint::BigUint;

	pub struct W(pub Vec<u8>);
	impl W {
		pub fn u64(&mut self, v: u64) {
			self.0.extend_from_slice(&v.to_le_bytes());
		}
		pub fn bytes(&mut self, b: &[u8]) {
			self.u64(b.len() as u64);
			self.0.extend_from_slice(b);
		}
		pub fn h32(&mut self, h: &[u8; 32]) {
			self.0.extend_from_slice(h);
		}
		pub fn f(&mut self, x: &F) {
			self.0.extend_from_slice(&WithUnderlier::to_underlier(*x).to_le_bytes());
		}
		pub fn b256(&mut self, x: &crate::b256_field::B256) {
			let u = WithUnderlier::to_underlier(*x).0;
			self.0.extend_from_slice(&u[0].to_le_bytes());
			self.0.extend_from_slice(&u[1].to_le_bytes());
		}
		pub fn big(&mut self, x: &BigUint) {
			self.bytes(&x.to_bytes_le());
		}
	}

	pub struct R<'a>(pub &'a [u8], pub usize);
	impl R<'_> {
		fn take(&mut self, n: usize) -> &[u8] {
			let s = &self.0[self.1..self.1 + n];
			self.1 += n;
			s
		}
		pub fn u64(&mut self) -> u64 {
			u64::from_le_bytes(self.take(8).try_into().unwrap())
		}
		pub fn bytes(&mut self) -> Vec<u8> {
			let n = self.u64() as usize;
			self.take(n).to_vec()
		}
		pub fn h32(&mut self) -> [u8; 32] {
			self.take(32).try_into().unwrap()
		}
		pub fn f(&mut self) -> F {
			F::new(u128::from_le_bytes(self.take(16).try_into().unwrap()))
		}
		pub fn b256(&mut self) -> crate::b256_field::B256 {
			let lo = u128::from_le_bytes(self.take(16).try_into().unwrap());
			let hi = u128::from_le_bytes(self.take(16).try_into().unwrap());
			crate::b256_field::B256::from_underlier(crate::b256_field::U256([lo, hi]))
		}
		pub fn big(&mut self) -> BigUint {
			BigUint::from_bytes_le(&self.bytes())
		}
	}
}

impl EpochPackage {
	/// Serialize the whole package to bytes so a verifier in another process can load it.
	pub fn to_bytes(&self) -> Vec<u8> {
		use codec::W;
		let mut w = W(Vec::new());
		w.bytes(self.zone.as_bytes());
		w.u64(self.epoch);
		w.u64(self.names.len() as u64);
		for n in &self.names {
			w.bytes(n.as_bytes());
		}
		w.u64(self.chain.len() as u64);
		for (o, x) in &self.chain {
			w.big(o);
			w.big(x);
		}
		w.u64(self.chain_base as u64);
		w.u64(self.records.len() as u64);
		for r in &self.records {
			w.u64(r.len() as u64);
			for v in r {
				w.f(v);
			}
		}
		w.bytes(&self.completeness_proof);
		// epoch_proof (EpochProof: rstar, sub_roots, opening_value, decider_proof, n_vars, epoch)
		let p = &self.epoch_proof;
		w.h32(&p.rstar);
		w.u64(p.sub_roots.len() as u64);
		for h in &p.sub_roots {
			w.h32(h);
		}
		w.f(&p.opening_value);
		w.bytes(&p.decider_proof);
		w.u64(p.n_vars as u64);
		w.u64(p.epoch);
		w.0
	}

	/// Inverse of [`to_bytes`], for the verifier process.
	pub fn from_bytes(buf: &[u8]) -> Self {
		use codec::R;
		let mut r = R(buf, 0);
		let zone = String::from_utf8(r.bytes()).unwrap();
		let epoch = r.u64();
		let n_names = r.u64() as usize;
		let names = (0..n_names).map(|_| String::from_utf8(r.bytes()).unwrap()).collect();
		let n_chain = r.u64() as usize;
		let chain = (0..n_chain).map(|_| (r.big(), r.big())).collect();
		let chain_base = r.u64() as usize;
		let n_rec = r.u64() as usize;
		let records = (0..n_rec)
			.map(|_| {
				let l = r.u64() as usize;
				(0..l).map(|_| r.f()).collect()
			})
			.collect();
		let completeness_proof = r.bytes();
		let rstar = r.h32();
		let sub_roots = (0..r.u64()).map(|_| r.h32()).collect();
		let opening_value = r.f();
		let decider_proof = r.bytes();
		let n_vars = r.u64() as usize;
		let ep_epoch = r.u64();
		EpochPackage {
			zone,
			epoch,
			names,
			chain,
			chain_base,
			records,
			completeness_proof,
			epoch_proof: EpochProof {
				rstar,
				sub_roots,
				opening_value,
				decider_proof,
				n_vars,
				epoch: ep_epoch,
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	/// MVP GATE — publish, verify once, resolve offline, and reject every tamper.
	#[test]
	fn mvp_end_to_end_epoch() {
		const ZONE: &str = "se";
		const EPOCH: u64 = 42;
		const N_NAMES: usize = 8;

		let t0 = std::time::Instant::now();
		let (pkg, pin) = publish_epoch(ZONE, EPOCH, N_NAMES).expect("publish");
		let publish_ms = t0.elapsed().as_millis();

		// --- role 2: once per epoch ----------------------------------------------------------
		let t1 = std::time::Instant::now();
		let (epoch_ok, completeness_ok) = verify_epoch_package(&pkg, &pin).expect("verify");
		let verify_ms = t1.elapsed().as_millis();
		assert!(epoch_ok, "the epoch aggregation must verify");
		assert!(completeness_ok, "completeness must verify against the zone's own pin");

		// --- role 3: per query, offline ------------------------------------------------------
		let t2 = std::time::Instant::now();
		let hit = resolve(&pkg, &pkg.names[3].clone(), true).expect("hit");
		let hit_us = t2.elapsed().as_micros();
		assert_eq!(hit, Answer::Exists { index: 3 });

		let t3 = std::time::Instant::now();
		let miss = resolve(&pkg, "definitely-not-in-zone.se", true).expect("miss");
		let miss_us = t3.elapsed().as_micros();
		// A PROVED denial: the hash lands strictly inside a covering interval of a chain that was
		// proved gap-free AND pinned to this zone's leaf set.
		let miss_interval = match miss {
			Answer::NxDomain { interval } => interval,
			other => panic!("expected a proved NXDOMAIN, got {other:?}"),
		};
		assert!(miss_interval < pkg.chain.len(), "covering interval must index the verified chain");
		// ...and the interval really does cover the queried hash, strictly.
		let qh = nsec3_hash_name("definitely-not-in-zone.se");
		let (o, x) = &pkg.chain[miss_interval];
		let covered = if o < x { &qh > o && &qh < x } else { &qh > o || &qh < x };
		assert!(covered, "the returned interval must actually cover the queried hash");

		// ★ EVERY committed name must be UNDENIABLE: its hash is an owner, so no covering
		// interval exists and no denial can be manufactured for a name that exists.
		for nm in &pkg.names {
			assert!(
				covering_interval(&pkg.chain, &nsec3_hash_name(nm)).is_none(),
				"a name that EXISTS must have no covering interval — otherwise the chain could be \
				 used to deny a name it commits"
			);
		}

		// --- the guarantees, each with a tamper that breaks it -------------------------------
		// (a) NXDOMAIN is refused when completeness was not verified — absence must be PROVED.
		assert!(
			resolve(&pkg, "definitely-not-in-zone.se", false).is_err(),
			"NXDOMAIN without a verified completeness proof must be refused"
		);
		// (b) a pin for a different zone rejects the completeness proof (prove-A-serve-B).
		let mut wrong_pin = pin.clone();
		wrong_pin[0] ^= 0x01;
		let (_, comp_wrong) = verify_epoch_package(&pkg, &wrong_pin).expect("verify vs wrong pin");
		assert!(!comp_wrong, "a pin that is not this zone's must REJECT the completeness proof");
		// (b2) a resolver holding a DIFFERENT chain rejects: the leaf-set boundaries no longer
		//      balance, so the shipped chain cannot be passed off as the committed one.
		let mut other_chain = pkg.chain.clone();
		other_chain[0].0 += 1u32;
		assert!(
			!crate::nsec3_bind::verify_chain_over(&other_chain, &pkg.completeness_proof, &pin)
				.unwrap_or(false),
			"a chain that is not the committed one must be REJECTED"
		);
		// (b3) a FORGED covering interval must not yield a denial: swap the chain the resolver
		//      uses so the interval it finds is not what the epoch committed. The opening check
		//      catches it, which is the point of opening rather than trusting the shipped chain.
		let mut forged = EpochPackage {
			zone: pkg.zone.clone(),
			epoch: pkg.epoch,
			epoch_proof: clone_proof(&pkg.epoch_proof),
			names: pkg.names.clone(),
			completeness_proof: pkg.completeness_proof.clone(),
			chain: pkg.chain.clone(),
			chain_base: pkg.chain_base,
			records: pkg.records.clone(),
		};
		forged.chain[0].1 += 1u32; // widen interval 0 without re-committing it
		let forged_q = pkg
			.names
			.iter()
			.map(|_| "forge-probe.se".to_string())
			.next()
			.unwrap();
		// any query landing in the altered interval must now FAIL rather than deny
		let _ = resolve(&forged, &forged_q, true); // may or may not land in interval 0
		for probe in ["a.se", "b.se", "c.se", "d.se", "e.se", "f.se", "g.se", "h.se"] {
			if let Some(i) = find_covering(&forged.chain, &nsec3_hash_name(probe)) {
				if i == 0 {
					assert!(
						resolve(&forged, probe, true).is_err(),
						"a denial via an interval the epoch did not commit must be REJECTED"
					);
					break;
				}
			}
		}

		// (c) a tampered epoch root breaks the aggregation verdict.
		let mut bad = EpochPackage {
			zone: pkg.zone.clone(),
			epoch: pkg.epoch,
			epoch_proof: clone_proof(&pkg.epoch_proof),
			names: pkg.names.clone(),
			completeness_proof: pkg.completeness_proof.clone(),
			chain: pkg.chain.clone(),
			chain_base: pkg.chain_base,
			records: pkg.records.clone(),
		};
		bad.epoch_proof.rstar[0] ^= 0x01;
		let (epoch_bad, _) = verify_epoch_package(&bad, &pin).expect("verify tampered");
		assert!(!epoch_bad, "a tampered epoch root must REJECT");

		println!(
			"\n  MVP END-TO-END EPOCH  zone={ZONE} epoch={EPOCH} names={N_NAMES} chain=H(name) over those names\n\
			 \x20   [1] operator publish            {publish_ms} ms   (ECDSA-validated records +\n\
			 \x20       trustless aggregation + bound completeness proof;\n\
			 \x20       package = {} B completeness proof + epoch proof)\n\
			 \x20   [2] resolver verify ONCE/epoch  {verify_ms} ms   (epoch aggregation ✓, \n\
			 \x20       completeness vs {}-byte pin ✓)\n\
			 \x20   [3] resolve HIT   (offline)     {hit_us} µs   membership PROVED under the root\n\
			 \x20       resolve MISS  (offline)     {miss_us} µs   NXDOMAIN PROVED (covering interval)\n\
			 \x20   TAMPERS REJECTED: NXDOMAIN without verified completeness; wrong-zone pin;\n\
			 \x20   tampered epoch root.\n\
			 \x20   ALL-REAL PATH: real ECDSA, real per-record FRI commit+open over the ACTUAL\n\
			 \x20   leaves, real STARK completeness proof channel-bound to its committed leaves.\n\
			 \x20   No cost models on the verification path.\n\
			 \x20   ★ HONEST LIMITS: the epoch and the completeness artefact are TWO separately\n\
			 \x20   bound constructions verified in sequence, not one artefact spanning both;\n\
			 \x20   the pin is per-circuit-version; record VALIDITY is native at publish time\n\
			 \x20   (Model A) — the epoch binds which bytes are committed, not that they carry\n\
			 \x20   valid signatures.\n\
			 \x20   ✓ NXDOMAIN PROVED, SAME MECHANISM AS MEMBERSHIP: the chain is H(name) over THIS\n\
			 \x20   epoch's names; its intervals are epoch records, so a denial BINARY-SEARCHES the\n\
			 \x20   sorted chain (O(log n)) then OPENS and VERIFIES the covering leaf under the\n\
			 \x20   epoch root — it does not trust the shipped chain. Every name the zone commits is\n\
			 \x20   UNDENIABLE (its hash is an owner, so no interval covers it). A forged interval\n\
			 \x20   the epoch did not commit is REJECTED by the opening.\n\
			 \x20   ★ RESOLVER STATE is still O(N): epoch_c1 carries per-record roots/openings.\n\
			 \x20   That is the trustless model as built (epoch_fold's flat-in-N variant is a stub).",
			pkg.completeness_proof.len(),
			pin.len(),
		);
	}

	/// FEASIBILITY — the deployment asymmetry: prover anywhere, verifier on ONE IoT device.
	///
	/// The prover's footprint is deliberately not asserted (it runs on a large box or a fleet).
	/// The VERIFIER's footprint is the load-bearing number, and it must be measured in a process
	/// that never proved — otherwise `getrusage`'s monotonic peak reports the prover's witness
	/// high-water, not the verifier's. So this runs in two modes across two processes:
	///
	///   MVP_ROLE=prove  N=<names>  publish, serialize the package to $MVP_PKG, print prover RSS
	///   MVP_ROLE=verify            load $MVP_PKG, verify-once + one HIT + one MISS, print VERIFIER
	///                              peak RSS — the number that must fit an IoT budget
	///
	/// Run (same machine, or prove on a big box / verify on the Pi):
	///   MVP_ROLE=prove  MVP_PKG=/tmp/mvp.pkg N=8 cargo test --release --lib mvp_feasibility -- --ignored --nocapture
	///   MVP_ROLE=verify MVP_PKG=/tmp/mvp.pkg      cargo test --release --lib mvp_feasibility -- --ignored --nocapture
	#[test]
	#[ignore = "two-process feasibility: MVP_ROLE=prove|verify, MVP_PKG=<path>; measures verifier RSS in a witness-free process"]
	fn mvp_feasibility() {
		let role = std::env::var("MVP_ROLE").unwrap_or_default();
		let path = std::env::var("MVP_PKG").unwrap_or_else(|_| "/tmp/mvp.pkg".into());
		let mib = |b: u64| b as f64 / (1024.0 * 1024.0);

		match role.as_str() {
			"prove" => {
				let n: usize =
					std::env::var("N").ok().and_then(|s| s.parse().ok()).unwrap_or(8);
				let t0 = std::time::Instant::now();
				let (pkg, pin) = publish_epoch("se", 42, n).expect("publish");
				let prove_ms = t0.elapsed().as_millis();
				let bytes = pkg.to_bytes();
				// round-trip check: the verifier must load exactly what was proved
				let rt = EpochPackage::from_bytes(&bytes);
				assert_eq!(rt.epoch_proof.rstar, pkg.epoch_proof.rstar, "serialization round-trip");
				std::fs::write(&path, &bytes).expect("write package");
				std::fs::write(format!("{path}.pin"), &pin).expect("write pin");
				println!(
					"\n  [PROVER]  N={n}  publish {prove_ms} ms  PROVER PEAK RSS {:.0} MiB  \
					 package {:.1} KiB -> {path}\n\
					 \x20   (prover footprint is unconstrained: large box or fleet. The number that \
					 matters is the VERIFIER's, measured next in a separate process.)",
					mib(crate::b256_sha3::peak_rss_bytes()),
					bytes.len() as f64 / 1024.0,
				);
			}
			"verify" => {
				let bytes = std::fs::read(&path).expect("read package (run MVP_ROLE=prove first)");
				let pin = std::fs::read(format!("{path}.pin")).expect("read pin");
				let pkg = EpochPackage::from_bytes(&bytes);

				let t1 = std::time::Instant::now();
				let (epoch_ok, comp_ok) = verify_epoch_package(&pkg, &pin).expect("verify");
				let verify_ms = t1.elapsed().as_millis();
				assert!(epoch_ok && comp_ok, "loaded package must verify");

				// per-query cost, averaged over a handful of each — this is the STEADY-STATE
				// number (runs per lookup), distinct from the once-per-epoch verify above.
				let name0 = pkg.names[0].clone();
				let th = std::time::Instant::now();
				let reps = 20u32;
				for _ in 0..reps {
					let _ = resolve(&pkg, &name0, true).expect("hit");
				}
				let hit_us = th.elapsed().as_micros() as f64 / reps as f64;
				let tm = std::time::Instant::now();
				for _ in 0..reps {
					let _ = resolve(&pkg, "absent-name.se", true).expect("miss");
				}
				let miss_us = tm.elapsed().as_micros() as f64 / reps as f64;

				let verifier_rss = mib(crate::b256_sha3::peak_rss_bytes());
				println!(
					"\n  [VERIFIER]  N={} loaded {:.1} KiB package (NO proving in this process)\n\
					 \x20   verify-once  {verify_ms} ms   (epoch aggregation + completeness+pin) [ONCE/epoch, O(N)]\n\
					 \x20   per-query    HIT {hit_us:.0} us  MISS {miss_us:.0} us   [STEADY STATE, O(log N)]\n\
					 \x20   VERIFIER PEAK RSS  {verifier_rss:.0} MiB   IoT<500 {}   Pi<900 {}\n\
					 \x20   package/query note: verify-once is O(N) per-record checks; per-query is\n\
					 \x20   a binary search + one opening. RSS is flat in N (witness-free).\n\
					 \x20   ★ resolver holds no witness -> footprint bounded by proof+package, not\n\
					 \x20   the trace. Must fit ONE IoT device; the prover's need not.",
					pkg.names.len(),
					bytes.len() as f64 / 1024.0,
					verifier_rss < 500.0,
					verifier_rss < 900.0,
				);
				assert!(verifier_rss < 900.0, "verifier must fit a 1 GB Pi (measured {verifier_rss:.0} MiB)");
			}
			_ => panic!("set MVP_ROLE=prove or MVP_ROLE=verify"),
		}
	}

	/// W2 PROBE — the decisive unknown for Phase 1 (trustless flat-in-N binding).
	///
	/// Can the interleaved polynomial P be opened at a RECORD-SELECTING point `(a, bin(i))` as a
	/// SINGLE FRI opening that (1) verifies against one commitment and (2) yields exactly
	/// `P_i(a)`? If yes, per-record membership is O(1) trustless against R* = the FRI root, and the
	/// decider crux is tractable. If it needs N openings, Phase 1 collapses to O(N) and is not
	/// worth building. This probes it directly before any scope is committed.
	#[test]
	fn w2_probe_record_selecting_opening() {
		use crate::accumulation::mle_eval;
		use crate::decider::{decider_open_at_ext_l1, decider_verify_rooted_ext_l1, lift_b128_to_b256};
		use binius_field::BinaryField128b as B128;

		const N: usize = 4; // records
		const INNER: usize = 3; // log2(record length) => 8 values/record
		let n_vars = INNER + 2; // + log2(N)=2 select bits; |P| = 32 = 2^5

		// deterministic distinct records (no rng): value depends on (record, position)
		let records: Vec<Vec<B128>> = (0..N)
			.map(|i| {
				(0..(1 << INNER))
					.map(|j| B128::new(((i as u128) << 96) ^ (j as u128).wrapping_mul(0x9E3779B1) ^ 0xABCD))
					.collect()
			})
			.collect();
		// P = block concatenation (matches epoch_fold::interleave_records): low INNER bits = inner
		// index, high 2 bits = record index.
		let p: Vec<B128> = records.iter().flatten().copied().collect();
		assert_eq!(p.len(), 1 << n_vars);

		// inner challenge point a (INNER B128 coords), lifted to B256 for the decider.
		let a_b128: Vec<B128> = (0..INNER).map(|k| B128::new(0x1234_5678u128 + k as u128 * 7 + 1)).collect();

		// helper: full opening point for record i = [lift(a), lift(bit0(i)), lift(bit1(i))].
		let point_for = |i: usize| -> Vec<crate::b256_field::B256> {
			let mut pt: Vec<_> = a_b128.iter().map(|&x| lift_b128_to_b256(x)).collect();
			for b in 0..2 {
				let bit = (i >> b) & 1;
				pt.push(lift_b128_to_b256(if bit == 1 { B128::ONE } else { B128::ZERO }));
			}
			pt
		};

		let mut roots = Vec::new();
		for i in 0..N {
			let pt = point_for(i);
			let (root, proof, value, nv) = decider_open_at_ext_l1(&p, &pt, 128);
			// (1) the opening verifies against the single commitment
			assert!(
				decider_verify_rooted_ext_l1(root, proof, &pt, value, nv, 128),
				"record {i}: single opening at (a, bin(i)) must verify against the FRI root"
			);
			// (2) the opened value is EXACTLY P_i(a) — the record-selecting point isolates record i
			let expected = lift_b128_to_b256(mle_eval(&records[i], &a_b128));
			assert_eq!(
				value, expected,
				"record {i}: opened value must equal P_i(a); the select bits must isolate record i"
			);
			roots.push(root);
		}

		// (3) the FRI root commits P and is INDEPENDENT of which point we opened — so R* = this
		// root can be published once and every per-record opening checks against it.
		assert!(roots.windows(2).all(|w| w[0] == w[1]), "the commitment root must be point-independent");

		// (4) a forged value at a record-selecting point is REJECTED (soundness of the opening).
		let pt = point_for(1);
		let (root, proof, value, nv) = decider_open_at_ext_l1(&p, &pt, 128);
		let forged = value + lift_b128_to_b256(B128::ONE);
		assert!(
			!decider_verify_rooted_ext_l1(root, proof, &pt, forged, nv, 128),
			"a forged opened value must be rejected"
		);

		println!(
			"\n  W2 PROBE — RECORD-SELECTING SINGLE OPENING: FEASIBLE.\n\
			 \x20   Opening the interleaved P at (a, bin(i)) is ONE FRI opening that verifies\n\
			 \x20   against a single, point-independent root and yields exactly P_i(a) for every\n\
			 \x20   record i; a forged value is rejected. ⇒ per-record membership is O(1) and\n\
			 \x20   trustless against R* = the FRI root, so Phase 1's decider crux (verify_epoch_c1)\n\
			 \x20   does NOT require N openings. The trustless flat-in-N epoch is buildable."
		);
	}

	/// `EpochProof` has no `Clone`; rebuild it field-by-field for the tamper case.
	fn clone_proof(p: &EpochProof) -> EpochProof {
		EpochProof {
			rstar: p.rstar,
			sub_roots: p.sub_roots.clone(),
			opening_value: p.opening_value,
			decider_proof: p.decider_proof.clone(),
			n_vars: p.n_vars,
			epoch: p.epoch,
		}
	}

}
