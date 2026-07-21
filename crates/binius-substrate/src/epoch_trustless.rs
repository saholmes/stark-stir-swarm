//! Phase 1 — the TRUSTLESS, flat-in-N epoch.
//!
//! `epoch_c1` is trustless but O(N) at the resolver (N per-record FRI verifies, O(N) state).
//! `epoch_fold` is flat-in-N but Model A (the resolver trusts the aggregator committed
//! `P = interleave(records)`). This module gives both at once, on the basis the W2 probe
//! confirmed (`mvp_epoch::tests::w2_probe_record_selecting_opening`): the interleaved polynomial
//! `P` can be opened at a record-selecting point `(a, bin(i))` as a SINGLE decider opening that
//! verifies against one FRI root and yields exactly `P_i(a)`.
//!
//! ## The construction
//!
//! `R*` is the FRI commitment root of `P = interleave(records)` — NOT a SHA3 Merkle parent over
//! per-record roots. Because the decider opening carries its own FRI low-degree proof, an opening
//! that verifies against `R*` proves both that `R*` commits a genuine low-degree `P` and that
//! `P` evaluates to the claimed value at the queried point. So:
//!
//! * **verify-once** (per epoch): one decider opening of `P` at an FS-derived point bound to
//!   `R*`. Proves `R*` is a sound polynomial commitment. `O(1)` in `N`, trustless.
//! * **per query**: one decider opening at `(a, bin(i))` where `a` is FS-derived from `R*`. The
//!   resolver checks the opened value equals `mle(record_i, a)` computed from the record bytes it
//!   was given, so a wrong record is rejected. `O(1)` in `N`, trustless — no Merkle path, no
//!   sub-roots, no trust in the aggregator.
//!
//! The FS points are derived from `R*` (which is fixed the instant `P` is committed), so a prover
//! cannot choose a point after committing. This is the standard commit-then-open discipline.
//!
//! ## What is trusted
//!
//! Nothing about the aggregator. The resolver holds `R*` (32 bytes) and, per query, one opening it
//! verifies itself. The only assumption is the FRI/Merkle soundness of the decider — the same
//! assumption the paper's soundness path already rests on.

use crate::decider::{decider_open_at_ext_l1, decider_verify_rooted_ext_l1, lift_b128_to_b256};
use crate::b256_field::B256;
use binius_field::BinaryField128b as B128;
use sha3::{Digest, Sha3_256};

/// The once-per-epoch trustless proof. `rstar` is the FRI root of `P = interleave(records)`.
#[derive(Clone)]
pub struct TrustlessEpoch {
	pub rstar: [u8; 32],
	pub zone: String,
	pub epoch: u64,
	pub inner_vars: usize, // log2(record length)
	pub log_n: usize,      // log2(record count)
	// the batch decider opening at the FS point — proves R* commits a sound P.
	pub batch_value: B256,
	pub batch_proof: Vec<u8>,
}

/// A per-query record opening against `R*`.
#[derive(Clone)]
pub struct RecordProof {
	pub index: usize,
	pub record: Vec<B128>,
	pub value: B256,
	pub proof: Vec<u8>,
}

fn n_vars(inner_vars: usize, log_n: usize) -> usize {
	inner_vars + log_n
}

/// Interleave records by block concatenation: `P[i·2^inner .. (i+1)·2^inner) = record i`, so the
/// low `inner_vars` index bits are the inner position and the high `log_n` bits select the record.
fn interleave(records: &[Vec<B128>]) -> Vec<B128> {
	records.iter().flatten().copied().collect()
}

/// Multilinear extension of `evals` (length `2^n`) at `point` (length `n`), over `B128`.
fn mle_eval(evals: &[B128], point: &[B128]) -> B128 {
	use binius_field::Field;
	let n = point.len();
	assert_eq!(evals.len(), 1 << n);
	let mut acc = B128::ZERO;
	for (i, &e) in evals.iter().enumerate() {
		let mut w = B128::ONE;
		for (j, &pj) in point.iter().enumerate() {
			w *= if (i >> j) & 1 == 1 { pj } else { B128::ONE + pj };
		}
		acc += e * w;
	}
	acc
}

/// Derive `k` `B128` field coordinates from a domain-separated hash of `R*` (+ tag). Because `R*`
/// is the FRI commitment, this is bound to the committed `P` and cannot be pre-empted by a prover.
fn fs_coords(rstar: &[u8; 32], zone: &str, epoch: u64, tag: &[u8], k: usize) -> Vec<B128> {
	(0..k)
		.map(|j| {
			let mut h = Sha3_256::new();
			h.update(rstar);
			h.update(zone.as_bytes());
			h.update(epoch.to_le_bytes());
			h.update(tag);
			h.update((j as u64).to_le_bytes());
			let d: [u8; 32] = h.finalize().into();
			B128::new(u128::from_le_bytes(d[0..16].try_into().unwrap()))
		})
		.collect()
}

/// The full batch open-point: `n_vars` FS coordinates over inner ‖ select, all free.
fn batch_point(rstar: &[u8; 32], zone: &str, epoch: u64, nv: usize) -> Vec<B256> {
	fs_coords(rstar, zone, epoch, b"epoch-batch", nv).iter().map(|&x| lift_b128_to_b256(x)).collect()
}

/// The inner challenge point `a` (length `inner_vars`), shared by every per-record opening.
fn inner_point(rstar: &[u8; 32], zone: &str, epoch: u64, inner_vars: usize) -> Vec<B128> {
	fs_coords(rstar, zone, epoch, b"record-inner", inner_vars)
}

/// The full opening point for record `index`: `a` (lifted) followed by the `log_n` select bits.
fn record_point(a: &[B128], index: usize, log_n: usize) -> Vec<B256> {
	use binius_field::Field;
	let mut pt: Vec<B256> = a.iter().map(|&x| lift_b128_to_b256(x)).collect();
	for b in 0..log_n {
		let bit = (index >> b) & 1;
		pt.push(lift_b128_to_b256(if bit == 1 { B128::ONE } else { B128::ZERO }));
	}
	pt
}

/// AGGREGATOR (once/epoch). Commit `P = interleave(records)`, open it at the FS batch point.
///
/// `records`: each a power-of-two-length `B128` vector, all the same length; count a power of two.
pub fn prove_epoch(records: &[Vec<B128>], zone: &str, epoch: u64) -> TrustlessEpoch {
	let n = records.len();
	assert!(n.is_power_of_two() && n >= 2, "record count must be a power of two >= 2");
	let inner_len = records[0].len();
	assert!(inner_len.is_power_of_two(), "record length must be a power of two");
	assert!(records.iter().all(|r| r.len() == inner_len), "records must be equal length");
	let inner_vars = inner_len.trailing_zeros() as usize;
	let log_n = n.trailing_zeros() as usize;
	let nv = n_vars(inner_vars, log_n);

	let p = interleave(records);
	// R* is point-independent (W2 probe #3), so committing/opening at any point yields the same
	// root. We open at the FS batch point; the returned root is R*.
	let rstar = crate::decider::decider_commit_root_l1(&p, 128);
	let pt = batch_point(&rstar, zone, epoch, nv);
	let (root2, batch_proof, batch_value, _nv) = decider_open_at_ext_l1(&p, &pt, 128);
	debug_assert_eq!(root2, rstar, "commit root must be point-independent");

	TrustlessEpoch {
		rstar,
		zone: zone.to_string(),
		epoch,
		inner_vars,
		log_n,
		batch_value,
		batch_proof,
	}
}

/// RESOLVER (once/epoch), TRUSTLESS. Verify the batch opening against `R*`: `O(1)` in `N`.
pub fn verify_epoch(ep: &TrustlessEpoch, zone: &str) -> bool {
	if ep.zone != zone {
		return false;
	}
	let nv = n_vars(ep.inner_vars, ep.log_n);
	let pt = batch_point(&ep.rstar, zone, ep.epoch, nv);
	decider_verify_rooted_ext_l1(ep.rstar, ep.batch_proof.clone(), &pt, ep.batch_value, nv, 128)
}

/// AGGREGATOR/OPERATOR (per query). Open `P` at `(a, bin(index))` to serve record `index`.
pub fn open_record(records: &[Vec<B128>], index: usize, ep: &TrustlessEpoch) -> RecordProof {
	let p = interleave(records);
	let a = inner_point(&ep.rstar, &ep.zone, ep.epoch, ep.inner_vars);
	let pt = record_point(&a, index, ep.log_n);
	let (_root, proof, value, _nv) = decider_open_at_ext_l1(&p, &pt, 128);
	RecordProof { index, record: records[index].clone(), value, proof }
}

/// RESOLVER (per query), TRUSTLESS. `O(1)` in `N`: verify the opening against `R*` AND check the
/// opened value equals `mle(record, a)`, so the record bytes are bound to what `R*` commits.
pub fn verify_record(ep: &TrustlessEpoch, op: &RecordProof) -> bool {
	let a = inner_point(&ep.rstar, &ep.zone, ep.epoch, ep.inner_vars);
	let pt = record_point(&a, op.index, ep.log_n);
	let nv = n_vars(ep.inner_vars, ep.log_n);
	if !decider_verify_rooted_ext_l1(ep.rstar, op.proof.clone(), &pt, op.value, nv, 128) {
		return false;
	}
	// the opened value must be this record's own MLE at a — otherwise the served bytes are not
	// the record R* commits at block `index`.
	op.value == lift_b128_to_b256(mle_eval(&op.record, &a))
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::Field;

	fn synth(n: usize, inner: usize, salt: u128) -> Vec<Vec<B128>> {
		(0..n)
			.map(|i| {
				(0..(1usize << inner))
					.map(|j| B128::new(((i as u128) << 96) ^ (j as u128).wrapping_mul(0x9E3779B1) ^ salt))
					.collect()
			})
			.collect()
	}

	/// Phase 1 GATE — trustless AND flat-in-N: verify-once and per-query both against R* alone,
	/// with every tamper rejected.
	#[test]
	fn trustless_flat_epoch() {
		let records = synth(8, 3, 0xABCD);
		let ep = prove_epoch(&records, "se", 42);

		// verify-once, trustless, O(1)
		assert!(verify_epoch(&ep, "se"), "honest epoch must verify");
		assert!(!verify_epoch(&ep, "com"), "wrong zone must reject (FS point differs)");

		// every record opens and verifies against R* alone
		for i in 0..records.len() {
			let op = open_record(&records, i, &ep);
			assert!(verify_record(&ep, &op), "record {i} must verify against R*");
		}

		// TAMPER 1: a forged record (right index, wrong bytes) is rejected — the opened value no
		// longer equals mle(record, a).
		let mut bad = open_record(&records, 3, &ep);
		bad.record[0] += B128::ONE;
		assert!(!verify_record(&ep, &bad), "forged record bytes must be rejected");

		// TAMPER 2: a forged opening value is rejected by the decider.
		let mut bad2 = open_record(&records, 3, &ep);
		bad2.value += lift_b128_to_b256(B128::ONE);
		assert!(!verify_record(&ep, &bad2), "forged opening value must be rejected");

		// TAMPER 3: a wrong R* (different epoch's commitment) rejects the batch opening.
		let other = prove_epoch(&synth(8, 3, 0x9999), "se", 42);
		let mut swapped = ep.clone();
		swapped.rstar = other.rstar;
		assert!(!verify_epoch(&swapped, "se"), "a substituted R* must reject the opening");

		println!(
			"\n  PHASE 1 GATE trustless-flat-epoch: verify-once and per-query both discharge\n\
			 \x20   against R* = FRI(interleave(records)) ALONE — O(1) in N, NO Merkle path, NO\n\
			 \x20   sub-roots, NO trust in the aggregator. Forged record bytes, forged opening\n\
			 \x20   value, and a substituted R* are each REJECTED. This is the trustless flat-in-N\n\
			 \x20   epoch the Model-A backend traded away."
		);
	}

	/// The construction must hold as N grows (the point of flat-in-N).
	#[test]
	fn trustless_flat_scales() {
		for (n, inner) in [(16usize, 3usize), (64, 4)] {
			let records = synth(n, inner, 0x1);
			let ep = prove_epoch(&records, "se", 7);
			assert!(verify_epoch(&ep, "se"), "verify-once at N={n}");
			let op = open_record(&records, n / 2, &ep);
			assert!(verify_record(&ep, &op), "per-query at N={n}");
		}
	}
}
