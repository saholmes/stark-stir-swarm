// binius-substrate — M2b-3 "expose the depth-2 chain ROOT as a PUBLIC BOUNDARY".
//
// M2b-2 (see `sha3_seam.rs`) built a SOUND depth-2 SHA3-256 chain
//
//     g1   = SHA3-256( A ‖ B )
//     g2   = SHA3-256( g1_digest ‖ C )
//     root = g2_digest
//
// and proved the g1->g2 seam in-circuit. But the ROOT itself was only read
// witness-side and cross-checked against the native `sha3` crate — the verifier
// trusted the prover's witness read-back. That is fine for a leaf circuit, but a
// recursion / Merkle-root-of-inner-roots needs the root to be a VERIFIER-ENFORCED
// public output so an outer verifier can pin it.
//
// ============================ HOW THE ROOT BECOMES PUBLIC ===================
// In Binius/m3, "public output" = flush an in-circuit value to a CHANNEL and put
// the expected value in `Statement.boundaries`; the verifier rejects if the
// channel does not balance (multiset check). Concretely (all in `SeamTable`,
// gated by `new_with_root_boundary`):
//
//   1. `cs.add_channel("depth2_root")` -> a `ChannelId`.
//   2. The g2 digest = g2 output lanes 0..3, which live on TRACK 7 of
//      `g2.packed_state_out()` (`PackedLane8 = Col<B1,512>`, 8 tracks * 64 bits).
//      For each lane i in 0..4 we extract that 64-bit track as a `Col<B1,64>`
//      block via `add_selected_block::<B1,512,64>(.., 7)` — a VIRTUAL oracle
//      structurally derived from g2's committed output, so the prover cannot
//      decouple it from g2's real digest — then `add_packed::<B1,64,B64,1>` packs
//      each block to a `Col<B64,1>` (aliasing the same bits).
//   3. `table.push(root_channel, [root_b64[0..4]])` flushes the 4 root lanes to
//      the channel, once per table row.
//
// The matching PULL is supplied publicly, NOT in-circuit: `Statement.boundaries`
// carries one `Boundary { values: <claimed root, 4 B64 lanes upcast to B128>,
// channel_id: root_channel, direction: Pull, multiplicity: 1 }`. The channel
// balances IFF the pushed (genuine g2 digest) tuple equals the pulled (claimed
// root) tuple. Flip any byte of the claimed root and the multiset check fails —
// the verifier returns `ChannelUnbalanced`.
//
// ============================ SOUNDNESS BOUNDARY ============================
//  * ENFORCED by this milestone: the verifier now checks the claimed root
//    against g2's in-circuit digest via the channel balance. A wrong claimed
//    root is rejected by the SHA-256 pipeline (see the gate below), not merely by
//    a witness-side `assert_eq!`.
//  * The pushed lanes are a `Packed`-of-`Projected` view of g2's committed
//    output column, i.e. structurally the digest; there is no separate committed
//    "root" the prover could set independently.
//  * STILL a leaf statement: the boundary makes the root a public IO of THIS
//    proof. Composing it into an actual outer recursive verifier (feeding this
//    root as an input wire of a parent circuit) is the next milestone — see the
//    report. We do NOT overclaim recursion here.
// ============================================================================

use anyhow::Result;
use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::tower::CanonicalTowerFamily;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{
	Boundary, ConstraintSystem, FlushDirection, Statement, WitnessIndex, B128, B64,
};
use sha2::Sha256;

use crate::sha3_seam::{SeamMode, SeamTable, P};

/// End-to-end outcome of a root-boundary run, recording every stage so the gate
/// can prove exactly WHERE (and whether) a wrong claimed root is rejected.
#[derive(Debug)]
pub struct RootBoundaryOutcome {
	/// The genuine in-circuit root (g2 digest) the honest witness produced.
	pub root: [u8; 32],
	/// Proof size in bytes (0 if proving was not reached / failed).
	pub proof_size: usize,
	pub validate_ok: bool,
	pub validate_error: String,
	pub prove_ok: bool,
	pub prove_error: String,
	pub verify_ok: bool,
	pub verify_error: String,
	/// First stage that rejected: "none" | "validate" | "prove" | "verify".
	pub reject_stage: &'static str,
}

impl RootBoundaryOutcome {
	pub fn accepted(&self) -> bool {
		self.reject_stage == "none"
	}
}

/// Turn a 32-byte claimed root into the 4 `Boundary` field values: each 8-byte
/// little-endian lane is a `B64` element, upcast (canonical tower embedding) to
/// the `B128` field the channel operates in — exactly matching the `add_packed`
/// B64 lanes the table pushes.
fn claimed_root_to_boundary_values(claimed_root: [u8; 32]) -> Vec<B128> {
	(0..4)
		.map(|i| {
			let lane = u64::from_le_bytes(claimed_root[i * 8..i * 8 + 8].try_into().unwrap());
			B128::from(B64::new(lane))
		})
		.collect()
}

/// M2b-3 deliverable. Build the honest depth-2 seam witness for a SINGLE chain,
/// PUSH the g2 digest to a channel, and supply `claimed_root` as the channel's
/// public PULL in `Statement.boundaries`. Runs `validate_witness`, then the full
/// SHA-256 (FIPS 180-4) prove/verify, recording which stage (if any) rejects.
///
/// * `claimed_root == SHA3-256(SHA3-256(A‖B)‖C)`  -> every stage ACCEPTS.
/// * any other `claimed_root`                     -> the channel is unbalanced
///   and the pipeline REJECTS (see `reject_stage` / `*_error`).
pub fn prove_verify_seam_root_boundary(
	children: &[(([u8; 32], [u8; 32]), [u8; 32])],
	claimed_root: [u8; 32],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<RootBoundaryOutcome> {
	assert_eq!(
		children.len(),
		1,
		"the root-boundary gate is defined for a single depth-2 chain (one claimed root)"
	);

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let root_channel = cs.add_channel("depth2_root");
	let table = SeamTable::new_with_root_boundary(&mut cs, root_channel);

	let n = children.len();
	let statement = Statement {
		boundaries: vec![Boundary {
			values: claimed_root_to_boundary_values(claimed_root),
			channel_id: root_channel,
			direction: FlushDirection::Pull,
			multiplicity: 1,
		}],
		table_sizes: vec![n],
	};

	// Honest witness: the table PUSHes g2's genuine digest regardless of the
	// claimed root; only the boundary carries the (possibly wrong) claim.
	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	let (_g1_digests, roots) = table.populate(&mut segment, children, SeamMode::Honest)?;
	drop(segment);
	let root = roots[0];

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// Stage 1: deterministic channel-balance + constraint check.
	let validate = binius_core::constraint_system::validate::validate_witness(
		&ccs,
		&statement.boundaries,
		&witness,
	);
	let validate_ok = validate.is_ok();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

	// Stage 2/3: full SHA-256 prove, then verify.
	let proof = binius_core::constraint_system::prove::<
		U,
		CanonicalTowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(
		&ccs,
		log_inv_rate,
		security_bits,
		&statement.boundaries,
		witness,
		&binius_hal::make_portable_backend(),
	);

	let (proof_size, prove_ok, prove_error, verify_ok, verify_error) = match proof {
		Err(e) => (0, false, e.to_string(), false, String::new()),
		Ok(proof) => {
			let proof_size = proof.get_proof_size();
			let verify = binius_core::constraint_system::verify::<
				U,
				CanonicalTowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
			>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof);
			match verify {
				Err(e) => (proof_size, true, String::new(), false, e.to_string()),
				Ok(()) => (proof_size, true, String::new(), true, String::new()),
			}
		}
	};

	let reject_stage = if !validate_ok {
		"validate"
	} else if !prove_ok {
		"prove"
	} else if !verify_ok {
		"verify"
	} else {
		"none"
	};

	Ok(RootBoundaryOutcome {
		root,
		proof_size,
		validate_ok,
		validate_error,
		prove_ok,
		prove_error,
		verify_ok,
		verify_error,
		reject_stage,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use sha3::{Digest, Sha3_256};

	fn native_sha3_256(msg: &[u8]) -> [u8; 32] {
		let mut h = Sha3_256::new();
		h.update(msg);
		h.finalize().into()
	}

	fn native_root(a: &[u8; 32], b: &[u8; 32], c: &[u8; 32]) -> [u8; 32] {
		let mut m1 = Vec::with_capacity(64);
		m1.extend_from_slice(a);
		m1.extend_from_slice(b);
		let d1 = native_sha3_256(&m1);
		let mut m2 = Vec::with_capacity(64);
		m2.extend_from_slice(&d1);
		m2.extend_from_slice(c);
		native_sha3_256(&m2)
	}

	/// M2b-3 gate #1: the CORRECT root as a public boundary -> the depth-2 chain
	/// proves AND verifies under SHA-256; the channel balances.
	#[test]
	fn root_boundary_correct_accepts() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let c = [0xCCu8; 32];
		let root_exp = native_root(&a, &b, &c);

		let children = vec![((a, b), c)];
		let outcome = prove_verify_seam_root_boundary(&children, root_exp, 1, 100)
			.expect("root-boundary harness must run to completion");

		assert_eq!(outcome.root, root_exp, "in-circuit root != native SHA3-256(g1‖C)");
		assert!(
			outcome.accepted(),
			"correct root rejected at stage '{}': validate='{}' prove='{}' verify='{}'",
			outcome.reject_stage,
			outcome.validate_error,
			outcome.prove_error,
			outcome.verify_error
		);
		assert!(outcome.validate_ok && outcome.prove_ok && outcome.verify_ok);
		assert!(outcome.proof_size > 0);
		println!(
			"M2b-3 correct-root ACCEPTS: root enforced as public boundary; proof = {} bytes",
			outcome.proof_size
		);
	}

	/// M2b-3 THE DELIVERABLE (gate #2): a WRONG claimed root (one byte flipped)
	/// with an otherwise-honest witness MUST be REJECTED, because the g2-digest
	/// PUSH no longer matches the boundary PULL and the channel is unbalanced.
	#[test]
	fn root_boundary_wrong_rejected() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let c = [0xCCu8; 32];
		let root_exp = native_root(&a, &b, &c);

		// Flip one byte of the genuine root -> a value that is not g2's digest.
		let mut wrong = root_exp;
		wrong[0] ^= 0x01;
		assert_ne!(wrong, root_exp);

		let children = vec![((a, b), c)];
		let outcome = prove_verify_seam_root_boundary(&children, wrong, 1, 100)
			.expect("root-boundary harness must run to completion");

		// The witness still computes the genuine root; only the public claim is wrong.
		assert_eq!(outcome.root, root_exp);
		assert!(
			!outcome.accepted(),
			"SOUNDNESS FAILURE: a WRONG claimed root was ACCEPTED (channel did not enforce the root)"
		);
		// And in particular the SHA-256 verifier (not just validate) must reject.
		assert!(
			!outcome.verify_ok,
			"SOUNDNESS FAILURE: SHA-256 verify ACCEPTED a wrong claimed root"
		);
		println!(
			"M2b-3 wrong-root REJECTED at stage '{}':\n  validate: ok={} err='{}'\n  prove   : ok={} err='{}'\n  verify  : ok={} err='{}'",
			outcome.reject_stage,
			outcome.validate_ok,
			outcome.validate_error,
			outcome.prove_ok,
			outcome.prove_error,
			outcome.verify_ok,
			outcome.verify_error
		);
	}
}
