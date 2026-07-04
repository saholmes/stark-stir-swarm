// binius-substrate — M2b-1 "SOUND single-block SHA3-256 padding binding".
//
// M2a proved the Keccak-f permutation in-circuit but left `state_in` a *free*
// committed column: a malicious prover could commit ANY 1600-bit state and get
// an accepting "some Keccak-f permutation" proof. M2b-1 closes that hole for a
// fixed-shape single-block message by pinning, IN-CIRCUIT, that track-0 of
// `state_in` (the real permutation input) is the FIPS-202 padded block of a
// committed message.
//
// ============================ WHAT IS NOW SOUND =============================
// We add zero-constraints on the *committed* `state_in` columns of the wrapped
// `Keccakf` gadget, so the verifier's zerocheck rejects any witness whose
// track-0 input deviates from the FIPS-202 padding. Concretely (fixed message
// length mlen = 3, e.g. "abc"; single block, rate 136):
//
//   * PADDING-CONSTANT BINDING (the load-bearing soundness step):
//       - lane 0, byte 3      == 0x06   (SHA-3 domain separator + pad10*1 start)
//       - lanes 1..=15        == 0       (message region past mlen up to pad)
//       - lane 16 (byte 135)  == 0x80    (pad10*1 closing bit)
//       - lanes 17..=24       == 0       (the 512-bit capacity)
//     A prover who commits a non-FIPS `state_in` (wrong domain byte, nonzero
//     capacity, missing closing bit, …) now FAILS the zerocheck.
//
//   * MESSAGE-COLUMN BINDING:
//       We add a separate committed column `msg_lane0` and constrain
//       `state_in[lane0]` to equal it on the message bytes (bits 0..=23). So the
//       proof is *about a specific committed message*, and that commitment is a
//       first-class column a later milestone (M2b-2 Merkle chaining) can open.
//
//   * DIGEST AS OUTPUT:
//       `state_out` track-0 lanes 0..=3 are already constrained by `Keccakf` to
//       be the permutation of the (now-pinned) `state_in`. Since `state_in`
//       track-0 is fully determined by (committed message bytes) + (pinned
//       constants), the squeezed digest is a deterministic function of the
//       committed message. We still *read* the digest witness-side for the NIST
//       cross-check; exposing it as a public boundary column is M2b-2 work.
//
// ============================ THE track-0 MECHANISM =========================
// The `Keccakf` gadget packs 8 SIMD "tracks" into each lane column
// (`PackedLane8 = Col<B1, 512>`): track 0 (bits 0..64) is the permutation input,
// tracks 1..7 (bits 64..512) are interior round states. A whole-column
// `assert_zero` against a constant would WRONGLY constrain the interior tracks.
//
// We isolate track 0 with a per-position MASK — exactly the trick the gadget
// itself uses with `link_sel` (all-ones on tracks 0..6, zero on track 7) to
// disable a check on one track. Our constraints have the shape
//
//     (state_in[lane] - target) * track0_mask == 0        (per B1 position)
//
// where `track0_mask` is a `Col<B1,512>` constant that is 1 on bit positions
// 0..64 (track 0) and 0 on 64..512. At masked-out positions the product is 0
// unconditionally, so tracks 1..7 stay free; at track-0 positions the product is
// zero iff `state_in == target` there. `target`/`mask` are transparent
// `add_constant` columns; the message bytes are left free (their mask bit is 0)
// and bound instead to the committed `msg_lane0` column.
// ============================================================================

use anyhow::Result;
use binius_field::{arch::OptimalUnderlier, as_packed_field::PackedType};
use binius_m3::{
	builder::{Col, ConstraintSystem, Statement, TableId, WitnessIndex, B1, B128},
	gadgets::hash::keccak::{self, Keccakf, StateMatrix},
};

use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::tower::CanonicalTowerFamily;
use binius_hash::sha2::Sha256Compression;
use sha2::Sha256;

use crate::sha3_gadget::digest_from_state;

/// Concrete packed field used throughout (same as M1/M2a).
type P = PackedType<OptimalUnderlier, B128>;

/// Fixed message length for the M2b-1 binding: single-block, 3-byte message
/// (e.g. "abc"). The 3 message BYTES are committed/free; the message LENGTH and
/// all padding are pinned by the circuit structure.
pub const FIXED_MLEN: usize = 3;

const LANE_BITS: usize = 512; // PackedLane8 = 8 tracks * 64 bits.

// Track-0 target/mask patterns (as the low 64 bits; tracks 1..7 are always 0 so
// the interior round states are never constrained).
const MASK_FULL: u64 = u64::MAX; //                    all 64 bits of the lane
const MASK_MSG_HIGH: u64 = 0xFFFF_FFFF_FF00_0000; //   bytes 3..=7 (domain + pad + zero)
const MASK_MSG_LOW: u64 = 0x0000_0000_00FF_FFFF; //    bytes 0..=2 (the committed message)
const TARGET_LANE0: u64 = 0x0000_0000_0600_0000; //    byte 3 = 0x06 (domain sep), bytes 4..=7 = 0
const TARGET_LANE16: u64 = 0x8000_0000_0000_0000; //   byte 135 = 0x80 (pad10*1 closing bit)

/// Build a `[B1; 512]` constant whose track 0 (bits 0..64) carries `track0` and
/// whose interior tracks (bits 64..512) are all zero.
fn track0_pattern(track0: u64) -> [B1; LANE_BITS] {
	std::array::from_fn(|pos| {
		if pos < 64 {
			B1::from(((track0 >> pos) & 1) as u8)
		} else {
			B1::from(0u8)
		}
	})
}

/// Pack a fixed-`mlen` message into the low bytes of a track-0 lane value.
fn msg_track0(msg: &[u8]) -> u64 {
	assert_eq!(msg.len(), FIXED_MLEN, "M2b-1 binding is fixed to mlen=3");
	(msg[0] as u64) | ((msg[1] as u64) << 8) | ((msg[2] as u64) << 16)
}

/// A single-table constraint system that proves a batch of single-block
/// SHA3-256 hashes AND binds each `state_in` to the FIPS-202 padding of a
/// committed 3-byte message.
pub struct Sha3BindingTable {
	pub table_id: TableId,
	pub keccakf: Keccakf,
	// Columns we must populate in witness generation.
	msg_lane0: Col<B1, LANE_BITS>,
	mask_full: Col<B1, LANE_BITS>,
	mask_msg_high: Col<B1, LANE_BITS>,
	mask_msg_low: Col<B1, LANE_BITS>,
	target_lane0: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
}

impl Sha3BindingTable {
	pub fn new(cs: &mut ConstraintSystem) -> Self {
		let mut table = cs.add_table("SHA3-256 sound single block (M2b-1)");

		// The Keccak-f gadget owns the committed `state_in` columns. Keep our own
		// handle (Col is Copy, so StateMatrix<Col> is Clone) to add constraints.
		let state_in =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = keccak::Keccakf::new(&mut table, state_in.clone());

		// Separate committed message column (message-column binding target).
		let msg_lane0: Col<B1, LANE_BITS> = table.add_committed("msg_lane0");

		// Transparent constant columns (track-0 targets and masks).
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let mask_msg_high = table.add_constant("mask_msg_high", track0_pattern(MASK_MSG_HIGH));
		let mask_msg_low = table.add_constant("mask_msg_low", track0_pattern(MASK_MSG_LOW));
		let target_lane0 = table.add_constant("target_lane0", track0_pattern(TARGET_LANE0));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		// ---- The binding zero-constraints (track-0 only, via the masks) ----
		let s = state_in.as_inner();

		// lane 0: message bytes bound to `msg_lane0` (bits 0..=23); domain byte
		// 0x06 + zero-fill pinned (bits 24..=63).
		table.assert_zero("bind_lane0_msg", (s[0] - msg_lane0) * mask_msg_low);
		table.assert_zero("bind_lane0_pad", (s[0] - target_lane0) * mask_msg_high);

		// lanes 1..=15: message region past mlen up to the pad — all zero.
		for i in 1..=15 {
			table.assert_zero(format!("bind_zero_lane{i}"), s[i] * mask_full);
		}

		// lane 16 (byte 135): pad10*1 closing bit 0x80.
		table.assert_zero("bind_lane16_pad", (s[16] - target_lane16) * mask_full);

		// lanes 17..=24: the 512-bit capacity — all zero.
		for i in 17..=24 {
			table.assert_zero(format!("bind_cap_zero_lane{i}"), s[i] * mask_full);
		}

		Self {
			table_id: table.id(),
			keccakf,
			msg_lane0,
			mask_full,
			mask_msg_high,
			mask_msg_low,
			target_lane0,
			target_lane16,
		}
	}

	/// Fill the transparent-constant witness buffers and the committed
	/// `msg_lane0` column. (Like the keccak gadget's `round_const`/`link_sel`,
	/// constant columns must be materialized so the prover's zerocheck matches
	/// the verifier's transparent oracle.)
	fn populate_binding(
		&self,
		seg: &mut binius_m3::builder::TableWitnessSegment<P>,
		messages: &[Vec<u8>],
	) -> Result<()> {
		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.mask_msg_high, MASK_MSG_HIGH)?;
		fill_track0_const(seg, self.mask_msg_low, MASK_MSG_LOW)?;
		fill_track0_const(seg, self.target_lane0, TARGET_LANE0)?;
		fill_track0_const(seg, self.target_lane16, TARGET_LANE16)?;

		// Per-row message column: track 0 = message bytes, interior tracks 0.
		let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(self.msg_lane0)?;
		for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
			let val = messages.get(k).map(|m| msg_track0(m)).unwrap_or(0);
			chunk.copy_from_slice(&[val, 0, 0, 0, 0, 0, 0, 0]);
		}
		Ok(())
	}
}

/// Write a track-0 constant `val` (interior tracks 0) into every row of a
/// `Col<B1,512>` witness buffer, viewed as 8 u64 tracks per row.
fn fill_track0_const(
	seg: &mut binius_m3::builder::TableWitnessSegment<P>,
	col: Col<B1, LANE_BITS>,
	val: u64,
) -> Result<()> {
	let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
	for chunk in d.chunks_exact_mut(8) {
		chunk.copy_from_slice(&[val, 0, 0, 0, 0, 0, 0, 0]);
	}
	Ok(())
}

/// How a witness state_in was tampered, for the adversarial soundness gate.
#[derive(Clone, Copy, Debug)]
pub enum Corruption {
	/// Zero the SHA-3 domain separator byte (byte 3, lane 0): 0x06 -> 0x00.
	/// The (in, out) pair stays a valid Keccak-f permutation, so ONLY the
	/// padding binding can reject it.
	DomainByte,
	/// Set a capacity lane (lane 17) nonzero — a non-sponge input.
	CapacityLane,
}

/// Build the track-0 `state_in` matrix for a message, optionally corrupted.
/// Honest path uses the FIPS-202 padding; corrupted paths produce a *valid*
/// Keccak-f input (so `populate` succeeds and the permutation constraints hold)
/// that violates only the padding structure.
fn state_in_for(msg: &[u8], corrupt: Option<Corruption>) -> StateMatrix<u64> {
	assert_eq!(msg.len(), FIXED_MLEN, "M2b-1 binding is fixed to mlen=3");
	let mut bytes = [0u8; 200];
	bytes[..FIXED_MLEN].copy_from_slice(msg);
	// FIPS-202 pad10*1 with the SHA-3 domain separator.
	bytes[FIXED_MLEN] ^= 0x06; // byte 3
	bytes[135] ^= 0x80; // closing bit

	match corrupt {
		None => {}
		Some(Corruption::DomainByte) => {
			// Remove the 0x06 domain separator — the load-bearing padding byte.
			bytes[FIXED_MLEN] = 0x00;
		}
		Some(Corruption::CapacityLane) => {
			// byte 136 is the first capacity byte (lane 17) — must be zero.
			bytes[136] = 0x01;
		}
	}

	let lanes: [u64; 25] =
		std::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()));
	StateMatrix::from_values(lanes)
}

/// Honest end-to-end: prove + verify sound single-block SHA3-256 for each 3-byte
/// message, under a SHA-256 (FIPS 180-4) Merkle commitment and SHA-256
/// Fiat–Shamir transcript. Returns `(proof_size_bytes, in_circuit_digests)`.
///
/// Internally asserts (`validate_witness`) that the honest witness satisfies all
/// binding constraints before proving.
pub fn prove_verify_bound_sha3(
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<[u8; 32]>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3BindingTable::new(&mut cs);

	let n = messages.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let events: Vec<StateMatrix<u64>> = messages.iter().map(|m| state_in_for(m, None)).collect();

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	table.keccakf.populate_state_in(&mut segment, &events)?;
	table.keccakf.populate(&mut segment)?;
	table.populate_binding(&mut segment, messages)?;
	let digests: Vec<[u8; 32]> = table
		.keccakf
		.read_state_outs(&segment)?
		.map(|state| digest_from_state(&state))
		.collect();
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// Deterministic sanity gate: the honest witness must satisfy every zero
	// constraint (permutation + binding) exactly.
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)
		.map_err(|e| anyhow::anyhow!("honest witness failed validate_witness: {e}"))?;

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
	)?;

	let proof_size = proof.get_proof_size();

	binius_core::constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;

	Ok((proof_size, digests))
}

/// Which stage rejected a corrupted witness, for reporting.
#[derive(Debug)]
pub struct RejectReport {
	/// `validate_witness` (deterministic constraint check) rejected, with the
	/// error string (names the violated constraint).
	pub validate_rejected: bool,
	pub validate_error: String,
	/// The full SHA-256 prove/verify pipeline rejected.
	pub pipeline_rejected: bool,
	/// Which pipeline stage produced the rejection ("prove" or "verify").
	pub pipeline_stage: &'static str,
	pub pipeline_error: String,
}

/// Adversarial soundness gate: build a *single-message* witness whose track-0
/// `state_in` is corrupted (bad padding) but is still a valid Keccak-f
/// (in, out) permutation pair, then check that the binding constraint REJECTS
/// it — first deterministically via `validate_witness`, then end-to-end via the
/// real SHA-256 prove/verify pipeline.
pub fn bad_witness_rejected(
	corrupt: Corruption,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<RejectReport> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3BindingTable::new(&mut cs);

	let msg = b"abc".to_vec();
	let messages = vec![msg.clone()];
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![1],
	};

	// Corrupted track-0 input; msg_lane0 is populated with the *honest* message
	// bytes, so the message-binding constraint still holds and the rejection is
	// isolated to the padding-constant constraint.
	let events = vec![state_in_for(&msg, Some(corrupt))];

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, 1)?;
	let mut segment = table_witness.full_segment();
	// `populate` must succeed on the corrupt-but-valid permutation input, so
	// that any rejection comes from OUR binding constraint, not a populate panic.
	table.keccakf.populate_state_in(&mut segment, &events)?;
	table.keccakf.populate(&mut segment)?;
	table.populate_binding(&mut segment, &messages)?;
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// 1) Deterministic: validate_witness must flag the violated binding.
	let validate = binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness);
	let validate_rejected = validate.is_err();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

	// 2) End-to-end SHA-256 pipeline: prove then verify. A zero-constraint
	//    violation makes either the prover error out or the verifier reject.
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

	let (pipeline_rejected, pipeline_stage, pipeline_error) = match proof {
		Err(e) => (true, "prove", e.to_string()),
		Ok(proof) => {
			let verify = binius_core::constraint_system::verify::<
				U,
				CanonicalTowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
			>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof);
			match verify {
				Err(e) => (true, "verify", e.to_string()),
				Ok(()) => (false, "none", String::new()),
			}
		}
	};

	Ok(RejectReport {
		validate_rejected,
		validate_error,
		pipeline_rejected,
		pipeline_stage,
		pipeline_error,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::sha3_gadget::padded_state;
	use sha3::{Digest, Sha3_256};

	const NIST_ABC: [u8; 32] = [
		0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3, 0x90,
		0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43,
		0x15, 0x32,
	];

	fn native_sha3_256(msg: &[u8]) -> [u8; 32] {
		let mut h = Sha3_256::new();
		h.update(msg);
		h.finalize().into()
	}

	/// Cross-check that the fixed-shape `state_in_for` reproduces exactly the
	/// M2a `padded_state` on the honest path (so the binding is over the real
	/// FIPS-202 block), and that the two corruptions actually differ from it.
	#[test]
	fn binding_state_matches_m2a_padding() {
		let honest = state_in_for(b"abc", None);
		assert_eq!(honest, padded_state(b"abc"), "honest binding state != M2a padded_state");

		let bad_dom = state_in_for(b"abc", Some(Corruption::DomainByte));
		assert_ne!(bad_dom, honest, "domain corruption must change the state");
		let bad_cap = state_in_for(b"abc", Some(Corruption::CapacityLane));
		assert_ne!(bad_cap, honest, "capacity corruption must change the state");
	}

	/// M2b-1 honest gate: the padded, message-bound `state_in` for "abc" proves
	/// and verifies under SHA-256, and the in-circuit digest equals the NIST
	/// SHA3-256("abc") vector.
	#[test]
	fn sound_sha3_honest_accepts() {
		let messages = vec![b"abc".to_vec()];
		let (proof_size, digests) = prove_verify_bound_sha3(&messages, 1, 100)
			.expect("honest bound SHA3-256 proof must verify");

		assert_eq!(digests.len(), 1);
		assert_eq!(digests[0], NIST_ABC, "in-circuit bound SHA3-256(\"abc\") != NIST vector");
		assert_eq!(digests[0], native_sha3_256(b"abc"));
		assert!(proof_size > 0);
		println!(
			"M2b-1 sound SHA3-256(\"abc\") verified (message-bound + padding-pinned); proof size = {proof_size} bytes"
		);
	}

	/// M2b-1 adversarial gate (domain byte): a witness whose track-0 `state_in`
	/// has the SHA-3 domain byte 0x06 zeroed — but is otherwise a valid Keccak-f
	/// (in, out) permutation pair — MUST be rejected. This is the deliverable:
	/// only the new padding binding can reject it.
	#[test]
	fn sound_sha3_bad_padding_rejected() {
		let report = bad_witness_rejected(Corruption::DomainByte, 1, 100)
			.expect("adversarial harness must run to completion");

		assert!(
			report.validate_rejected,
			"SOUNDNESS FAILURE: validate_witness accepted a bad-padding state_in"
		);
		assert!(
			report.pipeline_rejected,
			"SOUNDNESS FAILURE: SHA-256 prove/verify accepted a bad-padding state_in"
		);
		println!(
			"M2b-1 bad-padding (domain 0x06->0x00) REJECTED:\n  validate_witness: {}\n  pipeline stage : {}\n  pipeline error : {}",
			report.validate_error, report.pipeline_stage, report.pipeline_error
		);
	}

	/// M2b-1 adversarial gate (capacity): a nonzero capacity lane (non-sponge
	/// input) must also be rejected by the capacity binding.
	#[test]
	fn sound_sha3_bad_capacity_rejected() {
		let report = bad_witness_rejected(Corruption::CapacityLane, 1, 100)
			.expect("adversarial harness must run to completion");

		assert!(
			report.validate_rejected,
			"SOUNDNESS FAILURE: validate_witness accepted a nonzero-capacity state_in"
		);
		assert!(
			report.pipeline_rejected,
			"SOUNDNESS FAILURE: SHA-256 prove/verify accepted a nonzero-capacity state_in"
		);
		println!(
			"M2b-1 bad-capacity (lane17 != 0) REJECTED:\n  validate_witness: {}\n  pipeline stage : {}",
			report.validate_error, report.pipeline_stage
		);
	}
}
