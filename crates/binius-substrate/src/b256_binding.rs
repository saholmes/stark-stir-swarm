// binius-substrate — M2b-1 "SOUND single-block SHA3-256 padding binding", ported
// onto the 256-bit challenge/extension field `B256TowerFamily` (tower level 8) so
// the load-bearing IN-CIRCUIT soundness primitive proves AND verifies at NIST
// L1/L3 Fiat–Shamir security.
//
// This is `sha3_binding.rs` (M2b-1, over the DEFAULT CanonicalTowerFamily / B128)
// re-threaded through the B256 prove wiring proven out in `b256_keccak.rs` /
// `b256_sha3.rs`:
//   * `ConstraintSystem::<B256>` instead of the default `ConstraintSystem` (B128).
//   * `WitnessIndex::<B256>` (B256 is its own width-1 packed field), so the witness
//     segment is `TableWitnessSegment<B256>`.
//   * `prove/verify::<U256, B256TowerFamily, Sha256, Sha256Compression,
//     HasherChallenger<Sha256>>` — the 256-bit challenge field makes the FRI /
//     sumcheck error terms poly(N)/2^256 clear the NIST L1(128) and L3(192) query
//     budgets (that is the whole point of B256).
//
// ============================ WHAT IS SOUND (unchanged from M2b-1) ===========
// The binding zero-constraints on the *committed* `state_in` columns of the
// wrapped `Keccakf` gadget are IDENTICAL to the B128 version — they operate purely
// on B1 columns via a track-0 mask and `add_constant` transparent columns, both of
// which are field-generic (the fork's Phase B made `Keccakf` / `add_constant`
// generic over the top field). Concretely, for a fixed single-block 3-byte message
// (mlen = 3, e.g. "abc", rate 136):
//
//   * PADDING-CONSTANT BINDING (the load-bearing soundness step):
//       - lane 0, byte 3      == 0x06   (SHA-3 domain separator + pad10*1 start)
//       - lanes 1..=15        == 0
//       - lane 16 (byte 135)  == 0x80   (pad10*1 closing bit)
//       - lanes 17..=24       == 0      (the 512-bit capacity)
//   * MESSAGE-COLUMN BINDING: `state_in[lane0]` message bytes 0..=23 equal a
//     separate committed `msg_lane0` column.
//
// A prover who commits a non-FIPS `state_in` (wrong domain byte, nonzero capacity,
// missing closing bit, …) FAILS the zerocheck — now over the 256-bit field.
//
// ============================ THE track-0 MECHANISM (unchanged) ==============
// The `Keccakf` gadget packs 8 SIMD "tracks" into each lane column
// (`PackedLane8 = Col<B1, 512>`): track 0 (bits 0..64) is the permutation input,
// tracks 1..7 are interior round states. We isolate track 0 with a per-position
// MASK constant so the binding constraints
//
//     (state_in[lane] - target) * track0_mask == 0        (per B1 position)
//
// only bite on track 0 and never constrain interior round states. `target`/`mask`
// are transparent `add_constant` columns; message bytes are left free (mask bit 0)
// and bound instead to the committed `msg_lane0` column.
//
// ============================ FORK CHANGE ===================================
// NONE. Everything below is additive in our crate and reuses only the already-
// generic m3 surface (`add_committed`, `add_constant`, `assert_zero`,
// `TableWitnessSegment::get_mut_as`) plus the B256 tower family. `assert_zero`
// over `ConstraintSystem<B256>` and `add_constant` over B256 are exercised here for
// the first time OUTSIDE the Keccakf gadget internals, and both compile+prove
// unchanged — no residual B128 hard-coding in either op.
// ============================================================================

use anyhow::Result;
use binius_core::fiat_shamir::HasherChallenger;
use binius_hash::sha2::Sha256Compression;
use binius_m3::{
	builder::{Col, ConstraintSystem, Statement, TableId, WitnessIndex, B1},
	gadgets::hash::keccak::{self, Keccakf, StateMatrix},
};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::sha3_gadget::digest_from_state;

/// Witness segment packed type: B256 as its own width-1 packed field (matches
/// `WitnessIndex::<B256>` in `b256_keccak.rs`).
type Seg<'a> = binius_m3::builder::TableWitnessSegment<'a, OurB256>;

/// Fixed message length for the M2b-1 binding: single-block, 3-byte message.
pub const FIXED_MLEN: usize = 3;

const LANE_BITS: usize = 512; // PackedLane8 = 8 tracks * 64 bits.

// Track-0 target/mask patterns (as the low 64 bits; tracks 1..7 are always 0).
const MASK_FULL: u64 = u64::MAX;
const MASK_MSG_HIGH: u64 = 0xFFFF_FFFF_FF00_0000; //   bytes 3..=7 (domain + pad + zero)
const MASK_MSG_LOW: u64 = 0x0000_0000_00FF_FFFF; //    bytes 0..=2 (the committed message)
const TARGET_LANE0: u64 = 0x0000_0000_0600_0000; //    byte 3 = 0x06 (domain sep)
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

/// A single-table constraint system OVER B256 that proves a batch of single-block
/// SHA3-256 hashes AND binds each `state_in` to the FIPS-202 padding of a committed
/// 3-byte message.
pub struct Sha3BindingTableB256 {
	pub table_id: TableId,
	pub keccakf: Keccakf,
	msg_lane0: Col<B1, LANE_BITS>,
	mask_full: Col<B1, LANE_BITS>,
	mask_msg_high: Col<B1, LANE_BITS>,
	mask_msg_low: Col<B1, LANE_BITS>,
	target_lane0: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
}

impl Sha3BindingTableB256 {
	pub fn new(cs: &mut ConstraintSystem<OurB256>) -> Self {
		let mut table = cs.add_table("SHA3-256 sound single block over B256 (M2b-1)");

		let state_in =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = keccak::Keccakf::new(&mut table, state_in.clone());

		let msg_lane0: Col<B1, LANE_BITS> = table.add_committed("msg_lane0");

		// Transparent constant columns (track-0 targets and masks). `add_constant`
		// is generic over the top field (Phase B); this is its first use over B256
		// outside the Keccakf gadget internals.
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let mask_msg_high = table.add_constant("mask_msg_high", track0_pattern(MASK_MSG_HIGH));
		let mask_msg_low = table.add_constant("mask_msg_low", track0_pattern(MASK_MSG_LOW));
		let target_lane0 = table.add_constant("target_lane0", track0_pattern(TARGET_LANE0));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		// ---- The binding zero-constraints (track-0 only, via the masks) ----
		let s = state_in.as_inner();

		table.assert_zero("bind_lane0_msg", (s[0] - msg_lane0) * mask_msg_low);
		table.assert_zero("bind_lane0_pad", (s[0] - target_lane0) * mask_msg_high);

		for i in 1..=15 {
			table.assert_zero(format!("bind_zero_lane{i}"), s[i] * mask_full);
		}

		table.assert_zero("bind_lane16_pad", (s[16] - target_lane16) * mask_full);

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

	/// Fill the transparent-constant witness buffers and the committed `msg_lane0`
	/// column over the B256 witness segment.
	fn populate_binding(&self, seg: &mut Seg<'_>, messages: &[Vec<u8>]) -> Result<()> {
		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.mask_msg_high, MASK_MSG_HIGH)?;
		fill_track0_const(seg, self.mask_msg_low, MASK_MSG_LOW)?;
		fill_track0_const(seg, self.target_lane0, TARGET_LANE0)?;
		fill_track0_const(seg, self.target_lane16, TARGET_LANE16)?;

		let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(self.msg_lane0)?;
		for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
			let val = messages.get(k).map(|m| msg_track0(m)).unwrap_or(0);
			chunk.copy_from_slice(&[val, 0, 0, 0, 0, 0, 0, 0]);
		}
		Ok(())
	}
}

/// Write a track-0 constant `val` (interior tracks 0) into every row of a
/// `Col<B1,512>` witness buffer over the B256 segment, viewed as 8 u64 tracks/row.
fn fill_track0_const(seg: &mut Seg<'_>, col: Col<B1, LANE_BITS>, val: u64) -> Result<()> {
	let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
	for chunk in d.chunks_exact_mut(8) {
		chunk.copy_from_slice(&[val, 0, 0, 0, 0, 0, 0, 0]);
	}
	Ok(())
}

/// How a witness state_in was tampered, for the adversarial soundness gate.
#[derive(Clone, Copy, Debug)]
pub enum Corruption {
	/// Zero the SHA-3 domain separator byte (byte 3, lane 0): 0x06 -> 0x00. The
	/// (in, out) pair stays a valid Keccak-f permutation, so ONLY the padding
	/// binding can reject it.
	DomainByte,
	/// Set a capacity lane (lane 17) nonzero — a non-sponge input.
	CapacityLane,
}

/// Build the track-0 `state_in` matrix for a message, optionally corrupted.
fn state_in_for(msg: &[u8], corrupt: Option<Corruption>) -> StateMatrix<u64> {
	assert_eq!(msg.len(), FIXED_MLEN, "M2b-1 binding is fixed to mlen=3");
	let mut bytes = [0u8; 200];
	bytes[..FIXED_MLEN].copy_from_slice(msg);
	bytes[FIXED_MLEN] ^= 0x06; // byte 3
	bytes[135] ^= 0x80; // closing bit

	match corrupt {
		None => {}
		Some(Corruption::DomainByte) => bytes[FIXED_MLEN] = 0x00,
		Some(Corruption::CapacityLane) => bytes[136] = 0x01,
	}

	let lanes: [u64; 25] =
		std::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()));
	StateMatrix::from_values(lanes)
}

/// Honest end-to-end OVER B256: prove + verify sound single-block SHA3-256 for each
/// 3-byte message, under a SHA-256 (FIPS 180-4) Merkle commitment and SHA-256
/// Fiat–Shamir transcript, with the challenge/extension field = `B256` (2^256).
/// Returns `(proof_size_bytes, in_circuit_digests)`.
pub fn prove_verify_bound_sha3_b256(
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<[u8; 32]>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = Sha3BindingTableB256::new(&mut cs);

	let n = messages.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let events: Vec<StateMatrix<u64>> = messages.iter().map(|m| state_in_for(m, None)).collect();

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
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
		.map_err(|e| anyhow::anyhow!("honest witness failed validate_witness over B256: {e}"))?;

	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
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
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;

	Ok((proof_size, digests))
}

/// Which stage rejected a corrupted witness, for reporting.
#[derive(Debug)]
pub struct RejectReport {
	pub validate_rejected: bool,
	pub validate_error: String,
	pub pipeline_rejected: bool,
	pub pipeline_stage: &'static str,
	pub pipeline_error: String,
}

/// Adversarial soundness gate OVER B256: build a single-message witness whose
/// track-0 `state_in` is corrupted (bad padding) but is still a valid Keccak-f
/// (in, out) permutation pair, then check that the binding constraint REJECTS it —
/// first deterministically via `validate_witness`, then end-to-end via the real
/// SHA-256 prove/verify pipeline with the 256-bit challenge field.
pub fn bad_witness_rejected_b256(
	corrupt: Corruption,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<RejectReport> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = Sha3BindingTableB256::new(&mut cs);

	let msg = b"abc".to_vec();
	let messages = vec![msg.clone()];
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![1],
	};

	// Corrupted track-0 input; msg_lane0 populated with the HONEST message bytes so
	// the message-binding constraint still holds and the rejection is isolated to
	// the padding-constant constraint.
	let events = vec![state_in_for(&msg, Some(corrupt))];

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, 1)?;
	let mut segment = table_witness.full_segment();
	// `populate` must succeed on the corrupt-but-valid permutation input, so that
	// any rejection comes from OUR binding constraint, not a populate panic.
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

	// 2) End-to-end SHA-256 pipeline over B256: prove then verify.
	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
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
				U256,
				B256TowerFamily,
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

	/// Cross-check that the fixed-shape `state_in_for` reproduces exactly the M2a
	/// `padded_state` on the honest path, and that both corruptions differ from it.
	#[test]
	fn binding_state_matches_m2a_padding() {
		let honest = state_in_for(b"abc", None);
		assert_eq!(honest, padded_state(b"abc"), "honest binding state != M2a padded_state");
		assert_ne!(state_in_for(b"abc", Some(Corruption::DomainByte)), honest);
		assert_ne!(state_in_for(b"abc", Some(Corruption::CapacityLane)), honest);
	}

	/// REQUIRED DELIVERABLE (accepts): the padded, message-bound `state_in` for
	/// "abc" proves and verifies OVER B256 at NIST L1 (security_bits=128), and the
	/// in-circuit digest equals the NIST SHA3-256("abc") vector.
	#[test]
	fn bound_sha3_over_b256_accepts() {
		let messages = vec![b"abc".to_vec()];
		let (proof_size, digests) = prove_verify_bound_sha3_b256(&messages, 1, 128)
			.expect("honest bound SHA3-256 proof must VERIFY over B256 at NIST L1 (128)");

		assert_eq!(digests.len(), 1);
		assert_eq!(digests[0], NIST_ABC, "in-circuit bound SHA3-256(\"abc\") over B256 != NIST vector");
		assert_eq!(digests[0], native_sha3_256(b"abc"), "over B256 != sha3 crate");
		assert!(proof_size > 0);
		println!(
			"M2b-1/B256 ACCEPTS: sound SHA3-256(\"abc\") message-bound + padding-pinned, VERIFIED \
			 at NIST L1(128) over the 256-bit challenge field; digest == NIST + sha3; proof = {proof_size} bytes"
		);
	}

	/// REQUIRED DELIVERABLE at NIST L3: same, at security_bits=192.
	#[test]
	fn bound_sha3_over_b256_accepts_l3() {
		let messages = vec![b"abc".to_vec()];
		let (proof_size, digests) = prove_verify_bound_sha3_b256(&messages, 1, 192)
			.expect("honest bound SHA3-256 proof must VERIFY over B256 at NIST L3 (192)");
		assert_eq!(digests[0], NIST_ABC);
		assert!(proof_size > 0);
		println!(
			"M2b-1/B256 ACCEPTS at NIST L3(192): sound SHA3-256(\"abc\") VERIFIED over B256; proof = {proof_size} bytes"
		);
	}

	/// THE REQUIRED DELIVERABLE (bad padding rejects): a witness whose track-0
	/// `state_in` has the SHA-3 domain byte 0x06 zeroed — but is otherwise a valid
	/// Keccak-f (in, out) permutation pair — MUST be rejected OVER B256, isolated to
	/// the new padding binding.
	#[test]
	fn bound_sha3_over_b256_bad_padding_rejected() {
		let report = bad_witness_rejected_b256(Corruption::DomainByte, 1, 128)
			.expect("adversarial harness must run to completion over B256");

		assert!(
			report.validate_rejected,
			"SOUNDNESS FAILURE: validate_witness accepted a bad-padding state_in over B256"
		);
		assert!(
			report.pipeline_rejected,
			"SOUNDNESS FAILURE: SHA-256 prove/verify over B256 accepted a bad-padding state_in"
		);
		assert!(
			report.validate_error.contains("bind_lane0_pad"),
			"reject not isolated to the padding-constant binding; got: {}",
			report.validate_error
		);
		println!(
			"M2b-1/B256 bad-padding (domain 0x06->0x00) REJECTED at NIST L1(128):\n  \
			 firing constraint: {}\n  pipeline stage   : {}\n  pipeline error   : {}",
			report.validate_error, report.pipeline_stage, report.pipeline_error
		);
	}

	/// THE REQUIRED DELIVERABLE (bad capacity rejects): a nonzero capacity lane
	/// (non-sponge input) must also be rejected by the capacity binding over B256.
	#[test]
	fn bound_sha3_over_b256_bad_capacity_rejected() {
		let report = bad_witness_rejected_b256(Corruption::CapacityLane, 1, 128)
			.expect("adversarial harness must run to completion over B256");

		assert!(
			report.validate_rejected,
			"SOUNDNESS FAILURE: validate_witness accepted a nonzero-capacity state_in over B256"
		);
		assert!(
			report.pipeline_rejected,
			"SOUNDNESS FAILURE: SHA-256 prove/verify over B256 accepted a nonzero-capacity state_in"
		);
		assert!(
			report.validate_error.contains("bind_cap_zero_lane17"),
			"reject not isolated to the capacity binding; got: {}",
			report.validate_error
		);
		println!(
			"M2b-1/B256 bad-capacity (lane17 != 0) REJECTED at NIST L1(128):\n  \
			 firing constraint: {}\n  pipeline stage   : {}",
			report.validate_error, report.pipeline_stage
		);
	}
}
