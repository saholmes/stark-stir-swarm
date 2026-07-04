// binius-substrate — M2c "in-circuit SHA3-384 / SHA3-512 single-block gadgets".
//
// SHA3-384 and SHA3-512 reuse the SAME Keccak-f[1600] permutation as SHA3-256
// (M2a). Only three things change between the FIPS-202 SHA-3 variants:
//   * the rate / capacity split (rate_bytes),
//   * the position of the pad10*1 closing bit 0x80 (the last rate byte), and
//   * the output length (how many output lanes are squeezed for the digest).
// The SHA-3 domain separator byte 0x06 and the initial zero state are identical.
//
// This module generalises the M2a gadget (`sha3_gadget.rs`) and the M2b-1 sound
// padding binding (`sha3_binding.rs`) over a `Sha3Variant` enum. It is PURELY
// ADDITIVE: the SHA3-256 modules are untouched, and their 256-bit behaviour is
// unchanged.
//
// ============================ SOUNDNESS BOUNDARY (READ THIS) ================
// Exactly as M2a/M2b-1, and it matters just as much at L3/L5:
//
//   * IN-CIRCUIT (constrained): the Keccak-f permutation itself, plus — in the
//     binding table — that track-0 of `state_in` is the FIPS-202 padded block of
//     a committed message (correct domain byte, correct closing bit at the
//     VARIANT's rate boundary, zeroed capacity lanes).
//
//   * WITNESS-SIDE (gated against `sha3`, not an in-circuit boundary): the
//     squeezed digest is READ from the output state and compared to the native
//     `sha3` crate + NIST KATs. Exposing the digest as a public boundary column
//     is later-milestone work (cf. sha3_root_boundary.rs for SHA3-256).
//
//   * OUTER COMMITMENT IS STILL SHA-256. The Merkle commitment + Fiat–Shamir
//     transcript remain SHA-256 (FIPS 180-4) here — that is the *transcript*
//     hash and is independent of the *in-circuit* hash being proved. So this
//     module delivers the kappa_bind IN-CIRCUIT primitive for L3/L5, but FULL
//     kappa_bind at L3/L5 for the OUTER commitment additionally needs a
//     SHA-384/SHA-512 outer compression (a separate follow-up — see report).
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

/// Concrete packed field used throughout (same as M1/M2a/M2b-1).
type P = PackedType<OptimalUnderlier, B128>;

const STATE_BYTES: usize = 200; // 1600-bit Keccak state = 25 lanes.
const LANE_BITS: usize = 512; // PackedLane8 = 8 tracks * 64 bits.

/// A FIPS-202 SHA-3 fixed-output variant. Carries everything that differs from
/// SHA3-256 as pure functions of the rate:
///   * `rate_bytes`           — sponge rate r in bytes,
///   * `close_lane`           — lane holding the pad10*1 closing bit 0x80,
///   * `capacity_lane_start`  — first capacity lane (must be zero on absorb),
///   * `digest_lanes`         — number of output lanes squeezed for the digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sha3Variant {
	Sha3_256,
	Sha3_384,
	Sha3_512,
}

impl Sha3Variant {
	/// Sponge rate in bytes (r/8). SHA3-256 = 136, SHA3-384 = 104, SHA3-512 = 72.
	pub const fn rate_bytes(self) -> usize {
		match self {
			Sha3Variant::Sha3_256 => 136,
			Sha3Variant::Sha3_384 => 104,
			Sha3Variant::Sha3_512 => 72,
		}
	}

	/// Number of output lanes squeezed for the digest (digest_bits / 64).
	/// SHA3-256 = 4, SHA3-384 = 6, SHA3-512 = 8.
	pub const fn digest_lanes(self) -> usize {
		match self {
			Sha3Variant::Sha3_256 => 4,
			Sha3Variant::Sha3_384 => 6,
			Sha3Variant::Sha3_512 => 8,
		}
	}

	/// Digest length in bytes.
	pub const fn digest_bytes(self) -> usize {
		self.digest_lanes() * 8
	}

	/// Lane that holds the pad10*1 closing bit 0x80 = last rate byte's lane.
	/// = rate_bytes/8 - 1. SHA3-256 = 16, SHA3-384 = 12, SHA3-512 = 8.
	pub const fn close_lane(self) -> usize {
		self.rate_bytes() / 8 - 1
	}

	/// First capacity lane (must be zero on absorb) = rate_bytes/8.
	/// SHA3-256 = 17, SHA3-384 = 13, SHA3-512 = 9.
	pub const fn capacity_lane_start(self) -> usize {
		self.rate_bytes() / 8
	}

	/// Human name for table/column labels.
	pub const fn name(self) -> &'static str {
		match self {
			Sha3Variant::Sha3_256 => "SHA3-256",
			Sha3Variant::Sha3_384 => "SHA3-384",
			Sha3Variant::Sha3_512 => "SHA3-512",
		}
	}
}

/// Build the padded initial sponge state for a single-block absorb of `msg`
/// under the given variant. FIPS-202 pad10*1 with the SHA-3 domain separator:
///   bytes[..mlen]        = msg
///   bytes[mlen]         ^= 0x06                (domain sep + pad10*1 start)
///   bytes[rate_bytes-1] ^= 0x80                (pad10*1 closing bit)
///   bytes[rate_bytes..] = 0                    (capacity)
/// When `mlen == rate_bytes - 1` the two XOR writes coincide -> 0x86 (correct).
///
/// Lane mapping (FIPS-202 §B.1): state byte b lives in lane b/8, little-endian
/// within the lane; `StateMatrix` linear index x+5y == FIPS lane index x+5y, so
/// lane i = bytes[i*8 .. i*8+8] LE.
///
/// Panics if `msg.len() > rate_bytes - 1` (not a single block).
pub fn padded_state_var(variant: Sha3Variant, msg: &[u8]) -> StateMatrix<u64> {
	let rate = variant.rate_bytes();
	assert!(
		msg.len() <= rate - 1,
		"{} single-block only: mlen={} exceeds {} bytes",
		variant.name(),
		msg.len(),
		rate - 1
	);

	let mut bytes = [0u8; STATE_BYTES];
	bytes[..msg.len()].copy_from_slice(msg);
	bytes[msg.len()] ^= 0x06;
	bytes[rate - 1] ^= 0x80;

	let lanes: [u64; 25] = std::array::from_fn(|i| {
		u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap())
	});
	StateMatrix::from_values(lanes)
}

/// Squeeze the variant's digest from a Keccak-f output state: the first
/// `digest_lanes` output lanes serialized little-endian (`digest_bytes` bytes).
pub fn digest_var(variant: Sha3Variant, state: &StateMatrix<u64>) -> Vec<u8> {
	let lanes = state.as_inner();
	let mut digest = Vec::with_capacity(variant.digest_bytes());
	for lane in lanes.iter().take(variant.digest_lanes()) {
		digest.extend_from_slice(&lane.to_le_bytes());
	}
	digest
}

// ============================================================================
// Part 1: correctness (M2a-style, no in-circuit padding binding).
// ============================================================================

/// One-table constraint system holding a batch of single-block hashes for a
/// fixed variant. Each row is the FIPS-202-padded initial state of one message;
/// the wrapped `Keccakf` gadget constrains the permutation. Mirror of M2a's
/// `Sha3SingleBlockTable`, generalised over the variant (the variant only
/// affects witness generation + digest squeezing, not the permutation circuit).
pub struct Sha3VariantTable {
	pub table_id: TableId,
	pub keccakf: Keccakf,
	pub variant: Sha3Variant,
}

impl Sha3VariantTable {
	pub fn new(cs: &mut ConstraintSystem, variant: Sha3Variant) -> Self {
		let mut table = cs.add_table(format!("{} single block", variant.name()));
		let state_in =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = keccak::Keccakf::new(&mut table, state_in);
		Self {
			table_id: table.id(),
			keccakf,
			variant,
		}
	}
}

/// Prove + verify single-block `variant` hashing for each message, under a
/// SHA-256 (FIPS 180-4) Merkle commitment + SHA-256 Fiat–Shamir transcript.
/// Returns `(proof_size_bytes, in_circuit_digests)`; each digest is squeezed
/// from the witness output state (see the SOUNDNESS BOUNDARY note) and is
/// `digest_bytes` long.
pub fn prove_verify_sha3(
	variant: Sha3Variant,
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<Vec<u8>>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3VariantTable::new(&mut cs, variant);

	let n = messages.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let events: Vec<StateMatrix<u64>> =
		messages.iter().map(|m| padded_state_var(variant, m)).collect();

	// Populate through the gadget directly so we can read the output states back
	// (digest) before the witness is consumed by the prover (M2a path).
	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	table.keccakf.populate_state_in(&mut segment, &events)?;
	table.keccakf.populate(&mut segment)?;
	let digests: Vec<Vec<u8>> = table
		.keccakf
		.read_state_outs(&segment)?
		.map(|state| digest_var(variant, &state))
		.collect();
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

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

// ============================================================================
// Part 2: sound single-block padding binding (M2b-1-style), fixed mlen = 64.
//
// mlen = 64 is a 2x32-byte Merkle node — a valid single block for ALL three
// variants (64 <= 71 <= 103 <= 135 = the three rate_bytes-1 limits). The 64
// message bytes occupy lanes 0..=7 exactly; the SHA-3 domain byte 0x06 lands at
// byte 64 = lane 8, byte 0; and the closing bit 0x80 lands at the variant's
// close_lane, byte 7. For SHA3-512 the domain lane (8) IS the close lane, so
// that lane carries both 0x06 (byte 0) and 0x80 (byte 7) => 0x8000_0000_0000_0006.
// ============================================================================

/// Fixed message length for the binding: a 64-byte (two 32-byte hashes) node.
pub const BINDING_MLEN: usize = 64;

const MASK_FULL: u64 = u64::MAX;
const CLOSE_BIT_LANE: u64 = 0x8000_0000_0000_0000; // 0x80 at byte 7 of a lane.
const DOMAIN_BYTE_LANE: u64 = 0x0000_0000_0000_0006; // 0x06 at byte 0 of a lane.

/// Build a `[B1; 512]` constant whose track 0 (bits 0..64) carries `track0` and
/// whose interior tracks (bits 64..512) are all zero — the same track-isolation
/// trick M2b-1 uses so only the permutation INPUT (track 0) is constrained.
fn track0_pattern(track0: u64) -> [B1; LANE_BITS] {
	std::array::from_fn(|pos| {
		if pos < 64 {
			B1::from(((track0 >> pos) & 1) as u8)
		} else {
			B1::from(0u8)
		}
	})
}

/// LE u64 value of the 8 message bytes in lane `i` (i in 0..8).
fn msg_lane_val(msg: &[u8], i: usize) -> u64 {
	u64::from_le_bytes(msg[i * 8..i * 8 + 8].try_into().unwrap())
}

/// The combined domain-lane (lane 8) target: 0x06 at byte 0, plus 0x80 at byte 7
/// iff the variant's close bit shares lane 8 (SHA3-512).
fn domain_lane_target(variant: Sha3Variant) -> u64 {
	if variant.close_lane() == 8 {
		DOMAIN_BYTE_LANE | CLOSE_BIT_LANE
	} else {
		DOMAIN_BYTE_LANE
	}
}

/// A single-table constraint system that proves a batch of single-block hashes
/// for `variant` AND binds each `state_in` to the FIPS-202 padding of a
/// committed 64-byte message (mlen = 64). Generalises M2b-1's `Sha3BindingTable`
/// over the variant's rate boundary.
pub struct Sha3VariantBindingTable {
	pub table_id: TableId,
	pub keccakf: Keccakf,
	pub variant: Sha3Variant,
	// Committed message columns (one per message lane 0..=7).
	msg_cols: [Col<B1, LANE_BITS>; 8],
	// Transparent constant columns (track-0 targets / masks).
	mask_full: Col<B1, LANE_BITS>,
	target_domain: Col<B1, LANE_BITS>,
	// Present only when the close bit is on its own lane (SHA3-256 / SHA3-384).
	target_close: Option<Col<B1, LANE_BITS>>,
}

impl Sha3VariantBindingTable {
	pub fn new(cs: &mut ConstraintSystem, variant: Sha3Variant) -> Self {
		let mut table =
			cs.add_table(format!("{} sound single block (mlen=64)", variant.name()));

		let state_in =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = keccak::Keccakf::new(&mut table, state_in.clone());

		// Committed message columns (message-column binding targets).
		let msg_cols: [Col<B1, LANE_BITS>; 8] =
			std::array::from_fn(|i| table.add_committed(format!("msg_lane{i}")));

		// Transparent constants.
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_domain =
			table.add_constant("target_domain", track0_pattern(domain_lane_target(variant)));

		let close = variant.close_lane();
		let cap_start = variant.capacity_lane_start();
		let target_close = if close != 8 {
			Some(table.add_constant("target_close", track0_pattern(CLOSE_BIT_LANE)))
		} else {
			None
		};

		// ---- The binding zero-constraints (track-0 only, via mask_full) ----
		let s = state_in.as_inner();

		// lanes 0..=7: the 64 message bytes bound to committed `msg_cols`.
		for i in 0..8 {
			table.assert_zero(format!("bind_msg_lane{i}"), (s[i] - msg_cols[i]) * mask_full);
		}

		// lane 8: SHA-3 domain byte 0x06 (byte 0). For SHA3-512 this same lane is
		// the close lane, so its target additionally carries 0x80 at byte 7.
		table.assert_zero("bind_domain_lane8", (s[8] - target_domain) * mask_full);

		if let Some(target_close) = target_close {
			// Zero-fill rate lanes strictly between the domain lane and the close
			// lane (message region past the pad start, up to the closing bit).
			for i in 9..close {
				table.assert_zero(format!("bind_zero_lane{i}"), s[i] * mask_full);
			}
			// close lane: pad10*1 closing bit 0x80 at byte 7.
			table.assert_zero("bind_close_lane", (s[close] - target_close) * mask_full);
		}

		// capacity lanes cap_start..=24: the capacity — all zero.
		for i in cap_start..=24 {
			table.assert_zero(format!("bind_cap_zero_lane{i}"), s[i] * mask_full);
		}

		Self {
			table_id: table.id(),
			keccakf,
			variant,
			msg_cols,
			mask_full,
			target_domain,
			target_close,
		}
	}

	/// Fill the transparent constants and the committed message columns.
	fn populate_binding(
		&self,
		seg: &mut binius_m3::builder::TableWitnessSegment<P>,
		messages: &[Vec<u8>],
	) -> Result<()> {
		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.target_domain, domain_lane_target(self.variant))?;
		if let Some(target_close) = self.target_close {
			fill_track0_const(seg, target_close, CLOSE_BIT_LANE)?;
		}

		// One committed column per message lane; track 0 = message bytes, others 0.
		for (i, col) in self.msg_cols.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(*col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let val = messages
					.get(k)
					.map(|m| {
						assert_eq!(m.len(), BINDING_MLEN, "binding is fixed to mlen=64");
						msg_lane_val(m, i)
					})
					.unwrap_or(0);
				chunk.copy_from_slice(&[val, 0, 0, 0, 0, 0, 0, 0]);
			}
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

/// How a witness `state_in` was tampered, for the adversarial soundness gate.
#[derive(Clone, Copy, Debug)]
pub enum Corruption {
	/// Zero the SHA-3 domain separator byte (byte 64, lane 8, byte 0): 0x06 -> 0x00.
	/// The (in, out) pair stays a valid Keccak-f permutation, so ONLY the padding
	/// binding can reject it.
	DomainByte,
	/// Set the variant's first capacity byte nonzero — a non-sponge input.
	CapacityLane,
}

/// Build the track-0 `state_in` matrix for a 64-byte message under `variant`,
/// optionally corrupted. Corrupted paths produce a VALID Keccak-f input (so
/// `populate` succeeds and the permutation constraints hold) that violates only
/// the padding structure.
fn state_in_for(variant: Sha3Variant, msg: &[u8], corrupt: Option<Corruption>) -> StateMatrix<u64> {
	assert_eq!(msg.len(), BINDING_MLEN, "binding is fixed to mlen=64");
	let rate = variant.rate_bytes();
	let mut bytes = [0u8; STATE_BYTES];
	bytes[..BINDING_MLEN].copy_from_slice(msg);
	bytes[BINDING_MLEN] ^= 0x06; // byte 64: domain separator.
	bytes[rate - 1] ^= 0x80; // variant closing bit.

	match corrupt {
		None => {}
		Some(Corruption::DomainByte) => {
			// Remove the 0x06 domain separator — the load-bearing padding byte.
			bytes[BINDING_MLEN] = 0x00;
		}
		Some(Corruption::CapacityLane) => {
			// First capacity byte (must be zero on absorb).
			bytes[variant.capacity_lane_start() * 8] = 0x01;
		}
	}

	let lanes: [u64; 25] =
		std::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()));
	StateMatrix::from_values(lanes)
}

/// Honest end-to-end: prove + verify the sound single-block binding for each
/// 64-byte message under `variant`, with a SHA-256 commitment + transcript.
/// Returns `(proof_size_bytes, in_circuit_digests)`. Internally asserts
/// (`validate_witness`) that the honest witness satisfies every binding
/// constraint before proving.
pub fn prove_verify_bound_sha3(
	variant: Sha3Variant,
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<Vec<u8>>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3VariantBindingTable::new(&mut cs, variant);

	let n = messages.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let events: Vec<StateMatrix<u64>> =
		messages.iter().map(|m| state_in_for(variant, m, None)).collect();

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	table.keccakf.populate_state_in(&mut segment, &events)?;
	table.keccakf.populate(&mut segment)?;
	table.populate_binding(&mut segment, messages)?;
	let digests: Vec<Vec<u8>> = table
		.keccakf
		.read_state_outs(&segment)?
		.map(|state| digest_var(variant, &state))
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
	pub validate_rejected: bool,
	pub validate_error: String,
	pub pipeline_rejected: bool,
	pub pipeline_stage: &'static str,
	pub pipeline_error: String,
}

/// Adversarial soundness gate: build a single-message witness whose track-0
/// `state_in` is corrupted (bad padding) but is still a valid Keccak-f (in, out)
/// permutation pair, then check the binding constraint REJECTS it — first
/// deterministically via `validate_witness`, then end-to-end via the real
/// SHA-256 prove/verify pipeline. `msg_cols` are populated with the HONEST
/// message bytes, so the rejection is isolated to the padding-constant
/// constraint (not the message binding).
pub fn bad_witness_rejected(
	variant: Sha3Variant,
	corrupt: Corruption,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<RejectReport> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3VariantBindingTable::new(&mut cs, variant);

	// Deterministic 64-byte message (two 32-byte "hashes").
	let msg: Vec<u8> = (0..BINDING_MLEN as u8).collect();
	let messages = vec![msg.clone()];
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![1],
	};

	let events = vec![state_in_for(variant, &msg, Some(corrupt))];

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, 1)?;
	let mut segment = table_witness.full_segment();
	// `populate` must succeed on the corrupt-but-valid permutation input, so any
	// rejection comes from OUR binding constraint, not a populate panic.
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

	// 2) End-to-end SHA-256 pipeline: prove then verify.
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
	use sha3::{Digest, Sha3_384, Sha3_512};

	// ---- Published NIST FIPS-202 known-answer vectors (hex, from the task). ----
	const KAT_384_EMPTY: &str = "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004";
	const KAT_384_ABC: &str = "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b298d88cea927ac7f539f1edf228376d25";
	const KAT_512_EMPTY: &str = "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26";
	const KAT_512_ABC: &str = "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0";

	fn hex(s: &str) -> Vec<u8> {
		(0..s.len())
			.step_by(2)
			.map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
			.collect()
	}

	fn native_384(msg: &[u8]) -> Vec<u8> {
		let mut h = Sha3_384::new();
		h.update(msg);
		h.finalize().to_vec()
	}
	fn native_512(msg: &[u8]) -> Vec<u8> {
		let mut h = Sha3_512::new();
		h.update(msg);
		h.finalize().to_vec()
	}

	/// Sanity: confirm the enum's derived rate/lane constants for 384 and 512.
	#[test]
	fn variant_constants_are_correct() {
		let v384 = Sha3Variant::Sha3_384;
		assert_eq!(v384.rate_bytes(), 104);
		assert_eq!(v384.close_lane(), 12);
		assert_eq!(v384.capacity_lane_start(), 13);
		assert_eq!(v384.digest_lanes(), 6);
		assert_eq!(v384.digest_bytes(), 48);

		let v512 = Sha3Variant::Sha3_512;
		assert_eq!(v512.rate_bytes(), 72);
		assert_eq!(v512.close_lane(), 8);
		assert_eq!(v512.capacity_lane_start(), 9);
		assert_eq!(v512.digest_lanes(), 8);
		assert_eq!(v512.digest_bytes(), 64);

		// And 256 stays as M2a defined it.
		let v256 = Sha3Variant::Sha3_256;
		assert_eq!(v256.rate_bytes(), 136);
		assert_eq!(v256.close_lane(), 16);
		assert_eq!(v256.capacity_lane_start(), 17);
		assert_eq!(v256.digest_lanes(), 4);
	}

	/// The hardcoded KATs must agree with the authoritative `sha3` crate. If a
	/// KAT is wrong we would rather fail HERE (and drop it) than trust it.
	#[test]
	fn hardcoded_kats_agree_with_sha3_crate() {
		assert_eq!(native_384(b""), hex(KAT_384_EMPTY), "SHA3-384(\"\") KAT vs sha3 crate");
		assert_eq!(native_384(b"abc"), hex(KAT_384_ABC), "SHA3-384(\"abc\") KAT vs sha3 crate");
		assert_eq!(native_512(b""), hex(KAT_512_EMPTY), "SHA3-512(\"\") KAT vs sha3 crate");
		assert_eq!(native_512(b"abc"), hex(KAT_512_ABC), "SHA3-512(\"abc\") KAT vs sha3 crate");
	}

	/// In-circuit SHA3-384 of "" and "abc" equals the native crate AND the KATs.
	#[test]
	fn sha3_384_in_circuit_matches_native() {
		let v = Sha3Variant::Sha3_384;
		let messages = vec![b"".to_vec(), b"abc".to_vec()];
		let (proof_size, digests) =
			prove_verify_sha3(v, &messages, 1, 100).expect("in-circuit SHA3-384 must verify");

		assert_eq!(digests.len(), 2);
		assert_eq!(digests[0], native_384(b""), "in-circuit SHA3-384(\"\") != sha3 crate");
		assert_eq!(digests[1], native_384(b"abc"), "in-circuit SHA3-384(\"abc\") != sha3 crate");
		assert_eq!(digests[0], hex(KAT_384_EMPTY), "in-circuit SHA3-384(\"\") != NIST KAT");
		assert_eq!(digests[1], hex(KAT_384_ABC), "in-circuit SHA3-384(\"abc\") != NIST KAT");
		assert!(proof_size > 0);
		println!("M2c in-circuit SHA3-384 verified for \"\" and \"abc\"; proof size = {proof_size} bytes");
	}

	/// In-circuit SHA3-512 of "" and "abc" equals the native crate AND the KATs.
	#[test]
	fn sha3_512_in_circuit_matches_native() {
		let v = Sha3Variant::Sha3_512;
		let messages = vec![b"".to_vec(), b"abc".to_vec()];
		let (proof_size, digests) =
			prove_verify_sha3(v, &messages, 1, 100).expect("in-circuit SHA3-512 must verify");

		assert_eq!(digests.len(), 2);
		assert_eq!(digests[0], native_512(b""), "in-circuit SHA3-512(\"\") != sha3 crate");
		assert_eq!(digests[1], native_512(b"abc"), "in-circuit SHA3-512(\"abc\") != sha3 crate");
		assert_eq!(digests[0], hex(KAT_512_EMPTY), "in-circuit SHA3-512(\"\") != NIST KAT");
		assert_eq!(digests[1], hex(KAT_512_ABC), "in-circuit SHA3-512(\"abc\") != NIST KAT");
		assert!(proof_size > 0);
		println!("M2c in-circuit SHA3-512 verified for \"\" and \"abc\"; proof size = {proof_size} bytes");
	}

	/// Honest 64-byte binding for SHA3-384 proves + verifies; in-circuit digest
	/// equals the native `sha3` of the 64-byte message.
	#[test]
	fn sha3_384_honest_binding_accepts() {
		let v = Sha3Variant::Sha3_384;
		let msg: Vec<u8> = (0..BINDING_MLEN as u8).collect();
		let messages = vec![msg.clone()];
		let (proof_size, digests) =
			prove_verify_bound_sha3(v, &messages, 1, 100).expect("honest SHA3-384 binding must verify");

		assert_eq!(digests.len(), 1);
		assert_eq!(digests[0], native_384(&msg), "in-circuit bound SHA3-384 != sha3 crate");
		assert!(proof_size > 0);
		println!("M2c sound SHA3-384 (mlen=64) verified; proof size = {proof_size} bytes");
	}

	/// Honest 64-byte binding for SHA3-512 proves + verifies; in-circuit digest
	/// equals the native `sha3` of the 64-byte message.
	#[test]
	fn sha3_512_honest_binding_accepts() {
		let v = Sha3Variant::Sha3_512;
		let msg: Vec<u8> = (0..BINDING_MLEN as u8).collect();
		let messages = vec![msg.clone()];
		let (proof_size, digests) =
			prove_verify_bound_sha3(v, &messages, 1, 100).expect("honest SHA3-512 binding must verify");

		assert_eq!(digests.len(), 1);
		assert_eq!(digests[0], native_512(&msg), "in-circuit bound SHA3-512 != sha3 crate");
		assert!(proof_size > 0);
		println!("M2c sound SHA3-512 (mlen=64) verified; proof size = {proof_size} bytes");
	}

	/// Adversarial: a SHA3-384 witness with the domain byte 0x06 zeroed — but an
	/// otherwise-valid Keccak-f (in, out) pair — MUST be rejected by BOTH
	/// validate_witness and the SHA-256 verify, isolated to the padding binding.
	#[test]
	fn sha3_384_bad_padding_rejected() {
		let report = bad_witness_rejected(Sha3Variant::Sha3_384, Corruption::DomainByte, 1, 100)
			.expect("adversarial harness must run to completion");
		assert!(report.validate_rejected, "SOUNDNESS FAILURE: validate accepted bad SHA3-384 padding");
		assert!(report.pipeline_rejected, "SOUNDNESS FAILURE: SHA-256 pipeline accepted bad SHA3-384 padding");
		println!(
			"M2c SHA3-384 bad-padding (domain 0x06->0x00) REJECTED:\n  constraint: bind_domain_lane8\n  validate_witness: {}\n  pipeline stage  : {}\n  pipeline error  : {}",
			report.validate_error, report.pipeline_stage, report.pipeline_error
		);
	}

	/// Adversarial: same for SHA3-512.
	#[test]
	fn sha3_512_bad_padding_rejected() {
		let report = bad_witness_rejected(Sha3Variant::Sha3_512, Corruption::DomainByte, 1, 100)
			.expect("adversarial harness must run to completion");
		assert!(report.validate_rejected, "SOUNDNESS FAILURE: validate accepted bad SHA3-512 padding");
		assert!(report.pipeline_rejected, "SOUNDNESS FAILURE: SHA-256 pipeline accepted bad SHA3-512 padding");
		println!(
			"M2c SHA3-512 bad-padding (domain 0x06->0x00) REJECTED:\n  constraint: bind_domain_lane8\n  validate_witness: {}\n  pipeline stage  : {}\n  pipeline error  : {}",
			report.validate_error, report.pipeline_stage, report.pipeline_error
		);
	}

	/// Adversarial (capacity variant): a nonzero first capacity lane must also be
	/// rejected, for both variants — exercises the `bind_cap_zero_lane*` binding.
	#[test]
	fn variant_bad_capacity_rejected() {
		for v in [Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
			let report = bad_witness_rejected(v, Corruption::CapacityLane, 1, 100)
				.expect("adversarial harness must run to completion");
			assert!(report.validate_rejected, "SOUNDNESS FAILURE: validate accepted nonzero capacity for {}", v.name());
			assert!(report.pipeline_rejected, "SOUNDNESS FAILURE: pipeline accepted nonzero capacity for {}", v.name());
			println!(
				"M2c {} bad-capacity (lane{} != 0) REJECTED: validate={}, stage={}",
				v.name(), v.capacity_lane_start(), report.validate_error, report.pipeline_stage
			);
		}
	}
}
