// binius-substrate — M2b-2 "SOUND in-circuit binding seam between two SHA3-256
// hashes" (the Merkle-root-of-inner-roots / recursion-binding primitive).
//
// M2b-1 pinned a single hash's `state_in` to the FIPS-202 padding of a committed
// message. M2b-2 chains TWO such hashes in one circuit and proves, IN-CIRCUIT,
// that the second hash consumes the first hash's REAL digest — i.e. the g1 -> g2
// link cannot be forged. This is the depth-2 core of the whole recursion design:
// if a broken seam is not rejected, the recursion is unsound.
//
// ============================ TOPOLOGY ======================================
// One table, TWO `Keccakf` gadgets (`g1`, `g2`) in that table under separate
// namespaces. A single table ROW therefore computes a 2-hash chain:
//
//     A, B, C are 32-byte children.
//     g1 = SHA3-256( A ‖ B )              (64-byte, single-block, mlen=64)
//     g2 = SHA3-256( g1_digest ‖ C )      (64-byte, single-block, mlen=64)
//     root = g2_digest                    (the depth-2 chain root)
//
// Each gadget owns an independent committed `state_in` / `state_out` column set,
// so the two permutations are linked only by the explicit seam constraint below.
//
// ============================ THE track-0 / track-7 SUBTLETY =================
// The m3 `Keccakf` gadget packs 8 SIMD "tracks" per lane column
// (`PackedLane8 = Col<B1,512>`). The permutation INPUT lives on track 0 of
// `packed_state_in()` (bits 0..64); the permutation OUTPUT (the digest lanes)
// lives on track 7 of `packed_state_out()` (bits 448..512) — see the gadget's
// `STATE_IN_TRACK = 0` / `STATE_OUT_TRACK = 7`.
//
// So g1's digest and g2's input sit on DIFFERENT bit positions and cannot be
// compared by a single element-wise `assert_zero`. We realign g1's output track
// 7 down to track 0 with a `LogicalRight`-by-448 shifted column (exactly the
// mechanism the gadget itself uses for its `next_state_in` state-forwarding
// link), then compare on track 0.
//
// ============================ THE SEAM (the deliverable) ====================
// For each digest lane i in 0..4 we add the committed shifted column
//
//     g1_out_lo[i] = LogicalRight_448( g1.state_out[i] )   // track7 -> track0
//
// and the zero-constraint (track-0 mask, same trick as M2b-1)
//
//     (g1_out_lo[i] - g2.state_in[i]) * mask_full == 0      // i in 0..4
//
// g1_out_lo[i] on track 0 is exactly g1's real i-th digest lane; g2.state_in[i]
// on track 0 is g2's i-th input lane. The constraint forces them equal, so g2
// provably hashes g1's genuine output. Break the link (feed g2 any other
// 32-byte prefix) and this constraint — and only this constraint — rejects.
//
// The g2.state_in lanes 0..3 are otherwise UNCONSTRAINED by the padding binding
// (they are message bytes); the seam is their sole binding. Removing the seam
// would leave the chain forgeable — which is precisely what the adversarial test
// exercises.
//
// ============================ SOUNDNESS BOUNDARY ============================
//  * IN-CIRCUIT & SOUND: both permutations; both FIPS-202 mlen=64 paddings; the
//    message binding of A,B (g1) and C (g2, second 32 bytes) to committed
//    columns; and the g1->g2 digest seam.
//  * NOT a public boundary (this milestone): the final root (g2 digest) is read
//    witness-side and cross-checked against the native `sha3` crate, and left as
//    a committed/derived column. Exposing it as a `Boundary` for an outer
//    verifier is deferred to M2b-3 (see the report). We do NOT overclaim.
// ============================================================================

use anyhow::Result;
use binius_core::oracle::ShiftVariant;
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

/// Concrete packed field used throughout (same as M1/M2a/M2b-1).
type P = PackedType<OptimalUnderlier, B128>;

const LANE_BITS: usize = 512; // PackedLane8 = 8 tracks * 64 bits.
const LOG_LANE_BITS: usize = 9; // log2(512)
const OUT_TRACK_SHIFT: usize = 7 * 64; // track 7 -> track 0 (LogicalRight by 448)

// Track-0 constant patterns (interior tracks 1..7 are always 0, so round states
// are never constrained).
const MASK_FULL: u64 = u64::MAX;
const TARGET_LANE8: u64 = 0x0000_0000_0000_0006; // byte 64 (lane 8, byte 0) = 0x06 domain sep
const TARGET_LANE16: u64 = 0x8000_0000_0000_0000; // byte 135 (lane 16, byte 7) = 0x80 pad10*1 close

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

/// Build the FIPS-202-padded single-block state for a 64-byte message
/// `first32 ‖ second32` (SHA3-256, rate 136). `corrupt` optionally mangles the
/// padding for the adversarial padding gate; it never touches the message bytes.
fn padded_state_64(
	first32: &[u8; 32],
	second32: &[u8; 32],
	corrupt: Option<PadCorruption>,
) -> StateMatrix<u64> {
	let mut bytes = [0u8; 200];
	bytes[..32].copy_from_slice(first32);
	bytes[32..64].copy_from_slice(second32);
	// pad10*1 with the SHA-3 domain separator. mlen = 64 < 135, single block.
	bytes[64] ^= 0x06; // lane 8, byte 0
	bytes[135] ^= 0x80; // lane 16, byte 7

	match corrupt {
		None => {}
		Some(PadCorruption::DomainByte) => bytes[64] = 0x00, // drop the 0x06 domain sep
		Some(PadCorruption::CapacityLane) => bytes[136] = 0x01, // lane 17 must be zero
	}

	let lanes: [u64; 25] =
		std::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()));
	StateMatrix::from_values(lanes)
}

/// Padding corruptions for the (optional) two-gadget padding gate.
#[derive(Clone, Copy, Debug)]
pub enum PadCorruption {
	/// Zero the SHA-3 domain separator byte (lane 8, byte 0): 0x06 -> 0x00.
	DomainByte,
	/// Set a capacity lane (lane 17) nonzero — a non-sponge input.
	CapacityLane,
}

/// The two children hashed by g2's prefix can be forged; this selects whether g2
/// receives g1's real digest or an attacker-chosen 32-byte prefix.
#[derive(Clone, Copy, Debug)]
enum SeamMode {
	/// Honest: g2 input = g1_digest ‖ C.
	Honest,
	/// Forged: g2 input = `forged` ‖ C, with `forged` != g1_digest, but g2 is
	/// still a valid Keccak-f (in, out) pair with valid padding. Only the seam
	/// can reject.
	ForgedPrefix { forged: [u8; 32] },
	/// Honest link, but g1 or g2 padding is corrupted (padding gate).
	BadPadding { on_g2: bool, kind: PadCorruption },
}

/// One-table, two-gadget constraint system proving a depth-2 SHA3-256 chain with
/// an in-circuit binding seam.
pub struct SeamTable {
	pub table_id: TableId,
	g1: Keccakf,
	g2: Keccakf,
	// Seam: g1 output track-7 realigned to track-0 (LogicalRight by 448).
	g1_out_lo: [Col<B1, LANE_BITS>; 4],
	// Committed message columns.
	msg_g1: [Col<B1, LANE_BITS>; 8], // A ‖ B
	msg_c: [Col<B1, LANE_BITS>; 4],  // C (g2's second 32 bytes)
	// Transparent constants.
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
}

impl SeamTable {
	pub fn new(cs: &mut ConstraintSystem) -> Self {
		let mut table = cs.add_table("SHA3-256 depth-2 binding seam (M2b-2)");

		// ---- g1 gadget (namespace "g1") ----
		let g1_state_in: StateMatrix<Col<B1, LANE_BITS>>;
		let g1;
		{
			let mut t = table.with_namespace("g1");
			g1_state_in = StateMatrix::from_fn(|(x, y)| t.add_committed(format!("in[{x},{y}]")));
			g1 = keccak::Keccakf::new(&mut t, g1_state_in.clone());
		}

		// ---- g2 gadget (namespace "g2") ----
		let g2_state_in: StateMatrix<Col<B1, LANE_BITS>>;
		let g2;
		{
			let mut t = table.with_namespace("g2");
			g2_state_in = StateMatrix::from_fn(|(x, y)| t.add_committed(format!("in[{x},{y}]")));
			g2 = keccak::Keccakf::new(&mut t, g2_state_in.clone());
		}

		// ---- Seam realignment columns: g1 output track7 -> track0 ----
		let g1_out = g1.packed_state_out();
		let g1_out_inner = g1_out.as_inner();
		let g1_out_lo: [Col<B1, LANE_BITS>; 4] = std::array::from_fn(|i| {
			table.add_shifted(
				format!("g1_out_lo[{i}]"),
				g1_out_inner[i],
				LOG_LANE_BITS,
				OUT_TRACK_SHIFT,
				ShiftVariant::LogicalRight,
			)
		});

		// ---- Committed message + transparent constant columns ----
		let msg_g1: [Col<B1, LANE_BITS>; 8] =
			std::array::from_fn(|i| table.add_committed(format!("msg_g1[{i}]")));
		let msg_c: [Col<B1, LANE_BITS>; 4] =
			std::array::from_fn(|j| table.add_committed(format!("msg_c[{j}]")));
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_lane8 = table.add_constant("target_lane8", track0_pattern(TARGET_LANE8));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		let s1 = g1_state_in.as_inner();
		let s2 = g2_state_in.as_inner();

		// ---- g1 padding + message binding (mlen = 64) ----
		// lanes 0..7: full message A ‖ B, bound to committed msg_g1.
		for i in 0..8 {
			table.assert_zero(format!("g1_bind_msg_lane{i}"), (s1[i] - msg_g1[i]) * mask_full);
		}
		// lane 8: domain separator 0x06 (+ zero fill on bytes 1..7).
		table.assert_zero("g1_pad_lane8", (s1[8] - target_lane8) * mask_full);
		// lanes 9..15: message region past pad start — all zero.
		for i in 9..=15 {
			table.assert_zero(format!("g1_pad_zero_lane{i}"), s1[i] * mask_full);
		}
		// lane 16 (byte 135): pad10*1 closing bit 0x80.
		table.assert_zero("g1_pad_lane16", (s1[16] - target_lane16) * mask_full);
		// lanes 17..24: the 512-bit capacity — all zero.
		for i in 17..=24 {
			table.assert_zero(format!("g1_cap_zero_lane{i}"), s1[i] * mask_full);
		}

		// ---- g2 padding + message binding (mlen = 64) ----
		// lanes 0..3: g2's FIRST 32 bytes are bound ONLY by the seam below.
		// lanes 4..7: g2's SECOND 32 bytes = C, bound to committed msg_c.
		for j in 0..4 {
			table.assert_zero(
				format!("g2_bind_c_lane{}", 4 + j),
				(s2[4 + j] - msg_c[j]) * mask_full,
			);
		}
		table.assert_zero("g2_pad_lane8", (s2[8] - target_lane8) * mask_full);
		for i in 9..=15 {
			table.assert_zero(format!("g2_pad_zero_lane{i}"), s2[i] * mask_full);
		}
		table.assert_zero("g2_pad_lane16", (s2[16] - target_lane16) * mask_full);
		for i in 17..=24 {
			table.assert_zero(format!("g2_cap_zero_lane{i}"), s2[i] * mask_full);
		}

		// ---- THE SEAM: g2 input lanes 0..3 == g1 digest lanes 0..3 ----
		for i in 0..4 {
			table.assert_zero(
				format!("seam_g1_to_g2_lane{i}"),
				(g1_out_lo[i] - s2[i]) * mask_full,
			);
		}

		Self {
			table_id: table.id(),
			g1,
			g2,
			g1_out_lo,
			msg_g1,
			msg_c,
			mask_full,
			target_lane8,
			target_lane16,
		}
	}

	/// Populate one full-table witness for a batch of chains. Returns the g1 and
	/// g2 (root) digests read witness-side, per row.
	fn populate(
		&self,
		seg: &mut binius_m3::builder::TableWitnessSegment<P>,
		children: &[(([u8; 32], [u8; 32]), [u8; 32])],
		mode: SeamMode,
	) -> Result<(Vec<[u8; 32]>, Vec<[u8; 32]>)> {
		// 1) g1 = SHA3-256(A ‖ B).
		let g1_states: Vec<StateMatrix<u64>> = children
			.iter()
			.map(|((a, b), _)| {
				let g1_bad = matches!(mode, SeamMode::BadPadding { on_g2: false, .. });
				let kind = if let SeamMode::BadPadding { kind, .. } = mode {
					Some(kind)
				} else {
					None
				};
				padded_state_64(a, b, if g1_bad { kind } else { None })
			})
			.collect();
		self.g1.populate_state_in(seg, &g1_states)?;
		self.g1.populate(seg)?;

		// Read g1 output states (track 7) — owned, so the borrow ends here.
		let g1_out_states: Vec<StateMatrix<u64>> = self.g1.read_state_outs(seg)?.collect();
		let g1_digests: Vec<[u8; 32]> =
			g1_out_states.iter().map(digest_from_state).collect();

		// 2) g2 = SHA3-256(prefix ‖ C). `prefix` is g1's digest (honest) or a
		//    forged 32-byte value; either way g2 is a valid Keccak-f pair.
		let g2_states: Vec<StateMatrix<u64>> = children
			.iter()
			.enumerate()
			.map(|(k, (_, c))| {
				let prefix = match mode {
					SeamMode::ForgedPrefix { forged } => forged,
					_ => g1_digests[k],
				};
				let g2_bad = matches!(mode, SeamMode::BadPadding { on_g2: true, .. });
				let kind = if let SeamMode::BadPadding { kind, .. } = mode {
					Some(kind)
				} else {
					None
				};
				padded_state_64(&prefix, c, if g2_bad { kind } else { None })
			})
			.collect();
		self.g2.populate_state_in(seg, &g2_states)?;
		self.g2.populate(seg)?;
		let g2_digests: Vec<[u8; 32]> = self
			.g2
			.read_state_outs(seg)?
			.map(|s| digest_from_state(&s))
			.collect();

		// 3) Seam realignment columns: g1_out_lo[i] track0 = g1 digest lane i,
		//    interior tracks 0 — exactly LogicalRight_448(g1.state_out[i]).
		for (i, &col) in self.g1_out_lo.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let lane = g1_out_states[k].as_inner()[i];
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}

		// 4) Message columns: msg_g1 = g1 lanes 0..7 (= A ‖ B), msg_c = g2 lanes
		//    4..7 (= C). Taken from the honest built states so the message binding
		//    always holds; the ONLY broken relation in the forged case is the seam.
		for (i, &col) in self.msg_g1.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let lane = g1_states[k].as_inner()[i];
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}
		for (j, &col) in self.msg_c.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				// C is the honest second-32-bytes; use it directly (independent of
				// the forged prefix) so g2's message binding holds.
				let c = children[k].1;
				let lane = u64::from_le_bytes(c[j * 8..j * 8 + 8].try_into().unwrap());
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}

		// 5) Transparent constants.
		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.target_lane8, TARGET_LANE8)?;
		fill_track0_const(seg, self.target_lane16, TARGET_LANE16)?;

		Ok((g1_digests, g2_digests))
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

/// Honest end-to-end: prove + verify the depth-2 SHA3-256 chain with the binding
/// seam, under the SHA-256 (FIPS 180-4) commitment + transcript. Returns
/// `(proof_size_bytes, g1_digests, roots)`. Asserts the honest witness satisfies
/// every constraint via `validate_witness` before proving.
pub fn prove_verify_seam(
	children: &[(([u8; 32], [u8; 32]), [u8; 32])],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<[u8; 32]>, Vec<[u8; 32]>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = SeamTable::new(&mut cs);

	let n = children.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	let (g1_digests, roots) = table.populate(&mut segment, children, SeamMode::Honest)?;
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)
		.map_err(|e| anyhow::anyhow!("honest seam witness failed validate_witness: {e}"))?;

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

	Ok((proof_size, g1_digests, roots))
}

/// Which stage rejected an adversarial witness, and which constraint fired.
#[derive(Debug)]
pub struct SeamRejectReport {
	pub validate_rejected: bool,
	pub validate_error: String,
	pub pipeline_rejected: bool,
	pub pipeline_stage: &'static str,
	pub pipeline_error: String,
}

/// Adversarial gate. Build a single-chain witness under `mode` (a forged g1->g2
/// link, or a padding corruption) where every gadget's permutation and every
/// other binding holds, then check the offending constraint REJECTS — first
/// deterministically via `validate_witness`, then end-to-end via SHA-256
/// prove/verify.
fn adversarial_reject(
	mode: SeamMode,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<SeamRejectReport> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = SeamTable::new(&mut cs);

	// A single honest chain of children; `mode` decides the injected fault.
	let a = [0x11u8; 32];
	let b = [0x22u8; 32];
	let c = [0x33u8; 32];
	let children = vec![((a, b), c)];
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![1],
	};

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, 1)?;
	let mut segment = table_witness.full_segment();
	// `populate` must SUCCEED (both permutations are valid (in,out) pairs); any
	// rejection therefore comes from a constraint, not a populate panic.
	table.populate(&mut segment, &children, mode)?;
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// 1) Deterministic constraint check.
	let validate = binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness);
	let validate_rejected = validate.is_err();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

	// 2) Full SHA-256 pipeline: prove then verify.
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

	Ok(SeamRejectReport {
		validate_rejected,
		validate_error,
		pipeline_rejected,
		pipeline_stage,
		pipeline_error,
	})
}

/// Public wrapper: forged g1->g2 link (the deliverable).
pub fn forged_link_rejected(
	forged_prefix: [u8; 32],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<SeamRejectReport> {
	adversarial_reject(
		SeamMode::ForgedPrefix {
			forged: forged_prefix,
		},
		log_inv_rate,
		security_bits,
	)
}

/// Public wrapper: padding corruption on g1 or g2 (padding still bites in the
/// two-gadget table).
pub fn bad_padding_rejected(
	on_g2: bool,
	kind: PadCorruption,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<SeamRejectReport> {
	adversarial_reject(SeamMode::BadPadding { on_g2, kind }, log_inv_rate, security_bits)
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

	fn native_chain(a: &[u8; 32], b: &[u8; 32], c: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
		let mut m1 = Vec::with_capacity(64);
		m1.extend_from_slice(a);
		m1.extend_from_slice(b);
		let d1 = native_sha3_256(&m1);
		let mut m2 = Vec::with_capacity(64);
		m2.extend_from_slice(&d1);
		m2.extend_from_slice(c);
		let root = native_sha3_256(&m2);
		(d1, root)
	}

	/// M2b-2 honest gate: the depth-2 chain proves + verifies under SHA-256, and
	/// the in-circuit g1 digest and root match the native `sha3` reference.
	#[test]
	fn seam_honest_accepts() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let c = [0xCCu8; 32];
		let (d1_exp, root_exp) = native_chain(&a, &b, &c);

		let children = vec![((a, b), c)];
		let (proof_size, g1_digests, roots) =
			prove_verify_seam(&children, 1, 100).expect("honest seam proof must verify");

		assert_eq!(g1_digests.len(), 1);
		assert_eq!(roots.len(), 1);
		assert_eq!(g1_digests[0], d1_exp, "in-circuit g1 digest != native SHA3-256(A‖B)");
		assert_eq!(roots[0], root_exp, "in-circuit root != native SHA3-256(g1‖C)");
		assert!(proof_size > 0);
		println!(
			"M2b-2 seam honest: depth-2 chain verified; g1 digest & root match native; proof = {proof_size} bytes"
		);
	}

	/// M2b-2 THE DELIVERABLE: a forged g1->g2 link — g2's first 32 input bytes set
	/// to a value != g1's real digest, but with BOTH g1 and g2 valid Keccak-f
	/// (in,out) pairs AND valid paddings — MUST be rejected, and the rejection
	/// must be isolated to the seam constraint.
	#[test]
	fn seam_forged_link_rejected() {
		// A forged prefix that is (with overwhelming probability) not any real
		// SHA3-256 digest of A‖B — a fixed, obviously-adversarial pattern.
		let forged = [0xDEu8; 32];
		let report =
			forged_link_rejected(forged, 1, 100).expect("adversarial harness must run to completion");

		assert!(
			report.validate_rejected,
			"SOUNDNESS FAILURE: validate_witness ACCEPTED a forged g1->g2 link"
		);
		assert!(
			report.pipeline_rejected,
			"SOUNDNESS FAILURE: SHA-256 prove/verify ACCEPTED a forged g1->g2 link"
		);
		// The violated constraint must be one of the four seam lanes.
		assert!(
			report.validate_error.contains("seam_g1_to_g2_lane"),
			"reject was not isolated to the seam constraint; got: {}",
			report.validate_error
		);
		println!(
			"M2b-2 forged-link REJECTED (isolated to seam):\n  validate_witness: {}\n  pipeline stage : {}\n  pipeline error : {}",
			report.validate_error, report.pipeline_stage, report.pipeline_error
		);
	}

	/// M2b-2 padding gate (best-effort): a domain-byte corruption on g2 in the
	/// two-gadget table is still rejected by g2's padding binding.
	#[test]
	fn seam_bad_padding_rejected() {
		let report = bad_padding_rejected(true, PadCorruption::DomainByte, 1, 100)
			.expect("adversarial harness must run to completion");

		assert!(
			report.validate_rejected,
			"SOUNDNESS FAILURE: validate_witness accepted a bad-padding g2 state_in"
		);
		assert!(
			report.pipeline_rejected,
			"SOUNDNESS FAILURE: SHA-256 prove/verify accepted a bad-padding g2 state_in"
		);
		assert!(
			report.validate_error.contains("g2_pad_lane8"),
			"padding reject not isolated to g2 domain-byte constraint; got: {}",
			report.validate_error
		);
		println!(
			"M2b-2 bad-padding (g2 domain 0x06->0x00) REJECTED:\n  validate_witness: {}\n  pipeline stage : {}",
			report.validate_error, report.pipeline_stage
		);
	}
}
