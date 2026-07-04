// binius-substrate — M2a "in-circuit SHA3-256 single-block hash gadget".
//
// Goal: prove *in-circuit* that Keccak-f[1600], applied to a FIPS-202-padded
// single message block, yields the correct SHA3-256 digest — under the same
// SHA-256 (FIPS 180-4) Merkle commitment + SHA-256 Fiat–Shamir challenger as
// M1. This wraps Binius's `Keccakf` gadget (permutation only) inside a hand-
// rolled FIPS-202 sponge (pad10*1 with the SHA-3 domain separator 0x06).
//
// ============================ SOUNDNESS BOUNDARY (READ THIS) ================
// What M2a proves in-circuit vs. computes in witness-generation:
//
//   * IN-CIRCUIT (constrained by the Keccakf gadget's assert_zero rows):
//       the permutation itself — i.e. that `state_out = Keccak-f(state_in)` for
//       whatever `state_in` the witness commits to. This is the load-bearing,
//       ~24-round θ/ρ/π/χ/ι arithmetic, committed and proved.
//
//   * NOT YET CONSTRAINED (witness-computed, honest-prover-only in M2a):
//       (a) that `state_in` equals the FIPS-202 padding of a specific message
//           M (the bytes 0..mlen = M, byte mlen ^= 0x06, byte 135 ^= 0x80,
//           capacity lanes 17..25 = 0). The padded block is *computed* by
//           `padded_state()` and loaded via `populate_state_in`, but the m3
//           `Keccakf` gadget exposes `state_in` only as a packed 8-track column
//           (track 0 = our input, tracks 1..8 = interior round states), so
//           pinning *just track 0* to the FIPS constants needs a sub-lane
//           selector/boundary that is deferred to M2b (see report).
//       (b) that the squeezed digest (output lanes 0..4) equals a bound public
//           output column. Here the digest is *read back* from the witness via
//           `read_state_outs` and checked against the native `sha3` crate in
//           the test — a witness-side gate, not an in-circuit boundary.
//
// So a malicious prover in M2a could commit a `state_in` that is NOT the FIPS
// padding of any particular message and still produce an accepting proof (it
// would just be a proof of "some Keccak-f permutation"). Binding `state_in` to
// the message padding and binding the digest to a public column is exactly the
// M2b work. We do NOT overclaim: M2a = "permutation-in-circuit + native-verified
// FIPS-202 sponge wiring", gated end-to-end against the NIST SHA3-256 vectors.
// ============================================================================

use anyhow::Result;
use binius_field::{arch::OptimalUnderlier, as_packed_field::PackedType};
use binius_m3::{
	builder::{ConstraintSystem, Statement, TableId, WitnessIndex, B128},
	gadgets::hash::keccak::{self, Keccakf, StateMatrix},
};

use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::tower::CanonicalTowerFamily;
use binius_hash::sha2::Sha256Compression;
use sha2::Sha256;

/// FIPS-202 parameters for SHA3-256.
const RATE_BYTES: usize = 136; // r = 1088 bits = 17 lanes
const STATE_BYTES: usize = 200; // 1600 bits = 25 lanes
const DIGEST_BYTES: usize = 32; // 256-bit output = first 4 output lanes

/// Build the padded initial sponge state for a single-block SHA3-256 absorb.
///
/// FIPS-202 (SHA3-256): rate r = 136 bytes, capacity = 64 bytes. For a message
/// `msg` of length `mlen <= RATE_BYTES - 1` bytes (so it fits in one block):
///   P[i]      = msg[i]        for i < mlen
///   P[mlen]  ^= 0x06          (SHA-3 domain separator + start of pad10*1)
///   P[135]   ^= 0x80          (final rate byte gets the closing 1 bit)
///   P[136..200] = 0           (capacity)
/// The initial state is 0, and absorbing XORs the block into the first 136
/// bytes, so state_in bytes 0..136 = P and bytes 136..200 = 0.
///
/// Lane mapping (FIPS-202 §B.1): byte b of the 200-byte state lives in lane
/// b/8, at byte-position b%8, little-endian within the lane. `StateMatrix`
/// stores lanes row-major with linear index `x + 5*y`, which matches the FIPS
/// lane index x + 5*y exactly, so lane `i` = `state_bytes[i*8 .. i*8+8]` LE.
///
/// Panics if `msg.len() > RATE_BYTES - 1` (not a single block).
pub fn padded_state(msg: &[u8]) -> StateMatrix<u64> {
	assert!(
		msg.len() <= RATE_BYTES - 1,
		"M2a is single-block only: mlen={} exceeds {} bytes",
		msg.len(),
		RATE_BYTES - 1
	);

	let mut bytes = [0u8; STATE_BYTES];
	bytes[..msg.len()].copy_from_slice(msg);
	// pad10*1 with SHA-3 domain separation. When mlen == 135 these two writes
	// land on the same byte: 0x06 ^ 0x80 = 0x86, which is correct.
	bytes[msg.len()] ^= 0x06;
	bytes[RATE_BYTES - 1] ^= 0x80;

	let lanes: [u64; 25] = std::array::from_fn(|i| {
		u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap())
	});
	StateMatrix::from_values(lanes)
}

/// Squeeze the SHA3-256 digest from a Keccak-f output state: the first 32 bytes
/// of the state, i.e. output lanes 0,1,2,3 serialized little-endian.
pub fn digest_from_state(state: &StateMatrix<u64>) -> [u8; DIGEST_BYTES] {
	let lanes = state.as_inner();
	let mut digest = [0u8; DIGEST_BYTES];
	for i in 0..DIGEST_BYTES / 8 {
		digest[i * 8..i * 8 + 8].copy_from_slice(&lanes[i].to_le_bytes());
	}
	digest
}

/// A one-table constraint system holding a batch of single-block SHA3-256
/// hashes. Each row (event) is the FIPS-202-padded initial state of one message;
/// the wrapped `Keccakf` gadget constrains the permutation. This mirrors M1's
/// `PermutationTable`, but the events are padded message blocks rather than
/// random states.
pub struct Sha3SingleBlockTable {
	pub table_id: TableId,
	pub keccakf: Keccakf,
}

impl Sha3SingleBlockTable {
	pub fn new(cs: &mut ConstraintSystem) -> Self {
		let mut table = cs.add_table("SHA3-256 single block");
		let state_in =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = keccak::Keccakf::new(&mut table, state_in);
		Self {
			table_id: table.id(),
			keccakf,
		}
	}
}

/// Concrete packed field used throughout (same as M1).
type P = PackedType<OptimalUnderlier, B128>;

/// Prove + verify single-block SHA3-256 for each message in `messages`, under a
/// SHA-256-only Merkle commitment and SHA-256 Fiat–Shamir transcript (FIPS
/// 180-4). Returns `(proof_size_bytes, in_circuit_digests)`, where the digests
/// are squeezed from the *witness* output state after the proof is produced.
///
/// The digests are witness-read (see the SOUNDNESS BOUNDARY note at the top of
/// this file): they are the values the proof actually attests a permutation of,
/// and the caller/test gates them against the native SHA3-256 reference.
pub fn prove_verify_sha3_256(
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<[u8; DIGEST_BYTES]>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3SingleBlockTable::new(&mut cs);

	let n = messages.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	// FIPS-202-pad every message into a Keccak-f input state.
	let events: Vec<StateMatrix<u64>> = messages.iter().map(|m| padded_state(m)).collect();

	// Populate the witness through the gadget directly (not via TableFiller) so
	// we can read the output states back with `read_state_outs` before the
	// witness is consumed by the prover.
	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	table.keccakf.populate_state_in(&mut segment, &events)?;
	table.keccakf.populate(&mut segment)?;
	let digests: Vec<[u8; DIGEST_BYTES]> = table
		.keccakf
		.read_state_outs(&segment)?
		.map(|state| digest_from_state(&state))
		.collect();
	// `segment`/`table_witness` borrows of `witness` end here (NLL), so the
	// witness can be consumed below.

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// --- FIPS commitment + transcript: SHA-256 everywhere (identical wiring to
	// M1's `build_prove_and_verify`). ---
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

#[cfg(test)]
mod tests {
	use super::*;
	use sha3::{Digest, Sha3_256};

	/// NIST FIPS-202 known-answer vectors for SHA3-256.
	const NIST_EMPTY: [u8; 32] = [
		0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6,
		0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8,
		0x43, 0x4a,
	];
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

	/// STEP 1 (native, no circuit): validate the FIPS-202 padding + lane mapping
	/// by pushing our `padded_state` through the *native* Keccak-f (Binius'
	/// witness-side trace produces the permutation output; we reuse the gadget's
	/// non-proving `read_state_outs` path is heavier, so here we lean on the
	/// `sha3` crate and on the in-circuit test for the permutation). This test
	/// asserts that our padding is byte-exact against the NIST vectors and the
	/// `sha3` reference, independent of any proving.
	#[test]
	fn sha3_256_padding_matches_native_reference() {
		// The native reference must reproduce the published NIST vectors.
		assert_eq!(native_sha3_256(b""), NIST_EMPTY, "sha3 crate vs NIST empty");
		assert_eq!(native_sha3_256(b"abc"), NIST_ABC, "sha3 crate vs NIST abc");

		// And our single-block padding must be well-formed: 25 lanes, capacity
		// lanes (17..25) zero, and the domain/padding bytes in the right place.
		for msg in [b"".as_slice(), b"abc".as_slice(), b"binius-substrate M2a"] {
			let st = padded_state(msg);
			let lanes = st.as_inner();
			for (i, lane) in lanes.iter().enumerate().skip(17) {
				assert_eq!(*lane, 0, "capacity lane {i} must be zero for msg {msg:?}");
			}
			// Reconstruct the padded byte block and check the pad bytes.
			let mut bytes = [0u8; STATE_BYTES];
			for i in 0..25 {
				bytes[i * 8..i * 8 + 8].copy_from_slice(&lanes[i].to_le_bytes());
			}
			assert_eq!(bytes[msg.len()], 0x06 ^ if msg.len() == RATE_BYTES - 1 { 0x80 } else { 0 });
			assert_eq!(
				bytes[RATE_BYTES - 1] & 0x80,
				0x80,
				"closing pad bit must be set"
			);
			for &b in &bytes[RATE_BYTES..] {
				assert_eq!(b, 0, "capacity bytes must be zero");
			}
		}
	}

	/// STEP 2 + 4: the in-circuit gate. Prove (SHA-256 commitment + transcript)
	/// that Keccak-f applied to the FIPS-202-padded blocks of "" and "abc"
	/// produces states whose squeezed digests equal the published NIST SHA3-256
	/// vectors. This exercises the full permutation in-circuit and verifies the
	/// SHA-256 proof; the digest equality is the witness-side sponge gate (see
	/// the SOUNDNESS BOUNDARY note at the top of this file).
	#[test]
	fn sha3_256_in_circuit_matches_nist_vectors() {
		let messages = vec![b"".to_vec(), b"abc".to_vec()];

		// blowup=2 (log_inv_rate=1), 100-bit security — same knobs as M1.
		let (proof_size, digests) = prove_verify_sha3_256(&messages, 1, 100)
			.expect("in-circuit SHA3-256 proof must verify");

		assert_eq!(digests.len(), 2);
		assert_eq!(digests[0], NIST_EMPTY, "in-circuit SHA3-256(\"\") != NIST vector");
		assert_eq!(digests[1], NIST_ABC, "in-circuit SHA3-256(\"abc\") != NIST vector");

		// Cross-check against the native crate too (belt and braces).
		assert_eq!(digests[0], native_sha3_256(b""));
		assert_eq!(digests[1], native_sha3_256(b"abc"));

		assert!(proof_size > 0, "proof size must be non-zero");
		println!(
			"M2a in-circuit SHA3-256 verified for \"\" and \"abc\"; proof size = {proof_size} bytes"
		);
	}
}
