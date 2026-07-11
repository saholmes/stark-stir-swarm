// binius-substrate — M2a/M2c SHA-3 sponge, ported onto the 512-bit challenge
// field `B512TowerFamily` (tower level 9) so the IN-CIRCUIT kappa_bind hashes
// run at NIST L5 Fiat–Shamir security (security_bits = 256).
//
// This mirrors `b256_sha3.rs` exactly, ONE tower level up (B256 -> B512). It is
// the union of two already-proven pieces:
//   * `b512_keccak.rs` (NIST L5) — the REAL m3 `Keccakf` gadget building a table
//     over `ConstraintSystem<B512>` and proving/verifying with
//     `prove::<U512, B512TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>`.
//   * `sha3_variants.rs` (M2c) — the field-AGNOSTIC FIPS-202 sponge: `Sha3Variant`,
//     `padded_state_var` (message -> padded 25-lane Keccak input) and `digest_var`
//     (output state -> squeezed digest). These operate purely on `u64` lanes /
//     `StateMatrix<u64>`, so they are reused UNCHANGED over B512.
//
// So the only thing this module does is thread the M2a/M2c sponge through the
// B512 table + `B512TowerFamily` prover instead of the B256 one. No fork change
// beyond Phase-B's generic `Keccakf` is required: the SHA-3 sponge adds no new
// columns of its own — it is witness-side padding (`state_in`) plus a witness-side
// squeeze (`state_out`) around the SAME permutation gadget that already proves
// over B512.
//
// ============================ SOUNDNESS BOUNDARY (READ THIS) ================
// Identical to M2a/M2c, and unchanged by moving to B512:
//
//   * IN-CIRCUIT (constrained by the Keccakf zerocheck rows): the permutation
//     itself — `state_out = Keccak-f(state_in)` for whatever `state_in` the
//     witness commits. This is now proved over a 2^512 challenge/extension field,
//     so the Fiat–Shamir / sumcheck / FRI soundness terms poly(N)/|F| clear the
//     NIST L5 (256) query count — the exact security level where BOTH B128 and
//     B256 error out of `calculate_n_test_queries` (that is the whole point of B512).
//
//   * WITNESS-SIDE (gated against `sha3` + NIST KATs, NOT an in-circuit boundary):
//     that `state_in` is the FIPS-202 padding of a specific message, and that the
//     squeezed digest equals the public output. Binding those in-circuit over
//     B512 is `b512_binding.rs` (padding-binding) + `b512_recursion.rs` (seam /
//     root / join), the sound primitives that build on THIS module.
//
//   * OUTER COMMITMENT IS STILL SHA-256. The Merkle commitment + Fiat–Shamir
//     transcript remain SHA-256 (FIPS 180-4). For L5 the *outer* binding hash is
//     the M2d SHA-512 outer compression; THIS module delivers the IN-CIRCUIT hash
//     at NIST L5 FS security (the challenge field is 2^512, so the transcript's
//     soundness is not the limiting term). For a NIST L5 signature the natural
//     in-circuit binding hash is SHA3-512 (256-bit collision resistance); this
//     module proves BOTH SHA3-256 and SHA3-512 over B512.
// ============================================================================

use anyhow::Result;
use binius_core::fiat_shamir::HasherChallenger;
use binius_hash::sha2::Sha256Compression;
use binius_m3::{
	builder::{ConstraintSystem, Statement, TableId, WitnessIndex},
	gadgets::hash::keccak::{Keccakf, StateMatrix},
};
use bumpalo::Bump;
use sha2::Sha256;

use crate::b512_field::{B512TowerFamily, B512 as OurB512, U512};
// Reuse M2c's field-agnostic sponge (u64-lane only): the Sha3Variant enum, the
// FIPS-202 single-block padding, and the digest squeeze. Nothing here is
// field-specific, so it ports to B512 with zero changes.
use crate::sha3_variants::{digest_var, padded_state_var, Sha3Variant};

/// Output track of the permutation within a batch row (track 7 of 8) — used only
/// by the dishonest-witness soundness path to corrupt a real output lane.
#[cfg(test)]
const STATE_OUT_TRACK: usize = 7;

/// One single-block SHA-3 table over the top field `B512`, for a fixed variant.
/// Mirrors `b512_keccak::KeccakB512Table`, but the rows are FIPS-202-padded
/// message blocks and the digest is squeezed from the output state. The variant
/// only affects witness generation (padding boundary) and the squeeze width, not
/// the permutation circuit itself.
struct Sha3B512Table {
	table_id: TableId,
	keccakf: Keccakf,
}

impl Sha3B512Table {
	fn new(cs: &mut ConstraintSystem<OurB512>, variant: Sha3Variant) -> Self {
		let mut table = cs.add_table(format!("{} single block over B512", variant.name()));
		let state_in = StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = Keccakf::new(&mut table, state_in);
		Self {
			table_id: table.id(),
			keccakf,
		}
	}
}

/// Prove + verify single-block `variant` hashing of each message in `messages`,
/// IN-CIRCUIT over the 512-bit challenge/extension field `B512TowerFamily`, under
/// a SHA-256 (FIPS 180-4) Merkle commitment + SHA-256 Fiat–Shamir transcript.
///
/// Returns `(proof_size_bytes, in_circuit_digests)`. Each digest is squeezed from
/// the WITNESS output state (see the SOUNDNESS BOUNDARY note) and is
/// `variant.digest_bytes()` long; the caller/test gates it against the native
/// `sha3` crate + NIST KATs.
///
/// If `tamper_transcript` is set, a clone of the honest proof has one transcript
/// byte flipped and this fn errors unless that tampered proof is REJECTED by
/// verify (an in-band soundness gate).
fn build_prove_verify_sha3_b512(
	variant: Sha3Variant,
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
	tamper_transcript: bool,
) -> Result<(usize, Vec<Vec<u8>>, crate::b256_sha3::ProveVerifyMetrics)> {
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB512>::new();
	let table = Sha3B512Table::new(&mut cs, variant);

	let n = messages.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	// FIPS-202-pad every message into a Keccak-f input state (field-agnostic).
	let events: Vec<StateMatrix<u64>> = messages
		.iter()
		.map(|m| padded_state_var(variant, m))
		.collect();

	// Populate through the gadget directly so we can read the output states back
	// (digest) before the witness is consumed by the prover (M2a/M2c path).
	let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
	let digests: Vec<Vec<u8>>;
	{
		let table_witness = witness.init_table(table.table_id, n)?;
		let mut segment = table_witness.full_segment();
		table.keccakf.populate_state_in(&mut segment, &events)?;
		table.keccakf.populate(&mut segment)?;
		digests = table
			.keccakf
			.read_state_outs(&segment)?
			.map(|state| digest_var(variant, &state))
			.collect();
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// FIPS commitment + transcript; challenge/extension field = B512 (2^512).
	let t_prove = std::time::Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U512,
		B512TowerFamily,
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
	let prove_ms = t_prove.elapsed().as_millis();
	let peak_rss_bytes = crate::b256_sha3::peak_rss_bytes();

	let proof_size = proof.get_proof_size();

	let t_verify = std::time::Instant::now();
	binius_core::constraint_system::verify::<
		U512,
		B512TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;
	let verify_ms = t_verify.elapsed().as_millis();
	let metrics = crate::b256_sha3::ProveVerifyMetrics { proof_bytes: proof_size, prove_ms, verify_ms, peak_rss_bytes };

	if tamper_transcript {
		let mut bad = proof;
		let mid = bad.transcript.len() / 2;
		bad.transcript[mid] ^= 0xFF;
		let rejected = binius_core::constraint_system::verify::<
			U512,
			B512TowerFamily,
			Sha256,
			Sha256Compression,
			HasherChallenger<Sha256>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, bad)
		.is_err();
		anyhow::ensure!(
			rejected,
			"SOUNDNESS FAILURE: tampered transcript accepted over B512 ({})",
			variant.name()
		);
	}

	Ok((proof_size, digests, metrics))
}

/// Public entry: honest prove+verify of a single-block SHA-3 `variant` batch
/// IN-CIRCUIT over B512, returning `(proof_size_bytes, in_circuit_digests)`.
pub fn prove_verify_sha3_b512(
	variant: Sha3Variant,
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<Vec<u8>>)> {
	let (sz, d, _m) = build_prove_verify_sha3_b512(variant, messages, log_inv_rate, security_bits, false)?;
	Ok((sz, d))
}

/// Timed entry: same as `prove_verify_sha3_b512` but returns the prove/verify/RSS split.
pub fn prove_verify_sha3_b512_timed(
	variant: Sha3Variant,
	messages: &[Vec<u8>],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(Vec<Vec<u8>>, crate::b256_sha3::ProveVerifyMetrics)> {
	let (_sz, d, m) = build_prove_verify_sha3_b512(variant, messages, log_inv_rate, security_bits, false)?;
	Ok((d, m))
}

/// Build a DISHONEST witness: after honest population, flip one bit of the perm-0
/// `state_out` output lane so it is no longer `Keccak-f(state_in)`. Returns `true`
/// iff the tampered statement is rejected (the prover errors on the unsatisfied
/// zerocheck, or the verifier rejects the resulting proof). This is the
/// corrupted-output-lane soundness path over B512.
#[cfg(test)]
fn dishonest_sha3_b512_is_rejected(
	variant: Sha3Variant,
	log_inv_rate: usize,
	security_bits: usize,
) -> bool {
	use binius_m3::builder::B1;

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB512>::new();
	let table = Sha3B512Table::new(&mut cs, variant);

	let messages = vec![b"abc".to_vec()];
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![1],
	};
	let events = vec![padded_state_var(variant, &messages[0])];

	let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
	{
		let table_witness = match witness.init_table(table.table_id, 1) {
			Ok(tw) => tw,
			Err(_) => return true,
		};
		let mut segment = table_witness.full_segment();
		if table
			.keccakf
			.populate_state_in(&mut segment, &events)
			.is_err()
		{
			return true;
		}
		if table.keccakf.populate(&mut segment).is_err() {
			return true;
		}
		// Corrupt the actual output lane (track 7) of permutation 0: this breaks
		// the chi/iota zero-constraint that ties state_out to Keccak-f(state_in).
		let out_col = table.keccakf.packed_state_out()[(0, 0)];
		let mut lane = match segment.get_mut_as::<u64, B1, { 64 * 8 }>(out_col) {
			Ok(l) => l,
			Err(_) => return true,
		};
		lane[STATE_OUT_TRACK] ^= 1;
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	let proof = match binius_core::constraint_system::prove::<
		U512,
		B512TowerFamily,
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
	) {
		Ok(p) => p,
		Err(_) => return true, // prover refused the unsatisfiable witness
	};

	binius_core::constraint_system::verify::<
		U512,
		B512TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)
	.is_err()
}

#[cfg(test)]
mod tests {
	use super::*;
	use sha3::{Digest, Sha3_256, Sha3_384, Sha3_512};

	// ---- Published NIST FIPS-202 known-answer vectors. ----
	const NIST_256_EMPTY: &str =
		"a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a";
	const NIST_256_ABC: &str =
		"3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532";
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

	fn native_256(msg: &[u8]) -> Vec<u8> {
		let mut h = Sha3_256::new();
		h.update(msg);
		h.finalize().to_vec()
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

	/// REQUIRED DELIVERABLE 1 — in-circuit SHA3-256 of "" and "abc" proves AND
	/// verifies over `B512TowerFamily` at NIST L5 (security_bits=256); the squeezed
	/// digest equals BOTH the NIST vectors and the `sha3` crate. Prints proof size.
	/// (This is the exact security level where B128 and B256 both fail out of the
	/// verifier's query-count check — B512 is required.)
	#[test]
	fn sha3_256_over_b512_l5() {
		let v = Sha3Variant::Sha3_256;
		let messages = vec![b"".to_vec(), b"abc".to_vec()];
		let (proof_size, digests) = prove_verify_sha3_b512(v, &messages, 1, 256)
			.expect("in-circuit SHA3-256 must VERIFY over B512 at NIST L5 (256)");

		assert_eq!(digests.len(), 2);
		assert_eq!(digests[0], hex(NIST_256_EMPTY), "in-circuit SHA3-256(\"\") over B512 != NIST vector");
		assert_eq!(digests[1], hex(NIST_256_ABC), "in-circuit SHA3-256(\"abc\") over B512 != NIST vector");
		assert_eq!(digests[0], native_256(b""), "in-circuit SHA3-256(\"\") over B512 != sha3 crate");
		assert_eq!(digests[1], native_256(b"abc"), "in-circuit SHA3-256(\"abc\") over B512 != sha3 crate");
		assert!(proof_size > 0);
		println!(
			"DELIVERABLE 1 (L5): in-circuit SHA3-256 over B512 VERIFIED at security_bits=256 for \"\" and \"abc\"; \
			 digest == NIST + sha3 crate; proof size = {proof_size} bytes"
		);
	}

	/// REQUIRED DELIVERABLE (L5, natural binding hash) — SHA3-512 in-circuit over
	/// B512 at security_bits=256 matches its NIST KAT / the `sha3` crate. For a NIST
	/// L5 signature this is the natural binding hash (256-bit collision resistance).
	#[test]
	fn sha3_512_over_b512_l5() {
		let v = Sha3Variant::Sha3_512;
		let messages = vec![b"".to_vec(), b"abc".to_vec()];
		let (proof_size, digests) = prove_verify_sha3_b512(v, &messages, 1, 256)
			.expect("in-circuit SHA3-512 must VERIFY over B512 at NIST L5 (256)");

		assert_eq!(digests[0], hex(KAT_512_EMPTY), "SHA3-512(\"\") over B512 != NIST KAT");
		assert_eq!(digests[1], hex(KAT_512_ABC), "SHA3-512(\"abc\") over B512 != NIST KAT");
		assert_eq!(digests[0], native_512(b""), "SHA3-512(\"\") over B512 != sha3 crate");
		assert_eq!(digests[1], native_512(b"abc"), "SHA3-512(\"abc\") over B512 != sha3 crate");
		assert!(proof_size > 0);
		println!(
			"DELIVERABLE (L5): in-circuit SHA3-512 over B512 VERIFIED at security_bits=256; \
			 digest == NIST KAT + sha3 crate; proof size = {proof_size} bytes"
		);
	}

	/// STRETCH — SHA3-384 in-circuit over B512 at security_bits=256 matches its NIST
	/// KAT / the `sha3` crate (kappa for NIST L3 output width, proved at L5 FS).
	#[test]
	fn sha3_384_over_b512_l5() {
		let v384 = Sha3Variant::Sha3_384;
		let messages = vec![b"".to_vec(), b"abc".to_vec()];
		let (size_384, d384) = prove_verify_sha3_b512(v384, &messages, 1, 256)
			.expect("in-circuit SHA3-384 must VERIFY over B512 at L5 (256)");
		assert_eq!(d384[0], hex(KAT_384_EMPTY), "SHA3-384(\"\") over B512 != NIST KAT");
		assert_eq!(d384[1], hex(KAT_384_ABC), "SHA3-384(\"abc\") over B512 != NIST KAT");
		assert_eq!(d384[0], native_384(b""), "SHA3-384(\"\") over B512 != sha3 crate");
		assert_eq!(d384[1], native_384(b"abc"), "SHA3-384(\"abc\") over B512 != sha3 crate");
		println!(
			"STRETCH (L5): in-circuit SHA3-384 ({size_384} B) over B512 VERIFIED at security_bits=256; \
			 digest == NIST KAT + sha3 crate"
		);
	}

	/// REQUIRED DELIVERABLE — SOUNDNESS at L5. (a) a dishonest witness (a state_out
	/// lane that is not Keccak-f(state_in)) is rejected, and (b) a single flipped
	/// transcript byte on an honest SHA3-256-over-B512 proof is rejected.
	#[test]
	fn sha3_b512_tamper_rejected() {
		let v = Sha3Variant::Sha3_256;
		assert!(
			dishonest_sha3_b512_is_rejected(v, 1, 256),
			"SOUNDNESS FAILURE: a corrupted SHA3-256 state_out lane was accepted over B512 at L5"
		);
		let (size, _, _) = build_prove_verify_sha3_b512(v, &[b"abc".to_vec()], 1, 256, true)
			.expect("honest proof must verify AND tampered transcript must be rejected");
		println!(
			"DELIVERABLE (L5): corrupted-output-lane AND flipped-transcript both REJECTED over B512 \
			 at security_bits=256 (honest SHA3-256 proof size = {size} bytes)"
		);
	}
}
