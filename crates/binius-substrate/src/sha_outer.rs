// M2d — SHA-384 / SHA-512 OUTER commitment + Fiat–Shamir compression.
//
// Goal: let the OUTER Merkle commitment and Fiat–Shamir transcript of a Binius
// proof run at NIST L3 (SHA-384, 192-bit collision resistance) and L5 (SHA-512,
// 256-bit) binding strength — completing `kappa_bind` for the OUTER commitment.
// (M2c already delivered the in-circuit SHA3-384 / SHA3-512 hash; this is the
// complementary, out-of-circuit half.)
//
// Binius ships exactly one FIPS-family outer compression function,
// `binius_hash::sha2::Sha256Compression` (a 2:1 SHA-256 block compressor used as
// the Merkle node hash). We MIRROR that struct for SHA-512 and SHA-384 here, in
// OUR crate — the Binius checkout is left untouched. The orphan rule permits
// this: `PseudoCompressionFunction` / `CompressionFunction` are foreign traits,
// but `Sha512Compression` / `Sha384Compression` are our LOCAL structs, so the
// impls are legal.
//
// Everything below is additive: it does not modify any M1 / M2a-c item.

use anyhow::Result;
use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::tower::CanonicalTowerFamily;
use binius_hash::{CompressionFunction, PseudoCompressionFunction};
use binius_m3::builder::{ConstraintSystem, Statement, WitnessIndex, B128};
use binius_field::{arch::OptimalUnderlier, as_packed_field::PackedType};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::{
	compress512,
	digest::{
		core_api::{Block, BlockSizeUser},
		generic_array::GenericArray,
		Digest, FixedOutputReset, Output,
	},
	Sha384, Sha512,
};
use std::iter::repeat_with;

use crate::PermutationTable;
use binius_m3::gadgets::hash::keccak::StateMatrix;

// ---------------------------------------------------------------------------
// SHA-512 two-to-one outer compression (NIST L5 / 256-bit binding).
// ---------------------------------------------------------------------------

/// A two-to-one compression function for SHA-512 digests — the L5 analogue of
/// Binius' `Sha256Compression`. `compress([a, b])` places the two 64-byte
/// digests into a single 128-byte SHA-512 message block and runs one SHA-512
/// block permutation (`sha2::compress512`) starting from a domain-separated
/// initial state. Collision resistance reduces to that of the SHA-512 block
/// function (256-bit).
#[derive(Debug, Clone)]
pub struct Sha512Compression {
	/// Domain-separated 512-bit initial chaining state, held as 8 little-endian
	/// u64 words (mirrors `Sha256Compression`'s `[u32; 8]`).
	initial_state: [u64; 8],
}

impl Default for Sha512Compression {
	fn default() -> Self {
		// Same construction as `Sha256Compression`: derive the IV by hashing a
		// scheme-specific domain-separation tag. SHA-512 already yields the full
		// 64 bytes we need for the [u64; 8] state.
		let iv = Sha512::digest(b"BINIUS SHA-512 COMPRESS");
		Self {
			initial_state: bytes_to_u64x8(iv.as_slice()),
		}
	}
}

impl PseudoCompressionFunction<Output<Sha512>, 2> for Sha512Compression {
	fn compress(&self, input: [Output<Sha512>; 2]) -> Output<Sha512> {
		let mut state = self.initial_state;
		// block = input[0] (64 B) || input[1] (64 B) = one 128-byte SHA-512 block.
		let mut block = <Block<Sha512>>::default();
		block.as_mut_slice()[..64].copy_from_slice(input[0].as_slice());
		block.as_mut_slice()[64..].copy_from_slice(input[1].as_slice());
		compress512(&mut state, core::slice::from_ref(&block));
		u64x8_to_output::<Sha512>(&state, 64)
	}
}

impl CompressionFunction<Output<Sha512>, 2> for Sha512Compression {}

// ---------------------------------------------------------------------------
// SHA-384 two-to-one outer compression (NIST L3 / 192-bit binding).
// ---------------------------------------------------------------------------

/// A two-to-one compression function for SHA-384 digests — the L3 analogue of
/// Binius' `Sha256Compression`.
///
/// SHA-384 shares SHA-512's 128-byte block and `compress512` permutation, but a
/// digest is 48 bytes. This is a **fixed-input-length** 2:1 compressor: the two
/// 48-byte digests occupy the first 96 bytes of the 128-byte block and the
/// remaining 32 bytes are a constant zero pad. The 64-byte post-permutation
/// state is then truncated to its first 48 bytes to form the SHA-384 output.
///
/// Because the input length is fixed (always 2 × 48 B), the fixed pad is not a
/// length-extension / ambiguity hazard: collision resistance reduces to that of
/// `compress512` (any SHA-384 output collision is a collision of the truncated
/// 512-bit state), giving 384-bit output ⇒ 192-bit collision resistance.
#[derive(Debug, Clone)]
pub struct Sha384Compression {
	/// Domain-separated 512-bit initial chaining state (8 little-endian u64s).
	initial_state: [u64; 8],
}

impl Default for Sha384Compression {
	fn default() -> Self {
		// A SHA-384 digest is only 48 bytes but the chaining state is 64 bytes,
		// so we derive the full-width IV with SHA-512 over a SHA-384-flavoured
		// domain-separation tag (distinct tag ⇒ distinct IV from Sha512Compression).
		let iv = Sha512::digest(b"BINIUS SHA-384 COMPRESS");
		Self {
			initial_state: bytes_to_u64x8(iv.as_slice()),
		}
	}
}

impl PseudoCompressionFunction<Output<Sha384>, 2> for Sha384Compression {
	fn compress(&self, input: [Output<Sha384>; 2]) -> Output<Sha384> {
		let mut state = self.initial_state;
		// block = input[0] (48 B) || input[1] (48 B) || [0u8; 32]  (128-byte block).
		let mut block = <Block<Sha384>>::default(); // Sha384 block size == 128.
		block.as_mut_slice()[..48].copy_from_slice(input[0].as_slice());
		block.as_mut_slice()[48..96].copy_from_slice(input[1].as_slice());
		// bytes [96..128] are left as the default zero pad.
		compress512(&mut state, core::slice::from_ref(&block));
		// Truncate the 64-byte state to the first 48 bytes → SHA-384 output.
		u64x8_to_output::<Sha384>(&state, 48)
	}
}

impl CompressionFunction<Output<Sha384>, 2> for Sha384Compression {}

// ---------------------------------------------------------------------------
// Little-endian [u64; 8] <-> byte helpers (avoids a bytemuck dependency; byte
// order only has to be internally consistent, since these are Merkle-node
// compressors, not standard SHA digests).
// ---------------------------------------------------------------------------

fn bytes_to_u64x8(bytes: &[u8]) -> [u64; 8] {
	let mut out = [0u64; 8];
	for (i, word) in out.iter_mut().enumerate() {
		*word = u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap());
	}
	out
}

/// Serialise `state` little-endian and return the first `out_len` bytes as an
/// `Output<D>` (`out_len` must equal `D`'s output size: 64 for SHA-512, 48 for
/// SHA-384).
fn u64x8_to_output<D: Digest>(state: &[u64; 8], out_len: usize) -> Output<D> {
	let mut bytes = [0u8; 64];
	for (i, word) in state.iter().enumerate() {
		bytes[i * 8..i * 8 + 8].copy_from_slice(&word.to_le_bytes());
	}
	GenericArray::clone_from_slice(&bytes[..out_len])
}

// ---------------------------------------------------------------------------
// Generic outer-hash prove/verify over the M1 Keccak-f circuit.
// ---------------------------------------------------------------------------

/// Build the M1 Keccak-f constraint system for `n_permutations` permutations,
/// prove it, and verify — with the OUTER Merkle commitment AND Fiat–Shamir
/// transcript instantiated over an arbitrary FIPS hash `<Hash, Compress>`:
///
/// * `Hash`     — the digest used by the Merkle tree leaves and the challenger
///                (`Sha256` / `Sha384` / `Sha512`).
/// * `Compress` — the 2:1 Merkle-node compressor (`Sha256Compression` /
///                `Sha384Compression` / `Sha512Compression`).
///
/// The SAME circuit is therefore committed under SHA-256, SHA-384 or SHA-512 by
/// swapping only these two type parameters (challenger = `HasherChallenger<Hash>`).
///
/// The honest proof must accept. If `tamper` is set, a clone of the proof has one
/// transcript byte flipped and must be **rejected** (the soundness gate). Returns
/// the honest proof size in bytes.
pub fn prove_verify_keccak_outer<Hash, Compress>(
	n_permutations: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper: bool,
) -> Result<usize>
where
	// `Default` is additionally required because `HasherChallenger<Hash>` only
	// implements `Challenger` when `Hash: Default` (the challenger seeds a fresh
	// hasher). All of Sha256/Sha384/Sha512 satisfy it.
	Hash: Digest + BlockSizeUser + FixedOutputReset + Send + Sync + Clone + Default,
	Compress: PseudoCompressionFunction<Output<Hash>, 2> + Default + Sync,
{
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = PermutationTable::new(&mut cs);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_permutations],
	};

	// Deterministic witness (fixed seed), identical to M1's for reproducibility.
	let mut rng = StdRng::from_seed([7u8; 32]);
	let events = repeat_with(|| StateMatrix::from_fn(|_| rng.next_u64()))
		.take(n_permutations)
		.collect::<Vec<_>>();

	let mut witness = WitnessIndex::<PackedType<OptimalUnderlier, B128>>::new(&cs, &allocator);
	witness.fill_table_parallel(&table, &events)?;

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// --- OUTER commitment + transcript over <Hash, Compress>. ---
	let proof = binius_core::constraint_system::prove::<
		U,
		CanonicalTowerFamily,
		Hash,
		Compress,
		HasherChallenger<Hash>,
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

	// Honest proof must verify under the same outer hash.
	binius_core::constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Hash,
		Compress,
		HasherChallenger<Hash>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;

	// Soundness gate: one flipped transcript byte must be rejected.
	if tamper {
		let mut bad = proof;
		let mid = bad.transcript.len() / 2;
		bad.transcript[mid] ^= 0xFF;
		let rejected = binius_core::constraint_system::verify::<
			U,
			CanonicalTowerFamily,
			Hash,
			Compress,
			HasherChallenger<Hash>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, bad)
		.is_err();
		anyhow::ensure!(rejected, "SOUNDNESS FAILURE: tampered proof was accepted");
	}

	Ok(proof_size)
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_hash::sha2::Sha256Compression;
	use sha2::{Sha256, Sha384, Sha512};

	// Small Keccak-f batch for the outer-hash gates (keeps prove time low; the
	// outer hash choice is independent of batch size).
	const N_PERMS: usize = 8;
	const LOG_INV_RATE: usize = 1;
	const SECURITY_BITS: usize = 100;

	/// GATE 1 (pure unit, no proving): each compressor is deterministic and
	/// input-sensitive (one flipped input bit ⇒ different output) — the minimal
	/// binding check for a Merkle-node hash.
	#[test]
	fn compression_is_deterministic_and_binding() {
		// --- SHA-512 ---
		let c512 = Sha512Compression::default();
		let x: Output<Sha512> = GenericArray::clone_from_slice(&[0x11u8; 64]);
		let mut y_bytes = [0x22u8; 64];
		let y: Output<Sha512> = GenericArray::clone_from_slice(&y_bytes);

		let out_a = c512.compress([x.clone(), y.clone()]);
		let out_b = c512.compress([x.clone(), y.clone()]);
		assert_eq!(out_a, out_b, "SHA-512 compress must be deterministic");

		y_bytes[0] ^= 0x01; // flip one bit of the second input
		let y2: Output<Sha512> = GenericArray::clone_from_slice(&y_bytes);
		let out_c = c512.compress([x.clone(), y2]);
		assert_ne!(out_a, out_c, "SHA-512 compress must be input-sensitive");
		// asymmetry: swapping the two inputs changes the output.
		assert_ne!(out_a, c512.compress([y, x]), "SHA-512 compress order-sensitive");

		// --- SHA-384 ---
		let c384 = Sha384Compression::default();
		let p: Output<Sha384> = GenericArray::clone_from_slice(&[0x33u8; 48]);
		let mut q_bytes = [0x44u8; 48];
		let q: Output<Sha384> = GenericArray::clone_from_slice(&q_bytes);

		let a = c384.compress([p.clone(), q.clone()]);
		let b = c384.compress([p.clone(), q.clone()]);
		assert_eq!(a, b, "SHA-384 compress must be deterministic");
		assert_eq!(a.len(), 48, "SHA-384 output must be 48 bytes");

		q_bytes[47] ^= 0x80;
		let q2: Output<Sha384> = GenericArray::clone_from_slice(&q_bytes);
		let c = c384.compress([p, q2]);
		assert_ne!(a, c, "SHA-384 compress must be input-sensitive");

		// The two schemes have distinct domain-separated IVs.
		assert_ne!(
			Sha512Compression::default().initial_state,
			Sha384Compression::default().initial_state,
			"SHA-512 / SHA-384 compressors must use distinct domain-separated IVs",
		);
	}

	/// GATE 2a (real prove+verify): the Keccak-f batch proves AND verifies with
	/// the OUTER commitment + transcript over SHA-512.
	#[test]
	fn keccak_proves_under_sha512_outer() {
		let size = prove_verify_keccak_outer::<Sha512, Sha512Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, false,
		)
		.expect("Keccak-f proof must verify under a SHA-512 outer commitment");
		assert!(size > 0);
		println!("SHA-512 outer commitment: Keccak-f proof verified; proof size = {size} bytes");
	}

	/// GATE 2b (real prove+verify): same, over SHA-384.
	#[test]
	fn keccak_proves_under_sha384_outer() {
		let size = prove_verify_keccak_outer::<Sha384, Sha384Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, false,
		)
		.expect("Keccak-f proof must verify under a SHA-384 outer commitment");
		assert!(size > 0);
		println!("SHA-384 outer commitment: Keccak-f proof verified; proof size = {size} bytes");
	}

	/// GATE 3 (soundness, under SHA-512): honest proof verifies and a single
	/// flipped transcript byte is rejected by the SHA-512 verifier.
	#[test]
	fn sha512_outer_tamper_rejected() {
		let size = prove_verify_keccak_outer::<Sha512, Sha512Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, true,
		)
		.expect("honest SHA-512 proof must verify and tampered proof must be rejected");
		println!("SHA-512 outer tamper-reject gate passed; honest proof size = {size} bytes");
	}

	/// Companion soundness gate under SHA-384.
	#[test]
	fn sha384_outer_tamper_rejected() {
		let size = prove_verify_keccak_outer::<Sha384, Sha384Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, true,
		)
		.expect("honest SHA-384 proof must verify and tampered proof must be rejected");
		println!("SHA-384 outer tamper-reject gate passed; honest proof size = {size} bytes");
	}

	/// Cross-hash proof-size comparison: SHA-256 vs SHA-384 vs SHA-512 outer
	/// commitments over the identical circuit (larger digest ⇒ larger Merkle
	/// authentication paths ⇒ larger proof). Prints the three sizes.
	#[test]
	fn outer_hash_proof_size_comparison() {
		let s256 = prove_verify_keccak_outer::<Sha256, Sha256Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, false,
		)
		.expect("SHA-256 outer round-trip");
		let s384 = prove_verify_keccak_outer::<Sha384, Sha384Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, false,
		)
		.expect("SHA-384 outer round-trip");
		let s512 = prove_verify_keccak_outer::<Sha512, Sha512Compression>(
			N_PERMS, LOG_INV_RATE, SECURITY_BITS, false,
		)
		.expect("SHA-512 outer round-trip");
		println!(
			"OUTER proof sizes (N={N_PERMS}, blowup=2^{LOG_INV_RATE}, {SECURITY_BITS}-bit): \
			 SHA-256 = {s256} B, SHA-384 = {s384} B, SHA-512 = {s512} B"
		);
	}
}
