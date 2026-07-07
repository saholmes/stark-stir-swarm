// binius-substrate — M1 "substrate up" for the STARK-Binius-SWARM port.
//
// Proves the load-bearing feasibility claim behind the binary-field recursion
// design (DNS-STARK §binary-field-recursion): Binius's in-circuit Keccak-f[1600]
// gadget proves AND verifies with a **SHA-256 (FIPS 180-4)** Merkle commitment
// and a **SHA-256** Fiat–Shamir challenger — no Groestl / Vision / Poseidon on
// the soundness-critical path.
//
// This is the FIPS instantiation of Binius' own `examples/keccak.rs`: the only
// change vs. that example is the three hash type-parameters to prove/verify
// (Groestl256 -> Sha256), which is exactly the swap the design relies on.

// M3 (kappa_FS): a 256-bit binary tower field giving Binius a >2^128 challenge/
// extension field, so FRI/sumcheck error terms poly(N)/|F| are over 2^256 and the
// verifier's `calculate_n_test_queries` succeeds at NIST L1/L3 (additive; a new,
// local tower family — does NOT touch the default CanonicalTowerFamily path).
pub mod b256_field;

// M3 (kappa_FS) Phase-1b: the packing machinery (local packed subfield types over
// U256 + ProverTowerFamily) that lets Binius's constraint_system::prove/verify run
// over the 256-bit challenge field. Additive; no Binius file is modified.
pub mod b256_packed;

// M3 (kappa_FS) Phase-1b: a REAL end-to-end proof over B256 at NIST L1 (minimal
// non-Keccak circuit; see module docs for the Keccak-gadget wall). Additive.
pub mod b256_prove;

// M3 (kappa_FS) NIST L5: a 512-bit binary tower field (T_9, tower level 9) mirroring
// b256_field one level up, so `calculate_n_test_queries` succeeds at security_bits=256
// (where BOTH B128 and B256 error). Additive; a new, local tower family.
pub mod b512_field;

// M3 (kappa_FS) NIST L5 packing: local packed subfield types `Sub512<S>` over U512 +
// `ProverTowerFamily for B512TowerFamily`, cross-validated against Binius's canonical
// 512-bit packed types. Additive; no Binius file is modified.
pub mod b512_packed;

// M3 (kappa_FS) NIST L5 proofs: a REAL end-to-end Binius proof over the 512-bit
// challenge field `B512TowerFamily` at security_bits=256 (ring-switch square circuit +
// kappa-9 tensor transpose gate + tamper rejection). Additive.
pub mod b512_prove;

// M3 (kappa_FS) NIST L5 Keccak: the m3 Keccak-f[1600] gadget proving AND verifying
// over `B512TowerFamily` at security_bits=256. Additive.
pub mod b512_keccak;

// M3 (kappa_FS) Phase B: the REAL m3 Keccak-f[1600] gadget proving AND verifying
// over the 256-bit challenge/extension field `B256TowerFamily` at NIST L1/L3, made
// possible by generalizing binius_m3's `Keccakf` gadget (top field B128 -> generic
// `F: TowerField`) on the fork branch. Additive; the stock B128 M1 path
// (`PermutationTable` above) is unchanged.
pub mod b256_keccak;

// M3 (kappa_FS) — the M2a/M2c SHA-3 sponge ported onto `B256TowerFamily` so the
// IN-CIRCUIT SHA3-256/384/512 hashes prove AND verify over the 256-bit challenge
// field at NIST L1/L3 Fiat–Shamir security. Reuses `b256_keccak`'s tower-family
// prove wiring + `sha3_variants`' field-agnostic padding/squeeze. Additive.
pub mod b256_sha3;

// M2b-1 over B256: the SOUND single-block SHA3-256 padding binding ported onto
// `B256TowerFamily` so the load-bearing kappa_bind soundness primitive proves AND
// verifies at NIST L1/L3 over the 256-bit challenge field (additive; reuses the
// generic m3 assert_zero/add_constant surface + the b256_keccak prove wiring).
pub mod b256_binding;

// M2b-2/3/4 over B256: the seam, root-boundary and cross-table channel-join
// recursion-binding primitives ported onto `B256TowerFamily` so they prove AND
// verify at NIST L1/L3 with their adversarial rejects firing over the 256-bit
// challenge field (additive; reuses the field-agnostic seam helpers + generic m3
// add_shifted/add_selected_block/add_packed/push/pull + generic Boundary<F>).
pub mod b256_recursion;

// M3 (kappa_FS) NIST L5 — the M2a/M2c SHA-3 sponge ported onto `B512TowerFamily`
// (tower level 9) so the IN-CIRCUIT SHA3-256/384/512 hashes prove AND verify over
// the 512-bit challenge field at NIST L5 (security_bits=256) Fiat–Shamir security.
// Mirrors `b256_sha3` one tower level up. Additive.
pub mod b512_sha3;

// M2b-1 over B512 (NIST L5): the SOUND single-block SHA3-256 padding binding ported
// onto `B512TowerFamily` so the load-bearing kappa_bind soundness primitive proves
// AND verifies at security_bits=256 with its bad-padding / bad-capacity adversarial
// rejects firing, isolated to the binding constraint. Mirrors `b256_binding`. Additive.
pub mod b512_binding;

// M2b-2/3/4 over B512 (NIST L5): the seam, root-boundary and cross-table channel-join
// recursion-binding primitives ported onto `B512TowerFamily` so they prove AND verify
// at security_bits=256 with their adversarial rejects firing (forged-link / wrong-root
// / forged-inner-root). Mirrors `b256_recursion`. Additive.
pub mod b512_recursion;

// M2a lives in its own module (additive; does not touch the M1 items below).
pub mod sha3_gadget;

// M2b-1: sound single-block padding binding (additive; builds on M2a's gadget).
pub mod sha3_binding;

// M2c: in-circuit SHA3-384 / SHA3-512 single-block gadgets + sound padding
// binding (kappa_bind for NIST L3/L5; additive, generalises M2a/M2b-1 over a
// Sha3Variant enum).
pub mod sha3_variants;

// M2b-2: sound in-circuit binding seam between two SHA3-256 hashes (additive).
pub mod sha3_seam;

// M2b-3: expose the depth-2 chain root as a PUBLIC boundary via a channel push
// + Statement.boundaries pull (additive; builds on M2b-2's SeamTable).
pub mod sha3_root_boundary;

// M2b-4: in-circuit CROSS-TABLE channel join — a CHILD table pushes its SHA3-256
// root to a shared channel and a PARENT table PULLs it as its own hash-input
// segment (aggregation / master-binds-inner-root; additive).
pub mod sha3_join;

// M2d: SHA-384 / SHA-512 OUTER Merkle + Fiat–Shamir compression, so the OUTER
// commitment can run at NIST L3/L5 binding strength (completes kappa_bind for
// the outer commitment; M2c did the in-circuit hash). Additive; mirrors Binius'
// `Sha256Compression` for our LOCAL structs (Binius checkout unmodified).
pub mod sha_outer;

// Bench: separately-timed prove/verify harness over the M2a SHA3-256 gadget, for
// the prove-time / peak-RSS scaling table (additive; no soundness surface).
pub mod bench;

// S0 (signature-AIR port): a NON-NATIVE modular-multiply gadget `a*b mod m` built
// from hand-rolled shift-and-add over B1 bit-columns (NO fork change), proving AND
// verifying over `B256TowerFamily` at NIST L1. The prover supplies quotient `q` and
// remainder `r`; the circuit enforces the big-integer identity `a*b == q*m + r` and
// the soundness-critical strict reduction `0 <= r < m`. This is the arithmetic
// substrate S1 (ML-DSA verify over Z_q, q = 8380417) is built on. Additive; reuses
// `b256_keccak`'s tower-family prove wiring. See module docs for the construction.
pub mod nonnative;

// S1a (ML-DSA / FIPS 204 verify port): the R_q = Z_q[X]/(X^256+1) polynomial-arithmetic
// layer over q = 8380417 — sound modular add/sub, modular multiply-by-public-twiddle
// ζ·v, and the forward/inverse negacyclic 256-point NTT — proving AND verifying over
// `B256TowerFamily` at NIST L1. Built ENTIRELY on S0's audited `Adder`/reduction recipe
// (`nonnative`); no fork change, no reinvented modmul. Additive.
pub mod mldsa_ntt;

// ── Draft suite (S1b–e / S2 / S3 / R / D): native FIPS-204 / classical-signature verify
// references + in-circuit gadget designs, gated against independent oracles (NIST KATs,
// num-bigint, RFC vectors). Compiled under `cargo test` (they use the dev-dep reference
// crates sha3/num-bigint/tiny-keccak, visible to all crate code in the test profile). The
// heavy in-circuit prove paths are `#[ignore]`d until wired.
pub mod sha512_gadget; // SHA-1/256/384/512 hash-gadget references (S2/S3/D)
pub mod mldsa_shake; // S1b ExpandA / S1c SampleInBall (SHAKE)
pub mod mldsa_verify; // S1d/e ML-DSA verify assembly + decode
pub mod ec_verify; // S2 EdDSA / ECDSA verify (7 curves)
pub mod rsa_verify; // S3 RSA verify (PKCS#1-v1.5 + PSS, 1024–8192)
pub mod recursion; // R Tier-A aggregation + Tier-B verifier design
pub mod dns_stark; // D DNS-STARK zone assembly

use std::iter::repeat_with;

use anyhow::Result;
use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::{
	arch::OptimalUnderlier, as_packed_field::PackedType,
	linear_transformation::PackedTransformationFactory, tower::CanonicalTowerFamily,
	PackedExtension, PackedFieldIndexable, PackedSubfield,
};
use binius_hash::sha2::Sha256Compression;
use binius_m3::{
	builder::{
		ConstraintSystem, Statement, TableFiller, TableId, TableWitnessSegment, WitnessIndex, B1,
		B128, B8,
	},
	gadgets::hash::keccak::{self, Keccakf, StateMatrix},
};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::Sha256;

/// A one-table constraint system holding a batch of Keccak-f permutations.
pub struct PermutationTable {
	table_id: TableId,
	keccakf: Keccakf,
}

impl PermutationTable {
	pub fn new(cs: &mut ConstraintSystem) -> Self {
		let mut table = cs.add_table("Keccak permutation");
		let state_in =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = keccak::Keccakf::new(&mut table, state_in);
		Self {
			table_id: table.id(),
			keccakf,
		}
	}
}

impl<P> TableFiller<P> for PermutationTable
where
	P: PackedFieldIndexable<Scalar = B128> + PackedExtension<B1> + PackedExtension<B8>,
	PackedSubfield<P, B8>: PackedTransformationFactory<PackedSubfield<P, B8>>,
{
	type Event = StateMatrix<u64>;

	fn id(&self) -> TableId {
		self.table_id
	}

	fn fill<'a>(
		&self,
		rows: impl Iterator<Item = &'a Self::Event>,
		witness: &mut TableWitnessSegment<P>,
	) -> Result<()> {
		self.keccakf.populate_state_in(witness, rows)?;
		self.keccakf.populate(witness)?;
		Ok(())
	}
}

/// Build the Keccak-f constraint system for `n_permutations` permutations, prove
/// it, and verify the proof — Merkle commitment and Fiat–Shamir transcript both
/// over **SHA-256** (FIPS 180-4). Returns the proof size in bytes.
///
/// The honest proof is always verified and must accept. If `tamper` is set, a
/// *clone* of the proof has one transcript byte flipped and is fed back to the
/// verifier, which must **reject** it (the soundness gate).
///
/// The prove/verify generics `<U, Tower, Hash, Compress, Challenger>` are the
/// only place the hash choice appears; here `Hash = Sha256`,
/// `Compress = Sha256Compression`, `Challenger = HasherChallenger<Sha256>`.
fn build_prove_and_verify(
	n_permutations: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper: bool,
) -> Result<usize> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = PermutationTable::new(&mut cs);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_permutations],
	};

	// Deterministic witness (fixed seed) so the test is reproducible; any valid
	// 25-lane input is a legitimate Keccak-f permutation input.
	let mut rng = StdRng::from_seed([7u8; 32]);
	let events = repeat_with(|| StateMatrix::from_fn(|_| rng.next_u64()))
		.take(n_permutations)
		.collect::<Vec<_>>();

	let mut witness =
		WitnessIndex::<PackedType<OptimalUnderlier, B128>>::new(&cs, &allocator);
	witness.fill_table_parallel(&table, &events)?;

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// --- FIPS commitment + transcript: SHA-256 everywhere. ---
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

	// Honest proof must verify (SHA-256 commitment + transcript).
	binius_core::constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;

	// Soundness gate: a single flipped transcript byte must be rejected.
	if tamper {
		let mut bad = proof;
		let mid = bad.transcript.len() / 2;
		bad.transcript[mid] ^= 0xFF;
		let rejected = binius_core::constraint_system::verify::<
			U,
			CanonicalTowerFamily,
			Sha256,
			Sha256Compression,
			HasherChallenger<Sha256>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, bad)
		.is_err();
		anyhow::ensure!(rejected, "SOUNDNESS FAILURE: tampered proof was accepted");
	}

	Ok(proof_size)
}

/// Honest round-trip: prove + verify a batch of Keccak-f permutations under a
/// SHA-256-only commitment and transcript. Returns proof size in bytes.
pub fn prove_verify_keccak_fips(
	n_permutations: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<usize> {
	build_prove_and_verify(n_permutations, log_inv_rate, security_bits, false)
}

/// As [`prove_verify_keccak_fips`], but also asserts a one-byte-tampered proof is
/// rejected by the SHA-256 verifier.
pub fn prove_verify_keccak_fips_tamper_gated(
	n_permutations: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<usize> {
	build_prove_and_verify(n_permutations, log_inv_rate, security_bits, true)
}

#[cfg(test)]
mod tests {
	use super::*;

	/// M1 substrate gate (honest path): a batch of Keccak-f permutations proves
	/// and verifies under a SHA-256-only commitment + transcript. Same shape as
	/// Binius' `examples/keccak.rs` (512 perms, blowup 2, 100-bit security),
	/// FIPS-instantiated.
	#[test]
	fn fips_sha256_keccak_proof_round_trips() {
		let size = prove_verify_keccak_fips(512, 1, 100)
			.expect("FIPS (SHA-256) Keccak-f proof must verify");
		assert!(size > 0, "proof size must be non-zero");
		println!("FIPS SHA-256 Keccak-f proof verified; proof size = {size} bytes");
	}

	/// M1 soundness gate: the honest proof verifies, and a single flipped byte in
	/// the proof transcript is rejected by the SHA-256 verifier.
	#[test]
	fn fips_sha256_tampered_proof_is_rejected() {
		let size = prove_verify_keccak_fips_tamper_gated(512, 1, 100)
			.expect("honest proof must verify and tampered proof must be rejected");
		println!("FIPS SHA-256 tamper-reject gate passed; honest proof size = {size} bytes");
	}
}
