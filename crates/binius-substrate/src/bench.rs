// bench — timed prove/verify harness for the M2a in-circuit SHA3-256 gadget.
//
// This module is ADDITIVE: it reuses the exact FIPS wiring proven out in
// `sha3_gadget::prove_verify_sha3_256` (Sha256 Merkle commitment +
// Sha256Compression + HasherChallenger<Sha256>, CanonicalTowerFamily), but
// times `constraint_system::prove` and `constraint_system::verify` SEPARATELY
// with `std::time::Instant` so we can report a prove-time / verify-time / peak-
// RSS scaling table for a batch of `n` in-circuit SHA3-256 single-block hashes.
//
// The unit measured is: prove time for `n` in-circuit SHA3-256 single-block
// Keccak-f[1600] permutations (each ≈ one Keccak-256 node hash). See the header
// of `scripts/bench-sha3.sh` and the run report for the honest framing of the
// cross-system comparison against the Goldilocks 221 s / B=10 baseline — this is
// an INDICATIVE per-hash prover-cost datapoint, NOT an apples-to-apples number.

use anyhow::Result;
use std::time::Instant;

use binius_field::{arch::OptimalUnderlier, as_packed_field::PackedType};
use binius_m3::builder::{ConstraintSystem, Statement, WitnessIndex, B128};

use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::tower::CanonicalTowerFamily;
use binius_hash::sha2::Sha256Compression;
use sha2::Sha256;

use crate::sha3_gadget::{padded_state, Sha3SingleBlockTable};

/// Concrete packed field used throughout (same as M1 / M2a).
type P = PackedType<OptimalUnderlier, B128>;

/// One row of the scaling table: for a batch of `n` in-circuit SHA3-256 hashes at
/// the given `log_inv_rate` (blowup = 2^log_inv_rate), the separately-timed prove
/// and verify wall-times (ms), and the produced proof size (bytes).
#[derive(Debug, Clone, Copy)]
pub struct BenchResult {
	pub n: usize,
	pub log_inv_rate: usize,
	pub prove_ms: u128,
	pub verify_ms: u128,
	pub proof_bytes: usize,
}

/// Build the `Sha3SingleBlockTable` constraint system for `n` distinct single-
/// block messages, populate the witness through the gadget, then time
/// `constraint_system::prove` and `constraint_system::verify` SEPARATELY under
/// the FIPS SHA-256 commitment + transcript wiring.
///
/// Messages are `n` distinct 8-byte little-endian counters (`0, 1, 2, …`), each
/// a valid single-block SHA3-256 input; the content is immaterial to prover cost
/// (every row is one full Keccak-f[1600] permutation regardless of message).
///
/// Returns the timings and proof size. The honest proof is produced and then
/// verified; a verify failure surfaces as an `Err` (the bench never reports a
/// number for a proof that did not verify).
pub fn bench_sha3_256(n: usize, log_inv_rate: usize, security_bits: usize) -> Result<BenchResult> {
	assert!(n > 0, "bench_sha3_256 needs at least one message");

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let table = Sha3SingleBlockTable::new(&mut cs);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	// `n` distinct single-block messages (8-byte LE counters). Padding is exactly
	// the same FIPS-202 path M2a proves; message bytes don't change prover cost.
	let events: Vec<_> = (0..n as u64)
		.map(|i| padded_state(&i.to_le_bytes()))
		.collect();

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	table.keccakf.populate_state_in(&mut segment, &events)?;
	table.keccakf.populate(&mut segment)?;
	// `segment`/`table_witness` borrows end here (NLL) so the witness can be
	// consumed by the prover below.

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	let backend = binius_hal::make_portable_backend();

	// --- Timed PROVE (FIPS SHA-256 commitment + transcript). ---
	let t_prove = Instant::now();
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
		&backend,
	)?;
	let prove_ms = t_prove.elapsed().as_millis();

	let proof_bytes = proof.get_proof_size();

	// --- Timed VERIFY (same FIPS SHA-256 wiring). ---
	let t_verify = Instant::now();
	binius_core::constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;
	let verify_ms = t_verify.elapsed().as_millis();

	Ok(BenchResult {
		n,
		log_inv_rate,
		prove_ms,
		verify_ms,
		proof_bytes,
	})
}

// NOTE: intentionally no #[cfg(test)] module here. The timed harness reuses the
// exact FIPS wiring already gated by `sha3_gadget`'s M2a in-circuit + NIST-vector
// tests, so adding a bench-only test would just duplicate that coverage (and
// change the crate's authoritative "16 tests" count). The `bench_sha3` binary is
// the end-to-end exercise of this path.
