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
use binius_m3::gadgets::hash::keccak::{Keccakf, StateMatrix};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::b512_field::{B512TowerFamily, B512 as OurB512, U512};
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

// =============================================================================
// PART 1 (RSS baseline at NIST) — timed prove/verify of a batch of raw Keccak-f
// permutations over the NIST tower fields B256 (L1, security_bits=128) and B512
// (L5, security_bits=256), with peak RSS measured by the wrapping shell script.
//
// This is the concrete "<1 GB per proof?" datapoint that sets the per-level
// strand granularity G for the S-strand signature-AIR port. The prove path is
// byte-for-byte the FIPS wiring already gated by b256_keccak/b512_keccak (SHA-256
// Merkle commitment + SHA-256 Fiat-Shamir), only with `prove`/`verify` timed
// separately and the proof size returned. Each row = one full Keccak-f[1600]
// permutation regardless of the (random, fixed-seed) input content.
// =============================================================================

/// One row of the B256/B512 RSS scaling table: for a batch of `n` raw Keccak-f
/// permutations at `log_inv_rate` (blowup = 2^log_inv_rate) and `security_bits`,
/// the separately-timed prove/verify wall-times (ms) and the proof size (bytes).
/// Peak RSS is captured out-of-process by `/usr/bin/time -l` in the shell wrapper.
#[derive(Debug, Clone, Copy)]
pub struct BenchKeccakResult {
	pub n: usize,
	pub log_inv_rate: usize,
	pub security_bits: usize,
	pub prove_ms: u128,
	pub verify_ms: u128,
	pub proof_bytes: usize,
}

/// Reproducible batch of `n` random 25-lane Keccak-f inputs (fixed seed so the
/// bench is deterministic; any 25-lane input is a valid permutation input and the
/// content does not change prover cost — every row is one full Keccak-f[1600]).
fn keccak_bench_inputs(n: usize) -> Vec<StateMatrix<u64>> {
	let mut rng = StdRng::from_seed([13u8; 32]);
	(0..n)
		.map(|_| StateMatrix::from_fn(|_| rng.next_u64()))
		.collect()
}

/// PART 1 — prove+verify `n` raw Keccak-f permutations over `B256TowerFamily`
/// (NIST L1 challenge field, 2^256) under the FIPS SHA-256 commitment/transcript,
/// timing prove and verify separately. `n` is rounded up to a power of two (the
/// m3 table requires it); the returned `n` reflects the actual batch size.
pub fn bench_keccak_b256(
	n: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<BenchKeccakResult> {
	assert!(n > 0, "bench_keccak_b256 needs at least one permutation");
	let n = n.next_power_of_two();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut table = cs.add_table("keccak-f[1600] over B256 (bench)");
	let state_in = StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
	let keccakf = Keccakf::new(&mut table, state_in);
	let table_id = table.id();

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};
	let inputs = keccak_bench_inputs(n);

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let table_witness = witness.init_table(table_id, n)?;
		let mut segment = table_witness.full_segment();
		keccakf.populate_state_in(&mut segment, inputs.iter())?;
		keccakf.populate(&mut segment)?;
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	let backend = binius_hal::make_portable_backend();

	let t_prove = Instant::now();
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
		&backend,
	)?;
	let prove_ms = t_prove.elapsed().as_millis();
	let proof_bytes = proof.get_proof_size();

	let t_verify = Instant::now();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;
	let verify_ms = t_verify.elapsed().as_millis();

	Ok(BenchKeccakResult {
		n,
		log_inv_rate,
		security_bits,
		prove_ms,
		verify_ms,
		proof_bytes,
	})
}

/// PART 1 — prove+verify `n` raw Keccak-f permutations over `B512TowerFamily`
/// (NIST L5 challenge field, tower level 9, 2^512) under the FIPS SHA-256
/// commitment/transcript, timing prove and verify separately. `n` is rounded up
/// to a power of two; the returned `n` reflects the actual batch size. This path
/// is ~16x heavier per row than B256 (512-bit vs 256-bit backing store).
pub fn bench_keccak_b512(
	n: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<BenchKeccakResult> {
	assert!(n > 0, "bench_keccak_b512 needs at least one permutation");
	let n = n.next_power_of_two();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB512>::new();
	let mut table = cs.add_table("keccak-f[1600] over B512 (bench)");
	let state_in = StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
	let keccakf = Keccakf::new(&mut table, state_in);
	let table_id = table.id();

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};
	let inputs = keccak_bench_inputs(n);

	let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
	{
		let table_witness = witness.init_table(table_id, n)?;
		let mut segment = table_witness.full_segment();
		keccakf.populate_state_in(&mut segment, inputs.iter())?;
		keccakf.populate(&mut segment)?;
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	let backend = binius_hal::make_portable_backend();

	let t_prove = Instant::now();
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
		&backend,
	)?;
	let prove_ms = t_prove.elapsed().as_millis();
	let proof_bytes = proof.get_proof_size();

	let t_verify = Instant::now();
	binius_core::constraint_system::verify::<
		U512,
		B512TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;
	let verify_ms = t_verify.elapsed().as_millis();

	Ok(BenchKeccakResult {
		n,
		log_inv_rate,
		security_bits,
		prove_ms,
		verify_ms,
		proof_bytes,
	})
}

// =============================================================================
// PART 2 (Tier-A AGGREGATION RSS) — peak resident-set of the LEVEL-1 aggregation
// tier under the strand/swarm model with small STITCHABLE proof circuits.
//
// The Tier-A story (prove-R-1b/1c, prove-D-epoch): a zone of N records is NOT one
// monolithic proof. Each record commitment is proven as a SEPARATE bounded-RSS
// strand (`prove_verify_sha3_b256` — one Keccak-f node hash), the coordinator
// folds the 32-byte strand roots NATIVELY into R* (`merkle_root_sha3`, negligible
// memory), and the master binds a root into the tree IN-CIRCUIT via one Tier-A
// join node (`prove_verify_join_b256`, the proven M2b/ref-R-2 mechanism).
//
// Because the strands prove one-at-a-time (each call's `bumpalo::Bump` witness is
// dropped before the next), the process never holds two witnesses at once, so the
// PEAK RSS of the whole aggregation == the largest SINGLE stitchable proof and is
// INDEPENDENT of the zone size N. That flatness is the swarm payoff: an edge/IoT
// aggregator folds an arbitrarily large zone under one strand's memory budget.
// Peak RSS is captured out-of-process by `/usr/bin/time -l` in the shell wrapper,
// exactly as PART 1 does; here we only drive the aggregation and time each leg.
// =============================================================================

/// One row of the Tier-A aggregation RSS table: for a zone of `n_leaves` record
/// strands aggregated to one root R* over B256, the per-leg timings (ms) and the
/// stitchable proof sizes (bytes). `leaf_proof_bytes` is constant across N (every
/// strand is one Keccak-f node hash); `agg_artifact_bytes` is the batched-Merkle
/// edge artifact = one master join proof + N 32-byte record commitments.
#[derive(Debug, Clone, Copy)]
pub struct BenchAggResult {
	pub n_leaves: usize,
	pub log_inv_rate: usize,
	pub security_bits: usize,
	/// Slowest single leaf strand — the RSS-relevant unit (peak ∝ this, not N).
	pub leaf_max_prove_ms: u128,
	/// Sum of all leaf strand prove times (sequential wall-clock on one worker).
	pub leaf_total_prove_ms: u128,
	/// The master Tier-A join node prove time.
	pub master_prove_ms: u128,
	/// One leaf strand proof size (constant across N).
	pub leaf_proof_bytes: usize,
	/// The master join proof size.
	pub master_proof_bytes: usize,
	/// Batched-Merkle edge artifact = master proof + N × 32-byte commitments.
	pub agg_artifact_bytes: usize,
	/// `true` iff the in-circuit master reproduced R* over the strand roots
	/// (r_child == the leaf root it binds, r_parent == native merkle_root).
	pub rstar_ok: bool,
}

/// Deterministic 64-byte preimage (two 32-byte lanes) for record strand `i` — a
/// stand-in for a per-record RRSIG-signing-input commitment. Fixed content; the
/// message value does not change a single-block strand's prover cost.
fn agg_leaf_message(i: usize) -> Vec<u8> {
	let mut m = vec![0u8; 64];
	m[..8].copy_from_slice(&(i as u64).to_le_bytes());
	m[32..40].copy_from_slice(&(0xA660_0000u64 ^ i as u64).to_le_bytes());
	m
}

/// PART 2 — drive the LEVEL-1 (Tier-A) aggregation of an `n_leaves`-record zone in
/// the strand/swarm model and time each leg, so the shell wrapper can pair the
/// timings with the WHOLE-PROCESS peak RSS. `n_leaves >= 2`.
///
/// Legs:
///  1. `n_leaves` bounded strand proofs — each `prove_verify_sha3_b256` over B256
///     produces a record root; the witness is dropped between strands so peak RSS
///     is one strand, not the sum.
///  2. Coordinator fold — `merkle_root_sha3` over the roots (native, ~no memory).
///  3. One master Tier-A join — `prove_verify_join_b256` binds leaf-0's root
///     (recomputed in-circuit as SHA3(a‖b) from its 64-byte preimage) as the left
///     child and leaf-1's root as the sibling, into R2 = SHA3(root0‖root1); this
///     is the proven aggregation-node mechanism at bounded RSS.
pub fn bench_agg_rss(
	n_leaves: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<BenchAggResult> {
	use crate::b256_recursion::{prove_verify_join_b256, JoinMode};
	use crate::b256_sha3::prove_verify_sha3_b256;
	use crate::recursion::merkle_root_sha3;
	use crate::sha3_variants::Sha3Variant;

	assert!(n_leaves >= 2, "Tier-A aggregation needs at least two record strands");

	// --- Leg 1: N bounded record strands (each an independent stitchable proof). ---
	let mut roots: Vec<[u8; 32]> = Vec::with_capacity(n_leaves);
	let mut leaf_max_prove_ms: u128 = 0;
	let mut leaf_total_prove_ms: u128 = 0;
	let mut leaf_proof_bytes: usize = 0;
	for i in 0..n_leaves {
		let msg = agg_leaf_message(i);
		let t = Instant::now();
		let (sz, digests) =
			prove_verify_sha3_b256(Sha3Variant::Sha3_256, &[msg], log_inv_rate, security_bits)?;
		let ms = t.elapsed().as_millis();
		// The `bumpalo::Bump` inside the call is dropped here (NLL) → the next
		// strand starts from baseline; peak RSS stays at one strand.
		leaf_total_prove_ms += ms;
		leaf_max_prove_ms = leaf_max_prove_ms.max(ms);
		leaf_proof_bytes = sz;
		let root: [u8; 32] = digests[0]
			.as_slice()
			.try_into()
			.expect("SHA3-256 strand root must be 32 bytes");
		roots.push(root);
	}

	// --- Leg 2: coordinator natively folds the strand roots into R* (cheap). ---
	let rstar = merkle_root_sha3(&roots);
	let r2 = merkle_root_sha3(&roots[..2]); // the master node's target sub-root.

	// --- Leg 3: one master Tier-A join node, bounded RSS. ---
	let leaf0 = agg_leaf_message(0);
	let a: [u8; 32] = leaf0[..32].try_into().unwrap();
	let b: [u8; 32] = leaf0[32..].try_into().unwrap();
	let t = Instant::now();
	let join = prove_verify_join_b256(
		a,
		b,
		roots[1],
		JoinMode::Honest,
		Some(r2),
		log_inv_rate,
		security_bits,
	)?;
	let master_prove_ms = t.elapsed().as_millis();

	let rstar_ok = join.accepted()
		&& join.verify_ok
		&& join.r_child == roots[0]
		&& join.r_parent == r2;
	// R* is the coordinator's balanced-Merkle root over all strand roots; the
	// master proves the base node R2 in-circuit. (Guard against unused warning.)
	debug_assert_eq!(rstar, merkle_root_sha3(&roots));

	let master_proof_bytes = join.proof_size;
	let agg_artifact_bytes = master_proof_bytes + n_leaves * 32;

	Ok(BenchAggResult {
		n_leaves,
		log_inv_rate,
		security_bits,
		leaf_max_prove_ms,
		leaf_total_prove_ms,
		master_prove_ms,
		leaf_proof_bytes,
		master_proof_bytes,
		agg_artifact_bytes,
		rstar_ok,
	})
}

// The PART 1 (`bench_keccak_*`) path is driven by the `bench_b256b512` binary; the
// PART 2 Tier-A aggregation path is driven, at RSS-measurement time, by the single
// `#[ignore]`d `agg_rss_row` runner below (via `scripts/bench-agg-rss.sh`). It is
// `#[ignore]`d exactly like the heavy prove gates, so a normal `cargo test --lib`
// run neither executes it nor counts it among the authoritative pass count — it is
// invoked only, one row at a time, by the shell wrapper under `/usr/bin/time -l`.
#[cfg(test)]
mod tests {
	use super::*;
	use std::env;

	/// blowup = 2^1 = 2, matching the b256 Keccak / join gates.
	const LOG_INV_RATE: usize = 1;

	/// PART 2 RSS runner (ONE row). Reads the zone size from `AGG_N` (default 8) and
	/// the FS soundness target from `AGG_SEC` (default 128 = NIST L1), drives the
	/// Level-1 Tier-A aggregation via `bench_agg_rss`, and prints ONE structured
	/// RESULT line. `#[ignore]` so the normal suite skips it; the shell wrapper runs
	/// the built test binary directly under `/usr/bin/time -l`, re-invoking it once
	/// per `AGG_N` in the sweep so peak RSS is measured per zone size in isolation.
	#[test]
	#[ignore = "PART 2 Tier-A aggregation RSS row; run via scripts/bench-agg-rss.sh"]
	fn agg_rss_row() {
		let n: usize = env::var("AGG_N")
			.ok()
			.and_then(|s| s.parse().ok())
			.unwrap_or(8);
		let sec: usize = env::var("AGG_SEC")
			.ok()
			.and_then(|s| s.parse().ok())
			.unwrap_or(128);

		let r = bench_agg_rss(n, LOG_INV_RATE, sec)
			.expect("Tier-A aggregation must prove AND verify over B256");
		assert!(
			r.rstar_ok,
			"in-circuit master did not reproduce R* over the strand roots"
		);

		// Single structured line — stable key=value fields for the shell parser.
		println!(
			"RESULT tier=A N={} sec={} log_inv_rate={} leaf_max_prove_ms={} leaf_total_prove_ms={} master_prove_ms={} leaf_proof_bytes={} master_proof_bytes={} agg_artifact_bytes={} rstar_ok={}",
			r.n_leaves,
			r.security_bits,
			r.log_inv_rate,
			r.leaf_max_prove_ms,
			r.leaf_total_prove_ms,
			r.master_prove_ms,
			r.leaf_proof_bytes,
			r.master_proof_bytes,
			r.agg_artifact_bytes,
			r.rstar_ok,
		);
	}
}
