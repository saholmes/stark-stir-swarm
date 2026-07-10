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

/// PoC — prove+verify `n` Grøstl-256 P-permutations over the SAME field/commitment
/// wiring as `bench_sha3_256` (CanonicalTowerFamily / B128, SHA-256 commit + FS), so
/// Grøstl-vs-Keccak verify is an apples-to-apples hash comparison. Grøstl's state is
/// 64 B8 (byte) columns = a 512-bit permutation vs Keccak's 1600-bit state — the
/// "narrow hash" whose verify cost we want to quantify against Keccak's ~1.4 s floor.
/// (Grøstl is a SHA-3 finalist, NOT FIPS-standard — this measures the narrow-hash
/// ceiling; the production FIPS narrow master would be an M3 SHA-256.)
pub fn bench_groestl_perm(n: usize, log_inv_rate: usize, security_bits: usize) -> Result<BenchResult> {
	use binius_m3::builder::B8;
	use binius_m3::gadgets::hash::groestl::{Permutation, PermutationVariant};

	assert!(n > 0, "bench_groestl_perm needs at least one permutation");
	let n = n.next_power_of_two();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let mut table = cs.add_table("groestl P-permutation (bench)");
	let input = table.add_committed_multiple::<B8, 8, 8>("state_in");
	let perm = Permutation::new(&mut table, PermutationVariant::P, input);
	let table_id = table.id();

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let mut rng = StdRng::from_seed([7u8; 32]);
	let in_states: Vec<[B8; 64]> = (0..n)
		.map(|_| std::array::from_fn(|_| <B8 as binius_field::Field>::random(&mut rng)))
		.collect();

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	{
		let table_witness = witness.init_table(table_id, n)?;
		let mut segment = table_witness.full_segment();
		perm.populate_state_in(&mut segment, in_states.iter())?;
		perm.populate(&mut segment)?;
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	let backend = binius_hal::make_portable_backend();

	let t_prove = Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U,
		CanonicalTowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, witness, &backend)?;
	let prove_ms = t_prove.elapsed().as_millis();
	let proof_bytes = proof.get_proof_size();

	let t_verify = Instant::now();
	binius_core::constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;
	let verify_ms = t_verify.elapsed().as_millis();

	Ok(BenchResult { n, log_inv_rate, prove_ms, verify_ms, proof_bytes })
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

	// =========================================================================
	// PART 3 (PER-CIRCUIT-TYPE prove-RSS) — the atomic stitchable circuits the
	// streaming/"sliver" prover schedules to verify a signature. A full verify
	// decomposes into a KNOWN LIST of these circuits (see the per-scheme circuit
	// inventory); because the sliver prover proves them one-at-a-time, the peak
	// prover RSS of the WHOLE signature == the max over its circuit types. This
	// runner measures ONE instance of each circuit type so the shell wrapper can
	// pair it (under /usr/bin/time -l) with the whole-process peak RSS — the
	// per-circuit memory budget the sliver prover must fit.
	//
	// Circuits (CKT env):
	//   modmul — the non-native modular multiply `ModMul<W>` (nonnative::
	//            prove_verify::<W>), the dominant RSA/EC circuit; RSS ~ (W/512)^2.
	//            MM_W selects the column width, MM_N the operand bit-width (must
	//            satisfy 2*MM_N+1 <= MM_W). Scheme widths: Ed25519 (512,255),
	//            P-256 (1024,256), RSA-496 (1024,496), RSA-1024 (2048,1024),
	//            RSA-2048 (8192,2048), ML-DSA mod-q (64,23).
	//   keccak — one Keccak-f[1600] permutation over B256 (bench_keccak_b256, N=1)
	//            — the SHA3/SHAKE block underlying ML-DSA hashing, DNS commitments,
	//            and the aggregation leaves.
	//   join   — one Tier-A batched-Merkle aggregation node (prove_verify_join_b256).

	/// Little-endian W-bit vector of a BigUint (num-bigint, a dev-dep on the
	/// `cargo test` build path — this whole module is `#[cfg(test)]`).
	fn to_bits_w(v: &num_bigint::BigUint, w: usize) -> Vec<bool> {
		let bytes = v.to_bytes_le();
		(0..w)
			.map(|k| {
				let byte = k / 8;
				byte < bytes.len() && (bytes[byte] >> (k % 8)) & 1 == 1
			})
			.collect()
	}

	/// One honest `ModMul<W>` row for `n`-bit operands under an `n`-bit modulus.
	/// The RSS depends only on (W, n) — the trace geometry — not the modulus value,
	/// so a fixed near-`2^n` modulus/operands is a faithful stand-in for the field
	/// prime. Returns `(m_bits, row)`.
	fn modmul_fixture(n: usize, w: usize) -> (Vec<bool>, crate::nonnative::ModMulRow) {
		use num_bigint::BigUint;
		let one = BigUint::from(1u8);
		let m = (&one << n) - &one; // 2^n - 1 (odd), a valid n-bit modulus
		let a = (&one << n) - BigUint::from(3u8);
		let b = (&one << n) - BigUint::from(5u8);
		let prod = &a * &b;
		let q = &prod / &m;
		let r = &prod % &m;
		(
			to_bits_w(&m, w),
			crate::nonnative::ModMulRow {
				a: to_bits_w(&a, w),
				b: to_bits_w(&b, w),
				q: to_bits_w(&q, w),
				r: to_bits_w(&r, w),
			},
		)
	}

	/// Prove+verify ONE `ModMul<W>` over B256 at operand width `n`, timing prove and
	/// verify SEPARATELY; returns `(proof_bytes, prove_ms, verify_ms)`. The
	/// whole-process peak RSS (prove-dominated) is captured externally by the wrapper.
	fn run_modmul<const W: usize>(n: usize) -> (usize, u128, u128) {
		assert!(2 * n + 1 <= W, "ModMul needs 2n+1 <= W (n={n}, W={W})");
		let (m_bits, row) = modmul_fixture(n, W);
		crate::nonnative::prove_verify_timed::<W>(&m_bits, n, &[row])
			.expect("ModMul must prove AND verify over B256")
	}

	/// One honest raw-limb-product row `p = a*b` for `n`-bit operands in W-bit columns.
	fn limbproduct_fixture(n: usize, w: usize) -> crate::nonnative::LimbProductRow {
		use num_bigint::BigUint;
		let one = BigUint::from(1u8);
		let a = (&one << n) - BigUint::from(3u8);
		let b = (&one << n) - BigUint::from(5u8);
		let p = &a * &b; // < 2^{2n} <= 2^W
		crate::nonnative::LimbProductRow {
			a: to_bits_w(&a, w),
			b: to_bits_w(&b, w),
			p: to_bits_w(&p, w),
		}
	}

	/// Prove+verify ONE `LimbProduct<W>` (raw n-bit×n-bit multiply, W=2n) over B256 —
	/// the atomic sliver strand of the limb-decomposed big-integer multiply.
	fn run_limbproduct<const W: usize>(n: usize) -> (usize, u128, u128) {
		assert!(2 * n <= W, "LimbProduct needs 2n <= W (n={n}, W={W})");
		let row = limbproduct_fixture(n, W);
		crate::nonnative::prove_verify_limb_timed::<W>(n, &[row])
			.expect("LimbProduct must prove AND verify over B256")
	}

	/// PART 3 runner (ONE circuit). `CKT` selects the circuit type; the remaining
	/// env vars parameterize it. Prints ONE structured RESULT line. `#[ignore]` so
	/// the normal suite skips it; the shell wrapper runs the built test binary
	/// directly under `/usr/bin/time -l`, once per circuit, to capture peak RSS.
	#[test]
	#[ignore = "PART 3 per-circuit prove-RSS row; run via scripts/bench-circuit-rss.sh"]
	fn circuit_rss_row() {
		let ckt = env::var("CKT").unwrap_or_else(|_| "modmul".to_string());
		match ckt.as_str() {
			"modmul" => {
				let w: usize = env::var("MM_W").ok().and_then(|s| s.parse().ok()).unwrap_or(1024);
				let n: usize = env::var("MM_N").ok().and_then(|s| s.parse().ok()).unwrap_or(496);
				let (sz, pms, vms) = match w {
					64 => run_modmul::<64>(n),
					128 => run_modmul::<128>(n),
					256 => run_modmul::<256>(n),
					512 => run_modmul::<512>(n),
					1024 => run_modmul::<1024>(n),
					2048 => run_modmul::<2048>(n),
					4096 => run_modmul::<4096>(n),
					8192 => run_modmul::<8192>(n),
					other => panic!("unsupported MM_W={other}; add a match arm in circuit_rss_row"),
				};
				println!("RESULT circuit=ModMul W={w} n={n} prove_ms={pms} verify_ms={vms} proof_bytes={sz}");
			}
			"limbproduct" => {
				// The raw limb-product strand of LimbMul<L>: an L×L->2L multiply, W=2L.
				let l: usize = env::var("LP_L").ok().and_then(|s| s.parse().ok()).unwrap_or(256);
				let (sz, pms, vms) = match l {
					64 => run_limbproduct::<128>(64),
					128 => run_limbproduct::<256>(128),
					256 => run_limbproduct::<512>(256),
					512 => run_limbproduct::<1024>(512),
					other => panic!("unsupported LP_L={other}; add a match arm in circuit_rss_row"),
				};
				println!("RESULT circuit=LimbProduct W={} n={l} prove_ms={pms} verify_ms={vms} proof_bytes={sz}", 2 * l);
			}
			"keccak" => {
				// KECCAK_N = number of Keccak-f permutations proven as ROWS in one
				// narrow table (fixed width = one Keccak-f state). Verify is expected
				// ~constant in N (verify scales with column WIDTH, not rows) — the
				// property that makes a batched-Merkle master's verify N-independent.
				let kn: usize = env::var("KECCAK_N").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
				let r = bench_keccak_b256(kn, 1, 128).expect("Keccak-f must prove+verify over B256");
				println!(
					"RESULT circuit=Keccakf W=1600 n={} prove_ms={} verify_ms={} proof_bytes={}",
					r.n, r.prove_ms, r.verify_ms, r.proof_bytes
				);
			}
			"groestl" => {
				// Narrow-hash PoC: N Grøstl-256 P-permutations (512-bit byte-column
				// state) over B128, same commit/FS wiring as keccak128.
				let gn: usize = env::var("GROESTL_N").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
				let r = bench_groestl_perm(gn, 2, 100).expect("Groestl perm must prove+verify");
				println!(
					"RESULT circuit=Groestl W=512 n={} prove_ms={} verify_ms={} proof_bytes={}",
					r.n, r.prove_ms, r.verify_ms, r.proof_bytes
				);
			}
			"keccak128" => {
				// Keccak-f over B128 (CanonicalTowerFamily) — the same-field baseline
				// the Grøstl PoC is compared against.
				let kn: usize = env::var("KECCAK_N").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
				let r = bench_sha3_256(kn, 2, 100).expect("Keccak-f (B128) must prove+verify");
				println!(
					"RESULT circuit=Keccak128 W=1600 n={} prove_ms={} verify_ms={} proof_bytes={}",
					r.n, r.prove_ms, r.verify_ms, r.proof_bytes
				);
			}
			"join" => {
				use crate::b256_recursion::{prove_verify_join_b256, JoinMode};
				use crate::recursion::merkle_root_sha3;
				let a = [0x11u8; 32];
				let b = [0x22u8; 32];
				let d = [0x33u8; 32];
				let r2 = merkle_root_sha3(&[merkle_root_sha3(&[a, b]), d]);
				// r_child = SHA3(a||b); r_parent = SHA3(r_child||d) = merkle node.
				let rstar = {
					use sha3::{Digest, Sha3_256};
					let mut h = Sha3_256::new();
					h.update(a);
					h.update(b);
					let rc: [u8; 32] = h.finalize().into();
					let mut h2 = Sha3_256::new();
					h2.update(rc);
					h2.update(d);
					let rp: [u8; 32] = h2.finalize().into();
					rp
				};
				let _ = r2;
				let t = Instant::now();
				let j = prove_verify_join_b256(a, b, d, JoinMode::Honest, Some(rstar), 1, 128)
					.expect("join must prove+verify over B256");
				let ms = t.elapsed().as_millis();
				assert!(j.accepted() && j.verify_ok, "join must accept");
				println!(
					"RESULT circuit=Join W=256 n=1 prove_ms={} proof_bytes={} wall_ms={}",
					ms, j.proof_size, ms
				);
			}
			other => panic!("unknown CKT='{other}': expected modmul | keccak | join"),
		}
	}
}
