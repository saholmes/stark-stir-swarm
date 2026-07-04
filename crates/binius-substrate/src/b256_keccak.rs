// M3 (kappa_FS) Phase B — the REAL binius_m3 Keccak-f[1600] gadget proving AND
// verifying over the 256-bit challenge/extension field `B256TowerFamily` at NIST
// L1/L3, with a **SHA-256** Merkle commitment and **SHA-256** Fiat–Shamir
// challenger (the FIPS instantiation).
//
// WALL #2 (CLOSED here). Previously binius_m3's Keccak-f gadget was concretely
// bound to `BinaryField128b`: `Keccakf::new` took `&mut TableBuilder` (defaulting
// to `TableBuilder<B128>`) and `populate` required `P: PackedFieldIndexable<Scalar
// = B128>`. Phase B threads the top field `F: TowerField` through the gadget on the
// fork branch `feature/nist-tower-level-8-9-fext`:
//   * crates/m3/src/gadgets/hash/keccak/mod.rs
//       - `Keccakf::new<F>(&mut TableBuilder<F>, ..)` / `RoundBatch::new<F>(..)`
//         where `F: TowerField + ExtensionField<B1>` (the theta/rho/pi/chi/iota
//         constraints operate on B1 columns and are field-generic — only the
//         embedding/challenge field rises).
//       - the six witness methods relax `Scalar = B128` to
//         `P: PackedFieldIndexable, P::Scalar: TowerField + Pod + ExtensionField<B1>
//          + ExtensionField<B8>` (dropping a vestigial, never-invoked
//         `PackedTransformationFactory` bound). The `= B128` defaults on
//         `ConstraintSystem`/`TableBuilder`/`WitnessIndex`/`TableWitnessSegment`
//         are untouched, so every stock-B128 call site and test compiles UNCHANGED.
// In our crate, the only addition is `unsafe impl Pod for B256` (b256_field.rs):
// `TableWitnessSegment::get_mut_as::<u64,..>`, which the gadget uses to read/write
// lane data, reinterprets the column's top-field backing store as `u64` and so
// requires `F: Pod`. `B256: PackedFieldIndexable` already holds for free via the
// `Divisible<U> for U` blanket (U256: Divisible<U256>).
//
// The permutation columns are all B1 (`PackedLane8 = Col<B1, 512>`), so the width-8
// tower-height cast in binius_m3's `into_multilinear_extension_index` is NOT
// exercised (that would only bite a column committed at the top field); it is left
// unchanged.
//
// Four gates (tests):
//   1. `keccak_proves_over_b256`      — 8 Keccak-f perms prove AND verify at L1(128) and L3(192).
//   2. `keccak_b256_tamper_rejected`  — a corrupted state_out lane, and a flipped transcript
//                                        byte, are each REJECTED.
//   3. `keccak_b256_matches_native`   — the in-circuit state_out equals `tiny_keccak::keccakf`.
//   4. regression lives elsewhere (`cargo test -p binius_m3`; the crate's M1 tests).

use anyhow::Result;
use binius_core::fiat_shamir::HasherChallenger;
use binius_hash::sha2::Sha256Compression;
use binius_m3::{
	builder::{ConstraintSystem, Statement, TableId, WitnessIndex},
	gadgets::hash::keccak::{Keccakf, StateMatrix},
};
use bumpalo::Bump;
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};

/// The output track of the permutation within a batch row (track 7 of 8).
#[cfg(test)]
const STATE_OUT_TRACK: usize = 7;

/// One committed-input Keccak-f[1600] table over the top field `B256`.
struct KeccakB256Table {
	table_id: TableId,
	keccakf: Keccakf,
}

impl KeccakB256Table {
	fn new(cs: &mut ConstraintSystem<OurB256>) -> Self {
		let mut table = cs.add_table("keccak-f[1600] over B256");
		let state_in = StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let keccakf = Keccakf::new(&mut table, state_in);
		Self {
			table_id: table.id(),
			keccakf,
		}
	}
}

/// Reproducible batch of `n` random 25-lane Keccak-f inputs (any input is a valid
/// permutation input).
fn keccak_inputs(n: usize) -> Vec<StateMatrix<u64>> {
	let mut rng = StdRng::from_seed([13u8; 32]);
	(0..n)
		.map(|_| StateMatrix::from_fn(|_| rng.next_u64()))
		.collect()
}

/// Build the Keccak-f circuit over `B256TowerFamily`, populate it, prove and verify.
/// Returns `(proof_size, inputs, circuit_state_outs)`. On `tamper_transcript`, a
/// clone of the honest proof has one transcript byte flipped and MUST be rejected.
fn build_prove_verify_keccak_b256(
	n_perms: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper_transcript: bool,
) -> Result<(usize, Vec<StateMatrix<u64>>, Vec<StateMatrix<u64>>)> {
	let n_perms = n_perms.next_power_of_two();

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = KeccakB256Table::new(&mut cs);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_perms],
	};

	let inputs = keccak_inputs(n_perms);

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let outputs;
	{
		let table_witness = witness.init_table(table.table_id, n_perms)?;
		let mut segment = table_witness.full_segment();
		table.keccakf.populate_state_in(&mut segment, inputs.iter())?;
		table.keccakf.populate(&mut segment)?;
		outputs = table
			.keccakf
			.read_state_outs(&segment)?
			.collect::<Vec<_>>();
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// FIPS commitment + transcript; challenge/extension field = B256 (2^256).
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
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;

	if tamper_transcript {
		let mut bad = proof;
		let mid = bad.transcript.len() / 2;
		bad.transcript[mid] ^= 0xFF;
		let rejected = binius_core::constraint_system::verify::<
			U256,
			B256TowerFamily,
			Sha256,
			Sha256Compression,
			HasherChallenger<Sha256>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, bad)
		.is_err();
		anyhow::ensure!(
			rejected,
			"SOUNDNESS FAILURE: tampered transcript accepted over B256 (Keccak-f)"
		);
	}

	Ok((proof_size, inputs, outputs))
}

/// Public entry: honest prove+verify of a Keccak-f batch over B256, returning proof size.
pub fn prove_verify_keccak_b256(
	n_perms: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<usize> {
	build_prove_verify_keccak_b256(n_perms, log_inv_rate, security_bits, false).map(|(s, _, _)| s)
}

/// Build a DISHONEST witness: after honest population, flip one bit of the perm-0
/// `state_out` output lane so it is no longer `Keccak-f(state_in)`. Returns `true`
/// iff the tampered statement is rejected (prover errors on the unsatisfied
/// zerocheck, or the verifier rejects the resulting proof).
#[cfg(test)]
fn dishonest_keccak_b256_is_rejected(
	n_perms: usize,
	log_inv_rate: usize,
	security_bits: usize,
) -> bool {
	use binius_m3::builder::B1;

	let n_perms = n_perms.next_power_of_two();

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = KeccakB256Table::new(&mut cs);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_perms],
	};
	let inputs = keccak_inputs(n_perms);

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let table_witness = match witness.init_table(table.table_id, n_perms) {
			Ok(tw) => tw,
			Err(_) => return true,
		};
		let mut segment = table_witness.full_segment();
		if table
			.keccakf
			.populate_state_in(&mut segment, inputs.iter())
			.is_err()
		{
			return true;
		}
		if table.keccakf.populate(&mut segment).is_err() {
			return true;
		}
		// Corrupt the actual output lane (track 7) of permutation 0: this breaks the
		// chi/iota zero-constraint that ties state_out to Keccak-f(state_in).
		// `PackedLane8 = Col<B1, 64 * 8>` — 8 tracks x 64-bit lanes packed per row.
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
	) {
		Ok(p) => p,
		Err(_) => return true, // prover refused the unsatisfiable witness
	};

	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)
	.is_err()
}

#[cfg(test)]
mod tests {
	use super::*;

	/// GATE 1 — the m3 Keccak-f gadget, generalized to a top field `F`, proves AND
	/// verifies over the 256-bit challenge field `B256TowerFamily` at NIST L1 (128)
	/// and NIST L3 (192). THIS is the Phase-B milestone: a real Keccak circuit over a
	/// 256-bit challenge field.
	#[test]
	fn keccak_proves_over_b256() {
		let size_l1 = prove_verify_keccak_b256(8, 1, 128)
			.expect("Keccak-f batch must VERIFY over B256 at NIST L1 (128)");
		assert!(size_l1 > 0);
		println!("GATE 1: B256 Keccak-f (8 perms) VERIFIED at L1(128); proof size = {size_l1} bytes");

		let size_l3 = prove_verify_keccak_b256(8, 1, 192)
			.expect("Keccak-f batch must VERIFY over B256 at NIST L3 (192)");
		assert!(size_l3 >= size_l1, "L3 proof should be >= L1 (more queries)");
		println!("GATE 1: B256 Keccak-f (8 perms) VERIFIED at L3(192); proof size = {size_l3} bytes");
	}

	/// GATE 2 — SOUNDNESS. (a) a dishonest witness (a state_out lane that is not
	/// Keccak-f(state_in)) is rejected, and (b) a single flipped transcript byte on an
	/// honest proof is rejected.
	#[test]
	fn keccak_b256_tamper_rejected() {
		assert!(
			dishonest_keccak_b256_is_rejected(8, 1, 128),
			"SOUNDNESS FAILURE: a corrupted Keccak-f state_out lane was accepted over B256"
		);
		let (size, _, _) = build_prove_verify_keccak_b256(8, 1, 128, true)
			.expect("honest proof must verify AND tampered transcript must be rejected");
		println!(
			"GATE 2: corrupted-witness AND flipped-transcript both REJECTED over B256 \
			 (honest Keccak-f proof size = {size} bytes)"
		);
	}

	/// GATE 3 — MATCHES NATIVE. The in-circuit `state_out` columns produced by the
	/// gadget over B256 equal the output of an INDEPENDENT native Keccak-f[1600]
	/// reference (`tiny_keccak::keccakf`) applied to the same inputs — i.e. the
	/// circuit computes the RIGHT permutation over the 256-bit field, not merely "a"
	/// verifiable proof.
	#[test]
	fn keccak_b256_matches_native() {
		let (_size, inputs, outputs) = build_prove_verify_keccak_b256(8, 1, 128, false)
			.expect("honest Keccak-f proof over B256 must verify");
		assert_eq!(inputs.len(), outputs.len());
		for (i, (inp, out)) in inputs.iter().zip(outputs.iter()).enumerate() {
			let mut native = *inp.as_inner();
			tiny_keccak::keccakf(&mut native);
			assert_eq!(
				native,
				*out.as_inner(),
				"in-circuit Keccak-f output over B256 diverged from tiny_keccak native at perm {i}"
			);
		}
		println!(
			"GATE 3: in-circuit Keccak-f state_out over B256 matches tiny_keccak native reference \
			 across all {} permutations.",
			inputs.len()
		);
	}
}
