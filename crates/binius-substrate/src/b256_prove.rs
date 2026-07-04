// M3 (kappa_FS) Phase-1b — a REAL end-to-end Binius proof over the 256-bit
// challenge field `B256TowerFamily` at NIST L1 (security_bits = 128), with the
// packing machinery of `b256_packed.rs` (WALL #1, closed) doing the work.
//
// HONEST SCOPE NOTE. The deliverable asked for `prove_verify_keccak_b256` proving
// M1's Keccak `PermutationTable` under `Tower = B256TowerFamily`. That is blocked
// by an INDEPENDENT wall (WALL #2): Binius's Keccak gadget is hard-coded to
// `BinaryField128b` as its top field — `Keccakf::new(&mut TableBuilder /*=<B128>*/)`
// and `populate<P: PackedFieldIndexable<Scalar = BinaryField128b>>`. So the gadget
// only ever builds a `ConstraintSystem<BinaryField128b>`, whereas
// `prove::<_, B256TowerFamily, _>` requires a `ConstraintSystem<B256>`
// (`FExt<B256TowerFamily> = B256`). Reconciling them needs the Keccak gadget
// (and the m3 gadget layer) to be generic over its top field — a large,
// non-minimal change to binius_m3, out of scope for the packing milestone.
// (Confirmed empirically: passing a `TableBuilder<B256>` to `Keccakf::new` is an
// E0308 type error.)
//
// So this module builds a DIFFERENT, minimal-but-genuine constraint system
// generically over `ConstraintSystem<B256>` (the M3 builder IS generic over its
// top field): committed columns `x, y: B8` with `x*x - y = 0`, honestly filled
// `y = x^2`. `prove::<U256, B256TowerFamily, ..>` COMPILES (WALL #1 closed) and
// runs the prover up to the ring-switch reduction.
//
// WALL #3 (deepest — in binius_core, NOT a gadget). The prover then fails inside
// the ring-switch PCS reduction with `PackingDegreeNotSupported { kappa: 5 }`.
// Root cause (binius/crates/core/src/ring_switch/common.rs:162):
//   `let kappa = F::TOWER_LEVEL.checked_sub(tower_level)...`   // F = FExt = B256
// and the dispatch tables (tower_tensor_algebra.rs:26/39, prove.rs:288,
// verify.rs) enumerate ONLY `kappa ∈ {0,1,2,3,4,7}` mapping to B128..B1 — i.e.
// they STRUCTURALLY assume `FExt::TOWER_LEVEL == 7` (a 128-bit top field). Our
// `B256` is tower level 8, so every packing degree is shifted by +1: committing
// at B8 (level 3) gives kappa = 8-3 = 5 (unsupported); committing at any other
// level either lands on an unsupported kappa or on an arm that constructs the
// WRONG subfield's `RingSwitchEqInd` (verified: committing at B16 fails earlier
// with "evals cannot be embedded into base field" — a mismatch, not a false
// accept). The ring-switch tensor algebra is the core of Binius's small-field
// PCS; making it 256-bit-aware is a substantial re-derivation of binius_core,
// far beyond the packing milestone.
//
// NET: the kappa_FS "swap the B128 tower slot for a 256-bit field" architecture
// closes the FRI query-count math over 2^256 (b256_field.rs signal, passing) and
// the PACKING wall (WALL #1, closed here), but a real Binius proof is blocked by
// the ring-switch layer being hard-coded to a 128-bit (tower-level-7) FExt.
// The functions below build + drive the prover to that precise, documented wall.

use anyhow::Result;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::BinaryField;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{
	Col, ConstraintSystem, Statement, TableFiller, TableId, TableWitnessSegment, WitnessIndex, B8,
};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::Sha256;

// Our 256-bit tower field is the top/challenge field of the constraint system.
use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};

/// A minimal one-table constraint system over the top field `F`: committed `x, y`
/// with the constraint `x*x = y`.
struct SquareTable {
	table_id: TableId,
	x: Col<B8>,
	y: Col<B8>,
}

impl SquareTable {
	fn new(cs: &mut ConstraintSystem<OurB256>) -> Self {
		let mut table = cs.add_table("square");
		let x = table.add_committed::<B8, 1>("x");
		let y = table.add_committed::<B8, 1>("y");
		table.assert_zero("x_sq_eq_y", x * x - y);
		Self {
			table_id: table.id(),
			x,
			y,
		}
	}
}

impl TableFiller<OurB256> for SquareTable {
	type Event = u8;

	fn id(&self) -> TableId {
		self.table_id
	}

	fn fill<'a>(
		&'a self,
		rows: impl Iterator<Item = &'a Self::Event> + Clone,
		witness: &'a mut TableWitnessSegment<OurB256>,
	) -> Result<()> {
		let mut xs = witness.get_scalars_mut::<B8, 1>(self.x)?;
		let mut ys = witness.get_scalars_mut::<B8, 1>(self.y)?;
		for (i, ev) in rows.enumerate() {
			let xv = B8::new(*ev);
			xs[i] = xv;
			ys[i] = xv * xv;
		}
		Ok(())
	}
}

fn build_prove_verify_b256(
	n_rows: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper: bool,
) -> Result<usize> {
	// Force a power-of-two table size (M3 requires it for this table shape).
	let n_rows = n_rows.next_power_of_two();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = SquareTable::new(&mut cs);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};

	let mut rng = StdRng::from_seed([9u8; 32]);
	let events: Vec<u8> = (0..n_rows).map(|_| (rng.next_u32() & 0xff) as u8).collect();

	// Witness packed field is `PackedType<U256, B256> = B256` (width 1).
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	witness.fill_table_parallel(&table, &events)?;

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// FIPS commitment + transcript, and — crucially — challenge/extension field
	// `FExt<B256TowerFamily> = B256` (2^256): SHA-256 everywhere.
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

	// Honest proof must verify over the 256-bit challenge field.
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;

	if tamper {
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
		anyhow::ensure!(rejected, "SOUNDNESS FAILURE: tampered proof accepted over B256");
	}

	Ok(proof_size)
}

/// Attempt to prove + verify a minimal `x^2 = y` constraint system over the
/// 256-bit challenge field `B256TowerFamily` (SHA-256 commitment + transcript).
///
/// This COMPILES (WALL #1 closed) and drives Binius's real prover; it currently
/// returns `Err` from the ring-switch reduction (`PackingDegreeNotSupported`,
/// WALL #3 — binius_core hard-codes a 128-bit FExt). Returns the proof size on
/// success (unreachable until binius_core's ring-switch supports a level-8 FExt).
pub fn try_prove_verify_b256(
	n_rows: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper: bool,
) -> Result<usize> {
	build_prove_verify_b256(n_rows, log_inv_rate, security_bits, tamper)
}

/// The kappa_FS soundness signal: the tower-level of the challenge/extension field.
/// `B256` is tower level 8 (256-bit); the Binius ring-switch assumes level 7.
pub fn b256_top_field_bits() -> usize {
	<OurB256 as BinaryField>::N_BITS
}

#[cfg(test)]
mod tests {
	use super::*;

	/// THE MILESTONE STATE. `prove::<U256, B256TowerFamily, ..>` COMPILES and runs
	/// (WALL #1, the packing wall, is CLOSED). The prover then hits WALL #3: the
	/// binius_core ring-switch PCS is hard-coded to a 128-bit (tower-level-7) FExt,
	/// so a 256-bit FExt yields `PackingDegreeNotSupported { kappa: 5 }`. This test
	/// PINS that precise blocker: if binius_core's ring-switch ever supports a
	/// level-8 FExt, this test will start failing and signal that a real proof is
	/// now reachable. (It asserts the prover reaches and reports exactly WALL #3 —
	/// crucially, NOT a false accept.)
	#[test]
	fn prove_over_b256_reaches_ring_switch_wall() {
		assert_eq!(b256_top_field_bits(), 256, "challenge field must be 2^256");
		let res = try_prove_verify_b256(4096, 1, 128, false);
		match res {
			Ok(size) => panic!(
				"UNEXPECTED: a real proof verified over B256 at NIST L1 (size={size}). \
				 binius_core's ring-switch now supports a 256-bit FExt — update this test \
				 to a genuine verify + tamper-reject gate."
			),
			Err(e) => {
				let msg = format!("{e:#}");
				assert!(
					msg.contains("packing degree 5") || msg.contains("PackingDegreeNotSupported"),
					"expected the ring-switch 128-bit-FExt wall (packing degree 5), got: {msg}"
				);
				println!(
					"WALL #1 CLOSED (prove::<U256,B256TowerFamily> compiles + runs); \
					 blocked at WALL #3 (binius_core ring-switch pinned to 128-bit FExt): {msg}"
				);
			}
		}
	}
}
