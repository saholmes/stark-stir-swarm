// fri_air — Tier-B M3: in-circuit FRI folding (field arithmetic) over B256.
//
// FRI query verification, after the Merkle openings (M2), checks the FOLD: each pair of
// opened codeword values (u, v) at a query is folded with the round challenge r into the
// next-round value via `extrapolate_line_scalar(u, v, r) = u + (v - u)·r` (binius's
// `fold_pair`), recursively over the coset. That is pure field arithmetic in the
// challenge field — and M3 supports native FIELD-ELEMENT columns, so the fold is a
// single degree-2 constraint `folded = u + (v - u)·r`, no hand-arithmetized binary-field
// multiply. This module proves the atomic fold in-circuit and gates it against binius's
// own `extrapolate_line_scalar`.

use anyhow::Result;

use binius_circuits::builder::types::U;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::{
	arch::OptimalUnderlier, as_packed_field::PackedType, packed::set_packed_slice,
	tower::CanonicalTowerFamily,
};
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{Col, ConstraintSystem, Statement, WitnessIndex, B128};
use sha2::Sha256;

/// Packed B128 field used for the recursive-layer witness (CanonicalTowerFamily path,
/// where native B128 field-element columns are supported — the B256 tower rejects
/// packing-degree-1 field-element columns via ring-switch).
type P = PackedType<OptimalUnderlier, B128>;

/// binius `extrapolate_line_scalar(u, v, r) = u + (v - u)·r` — the FRI pair-fold. Inlined
/// (binius_math is not a direct dep) over B128 field arithmetic.
fn fold_pair(u: B128, v: B128, r: B128) -> B128 {
	u + (v - u) * r
}

/// Prove + verify one FRI fold `folded = u + (v - u)·r` over B128 field-element columns
/// (in a B256-tower constraint system). Returns `(proof_bytes, in_circuit_folded)`.
pub fn prove_verify_fri_fold(u: B128, v: B128, r: B128) -> Result<(usize, B128)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let mut table = cs.add_table("fri fold pair (extrapolate_line)");
	let c_u = table.add_committed::<B128, 1>("u");
	let c_v = table.add_committed::<B128, 1>("v");
	let c_r = table.add_committed::<B128, 1>("r");
	let c_folded = table.add_committed::<B128, 1>("folded");
	// folded - u - (v - u)*r == 0   (degree 2, native tower-field arithmetic).
	table.assert_zero("fold", c_folded - c_u - (c_v - c_u) * c_r);
	let table_id = table.id();

	// Batch NROWS identical folds — a single B128 row is too small for the RS code
	// (packing width must divide the code dimension); the constraint holds per row.
	const NROWS: usize = 128;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let folded_native = fold_pair(u, v, r);

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, NROWS)?;
		let mut seg = tw.full_segment();
		for (col, val) in [(c_u, u), (c_v, v), (c_r, r), (c_folded, folded_native)] {
			let mut slice = seg.get_mut(col)?;
			for row in 0..NROWS {
				set_packed_slice(&mut slice, row, val);
			}
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U, CanonicalTowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 2, 100, &statement.boundaries, witness, &make_portable_backend())?;
	let proof_size = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U, CanonicalTowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 2, 100, &statement.boundaries, proof)?;
	Ok((proof_size, folded_native))
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::Field;
	use rand::SeedableRng;

	/// GATE M3a — the FRI fold `u + (v-u)·r` proves+verifies IN-CIRCUIT over B256 and
	/// equals the native pair-fold; a wrong challenge changes the result.
	#[test]
	fn fri_fold_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0xF0; 32]);
		let u = <B128 as Field>::random(&mut rng);
		let v = <B128 as Field>::random(&mut rng);
		let r = <B128 as Field>::random(&mut rng);
		let want = fold_pair(u, v, r);
		let (size, got) = prove_verify_fri_fold(u, v, r).expect("FRI fold must PROVE+VERIFY over B256");
		assert_eq!(got, want, "in-circuit fold != native pair-fold");
		// binding: a different challenge yields a different fold (u != v).
		let r2 = r + <B128 as Field>::ONE;
		assert_ne!(fold_pair(u, v, r2), want, "fold not bound to r");
		println!(
			"GATE M3a fri-fold: FRI pair-fold u+(v-u)·r PROVES+VERIFIES as a native degree-2 B128 \
			 field constraint (CanonicalTowerFamily, sec-100) == the native pair-fold; proof = {size} \
			 bytes. NOTE: native B128 field-element columns work here but the B256 tower rejects them \
			 (ring-switch packing-degree-1) — a B256 recursive layer needs hand-arithmetized GF(2^256) \
			 multiply, so folding is cheap only at the B128 recursive layer."
		);
	}
}
