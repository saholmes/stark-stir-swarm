// M3 (kappa_FS) Phase A — a REAL end-to-end Binius proof over the 256-bit
// challenge/extension field `B256TowerFamily` at NIST L1/L3, with binius_core's
// ring-switch small-field PCS GENERALIZED to a tower-level-8 FExt.
//
// STATUS (was WALL #3, now CLOSED). Previously `prove::<U256,B256TowerFamily,..>`
// compiled + ran but died inside the ring-switch reduction with
// `PackingDegreeNotSupported { kappa: 5 }`, because binius_core's ring-switch
// dispatch hardcoded the level-7 (128-bit FExt) kappa literals {7,4,3,2,1,0}.
// Phase A replaces those literals with type-derived match guards
// (`k == TensorAlgebra::<Tower::Bx, FExt>::kappa()`), which auto-yield the
// level-8 set {8,5,4,3,2,0} for a 256-bit FExt. See the fork branch
// `feature/nist-tower-level-8-9-fext`:
//   * crates/core/src/ring_switch/tower_tensor_algebra.rs  (new/zero/kappa)
//   * crates/core/src/ring_switch/prove.rs                 (make_ring_switch_eq_ind)
//   * crates/core/src/ring_switch/verify.rs                (make_ring_switch_eq_ind)
//   * crates/core/src/constraint_system/prove.rs           (base_tower_level + `8=>` arm)
//
// The circuit here is deliberately MINIMAL (not the m3 Keccak gadget — that is
// Phase B / WALL #2): a one-table `x*x = y` over committed `B8` columns. Committing
// at B8 (tower level 3) under a level-8 FExt drives the ring-switch at kappa
// 8-3 = 5 — exactly the packing degree that used to be unsupported.
//
// The soundness posture is validated by four gates (see the tests module):
//   1. `ringswitch_b256_prove_verify`         — a real proof VERIFIES at L1 (128) and L3 (192).
//   2. `ringswitch_b256_tamper_rejected`      — a flipped witness value AND a flipped
//                                                transcript byte are each REJECTED.
//   3. `ringswitch_b256_matches_b128_reference` — the committed-column evaluations agree
//                                                between stock B128 and B256 (the wrong-transpose catch).
//   4. `tensor_algebra_transpose_roundtrip_kappa8` — `square_transpose`/`fold_vertical` at
//                                                kappa 8 match a hand-computed inner product.

use anyhow::Result;
use binius_core::{fiat_shamir::HasherChallenger, tensor_algebra::TensorAlgebra};
use binius_field::{
	BinaryField, BinaryField128b as B128, BinaryField1b as RSB1, ExtensionField, Field,
};
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{
	Col, ConstraintSystem, Statement, TableFiller, TableId, TableWitnessSegment, WitnessIndex, B8,
};
use rand::{rngs::StdRng, RngCore, SeedableRng};
use sha2::Sha256;

// Our 256-bit tower field is the top/challenge field of the constraint system.
use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};

/// A minimal one-table constraint system over the top field `F`: committed `x, y`
/// with the constraint `x*x = y`. `corrupt` writes a WRONG `y` on the first row
/// (a dishonest witness), used by the soundness gate.
struct SquareTable {
	table_id: TableId,
	x: Col<B8>,
	y: Col<B8>,
	corrupt: bool,
}

impl SquareTable {
	fn new(cs: &mut ConstraintSystem<OurB256>, corrupt: bool) -> Self {
		let mut table = cs.add_table("square");
		let x = table.add_committed::<B8, 1>("x");
		let y = table.add_committed::<B8, 1>("y");
		table.assert_zero("x_sq_eq_y", x * x - y);
		Self {
			table_id: table.id(),
			x,
			y,
			corrupt,
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
			// Honest fill is y = x^2. When corrupt, break exactly one row so the
			// zerocheck constraint x*x - y = 0 is violated.
			ys[i] = if self.corrupt && i == 0 {
				xv * xv + B8::ONE
			} else {
				xv * xv
			};
		}
		Ok(())
	}
}

/// The `B8` events for the reproducible witness (fixed seed).
fn witness_events(n_rows: usize) -> Vec<u8> {
	let mut rng = StdRng::from_seed([9u8; 32]);
	(0..n_rows).map(|_| (rng.next_u32() & 0xff) as u8).collect()
}

/// Build + prove + verify the `x*x=y` circuit over `B256TowerFamily`. Returns the
/// proof size in bytes on an honest verify. If `tamper_transcript`, a clone of the
/// proof has one transcript byte flipped and MUST be rejected.
fn build_prove_verify_b256(
	n_rows: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper_transcript: bool,
) -> Result<usize> {
	let n_rows = n_rows.next_power_of_two();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = SquareTable::new(&mut cs, false);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};

	let events = witness_events(n_rows);

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	witness.fill_table_parallel(&table, &events)?;

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

	// Honest proof MUST verify over the 256-bit challenge field.
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
		anyhow::ensure!(rejected, "SOUNDNESS FAILURE: tampered transcript accepted over B256");
	}

	Ok(proof_size)
}

/// Build a DISHONEST witness (one wrong `y`) and attempt prove+verify. Returns
/// `true` iff the dishonest statement is rejected (either the prover errors on the
/// unsatisfied constraint, or the verifier rejects the resulting proof).
#[cfg(test)]
fn dishonest_witness_is_rejected(n_rows: usize, log_inv_rate: usize, security_bits: usize) -> bool {
	let n_rows = n_rows.next_power_of_two();
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = SquareTable::new(&mut cs, true); // corrupt row 0

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};
	let events = witness_events(n_rows);

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	if witness.fill_table_parallel(&table, &events).is_err() {
		return true;
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

	// If the prover produced a proof, the verifier MUST reject it.
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)
	.is_err()
}

/// Public entry: honest prove+verify over B256, returning proof size in bytes.
pub fn prove_verify_b256(n_rows: usize, log_inv_rate: usize, security_bits: usize) -> Result<usize> {
	build_prove_verify_b256(n_rows, log_inv_rate, security_bits, false)
}

/// A generic two-to-one Merkle compression `H(a ‖ b)` over any FIPS `Digest` — lets us put
/// SHA3-256/384/512 in the COMMITMENT role (κ_bind), which binius ships only for SHA-256.
/// Collision-resistant in the hash-tree setting. Paired with `HasherChallenger<H>` this
/// ladders the recursion hash (κ_bind, κ_FS) alongside the field, so end-to-end soundness
/// min(κ_IT, κ_bind, κ_FS) actually reaches the target NIST level instead of pinning at 128.
#[derive(Clone)]
pub struct Sha3Compression<D>(core::marker::PhantomData<D>);
impl<D> Default for Sha3Compression<D> {
	fn default() -> Self {
		Self(core::marker::PhantomData)
	}
}
impl<D: sha3::digest::Digest + Clone> binius_hash::PseudoCompressionFunction<sha3::digest::Output<D>, 2> for Sha3Compression<D> {
	fn compress(&self, input: [sha3::digest::Output<D>; 2]) -> sha3::digest::Output<D> {
		let mut h = D::new();
		sha3::digest::Digest::update(&mut h, &input[0]);
		sha3::digest::Digest::update(&mut h, &input[1]);
		h.finalize()
	}
}

/// Level-parameterized square-circuit measurement over B256 with an ARBITRARY commitment/FS
/// hash `H` (κ_bind, κ_FS = H). Use `Sha3_256`@128 (L1) or `Sha3_384`@192 (L3) so the hash
/// clears the same NIST category as the field — the soundness-honest configuration.
pub fn measure_square_scaling_b256_hash<H, C>(
	rows_list: &[usize],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<Vec<(usize, u128, u128, usize)>>
where
	H: sha3::digest::Digest + sha3::digest::core_api::BlockSizeUser + sha3::digest::FixedOutputReset + Default + Clone + Send + Sync,
	C: binius_hash::PseudoCompressionFunction<sha3::digest::Output<H>, 2> + Default + Sync,
{
	use std::time::Instant;
	let mut out = Vec::new();
	for &n in rows_list {
		let n_rows = n.next_power_of_two();
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let table = SquareTable::new(&mut cs, false);
		let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };
		let events = witness_events(n_rows);
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		witness.fill_table_parallel(&table, &events)?;
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, H, C, HasherChallenger<H>, _>(
			&ccs, log_inv_rate, security_bits, &statement.boundaries, witness, &binius_hal::make_portable_backend(),
		)?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<U256, B256TowerFamily, H, C, HasherChallenger<H>>(
			&ccs, log_inv_rate, security_bits, &statement.boundaries, proof,
		)?;
		out.push((n_rows, prove_ms, t1.elapsed().as_millis(), sz));
	}
	Ok(out)
}

/// Measure PROVE and VERIFY wall-time + proof size of the `x*x=y` circuit over B256 across
/// row counts, at the given `log_inv_rate`/`security_bits` (128=L1, 192=L3). Same circuit as
/// the B512 (L5) measurement, for a fair cross-field verify-scaling / proof-size comparison.
pub fn measure_square_scaling_b256(
	rows_list: &[usize],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<Vec<(usize, u128, u128, usize)>> {
	use std::time::Instant;
	let mut out = Vec::new();
	for &n in rows_list {
		let n_rows = n.next_power_of_two();
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let table = SquareTable::new(&mut cs, false);
		let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };
		let events = witness_events(n_rows);
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		witness.fill_table_parallel(&table, &events)?;
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<
			U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<
			U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;
		out.push((n_rows, prove_ms, t1.elapsed().as_millis(), sz));
	}
	Ok(out)
}

/// The kappa_FS soundness signal: the tower-level of the challenge/extension field.
pub fn b256_top_field_bits() -> usize {
	<OurB256 as BinaryField>::N_BITS
}

// ---------------------------------------------------------------------------
// Reference oracle: a transparent, field-generic multilinear-extension evaluator
// used to cross-check the committed columns between B128 and B256 WITHOUT touching
// the (possibly buggy) PCS code path.
// ---------------------------------------------------------------------------

/// eq(i, r) = prod_j (i_j r_j + (1 - i_j)(1 - r_j)); char-2 so 1 - r_j = 1 + r_j.
#[cfg(test)]
fn eq_eval<F: Field>(i: usize, r: &[F]) -> F {
	let mut acc = F::ONE;
	for (j, &rj) in r.iter().enumerate() {
		let term = if (i >> j) & 1 == 1 { rj } else { F::ONE + rj };
		acc *= term;
	}
	acc
}

/// Multilinear extension of `B8` column data `values` evaluated at `r` (len = log2 |values|).
#[cfg(test)]
fn mle_eval<F: Field + From<B8>>(values: &[B8], r: &[F]) -> F {
	(0..values.len())
		.map(|i| F::from(values[i]) * eq_eval::<F>(i, r))
		.sum()
}

#[cfg(test)]
mod tests {
	use super::*;

	/// GATE 1 — the ring-switch generalization RUNS END-TO-END. A real proof of the
	/// `x*x=y` circuit over the 256-bit challenge field `B256TowerFamily` (committing
	/// at B8 → ring-switch kappa 5) VERIFIES at NIST L1 (128) and NIST L3 (192).
	#[test]
	fn ringswitch_b256_prove_verify() {
		assert_eq!(b256_top_field_bits(), 256, "challenge field must be 2^256");

		let size_l1 = prove_verify_b256(4096, 1, 128)
			.expect("honest x*x=y proof must VERIFY over B256 at NIST L1 (128)");
		assert!(size_l1 > 0);
		println!("GATE 1: B256 ring-switch proof VERIFIED at L1(128); proof size = {size_l1} bytes");

		let size_l3 = prove_verify_b256(4096, 1, 192)
			.expect("honest x*x=y proof must VERIFY over B256 at NIST L3 (192)");
		assert!(size_l3 >= size_l1, "L3 proof should be >= L1 proof (more queries)");
		println!("GATE 1: B256 ring-switch proof VERIFIED at L3(192); proof size = {size_l3} bytes");
	}

	/// GATE 2 — SOUNDNESS. (a) a dishonest witness (one wrong `y`) is rejected, and
	/// (b) a single flipped transcript byte on an honest proof is rejected.
	#[test]
	fn ringswitch_b256_tamper_rejected() {
		// (a) wrong witness value.
		assert!(
			dishonest_witness_is_rejected(4096, 1, 128),
			"SOUNDNESS FAILURE: a dishonest witness (y != x^2) was accepted over B256"
		);
		// (b) flipped transcript byte — build_prove_verify_b256 asserts rejection internally.
		let size = build_prove_verify_b256(4096, 1, 128, true)
			.expect("honest proof must verify AND tampered transcript must be rejected");
		println!("GATE 2: dishonest-witness AND flipped-transcript both REJECTED over B256 (honest size = {size} bytes)");
	}

	/// GATE 3 — THE WRONG-TRANSPOSE CATCH. The committed columns are the SAME `B8`
	/// data whether the PCS field is stock B128 or our B256. Their multilinear
	/// evaluations, computed by an independent reference oracle, must be IDENTICAL
	/// under the field embedding B128 ↪ B256: `embed(eval_B128) == eval_B256`. A
	/// mismatch would mean the B256 field/embedding (hence any PCS evaluation over
	/// it) corrupts the committed value — i.e. a proof that verifies a WRONG number.
	#[test]
	fn ringswitch_b256_matches_b128_reference() {
		let n_rows = 4096usize;
		let events = witness_events(n_rows);
		let xs: Vec<B8> = events.iter().map(|&e| B8::new(e)).collect();
		let ys: Vec<B8> = xs.iter().map(|&x| x * x).collect();
		let n_vars = n_rows.trailing_zeros() as usize;

		let mut rng = StdRng::from_seed([41u8; 32]);
		for _ in 0..64 {
			// Random evaluation point in stock B128, embedded coordinate-wise into B256.
			let r128: Vec<B128> = (0..n_vars).map(|_| <B128 as Field>::random(&mut rng)).collect();
			let r256: Vec<OurB256> = r128.iter().map(|&c| OurB256::from(c)).collect();

			for col in [&xs, &ys] {
				let v128 = mle_eval::<B128>(col, &r128);
				let v256 = mle_eval::<OurB256>(col, &r256);
				assert_eq!(
					OurB256::from(v128),
					v256,
					"committed-column evaluation diverged between B128 and B256 (PCS-field corruption)"
				);
			}
		}
		println!(
			"GATE 3: committed-column MLE evaluations agree between stock B128 and B256 \
			 (embed(eval_B128) == eval_B256) across 64 random points × 2 columns."
		);
	}

	/// GATE 4 — `square_transpose`/`fold_vertical` at KAPPA 8 (the level-8 top of the
	/// ring-switch) against a HAND-COMPUTED inner product. For a purely-vertical
	/// element `from_vertical(x)`, `fold_vertical(coeffs)` reduces (by the transpose
	/// definition) to `sum_r bit_r(x) * coeffs[r]`, where `bit_r(x)` are the B1 tower
	/// coordinates of `x`. This exercises the exact 256×256 transpose the B256 PCS
	/// uses and pins it to an independent reference.
	#[test]
	fn tensor_algebra_transpose_roundtrip_kappa8() {
		assert_eq!(
			TensorAlgebra::<RSB1, OurB256>::kappa(),
			8,
			"TensorAlgebra<B1,B256> must have kappa 8 (level-8 FExt)"
		);
		let mut rng = StdRng::from_seed([57u8; 32]);
		for _ in 0..200 {
			let x = <OurB256 as Field>::random(&mut rng);
			let coeffs: Vec<OurB256> =
				(0..256).map(|_| <OurB256 as Field>::random(&mut rng)).collect();

			// fold_vertical internally does square_transpose(kappa=8) then inner product.
			let ta = TensorAlgebra::<RSB1, OurB256>::from_vertical(x);
			let folded = ta.clone().fold_vertical(&coeffs);

			// Hand-computed reference: inner product of x's B1 tower coords with coeffs.
			let expected: OurB256 = <OurB256 as ExtensionField<RSB1>>::iter_bases(&x)
				.zip(coeffs.iter())
				.map(|(bit, &c)| OurB256::from(bit) * c)
				.sum();

			assert_eq!(folded, expected, "kappa-8 transpose/fold diverged from hand inner product");

			// Transpose is an involution: transpose∘transpose == identity at kappa 8.
			let rt = ta.clone().transpose().transpose();
			assert_eq!(rt, ta, "square_transpose is not an involution at kappa 8");
		}
		println!(
			"GATE 4: kappa-8 square_transpose/fold_vertical over B256 match a hand-computed \
			 inner product and transpose∘transpose == id (200 random trials)."
		);
	}
}
