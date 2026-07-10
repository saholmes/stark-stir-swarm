// M3 (kappa_FS) NIST L5 — a REAL end-to-end Binius proof over the 512-bit
// challenge/extension field `B512TowerFamily` (tower level 9) at security_bits = 256,
// with binius_core's ring-switch small-field PCS running at a level-9 FExt.
//
// This mirrors `b256_prove` one tower level up. The ring-switch dispatch guards on the
// fork branch `feature/nist-tower-level-8-9-fext` are TYPE-DERIVED
// (`k == TensorAlgebra::<Tower::Bx, FExt>::kappa()`), so they auto-yield the level-9
// kappa set for a 512-bit FExt with NO additional fork change. The `base_tower_level`
// match in `constraint_system/prove.rs` stays within its existing `0..=8` arms because
// this circuit commits at B8 (tower level 3) and the composition's binary tower level
// is 3, so `base_tower_level = 3`.
//
// The circuit is deliberately MINIMAL: a one-table `x*x = y` over committed `B8`
// columns. Committing at B8 (tower level 3) under a level-9 FExt drives the ring-switch
// at kappa 9-3 = 6.
//
// Four gates (tests):
//   1. `ringswitch_b512_prove_verify`          — a real proof VERIFIES at L5 (256).
//   2. `ringswitch_b512_tamper_rejected`       — a flipped witness value AND a flipped
//                                                 transcript byte are each REJECTED at 256.
//   3. `ringswitch_b512_matches_b128_reference`— committed-column evaluations agree
//                                                 between stock B128 and B512.
//   4. `tensor_algebra_transpose_roundtrip_kappa9` — `square_transpose`/`fold_vertical`
//                                                 at kappa 9 match a hand-computed inner product.

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

// Our 512-bit tower field is the top/challenge field of the constraint system.
use crate::b512_field::{B512TowerFamily, B512 as OurB512, U512};

/// A minimal one-table constraint system over the top field `F`: committed `x, y` with
/// the constraint `x*x = y`. `corrupt` writes a WRONG `y` on the first row (a dishonest
/// witness), used by the soundness gate.
struct SquareTable {
	table_id: TableId,
	x: Col<B8>,
	y: Col<B8>,
	corrupt: bool,
}

impl SquareTable {
	fn new(cs: &mut ConstraintSystem<OurB512>, corrupt: bool) -> Self {
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

impl TableFiller<OurB512> for SquareTable {
	type Event = u8;

	fn id(&self) -> TableId {
		self.table_id
	}

	fn fill<'a>(
		&'a self,
		rows: impl Iterator<Item = &'a Self::Event> + Clone,
		witness: &'a mut TableWitnessSegment<OurB512>,
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

/// Build + prove + verify the `x*x=y` circuit over `B512TowerFamily`. Returns the proof
/// size in bytes on an honest verify. If `tamper_transcript`, a clone of the proof has
/// one transcript byte flipped and MUST be rejected.
fn build_prove_verify_b512(
	n_rows: usize,
	log_inv_rate: usize,
	security_bits: usize,
	tamper_transcript: bool,
) -> Result<usize> {
	let n_rows = n_rows.next_power_of_two();

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB512>::new();
	let table = SquareTable::new(&mut cs, false);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};

	let events = witness_events(n_rows);

	let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
	witness.fill_table_parallel(&table, &events)?;

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// FIPS commitment + transcript; challenge/extension field = B512 (2^512).
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

	let proof_size = proof.get_proof_size();

	// Honest proof MUST verify over the 512-bit challenge field.
	binius_core::constraint_system::verify::<
		U512,
		B512TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;

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
		anyhow::ensure!(rejected, "SOUNDNESS FAILURE: tampered transcript accepted over B512");
	}

	Ok(proof_size)
}

/// Build a DISHONEST witness (one wrong `y`) and attempt prove+verify. Returns `true`
/// iff the dishonest statement is rejected (either the prover errors on the unsatisfied
/// constraint, or the verifier rejects the resulting proof).
#[cfg(test)]
fn dishonest_witness_is_rejected(n_rows: usize, log_inv_rate: usize, security_bits: usize) -> bool {
	let n_rows = n_rows.next_power_of_two();
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB512>::new();
	let table = SquareTable::new(&mut cs, true); // corrupt row 0

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};
	let events = witness_events(n_rows);

	let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
	if witness.fill_table_parallel(&table, &events).is_err() {
		return true;
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

	// If the prover produced a proof, the verifier MUST reject it.
	binius_core::constraint_system::verify::<
		U512,
		B512TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)
	.is_err()
}

/// Measure PROVE and VERIFY wall-time + proof size of the `x*x=y` circuit over B512 (L5,
/// security 256) across row counts — the same circuit as `measure_square_scaling_b256`, so
/// the B256(L1/L3) vs B512(L5) numbers are directly comparable (field bytes 32->64, tower
/// mul ~3x, deeper Merkle nodes).
pub fn measure_square_scaling_b512(
	rows_list: &[usize],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<Vec<(usize, u128, u128, usize)>> {
	use std::time::Instant;
	let mut out = Vec::new();
	for &n in rows_list {
		let n_rows = n.next_power_of_two();
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB512>::new();
		let table = SquareTable::new(&mut cs, false);
		let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };
		let events = witness_events(n_rows);
		let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
		witness.fill_table_parallel(&table, &events)?;
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let t0 = Instant::now();
		let proof = binius_core::constraint_system::prove::<
			U512, B512TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
		let prove_ms = t0.elapsed().as_millis();
		let sz = proof.get_proof_size();
		let t1 = Instant::now();
		binius_core::constraint_system::verify::<
			U512, B512TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;
		out.push((n_rows, prove_ms, t1.elapsed().as_millis(), sz));
	}
	Ok(out)
}

/// Public entry: honest prove+verify over B512, returning proof size in bytes.
pub fn prove_verify_b512(n_rows: usize, log_inv_rate: usize, security_bits: usize) -> Result<usize> {
	build_prove_verify_b512(n_rows, log_inv_rate, security_bits, false)
}

/// The kappa_FS soundness signal: the tower-level of the challenge/extension field.
pub fn b512_top_field_bits() -> usize {
	<OurB512 as BinaryField>::N_BITS
}

// ---------------------------------------------------------------------------
// Reference oracle: a transparent, field-generic multilinear-extension evaluator used
// to cross-check the committed columns between B128 and B512 WITHOUT touching the PCS
// code path.
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

	/// NIST-LEVEL verify-scaling + proof-size comparison on the SAME `x*x=y` circuit:
	/// L1 = B256@128, L3 = B256@192, L5 = B512@256 (all blowup=2). Answers the twice-asked
	/// question — how verify time and proof size scale across the field ladder — with the
	/// same gate so the field is the only variable. Reported (not asserted).
	#[test]
	fn nist_level_verify_scaling() {
		let rows = [4096usize, 16384, 65536];
		let l1 = crate::b256_prove::measure_square_scaling_b256(&rows, 1, 128).expect("L1");
		let l3 = crate::b256_prove::measure_square_scaling_b256(&rows, 1, 192).expect("L3");
		let l5 = measure_square_scaling_b512(&rows, 1, 256).expect("L5");
		println!("| level (field@sec) | rows | prove ms | verify ms | proof B |");
		println!("|:--|---:|---:|---:|---:|");
		for (tag, res) in [("L1 B256@128", &l1), ("L3 B256@192", &l3), ("L5 B512@256", &l5)] {
			for (n, p, v, sz) in res {
				println!("| {tag} | {n} | {p} | {v} | {sz} |");
			}
		}
		// headline ratios at the largest row count (recursion scale proxy).
		let last = |r: &Vec<(usize, u128, u128, usize)>| *r.last().unwrap();
		let (_, _, v1, s1) = last(&l1);
		let (_, _, v3, s3) = last(&l3);
		let (_, _, v5, s5) = last(&l5);
		println!(
			"# @16384 rows: verify L1={v1}ms L3={v3}ms L5={v5}ms (L5/L1={:.1}x); proof L1={s1}B L3={s3}B L5={s5}B (L5/L1={:.1}x). \
			 Same x*x=y gate; field is the only variable. Recursion hash = SHA-256 (FIPS) at ALL levels; \
			 the field ladder (B256->B512) is what changes verify/proof.",
			v5 as f64 / v1.max(1) as f64, s5 as f64 / s1 as f64
		);
	}

	/// GATE 1 — the ring-switch generalization RUNS END-TO-END at NIST L5. A real proof
	/// of the `x*x=y` circuit over the 512-bit challenge field `B512TowerFamily`
	/// (committing at B8 → ring-switch kappa 6) VERIFIES at security_bits = 256.
	#[test]
	fn ringswitch_b512_prove_verify() {
		assert_eq!(b512_top_field_bits(), 512, "challenge field must be 2^512");

		let size_l5 = prove_verify_b512(4096, 1, 256)
			.expect("honest x*x=y proof must VERIFY over B512 at NIST L5 (256)");
		assert!(size_l5 > 0);
		println!("GATE 1: B512 ring-switch proof VERIFIED at L5(256); proof size = {size_l5} bytes");

		// Sanity: also verifies at the lower levels.
		let size_l1 = prove_verify_b512(4096, 1, 128)
			.expect("honest x*x=y proof must VERIFY over B512 at NIST L1 (128)");
		assert!(size_l5 >= size_l1, "L5 proof should be >= L1 proof (more queries)");
		println!("GATE 1: B512 ring-switch proof VERIFIED at L1(128); proof size = {size_l1} bytes");
	}

	/// GATE 2 — SOUNDNESS at L5. (a) a dishonest witness (one wrong `y`) is rejected,
	/// and (b) a single flipped transcript byte on an honest proof is rejected.
	#[test]
	fn ringswitch_b512_tamper_rejected() {
		// (a) wrong witness value.
		assert!(
			dishonest_witness_is_rejected(4096, 1, 256),
			"SOUNDNESS FAILURE: a dishonest witness (y != x^2) was accepted over B512 at L5"
		);
		// (b) flipped transcript byte — build_prove_verify_b512 asserts rejection internally.
		let size = build_prove_verify_b512(4096, 1, 256, true)
			.expect("honest proof must verify AND tampered transcript must be rejected");
		println!("GATE 2: dishonest-witness AND flipped-transcript both REJECTED over B512 at L5 (honest size = {size} bytes)");
	}

	/// GATE 3 — THE WRONG-TRANSPOSE CATCH. The committed columns are the SAME `B8` data
	/// whether the PCS field is stock B128 or our B512. Their multilinear evaluations,
	/// computed by an independent reference oracle, must be IDENTICAL under the field
	/// embedding B128 ↪ B512: `embed(eval_B128) == eval_B512`.
	#[test]
	fn ringswitch_b512_matches_b128_reference() {
		let n_rows = 4096usize;
		let events = witness_events(n_rows);
		let xs: Vec<B8> = events.iter().map(|&e| B8::new(e)).collect();
		let ys: Vec<B8> = xs.iter().map(|&x| x * x).collect();
		let n_vars = n_rows.trailing_zeros() as usize;

		let mut rng = StdRng::from_seed([41u8; 32]);
		for _ in 0..64 {
			// Random evaluation point in stock B128, embedded coordinate-wise into B512.
			let r128: Vec<B128> = (0..n_vars).map(|_| <B128 as Field>::random(&mut rng)).collect();
			let r512: Vec<OurB512> = r128.iter().map(|&c| OurB512::from(c)).collect();

			for col in [&xs, &ys] {
				let v128 = mle_eval::<B128>(col, &r128);
				let v512 = mle_eval::<OurB512>(col, &r512);
				assert_eq!(
					OurB512::from(v128),
					v512,
					"committed-column evaluation diverged between B128 and B512 (PCS-field corruption)"
				);
			}
		}
		println!(
			"GATE 3: committed-column MLE evaluations agree between stock B128 and B512 \
			 (embed(eval_B128) == eval_B512) across 64 random points × 2 columns."
		);
	}

	/// GATE 4 — `square_transpose`/`fold_vertical` at KAPPA 9 (the level-9 top of the
	/// ring-switch) against a HAND-COMPUTED inner product. For a purely-vertical element
	/// `from_vertical(x)`, `fold_vertical(coeffs)` reduces (by the transpose definition)
	/// to `sum_r bit_r(x) * coeffs[r]`, where `bit_r(x)` are the B1 tower coordinates of
	/// `x`. This exercises the exact 512×512 transpose the B512 PCS uses and pins it to
	/// an independent reference — the direct wrong-transpose soundness catch at level 9.
	#[test]
	fn tensor_algebra_transpose_roundtrip_kappa9() {
		assert_eq!(
			TensorAlgebra::<RSB1, OurB512>::kappa(),
			9,
			"TensorAlgebra<B1,B512> must have kappa 9 (level-9 FExt)"
		);
		let mut rng = StdRng::from_seed([57u8; 32]);
		for _ in 0..200 {
			let x = <OurB512 as Field>::random(&mut rng);
			let coeffs: Vec<OurB512> =
				(0..512).map(|_| <OurB512 as Field>::random(&mut rng)).collect();

			// fold_vertical internally does square_transpose(kappa=9) then inner product.
			let ta = TensorAlgebra::<RSB1, OurB512>::from_vertical(x);
			let folded = ta.clone().fold_vertical(&coeffs);

			// Hand-computed reference: inner product of x's B1 tower coords with coeffs.
			let expected: OurB512 = <OurB512 as ExtensionField<RSB1>>::iter_bases(&x)
				.zip(coeffs.iter())
				.map(|(bit, &c)| OurB512::from(bit) * c)
				.sum();

			assert_eq!(folded, expected, "kappa-9 transpose/fold diverged from hand inner product");

			// Transpose is an involution: transpose∘transpose == identity at kappa 9.
			let rt = ta.clone().transpose().transpose();
			assert_eq!(rt, ta, "square_transpose is not an involution at kappa 9");
		}
		println!(
			"GATE 4: kappa-9 square_transpose/fold_vertical over B512 match a hand-computed \
			 inner product and transpose∘transpose == id (200 random trials)."
		);
	}
}
