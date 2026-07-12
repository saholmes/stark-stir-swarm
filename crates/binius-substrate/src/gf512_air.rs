// gf512_air — in-circuit GF(2^512) multiply for the B512 recursive/epoch layer (NIST L5).
//
// The epoch-Π prover over B256 (`accumulation_air::measure_epoch_verify_hash`) caps `κ_IT` at
// 192 because the challenge field is B256. Full L5 (`κ_IT = 256`) needs the epoch AIR over the
// B512 tower — which needs an in-circuit GF(2^512) multiply. This is the B256 nested-Karatsuba
// multiply (`gf256_air`) lifted ONE tower level: B512 = B256[w]/(w² + α₉·w + 1), α₉ = B256(1<<128).
//
//   B512 element = 8 B64 tower components [c0..c7]; c0..3 = the B256 "lo" half, c4..7 = "hi".
//   Karatsuba over the two B256 halves:
//     z0 = A_lo·B_lo, z2 = A_hi·B_hi, s = (A_lo+A_hi)(B_lo+B_hi)   (each a B256 mul, reused)
//     Z1 = s - z0 - z2;  result = (z0+z2) + (Z1 + z2·α₉)·w
//   with z2·α₉ = (z2_hi, z2_lo + z2_hi·α₈) as B256 halves ⇒ in B64 components:
//     [z2.c2, z2.c3, z2.c0 + z2.c3, z2.c1 + z2.c2 + z2.c3·β]   (β = B64(1<<32), the only scaling)
//
// The B256 sub-multiply and its populate are REUSED from `gf256_air` (now generic over the table
// field), so only the outer B256[w] layer is new. Gated against the native `B512 *`.

use anyhow::Result;

use binius_core::fiat_shamir::HasherChallenger;
use binius_m3::builder::{Col, ConstraintSystem, Statement, TableBuilder, WitnessIndex};

use crate::b512_field::{B512TowerFamily, B512 as OurB512, U512};
use crate::gf256_air::{beta, build_b256_mul, col8, pop_b256_mul, split256, wc64, B256MulCols, B64};

/// Split a B512 element into its eight B64 tower components (lo B256 ‖ hi B256).
pub(crate) fn split512(x: OurB512) -> [B64; 8] {
	let lo = split256(x.lo());
	let hi = split256(x.hi());
	[lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
}

/// The committed columns of one in-circuit B512 multiply `c = a·b` (Karatsuba over B256 halves).
pub(crate) struct B512MulCols {
	z0: B256MulCols,
	z2: B256MulCols,
	s: B256MulCols,
	sums: [Col<B64, 1>; 8], // sa0..3 (A_lo+A_hi), sb0..3 (B_lo+B_hi)
	z2c3b: Col<B64, 1>,     // z2.c3 · β  (the α₈ cross term)
	pub(crate) c: [Col<B64, 1>; 8],
}

/// Build `c = a·b` over B512 on given 8-component input columns. `pfx` namespaces the columns.
pub(crate) fn build_b512_mul<F: binius_field::TowerField + binius_field::ExtensionField<B64>>(
	t: &mut TableBuilder<F>,
	beta_col: Col<B64, 1>,
	a: [Col<B64, 1>; 8],
	b: [Col<B64, 1>; 8],
	pfx: &str,
) -> B512MulCols {
	let alo: [Col<B64, 1>; 4] = [a[0], a[1], a[2], a[3]];
	let ahi: [Col<B64, 1>; 4] = [a[4], a[5], a[6], a[7]];
	let blo: [Col<B64, 1>; 4] = [b[0], b[1], b[2], b[3]];
	let bhi: [Col<B64, 1>; 4] = [b[4], b[5], b[6], b[7]];

	let z0 = build_b256_mul(t, beta_col, alo, blo, &format!("{pfx}z0"));
	let z2 = build_b256_mul(t, beta_col, ahi, bhi, &format!("{pfx}z2"));

	// sums = (A_lo+A_hi), (B_lo+B_hi) per B64 component.
	let sums: [Col<B64, 1>; 8] = std::array::from_fn(|i| {
		let col = t.add_committed::<B64, 1>(format!("{pfx}sum{i}"));
		if i < 4 {
			t.assert_zero(format!("{pfx}sum{i}c"), col - (a[i] + a[i + 4]));
		} else {
			let j = i - 4;
			t.assert_zero(format!("{pfx}sum{i}c"), col - (b[j] + b[j + 4]));
		}
		col
	});
	let sa: [Col<B64, 1>; 4] = [sums[0], sums[1], sums[2], sums[3]];
	let sb: [Col<B64, 1>; 4] = [sums[4], sums[5], sums[6], sums[7]];
	let s = build_b256_mul(t, beta_col, sa, sb, &format!("{pfx}s"));

	// z2·α₉ cross-term scaling: z2c3b = z2.c3 · β.
	let z2c3b = t.add_committed::<B64, 1>(format!("{pfx}z2c3b"));
	t.assert_zero(format!("{pfx}z2c3bc"), z2c3b - z2.c[3] * beta_col);

	let c: [Col<B64, 1>; 8] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("{pfx}c{i}")));
	// result_lo = z0 + z2
	t.assert_zero(format!("{pfx}c0"), c[0] - (z0.c[0] + z2.c[0]));
	t.assert_zero(format!("{pfx}c1"), c[1] - (z0.c[1] + z2.c[1]));
	t.assert_zero(format!("{pfx}c2"), c[2] - (z0.c[2] + z2.c[2]));
	t.assert_zero(format!("{pfx}c3"), c[3] - (z0.c[3] + z2.c[3]));
	// result_hi = Z1 + z2·α₉, Z1 = s - z0 - z2, z2·α₉ = [z2.c2, z2.c3, z2.c0+z2.c3, z2.c1+z2.c2+z2.c3·β]
	t.assert_zero(format!("{pfx}c4"), c[4] - ((s.c[0] - z0.c[0] - z2.c[0]) + z2.c[2]));
	t.assert_zero(format!("{pfx}c5"), c[5] - ((s.c[1] - z0.c[1] - z2.c[1]) + z2.c[3]));
	t.assert_zero(format!("{pfx}c6"), c[6] - ((s.c[2] - z0.c[2] - z2.c[2]) + (z2.c[0] + z2.c[3])));
	t.assert_zero(format!("{pfx}c7"), c[7] - ((s.c[3] - z0.c[3] - z2.c[3]) + (z2.c[1] + z2.c[2] + z2c3b)));
	B512MulCols { z0, z2, s, sums, z2c3b, c }
}

/// Populate a B512 mul from operand B64 components; writes `c` and returns its value.
pub(crate) fn pop_b512_mul<P>(
	m: &B512MulCols,
	seg: &mut binius_m3::builder::TableWitnessSegment<P>,
	row: usize,
	av: [B64; 8],
	bv: [B64; 8],
) -> Result<[B64; 8]>
where
	P: binius_field::PackedExtension<B64>,
	P::Scalar: binius_field::TowerField,
{
	// sums
	for i in 0..4 {
		wc64(seg, m.sums[i], row, av[i] + av[i + 4])?;
	}
	for j in 0..4 {
		wc64(seg, m.sums[4 + j], row, bv[j] + bv[j + 4])?;
	}
	let z0 = pop_b256_mul(&m.z0, seg, row, [av[0], av[1], av[2], av[3]], [bv[0], bv[1], bv[2], bv[3]])?;
	let z2 = pop_b256_mul(&m.z2, seg, row, [av[4], av[5], av[6], av[7]], [bv[4], bv[5], bv[6], bv[7]])?;
	let sa = [av[0] + av[4], av[1] + av[5], av[2] + av[6], av[3] + av[7]];
	let sb = [bv[0] + bv[4], bv[1] + bv[5], bv[2] + bv[6], bv[3] + bv[7]];
	let s = pop_b256_mul(&m.s, seg, row, sa, sb)?;
	let z2c3b = z2[3] * beta();
	wc64(seg, m.z2c3b, row, z2c3b)?;
	let cv = [
		z0[0] + z2[0],
		z0[1] + z2[1],
		z0[2] + z2[2],
		z0[3] + z2[3],
		(s[0] - z0[0] - z2[0]) + z2[2],
		(s[1] - z0[1] - z2[1]) + z2[3],
		(s[2] - z0[2] - z2[2]) + (z2[0] + z2[3]),
		(s[3] - z0[3] - z2[3]) + (z2[1] + z2[2] + z2c3b),
	];
	for i in 0..8 {
		wc64(seg, m.c[i], row, cv[i])?;
	}
	Ok(cv)
}

/// Prove + verify one GF(2^512) multiply `c = a·b` in-circuit over B512, gated against the native
/// `B512 *`. Returns `(proof_bytes, in_circuit_c)`. Used to validate the B256→B512 combine.
pub fn prove_verify_b512_mul(a: OurB512, b: OurB512, security_bits: usize) -> Result<(usize, OurB512)> {
	use crate::b256_prove::Sha3Compression;
	use sha3::Sha3_512;

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB512>::new();
	let mut t = cs.add_table("gf(2^512) multiply");
	let beta_col = t.add_committed::<B64, 1>("beta");
	let ca = col8(&mut t, "a");
	let cb = col8(&mut t, "b");
	let m = build_b512_mul(&mut t, beta_col, ca, cb, "");
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let c_native = a * b;
	let (av, bv) = (split512(a), split512(b));

	let mut witness = WitnessIndex::<OurB512>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, NROWS)?;
		let mut seg = tw.full_segment();
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..8 {
				wc64(&mut seg, ca[i], row, av[i])?;
				wc64(&mut seg, cb[i], row, bv[i])?;
			}
			let cv = pop_b512_mul(&m, &mut seg, row, av, bv)?;
			// In-circuit result MUST equal the native split — the combine correctness gate.
			anyhow::ensure!(cv == split512(c_native), "in-circuit B512 mul != native (combine bug) at row {row}");
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U512, B512TowerFamily, Sha3_512, Sha3Compression<Sha3_512>, HasherChallenger<Sha3_512>, _,
	>(&ccs, 1, security_bits, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
	let sz = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U512, B512TowerFamily, Sha3_512, Sha3Compression<Sha3_512>, HasherChallenger<Sha3_512>,
	>(&ccs, 1, security_bits, &statement.boundaries, proof)?;
	Ok((sz, c_native))
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::Field;
	use rand::{rngs::StdRng, SeedableRng};

	/// GATE gf512-mul — the in-circuit GF(2^512) multiply == native `B512 *`, proven+verified over
	/// B512 with the SHA3-512@256 (L5) challenger. This is the multiply the B512 epoch-Π needs.
	#[test]
	fn gf512_mul_matches_native() {
		let mut rng = StdRng::seed_from_u64(0x512_A11);
		let a = OurB512::random(&mut rng);
		let b = OurB512::random(&mut rng);
		let (sz, c) = prove_verify_b512_mul(a, b, 256).expect("B512 mul must PROVE+VERIFY @L5(256)");
		assert_eq!(c, a * b, "native check");
		println!(
			"GATE gf512-mul: in-circuit GF(2^512) multiply == native B512 `*`, PROVEN+VERIFIED over B512 \
			 with the SHA3-512@256 challenger (nested Karatsuba B512=B256[w]; {} KB proof). This is the \
			 field-op the B512 epoch-Π (L5 κ_IT=256) is built from.",
			sz / 1024
		);
	}
}
