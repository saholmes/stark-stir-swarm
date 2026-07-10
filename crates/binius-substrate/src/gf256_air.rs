// gf256_air — Tier-B M3b: in-circuit GF(2^256) multiply for the B256 recursive layer.
//
// FRI folding over the B256 challenge field needs a field multiply in-circuit. M3a found
// native B128 field-element columns are ring-switch-rejected in the B256 tower ("packing
// degree 1"). This module first PROBES whether SMALLER field-element columns (B64, B32),
// which pack at higher degree in the B256 tower, are accepted — if so, GF(2^256) multiply
// is Karatsuba over a few NATIVE B64 mul constraints (b256_field.rs:129 b256_mul), not a
// hand-rolled bit-level carryless multiply.

use anyhow::Result;

use binius_core::fiat_shamir::HasherChallenger;
use binius_field::underlier::WithUnderlier;
use binius_field::{packed::set_packed_slice, BinaryField128b, BinaryField32b, BinaryField64b};
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{Col, ConstraintSystem, Statement, TableBuilder, WitnessIndex};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};

type B64 = BinaryField64b;

/// The B64->B128 tower constant (B128 = B64[y]/(y^2 + BETA·y + 1)); verified in tests.
fn beta() -> B64 {
	B64::new(1u64 << 32)
}

// --- native tower splits (for populate + gating) ---------------------------------

/// Split a B128 element into its two B64 tower halves `(lo, hi)`.
fn split128(x: BinaryField128b) -> (B64, B64) {
	let u: u128 = x.to_underlier();
	(B64::new(u as u64), B64::new((u >> 64) as u64))
}
/// Split a B256 element into its four B64 tower components `[lo.lo, lo.hi, hi.lo, hi.hi]`.
fn split256(x: OurB256) -> [B64; 4] {
	let (l0, l1) = split128(x.lo());
	let (h0, h1) = split128(x.hi());
	[l0, l1, h0, h1]
}

// --- in-circuit B128 mul over B64 halves (inner Karatsuba) ------------------------

/// The committed columns of one in-circuit B128 multiply `(r0,r1) = (p0,p1)·(q0,q1)`.
#[derive(Clone, Copy)]
struct B128Mul {
	w0: Col<B64, 1>,
	w2: Col<B64, 1>,
	w1m: Col<B64, 1>,
	w2b: Col<B64, 1>,
	r0: Col<B64, 1>,
	r1: Col<B64, 1>,
}

/// Build B128 mul: r_lo = p0·q0 + p1·q1; r_hi = (p0+p1)(q0+q1) - p0·q0 - p1·q1 + (p1·q1)·β.
/// Operands are given as expressions (so callers can pass `a+b` for the Karatsuba middle).
fn build_b128_mul(
	t: &mut TableBuilder<OurB256>,
	beta_col: Col<B64, 1>,
	p0: Col<B64, 1>,
	p1: Col<B64, 1>,
	q0: Col<B64, 1>,
	q1: Col<B64, 1>,
	nm: &str,
) -> B128Mul {
	let w0 = t.add_committed::<B64, 1>(format!("{nm}_w0"));
	t.assert_zero(format!("{nm}_w0c"), w0 - p0 * q0);
	let w2 = t.add_committed::<B64, 1>(format!("{nm}_w2"));
	t.assert_zero(format!("{nm}_w2c"), w2 - p1 * q1);
	let w1m = t.add_committed::<B64, 1>(format!("{nm}_w1m"));
	t.assert_zero(format!("{nm}_w1mc"), w1m - (p0 + p1) * (q0 + q1));
	let w2b = t.add_committed::<B64, 1>(format!("{nm}_w2b"));
	t.assert_zero(format!("{nm}_w2bc"), w2b - w2 * beta_col);
	let r0 = t.add_committed::<B64, 1>(format!("{nm}_r0"));
	t.assert_zero(format!("{nm}_r0c"), r0 - (w0 + w2));
	let r1 = t.add_committed::<B64, 1>(format!("{nm}_r1"));
	t.assert_zero(format!("{nm}_r1c"), r1 - (w1m - w0 - w2 + w2b));
	B128Mul { w0, w2, w1m, w2b, r0, r1 }
}

fn wc64(seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, col: Col<B64, 1>, row: usize, v: B64) -> Result<()> {
	let mut slice = seg.get_mut(col)?;
	set_packed_slice(&mut slice, row, v);
	Ok(())
}

/// Populate a B128Mul from operand B64 values; returns `(r0, r1)`.
fn pop_b128_mul(
	m: &B128Mul,
	seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>,
	row: usize,
	p0: B64,
	p1: B64,
	q0: B64,
	q1: B64,
) -> Result<(B64, B64)> {
	let w0 = p0 * q0;
	let w2 = p1 * q1;
	let w1m = (p0 + p1) * (q0 + q1);
	let w2b = w2 * beta();
	let r0 = w0 + w2;
	let r1 = w1m - w0 - w2 + w2b;
	for (c, v) in [(m.w0, w0), (m.w2, w2), (m.w1m, w1m), (m.w2b, w2b), (m.r0, r0), (m.r1, r1)] {
		wc64(seg, c, row, v)?;
	}
	Ok((r0, r1))
}

/// Probe: prove `c = a*b` for one field type `FSub` (a native degree-2 field constraint)
/// under the B256 tower, to learn whether `FSub` field-element columns are accepted.
macro_rules! probe_mul {
	($fn_name:ident, $F:ty, $name:literal) => {
		pub fn $fn_name(a: $F, b: $F) -> Result<usize> {
			let allocator = bumpalo::Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let mut table = cs.add_table(concat!($name, " mul probe"));
			let ca = table.add_committed::<$F, 1>("a");
			let cb = table.add_committed::<$F, 1>("b");
			let cc = table.add_committed::<$F, 1>("c");
			table.assert_zero("mul", cc - ca * cb);
			let table_id = table.id();

			const NROWS: usize = 128;
			let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
			let c = a * b;

			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(table_id, NROWS)?;
				let mut seg = tw.full_segment();
				for (col, val) in [(ca, a), (cb, b), (cc, c)] {
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
				U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
			>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
			let sz = proof.get_proof_size();
			binius_core::constraint_system::verify::<
				U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
			>(&ccs, 1, 128, &statement.boundaries, proof)?;
			Ok(sz)
		}
	};
}

probe_mul!(probe_b64_mul, BinaryField64b, "B64");
probe_mul!(probe_b32_mul, BinaryField32b, "B32");

// --- reusable B256 mul builder (namespaced, so a table can hold several) ----------

/// The committed columns of one in-circuit B256 multiply `c = a·b` (a,b,c as [B64;4]).
struct B256MulCols {
	z0: B128Mul,
	z2: B128Mul,
	s: B128Mul,
	sa: [Col<B64, 1>; 4], // sa0,sa1,sb0,sb1
	z2ab: Col<B64, 1>,
	c: [Col<B64, 1>; 4],
}

/// Build `c = a·b` over B256 (nested Karatsuba) on given input columns; commits the 4
/// result components `c`. `pfx` namespaces the columns so multiple muls coexist.
fn build_b256_mul(
	t: &mut TableBuilder<OurB256>,
	beta_col: Col<B64, 1>,
	a: [Col<B64, 1>; 4],
	b: [Col<B64, 1>; 4],
	pfx: &str,
) -> B256MulCols {
	let z0 = build_b128_mul(t, beta_col, a[0], a[1], b[0], b[1], &format!("{pfx}z0"));
	let z2 = build_b128_mul(t, beta_col, a[2], a[3], b[2], b[3], &format!("{pfx}z2"));
	let mk = |t: &mut TableBuilder<OurB256>, nm: String, e: Col<B64, 1>, f: Col<B64, 1>| {
		let c = t.add_committed::<B64, 1>(nm.clone());
		t.assert_zero(format!("{nm}c"), c - (e + f));
		c
	};
	let sa0 = mk(t, format!("{pfx}sa0"), a[0], a[2]);
	let sa1 = mk(t, format!("{pfx}sa1"), a[1], a[3]);
	let sb0 = mk(t, format!("{pfx}sb0"), b[0], b[2]);
	let sb1 = mk(t, format!("{pfx}sb1"), b[1], b[3]);
	let s = build_b128_mul(t, beta_col, sa0, sa1, sb0, sb1, &format!("{pfx}s"));
	let z2ab = t.add_committed::<B64, 1>(format!("{pfx}z2ab"));
	t.assert_zero(format!("{pfx}z2abc"), z2ab - z2.r1 * beta_col);
	let c: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("{pfx}c{i}")));
	t.assert_zero(format!("{pfx}c0"), c[0] - (z0.r0 + z2.r0));
	t.assert_zero(format!("{pfx}c1"), c[1] - (z0.r1 + z2.r1));
	t.assert_zero(format!("{pfx}c2"), c[2] - ((s.r0 - z0.r0 - z2.r0) + z2.r1));
	t.assert_zero(format!("{pfx}c3"), c[3] - ((s.r1 - z0.r1 - z2.r1) + (z2.r0 + z2ab)));
	B256MulCols { z0, z2, s, sa: [sa0, sa1, sb0, sb1], z2ab, c }
}

/// Populate a B256 mul from operand B64 components; writes `c` and returns its value.
fn pop_b256_mul(
	m: &B256MulCols,
	seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>,
	row: usize,
	av: [B64; 4],
	bv: [B64; 4],
) -> Result<[B64; 4]> {
	wc64(seg, m.sa[0], row, av[0] + av[2])?;
	wc64(seg, m.sa[1], row, av[1] + av[3])?;
	wc64(seg, m.sa[2], row, bv[0] + bv[2])?;
	wc64(seg, m.sa[3], row, bv[1] + bv[3])?;
	let (z0r0, z0r1) = pop_b128_mul(&m.z0, seg, row, av[0], av[1], bv[0], bv[1])?;
	let (z2r0, z2r1) = pop_b128_mul(&m.z2, seg, row, av[2], av[3], bv[2], bv[3])?;
	let (sr0, sr1) = pop_b128_mul(&m.s, seg, row, av[0] + av[2], av[1] + av[3], bv[0] + bv[2], bv[1] + bv[3])?;
	let z2ab = z2r1 * beta();
	wc64(seg, m.z2ab, row, z2ab)?;
	let cv = [
		z0r0 + z2r0,
		z0r1 + z2r1,
		(sr0 - z0r0 - z2r0) + z2r1,
		(sr1 - z0r1 - z2r1) + (z2r0 + z2ab),
	];
	for i in 0..4 {
		wc64(seg, m.c[i], row, cv[i])?;
	}
	Ok(cv)
}

// --- in-circuit B256 mul = nested Karatsuba over B64 native muls ------------------

/// Prove + verify one GF(2^256) multiply `c = a·b` in-circuit over B256 (B256 element =
/// 4 B64 tower components; nested Karatsuba with α₈=B128(1<<64), α₇=B64(1<<32)). Returns
/// `(proof_bytes, in_circuit_c)`. Gated against the native B256 `*`.
pub fn prove_verify_b256_mul(a: OurB256, b: OurB256) -> Result<(usize, OurB256)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("gf(2^256) multiply");
	let beta_col = {
		let c = t.add_committed::<B64, 1>("beta");
		c
	};
	let ca: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("a{i}")));
	let cb: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("b{i}")));
	let cc: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("c{i}")));

	// Outer Karatsuba over B128 halves A_lo=(a0,a1), A_hi=(a2,a3); B_lo, B_hi.
	let z0 = build_b128_mul(&mut t, beta_col, ca[0], ca[1], cb[0], cb[1], "z0");
	let z2 = build_b128_mul(&mut t, beta_col, ca[2], ca[3], cb[2], cb[3], "z2");
	// s = (A_lo+A_hi)·(B_lo+B_hi); Karatsuba middle Z1 = s - z0 - z2. Commit the XOR sums.
	let sa0 = t.add_committed::<B64, 1>("sa0");
	t.assert_zero("sa0c", sa0 - (ca[0] + ca[2]));
	let sa1 = t.add_committed::<B64, 1>("sa1");
	t.assert_zero("sa1c", sa1 - (ca[1] + ca[3]));
	let sb0 = t.add_committed::<B64, 1>("sb0");
	t.assert_zero("sb0c", sb0 - (cb[0] + cb[2]));
	let sb1 = t.add_committed::<B64, 1>("sb1");
	t.assert_zero("sb1c", sb1 - (cb[1] + cb[3]));
	let s = build_b128_mul(&mut t, beta_col, sa0, sa1, sb0, sb1, "s");
	// Z2·α (α=B128(1<<64)=(0,1) over B64): Z2α = (z2.r1, z2.r0 + z2.r1·β).
	let z2ab = t.add_committed::<B64, 1>("z2ab");
	t.assert_zero("z2abc", z2ab - z2.r1 * beta_col);
	// c = (Z0+Z2) + (Z1 + Z2α)·x, per B64 component.
	t.assert_zero("c0", cc[0] - (z0.r0 + z2.r0));
	t.assert_zero("c1", cc[1] - (z0.r1 + z2.r1));
	t.assert_zero("c2", cc[2] - ((s.r0 - z0.r0 - z2.r0) + z2.r1));
	t.assert_zero("c3", cc[3] - ((s.r1 - z0.r1 - z2.r1) + (z2.r0 + z2ab)));
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let c_native = a * b;
	let (av, bv, cv) = (split256(a), split256(b), split256(c_native));

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, NROWS)?;
		let mut seg = tw.full_segment();
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, ca[i], row, av[i])?;
				wc64(&mut seg, cb[i], row, bv[i])?;
				wc64(&mut seg, cc[i], row, cv[i])?;
			}
			wc64(&mut seg, sa0, row, av[0] + av[2])?;
			wc64(&mut seg, sa1, row, av[1] + av[3])?;
			wc64(&mut seg, sb0, row, bv[0] + bv[2])?;
			wc64(&mut seg, sb1, row, bv[1] + bv[3])?;
			pop_b128_mul(&z0, &mut seg, row, av[0], av[1], bv[0], bv[1])?;
			let (_z2r0, z2r1) = pop_b128_mul(&z2, &mut seg, row, av[2], av[3], bv[2], bv[3])?;
			pop_b128_mul(&s, &mut seg, row, av[0] + av[2], av[1] + av[3], bv[0] + bv[2], bv[1] + bv[3])?;
			// z2ab = Z2.hi · β.
			wc64(&mut seg, z2ab, row, z2r1 * beta())?;
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let sz = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((sz, c_native))
}

/// Prove + verify the FRI fold `folded = u + (v - u)·r` over the FULL B256 field
/// in-circuit (M3a's fold, now at NIST L1 via the M3b GF(2^256) multiply). Returns
/// `(proof_bytes, in_circuit_folded)`; gated against the native B256 fold.
pub fn prove_verify_b256_fold(u: OurB256, v: OurB256, r: OurB256) -> Result<(usize, OurB256)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("gf(2^256) FRI fold u+(v-u)*r");
	let beta_col = t.add_committed::<B64, 1>("beta");
	let cu: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("u{i}")));
	let cv: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("v{i}")));
	let cr: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("r{i}")));
	let cf: [Col<B64, 1>; 4] = std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("f{i}")));
	// d = v - u (per B64 component; subtraction == addition == XOR in GF(2)).
	let cd: [Col<B64, 1>; 4] = std::array::from_fn(|i| {
		let d = t.add_committed::<B64, 1>(format!("d{i}"));
		t.assert_zero(format!("d{i}c"), d - (cv[i] - cu[i]));
		d
	});
	// p = d · r  (nested Karatsuba, operands d and r).
	let z0 = build_b128_mul(&mut t, beta_col, cd[0], cd[1], cr[0], cr[1], "z0");
	let z2 = build_b128_mul(&mut t, beta_col, cd[2], cd[3], cr[2], cr[3], "z2");
	let sa0 = t.add_committed::<B64, 1>("sa0");
	t.assert_zero("sa0c", sa0 - (cd[0] + cd[2]));
	let sa1 = t.add_committed::<B64, 1>("sa1");
	t.assert_zero("sa1c", sa1 - (cd[1] + cd[3]));
	let sb0 = t.add_committed::<B64, 1>("sb0");
	t.assert_zero("sb0c", sb0 - (cr[0] + cr[2]));
	let sb1 = t.add_committed::<B64, 1>("sb1");
	t.assert_zero("sb1c", sb1 - (cr[1] + cr[3]));
	let s = build_b128_mul(&mut t, beta_col, sa0, sa1, sb0, sb1, "s");
	let z2ab = t.add_committed::<B64, 1>("z2ab");
	t.assert_zero("z2abc", z2ab - z2.r1 * beta_col);
	// p components (as in the mul), then folded = u + p.
	let p0 = z0.r0 + z2.r0;
	let p1 = z0.r1 + z2.r1;
	let p2 = (s.r0 - z0.r0 - z2.r0) + z2.r1;
	let p3 = (s.r1 - z0.r1 - z2.r1) + (z2.r0 + z2ab);
	t.assert_zero("f0", cf[0] - (cu[0] + p0));
	t.assert_zero("f1", cf[1] - (cu[1] + p1));
	t.assert_zero("f2", cf[2] - (cu[2] + p2));
	t.assert_zero("f3", cf[3] - (cu[3] + p3));
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	let folded_native = u + (v - u) * r;
	let (uv, vv, rv, dv, fv) =
		(split256(u), split256(v), split256(r), split256(v - u), split256(folded_native));

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(table_id, NROWS)?;
		let mut seg = tw.full_segment();
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cu[i], row, uv[i])?;
				wc64(&mut seg, cv[i], row, vv[i])?;
				wc64(&mut seg, cr[i], row, rv[i])?;
				wc64(&mut seg, cf[i], row, fv[i])?;
				wc64(&mut seg, cd[i], row, dv[i])?;
			}
			wc64(&mut seg, sa0, row, dv[0] + dv[2])?;
			wc64(&mut seg, sa1, row, dv[1] + dv[3])?;
			wc64(&mut seg, sb0, row, rv[0] + rv[2])?;
			wc64(&mut seg, sb1, row, rv[1] + rv[3])?;
			pop_b128_mul(&z0, &mut seg, row, dv[0], dv[1], rv[0], rv[1])?;
			let (_z2r0, z2r1) = pop_b128_mul(&z2, &mut seg, row, dv[2], dv[3], rv[2], rv[3])?;
			pop_b128_mul(&s, &mut seg, row, dv[0] + dv[2], dv[1] + dv[3], rv[0] + rv[2], rv[1] + rv[3])?;
			wc64(&mut seg, z2ab, row, z2r1 * beta())?;
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let sz = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((sz, folded_native))
}

/// Native FRI `fold_pair` (binius fri/common.rs:25): v'=v+u; u'=u+v'·t; folded =
/// u'+(v'-u')·r, where `t` is the domain twiddle (verifier-computed subspace eval).
pub fn fold_pair_native(u: OurB256, v: OurB256, r: OurB256, t: OurB256) -> OurB256 {
	let vp = v + u;
	let up = u + vp * t;
	up + (vp - up) * r
}

/// Prove + verify the FULL FRI `fold_pair` (with domain twiddle `t`) in-circuit over
/// B256 — two GF(2^256) muls (`v'·t` and `(v'-u')·r`) + XORs. This is the exact
/// per-pair operation `fold_chunk` applies across a coset. Gated against the native.
pub fn prove_verify_b256_fold_pair(
	u: OurB256,
	v: OurB256,
	r: OurB256,
	tw: OurB256,
) -> Result<(usize, OurB256)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("fri fold_pair over B256 (twiddle-adjusted)");
	let beta_col = t.add_committed::<B64, 1>("beta");
	let col4 = |t: &mut TableBuilder<OurB256>, nm: &str| -> [Col<B64, 1>; 4] {
		std::array::from_fn(|i| t.add_committed::<B64, 1>(format!("{nm}{i}")))
	};
	let cu = col4(&mut t, "u");
	let cv = col4(&mut t, "v");
	let cr = col4(&mut t, "r");
	let ct = col4(&mut t, "t");
	let cf = col4(&mut t, "f");
	// v' = v + u
	let vp = col4(&mut t, "vp");
	for i in 0..4 {
		t.assert_zero(format!("vp{i}c"), vp[i] - (cv[i] + cu[i]));
	}
	// p1 = v'·t ; u' = u + p1
	let m1 = build_b256_mul(&mut t, beta_col, vp, ct, "m1_");
	let up = col4(&mut t, "up");
	for i in 0..4 {
		t.assert_zero(format!("up{i}c"), up[i] - (cu[i] + m1.c[i]));
	}
	// d = v' - u' ; p2 = d·r ; folded = u' + p2
	let cd = col4(&mut t, "d");
	for i in 0..4 {
		t.assert_zero(format!("d{i}c"), cd[i] - (vp[i] + up[i]));
	}
	let m2 = build_b256_mul(&mut t, beta_col, cd, cr, "m2_");
	for i in 0..4 {
		t.assert_zero(format!("f{i}c"), cf[i] - (up[i] + m2.c[i]));
	}
	let table_id = t.id();

	const NROWS: usize = 64;
	let statement = Statement { boundaries: vec![], table_sizes: vec![NROWS] };
	// native intermediates
	let vpn = v + u;
	let upn = u + vpn * tw;
	let dn = vpn - upn;
	let folded = upn + dn * r;
	let (uv, vv, rv, tv, fv, vpv, upv, dv) = (
		split256(u), split256(v), split256(r), split256(tw), split256(folded), split256(vpn),
		split256(upn), split256(dn),
	);

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw_ = witness.init_table(table_id, NROWS)?;
		let mut seg = tw_.full_segment();
		for row in 0..NROWS {
			wc64(&mut seg, beta_col, row, beta())?;
			for i in 0..4 {
				wc64(&mut seg, cu[i], row, uv[i])?;
				wc64(&mut seg, cv[i], row, vv[i])?;
				wc64(&mut seg, cr[i], row, rv[i])?;
				wc64(&mut seg, ct[i], row, tv[i])?;
				wc64(&mut seg, cf[i], row, fv[i])?;
				wc64(&mut seg, vp[i], row, vpv[i])?;
				wc64(&mut seg, up[i], row, upv[i])?;
				wc64(&mut seg, cd[i], row, dv[i])?;
			}
			pop_b256_mul(&m1, &mut seg, row, vpv, tv)?;
			pop_b256_mul(&m2, &mut seg, row, dv, rv)?;
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let sz = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((sz, folded))
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::{BinaryField128b as B128, Field};
	use binius_field::underlier::WithUnderlier;
	use rand::SeedableRng;

	/// Find the B64->B128 tower constant so GF(2^128) mul = Karatsuba over native B64
	/// muls (validates the decomposition before building the circuit gadget).
	#[test]
	fn find_b128_over_b64_karatsuba() {
		let split = |x: B128| -> (BinaryField64b, BinaryField64b) {
			let u: u128 = x.to_underlier();
			(BinaryField64b::new(u as u64), BinaryField64b::new((u >> 64) as u64))
		};
		let join = |lo: BinaryField64b, hi: BinaryField64b| -> B128 {
			B128::new((lo.to_underlier() as u128) | ((hi.to_underlier() as u128) << 64))
		};
		// Candidate tower constants to test (pattern: B256 used B128(1<<64)).
		let candidates = [1u64 << 32, 1u64 << 63, 1, 2];
		let mut rng = rand::rngs::StdRng::from_seed([0x7c; 32]);
		for &cand in &candidates {
			let alpha = BinaryField64b::new(cand);
			let ok = (0..200).all(|_| {
				let a = <B128 as Field>::random(&mut rng);
				let b = <B128 as Field>::random(&mut rng);
				let (a0, a1) = split(a);
				let (b0, b1) = split(b);
				let z0 = a0 * b0;
				let z2 = a1 * b1;
				let z1 = (a0 + a1) * (b0 + b1) - z0 - z2;
				join(z0 + z2, z1 + z2 * alpha) == a * b
			});
			println!("B64->B128 alpha candidate 0x{cand:x}: Karatsuba matches native = {ok}");
		}
	}

	/// GATE M3b — GF(2^256) multiply proves+verifies IN-CIRCUIT over B256 (nested
	/// Karatsuba over native B64 muls) == the native B256 `*`; a wrong operand changes it.
	#[test]
	fn gf256_mul_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0x25; 32]);
		let a = <OurB256 as Field>::random(&mut rng);
		let b = <OurB256 as Field>::random(&mut rng);
		let (size, got) = prove_verify_b256_mul(a, b).expect("GF(2^256) mul must PROVE+VERIFY over B256");
		assert_eq!(got, a * b, "in-circuit GF(2^256) product != native B256 mul");
		assert_ne!((a + <OurB256 as Field>::ONE) * b, a * b, "product not bound to a");
		println!(
			"GATE M3b gf256-mul: GF(2^256) multiply PROVES+VERIFIES over B256 @L1(128) as nested \
			 Karatsuba over native B64 muls (α₈=B128(1<<64), α₇=B64(1<<32)) == native B256 *; \
			 proof = {size} bytes"
		);
	}

	/// GATE M3 — the FRI fold u+(v-u)·r over the FULL B256 field (NIST L1) proves+
	/// verifies in-circuit == the native B256 fold; wrong challenge changes it.
	#[test]
	fn b256_fri_fold_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0xF0; 32]);
		let u = <OurB256 as Field>::random(&mut rng);
		let v = <OurB256 as Field>::random(&mut rng);
		let r = <OurB256 as Field>::random(&mut rng);
		let (size, got) = prove_verify_b256_fold(u, v, r).expect("B256 FRI fold must PROVE+VERIFY");
		assert_eq!(got, u + (v - u) * r, "in-circuit B256 fold != native");
		assert_ne!(u + (v - u) * (r + <OurB256 as Field>::ONE), got, "fold not bound to r");
		println!(
			"GATE M3 b256-fold: FRI fold u+(v-u)·r over the FULL B256 field (NIST L1, via M3b \
			 GF(2^256) mul) PROVES+VERIFIES == native B256 fold; proof = {size} bytes"
		);
	}

	/// GATE M3c — the exact FRI fold_pair (with domain twiddle) proves+verifies
	/// in-circuit over B256 == binius fold_pair; a wrong twiddle changes the result.
	#[test]
	fn b256_fold_pair_proves_over_b256() {
		let mut rng = rand::rngs::StdRng::from_seed([0xFC; 32]);
		let u = <OurB256 as Field>::random(&mut rng);
		let v = <OurB256 as Field>::random(&mut rng);
		let r = <OurB256 as Field>::random(&mut rng);
		let tw = <OurB256 as Field>::random(&mut rng);
		let want = fold_pair_native(u, v, r, tw);
		let (size, got) = prove_verify_b256_fold_pair(u, v, r, tw).expect("fold_pair must PROVE+VERIFY");
		assert_eq!(got, want, "in-circuit fold_pair != native");
		assert_ne!(fold_pair_native(u, v, r, tw + <OurB256 as Field>::ONE), want, "not bound to twiddle");
		println!(
			"GATE M3c fold_pair: the exact FRI fold_pair (v'=v+u; u'=u+v'·t; folded=u'+(v'-u')·r) \
			 PROVES+VERIFIES over B256 @L1(128) via 2 GF(2^256) muls == binius fold_pair; proof = {size} bytes"
		);
	}

	#[test]
	fn probe_field_columns_in_b256_tower() {
		let mut rng = rand::rngs::StdRng::from_seed([0x3b; 32]);
		let a64 = <BinaryField64b as Field>::random(&mut rng);
		let b64 = <BinaryField64b as Field>::random(&mut rng);
		match probe_b64_mul(a64, b64) {
			Ok(sz) => println!("PROBE B64: native field-element columns WORK in B256 tower; proof {sz} bytes"),
			Err(e) => println!("PROBE B64: rejected in B256 tower: {e}"),
		}
		let a32 = <BinaryField32b as Field>::random(&mut rng);
		let b32 = <BinaryField32b as Field>::random(&mut rng);
		match probe_b32_mul(a32, b32) {
			Ok(sz) => println!("PROBE B32: native field-element columns WORK in B256 tower; proof {sz} bytes"),
			Err(e) => println!("PROBE B32: rejected in B256 tower: {e}"),
		}
	}
}
