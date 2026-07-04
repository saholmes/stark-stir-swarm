// M3 (kappa_FS) Phase-1b — the PACKING machinery that lets Binius's
// `constraint_system::prove/verify` run over the 256-bit challenge field
// `B256TowerFamily`.
//
// THE WALL (documented in b256_field.rs): `prove::<U, B256TowerFamily, ..>`
// requires `U: ProverTowerUnderlier<B256TowerFamily>`, i.e. ONE prover underlier
// `U` that `PackScalar`s EVERY tower subfield (B1,B8,B16,B32,B64 AND the 256-bit
// top B256) plus, on the top packed field, `RepackedExtension<PackedType<U,B_sub>>`
// for each subfield and `PackedTransformationFactory`, and `ProverTowerFamily for
// B256TowerFamily`.
//
// PATH TAKEN (Path A' — NO Binius fork): Binius's generic `PackedPrimitiveType`
// and its `UnderlierWithBitConstants`/`TowerConstants` packed-arithmetic machinery
// are `pub(crate)`/`pub(super)` — NOT nameable from this crate. So the "reuse the
// generic packed multiply" route of Path A is not reachable without patching
// Binius. Instead we define LOCAL packed subfield types `Sub256<S>` (transparent
// over the local `U256` underlier) and implement `PackedField` for them with
// **element-wise** (scalar) arithmetic — trivially correct, and validated against
// scalar ops by `packed_subfield_ops_match_scalar`. The heavy blanket traits
// (`PackedExtension`, `RepackedExtension`, `PackedFieldIndexable`,
// `PackedDivisible`) are derived by Binius for free once `PackScalar` +
// `WithUnderlier` + `Divisible` hold. No Binius file is touched.
//
// Layout invariant that makes the `PackedExtension` casts SEMANTICALLY correct:
// `U256` is little-endian `[u128;2]`, and `B256 = lo + hi*x` with `lo,hi`
// `BinaryField128b` limbs. `Sub256<S>::get(i)` reads the i-th `S::N_BITS`-bit
// little-endian chunk of the `U256`; because `B256`'s own tower basis over `S`
// (its `ExtensionField<S>::iter_bases`) enumerates exactly those same chunks in
// the same order, reinterpreting a `U256` between `PackedType<U256,B256>` (=B256,
// width 1) and `Sub256<S>` yields the tower-consistent subfield coordinates.

use std::{
	iter,
	marker::PhantomData,
	ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};

use binius_field::{
	arithmetic_traits::{InvertOrZero, Square},
	as_packed_field::PackScalar,
	linear_transformation::{
		FieldLinearTransformation, IDTransformation, PackedTransformationFactory, Transformation,
	},
	tower::{PackedTop, ProverTowerFamily},
	underlier::{Divisible, WithUnderlier},
	BinaryField, BinaryField128b as RealB128, BinaryField1b as B1, BinaryField16b as B16,
	BinaryField32b as B32, BinaryField64b as B64, BinaryField8b as B8, ExtensionField, PackedField,
};
use bytemuck::Zeroable;
use rand::RngCore;

use crate::b256_field::{B256TowerFamily, U256, B256};

// ---------------------------------------------------------------------------
// U256 chunk get/set. `n_bits <= 64` and offsets are multiples of `n_bits`, and
// 128 is a multiple of `n_bits`, so an `n_bits`-chunk NEVER straddles the 128-bit
// limb boundary — each chunk lies entirely within one `u128` limb.
// ---------------------------------------------------------------------------

#[inline]
fn chunk_mask(n_bits: usize) -> u128 {
	if n_bits >= 128 {
		u128::MAX
	} else {
		(1u128 << n_bits) - 1
	}
}

impl U256 {
	#[inline]
	fn get_chunk(self, bit_off: usize, n_bits: usize) -> u128 {
		let limb = usize::from(bit_off >= 128);
		let pos = bit_off & 127;
		(self.0[limb] >> pos) & chunk_mask(n_bits)
	}

	#[inline]
	fn set_chunk(&mut self, bit_off: usize, n_bits: usize, v: u128) {
		let limb = usize::from(bit_off >= 128);
		let pos = bit_off & 127;
		let m = chunk_mask(n_bits);
		self.0[limb] = (self.0[limb] & !(m << pos)) | ((v & m) << pos);
	}
}

// ---------------------------------------------------------------------------
// SubScalar: per-field bit read/write into a U256. One tiny impl per tower level.
// ---------------------------------------------------------------------------

/// A tower subfield that can be read from / written to an `n`-bit slot of a `U256`.
pub trait SubScalar:
	BinaryField + WithUnderlier + Square + InvertOrZero + Mul<Output = Self>
{
	/// Read the `i`-th `Self::N_BITS`-bit little-endian slot of `u` as a scalar.
	fn read(u: U256, i: usize) -> Self;
	/// Write scalar `v` into the `i`-th slot of `u`.
	fn write(u: &mut U256, i: usize, v: Self);
}

macro_rules! impl_sub_scalar_prim {
	($field:ty, $prim:ty) => {
		impl SubScalar for $field {
			#[inline]
			fn read(u: U256, i: usize) -> Self {
				let v = u.get_chunk(i * <$field as BinaryField>::N_BITS, <$field as BinaryField>::N_BITS);
				<$field>::from_underlier(v as $prim)
			}
			#[inline]
			fn write(u: &mut U256, i: usize, v: Self) {
				u.set_chunk(
					i * <$field as BinaryField>::N_BITS,
					<$field as BinaryField>::N_BITS,
					v.to_underlier() as u128,
				);
			}
		}
	};
}

impl_sub_scalar_prim!(B8, u8);
impl_sub_scalar_prim!(B16, u16);
impl_sub_scalar_prim!(B32, u32);
impl_sub_scalar_prim!(B64, u64);
// The REAL BinaryField128b (NOT our B256): needed only so that our top field
// `B256` is a `PackedExtension<BinaryField128b>`, which binius_m3's
// `into_multilinear_extension_index` demands (it hard-codes the tower's 128-bit
// level to `BinaryField128b`). `n_bits == 128` chunks land exactly on a `u128`
// limb boundary, so `get_chunk`/`set_chunk` handle them.
impl_sub_scalar_prim!(RealB128, u128);

impl SubScalar for B1 {
	#[inline]
	fn read(u: U256, i: usize) -> Self {
		let bit = u.get_chunk(i, 1) as u8;
		B1::from_underlier(binius_field::underlier::U1::new(bit))
	}
	#[inline]
	fn write(u: &mut U256, i: usize, v: Self) {
		u.set_chunk(i, 1, u128::from(v.to_underlier().val()));
	}
}

// ---------------------------------------------------------------------------
// Sub256<S> — a packed field of `256/S::N_BITS` copies of `S`, transparent U256.
// ---------------------------------------------------------------------------

/// Packed tower subfield over the local 256-bit underlier. Element-wise arithmetic.
#[repr(transparent)]
pub struct Sub256<S: SubScalar>(pub U256, PhantomData<S>);

impl<S: SubScalar> Sub256<S> {
	#[inline]
	const fn new(u: U256) -> Self {
		Self(u, PhantomData)
	}
	#[inline]
	const fn width() -> usize {
		256 / S::N_BITS
	}
}

// Manual trait impls that must NOT carry an `S`-bound beyond `SubScalar`.
impl<S: SubScalar> Clone for Sub256<S> {
	#[inline]
	fn clone(&self) -> Self {
		*self
	}
}
impl<S: SubScalar> Copy for Sub256<S> {}
impl<S: SubScalar> PartialEq for Sub256<S> {
	#[inline]
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}
impl<S: SubScalar> Eq for Sub256<S> {}
impl<S: SubScalar> Default for Sub256<S> {
	#[inline]
	fn default() -> Self {
		Self::new(U256::default())
	}
}
impl<S: SubScalar> std::fmt::Debug for Sub256<S> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Sub256<{}bit>[", S::N_BITS)?;
		for i in 0..Self::width() {
			if i != 0 {
				write!(f, ",")?;
			}
			write!(f, "{}", S::read(self.0, i))?;
		}
		write!(f, "]")
	}
}

// SAFETY: repr(transparent) over U256, whose all-zero pattern is a valid (zero) value.
unsafe impl<S: SubScalar> Zeroable for Sub256<S> {}

// SAFETY: Sub256<S> is repr(transparent) over U256.
unsafe impl<S: SubScalar> WithUnderlier for Sub256<S> {
	type Underlier = U256;
	#[inline]
	fn to_underlier(self) -> U256 {
		self.0
	}
	#[inline]
	fn to_underlier_ref(&self) -> &U256 {
		&self.0
	}
	#[inline]
	fn to_underlier_ref_mut(&mut self) -> &mut U256 {
		&mut self.0
	}
	#[inline]
	fn to_underliers_ref(val: &[Self]) -> &[U256] {
		unsafe { std::slice::from_raw_parts(val.as_ptr().cast::<U256>(), val.len()) }
	}
	#[inline]
	fn to_underliers_ref_mut(val: &mut [Self]) -> &mut [U256] {
		unsafe { std::slice::from_raw_parts_mut(val.as_mut_ptr().cast::<U256>(), val.len()) }
	}
	#[inline]
	fn from_underlier(val: U256) -> Self {
		Self::new(val)
	}
	#[inline]
	fn from_underlier_ref(val: &U256) -> &Self {
		unsafe { &*(val as *const U256).cast::<Self>() }
	}
	#[inline]
	fn from_underlier_ref_mut(val: &mut U256) -> &mut Self {
		unsafe { &mut *(val as *mut U256).cast::<Self>() }
	}
	#[inline]
	fn from_underliers_ref(val: &[U256]) -> &[Self] {
		unsafe { std::slice::from_raw_parts(val.as_ptr().cast::<Self>(), val.len()) }
	}
	#[inline]
	fn from_underliers_ref_mut(val: &mut [U256]) -> &mut [Self] {
		unsafe { std::slice::from_raw_parts_mut(val.as_mut_ptr().cast::<Self>(), val.len()) }
	}
}

// --- Arithmetic (element-wise) ---------------------------------------------

impl<S: SubScalar> Add for Sub256<S> {
	type Output = Self;
	#[inline]
	fn add(self, rhs: Self) -> Self {
		Self::new(U256([self.0 .0[0] ^ rhs.0 .0[0], self.0 .0[1] ^ rhs.0 .0[1]]))
	}
}
impl<S: SubScalar> Sub for Sub256<S> {
	type Output = Self;
	#[inline]
	fn sub(self, rhs: Self) -> Self {
		self + rhs // characteristic 2
	}
}
impl<S: SubScalar> Mul for Sub256<S> {
	type Output = Self;
	#[inline]
	fn mul(self, rhs: Self) -> Self {
		<Self as PackedField>::from_fn(|i| S::read(self.0, i) * S::read(rhs.0, i))
	}
}
impl<S: SubScalar> AddAssign for Sub256<S> {
	#[inline]
	fn add_assign(&mut self, rhs: Self) {
		*self = *self + rhs;
	}
}
impl<S: SubScalar> SubAssign for Sub256<S> {
	#[inline]
	fn sub_assign(&mut self, rhs: Self) {
		*self = *self - rhs;
	}
}
impl<S: SubScalar> MulAssign for Sub256<S> {
	#[inline]
	fn mul_assign(&mut self, rhs: Self) {
		*self = *self * rhs;
	}
}

// Scalar-rhs ops (broadcast then op).
impl<S: SubScalar> Add<S> for Sub256<S> {
	type Output = Self;
	#[inline]
	fn add(self, rhs: S) -> Self {
		self + <Self as PackedField>::broadcast(rhs)
	}
}
impl<S: SubScalar> Sub<S> for Sub256<S> {
	type Output = Self;
	#[inline]
	fn sub(self, rhs: S) -> Self {
		self + <Self as PackedField>::broadcast(rhs)
	}
}
impl<S: SubScalar> Mul<S> for Sub256<S> {
	type Output = Self;
	#[inline]
	fn mul(self, rhs: S) -> Self {
		self * <Self as PackedField>::broadcast(rhs)
	}
}
impl<S: SubScalar> AddAssign<S> for Sub256<S> {
	#[inline]
	fn add_assign(&mut self, rhs: S) {
		*self = *self + rhs;
	}
}
impl<S: SubScalar> SubAssign<S> for Sub256<S> {
	#[inline]
	fn sub_assign(&mut self, rhs: S) {
		*self = *self - rhs;
	}
}
impl<S: SubScalar> MulAssign<S> for Sub256<S> {
	#[inline]
	fn mul_assign(&mut self, rhs: S) {
		*self = *self * rhs;
	}
}

impl<S: SubScalar> iter::Sum for Sub256<S> {
	fn sum<I: Iterator<Item = Self>>(it: I) -> Self {
		it.fold(Self::default(), |a, b| a + b)
	}
}
impl<S: SubScalar> iter::Product for Sub256<S> {
	fn product<I: Iterator<Item = Self>>(it: I) -> Self {
		it.fold(<Self as PackedField>::broadcast(S::ONE), |a, b| a * b)
	}
}

// --- PackedField ------------------------------------------------------------

impl<S: SubScalar> PackedField for Sub256<S> {
	type Scalar = S;
	const LOG_WIDTH: usize = {
		let w = 256 / S::N_BITS;
		w.trailing_zeros() as usize
	};

	#[inline]
	unsafe fn get_unchecked(&self, i: usize) -> S {
		S::read(self.0, i)
	}
	#[inline]
	unsafe fn set_unchecked(&mut self, i: usize, scalar: S) {
		S::write(&mut self.0, i, scalar);
	}
	#[inline]
	fn random(mut rng: impl RngCore) -> Self {
		Self::new(U256([rng.next_u64() as u128 | ((rng.next_u64() as u128) << 64),
			rng.next_u64() as u128 | ((rng.next_u64() as u128) << 64)]))
	}
	#[inline]
	fn broadcast(scalar: S) -> Self {
		let mut u = U256::default();
		for i in 0..Self::width() {
			S::write(&mut u, i, scalar);
		}
		Self::new(u)
	}
	#[inline]
	fn from_fn(mut f: impl FnMut(usize) -> S) -> Self {
		let mut u = U256::default();
		for i in 0..Self::width() {
			S::write(&mut u, i, f(i));
		}
		Self::new(u)
	}
	#[inline]
	fn square(self) -> Self {
		Self::from_fn(|i| Square::square(S::read(self.0, i)))
	}
	#[inline]
	fn invert_or_zero(self) -> Self {
		Self::from_fn(|i| InvertOrZero::invert_or_zero(S::read(self.0, i)))
	}
	#[inline]
	fn interleave(self, other: Self, log_block_len: usize) -> (Self, Self) {
		let bs = 1usize << log_block_len;
		let nblocks = Self::width() >> log_block_len;
		let a: Vec<S> = self.into_iter().collect();
		let b: Vec<S> = other.into_iter().collect();
		let block = |v: &[S], blk: usize, pos: usize| v[blk * bs + pos];
		let c = Self::from_fn(|idx| {
			let (blk, pos) = (idx / bs, idx % bs);
			if blk % 2 == 0 {
				block(&a, blk, pos)
			} else {
				block(&b, blk - 1, pos)
			}
		});
		let d = Self::from_fn(|idx| {
			let (blk, pos) = (idx / bs, idx % bs);
			if blk % 2 == 0 {
				block(&a, blk + 1, pos)
			} else {
				block(&b, blk, pos)
			}
		});
		let _ = nblocks;
		(c, d)
	}
	#[inline]
	fn unzip(self, other: Self, log_block_len: usize) -> (Self, Self) {
		let bs = 1usize << log_block_len;
		let nblocks = Self::width() >> log_block_len; // per side
		let a: Vec<S> = self.into_iter().collect();
		let b: Vec<S> = other.into_iter().collect();
		// Concatenated block stream C = A-blocks ++ B-blocks.
		let cblock = |blk: usize, pos: usize| -> S {
			if blk < nblocks {
				a[blk * bs + pos]
			} else {
				b[(blk - nblocks) * bs + pos]
			}
		};
		let c = Self::from_fn(|idx| {
			let (blk, pos) = (idx / bs, idx % bs);
			cblock(2 * blk, pos)
		});
		let d = Self::from_fn(|idx| {
			let (blk, pos) = (idx / bs, idx % bs);
			cblock(2 * blk + 1, pos)
		});
		(c, d)
	}
}

// --- PackScalar wiring for U256 --------------------------------------------

macro_rules! impl_pack_scalar {
	($field:ty) => {
		impl PackScalar<$field> for U256 {
			type Packed = Sub256<$field>;
		}
	};
}
impl_pack_scalar!(B1);
impl_pack_scalar!(B8);
impl_pack_scalar!(B16);
impl_pack_scalar!(B32);
impl_pack_scalar!(B64);
impl_pack_scalar!(RealB128);

// --- Divisible<uN> for U256 (byte/word reinterpret; little-endian) ---------
// Enables Binius's blanket `PackedFieldIndexable`/`PackedDivisible` for the
// byte-aligned subfield packed types and for B256 itself.

macro_rules! impl_divisible {
	($prim:ty) => {
		unsafe impl Divisible<$prim> for U256 {
			type Array = [$prim; 256 / (8 * std::mem::size_of::<$prim>())];
			#[inline]
			fn split_val(self) -> Self::Array {
				bytemuck::must_cast(self.0)
			}
			#[inline]
			fn split_ref(&self) -> &[$prim] {
				bytemuck::must_cast_ref::<[u128; 2], [$prim; 256 / (8 * std::mem::size_of::<$prim>())]>(
					&self.0,
				)
			}
			#[inline]
			fn split_mut(&mut self) -> &mut [$prim] {
				bytemuck::must_cast_mut::<[u128; 2], [$prim; 256 / (8 * std::mem::size_of::<$prim>())]>(
					&mut self.0,
				)
			}
		}
	};
}
impl_divisible!(u8);
impl_divisible!(u16);
impl_divisible!(u32);
impl_divisible!(u64);
impl_divisible!(u128);

// ===========================================================================
// ProverTowerFamily: FastB128 = B256 (identity fast field; there is no
// polyval-256, and the prover only needs an isomorphism — identity is one).
// ===========================================================================

/// The identity F2-linear transformation on B256 (256 standard basis images).
fn b256_identity_transformation() -> FieldLinearTransformation<B256, Vec<B256>> {
	FieldLinearTransformation::new(
		(0..<B256 as ExtensionField<B1>>::DEGREE)
			.map(|i| <B256 as ExtensionField<B1>>::basis(i))
			.collect::<Vec<_>>(),
	)
}

// B256 is its own width-1 packed field (Binius blanket `impl<F:Field> PackedField
// for F`); make it a transformation factory to itself via the identity map.
impl PackedTransformationFactory<B256> for B256 {
	type PackedTransformation<Data: AsRef<[B256]> + Sync> = IDTransformation;
	fn make_packed_transformation<Data: AsRef<[B256]> + Sync>(
		_transformation: FieldLinearTransformation<B256, Data>,
	) -> Self::PackedTransformation<Data> {
		IDTransformation
	}
}

impl ProverTowerFamily for B256TowerFamily {
	type FastB128 = B256;

	fn packed_transformation_to_fast<Top, FastTop>() -> impl Transformation<Top, FastTop>
	where
		Top: PackedTop<Self> + PackedTransformationFactory<FastTop>,
		FastTop: PackedField<Scalar = Self::FastB128>,
	{
		Top::make_packed_transformation(b256_identity_transformation())
	}

	fn packed_transformation_from_fast<FastTop, Top>() -> impl Transformation<FastTop, Top>
	where
		FastTop: PackedTransformationFactory<Top>,
		Top: PackedField<Scalar = Self::B128>,
	{
		FastTop::make_packed_transformation(b256_identity_transformation())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::{
		PackedBinaryField16x16b, PackedBinaryField256x1b, PackedBinaryField32x8b,
		PackedBinaryField4x64b, PackedBinaryField8x32b, PackedField,
	};
	use rand::{rngs::StdRng, SeedableRng};

	fn seq<P: PackedField>(p: P) -> Vec<P::Scalar> {
		p.iter().collect()
	}

	// THE CORRECTNESS GATE. For every packed subfield type `Sub256<S>`, cross-check
	// EVERY operation (add / mul / square / invert / broadcast / get-set / interleave
	// / unzip) against Binius's OWN canonical 256-bit packed type for the same scalar
	// (an independent, battle-tested implementation). Feeding both the same scalar
	// sequence and comparing the resulting scalar sequences validates BOTH the packed
	// bit-layout AND the arithmetic. A mismatch here would be a silent soundness hole,
	// so this MUST pass before any proof over B256 means anything.
	macro_rules! xcheck {
		($S:ty, $Ref:ty, $rng:expr) => {{
			type Mine = Sub256<$S>;
			type Ref = $Ref;
			let w = Mine::width();
			assert_eq!(w, Ref::WIDTH, "width mismatch");
			let lw = <Mine as PackedField>::LOG_WIDTH;
			for _ in 0..300 {
				let sa: Vec<$S> = (0..w).map(|_| <$S>::random(&mut *$rng)).collect();
				let sb: Vec<$S> = (0..w).map(|_| <$S>::random(&mut *$rng)).collect();
				let ma = Mine::from_scalars(sa.iter().copied());
				let mb = Mine::from_scalars(sb.iter().copied());
				let ra = Ref::from_scalars(sa.iter().copied());
				let rb = Ref::from_scalars(sb.iter().copied());

				// layout: same scalars come back out
				assert_eq!(seq(ma), seq(ra), "layout/from_scalars");
				// add, mul, square, invert, broadcast
				assert_eq!(seq(ma + mb), seq(ra + rb), "add");
				assert_eq!(seq(ma * mb), seq(ra * rb), "mul");
				assert_eq!(
					seq(PackedField::square(ma)),
					seq(PackedField::square(ra)),
					"square"
				);
				assert_eq!(
					seq(PackedField::invert_or_zero(ma)),
					seq(PackedField::invert_or_zero(ra)),
					"invert_or_zero"
				);
				assert_eq!(
					seq(Mine::broadcast(sa[0])),
					seq(Ref::broadcast(sa[0])),
					"broadcast"
				);
				// interleave / unzip at every valid block length
				for l in 0..lw {
					let (mc, md) = ma.interleave(mb, l);
					let (rc, rd) = ra.interleave(rb, l);
					assert_eq!(seq(mc), seq(rc), "interleave.0 l={}", l);
					assert_eq!(seq(md), seq(rd), "interleave.1 l={}", l);
					let (mu, mv) = ma.unzip(mb, l);
					let (ru, rv) = ra.unzip(rb, l);
					assert_eq!(seq(mu), seq(ru), "unzip.0 l={}", l);
					assert_eq!(seq(mv), seq(rv), "unzip.1 l={}", l);
				}
			}
		}};
	}

	#[test]
	fn packed_subfield_ops_match_scalar() {
		let mut rng = StdRng::from_seed([11u8; 32]);
		xcheck!(B1, PackedBinaryField256x1b, &mut rng);
		xcheck!(B8, PackedBinaryField32x8b, &mut rng);
		xcheck!(B16, PackedBinaryField16x16b, &mut rng);
		xcheck!(B32, PackedBinaryField8x32b, &mut rng);
		xcheck!(B64, PackedBinaryField4x64b, &mut rng);
		println!(
			"packed_subfield_ops_match_scalar: Sub256<B1/B8/B16/B32/B64> add/mul/square/invert/\
			 broadcast/interleave/unzip all agree with Binius canonical 256-bit packed types."
		);
	}

	// STEP 0 — THE RING-SWITCH LANDMINE GATE.
	//
	// The ring-switch PCS transpose (`TensorAlgebra::transpose` -> `square_transpose`)
	// operates on `FE::cast_bases_mut(&mut [FE])`, i.e. it reinterprets a slice of
	// the width-1 top field `B256` as `PackedExtension::<S>::PackedSubfield = Sub256<S>`
	// and treats lane `i` of that packed subfield as the `i`-th tower-basis coordinate
	// of the `B256` scalar. For the transpose (hence the whole small-field opening) to
	// be SOUND, `Sub256<S>::get(i)` MUST equal `<B256 as ExtensionField<S>>::iter_bases()[i]`
	// for every subfield `S`. A width or byte-layout error here would make the transpose
	// silently emit a WRONG tensor element -> a proof that verifies a WRONG evaluation.
	//
	// This gate checks that invariant DIRECTLY (independent of the ops cross-check above,
	// which only compares Sub256 against Binius's canonical packed types fed the same
	// scalars; it does NOT tie the scalar `B256`'s own `iter_bases` to the packed lanes).
	#[test]
	fn b256_packed_extension_transpose_roundtrip() {
		use binius_field::{ExtensionField, Field, PackedExtension};
		let mut rng = StdRng::from_seed([29u8; 32]);
		macro_rules! check_bx {
			($S:ty, $expect_width:expr) => {{
				assert_eq!(
					<B256 as ExtensionField<$S>>::DEGREE,
					$expect_width,
					"ExtensionField degree (== PackedSubfield width) for {}bit subfield",
					<$S as BinaryField>::N_BITS
				);
				assert_eq!(
					<Sub256<$S>>::width(),
					$expect_width,
					"Sub256 packed width for {}bit subfield",
					<$S as BinaryField>::N_BITS
				);
				for _ in 0..500 {
					let x = <B256 as Field>::random(&mut rng);
					// Tower-basis subfield coordinates of the SCALAR B256.
					let bases: Vec<$S> =
						<B256 as ExtensionField<$S>>::iter_bases(&x).collect();
					assert_eq!(bases.len(), $expect_width);
					// The exact cast the PCS transpose uses: width-1 B256 -> Sub256<S>.
					let packed: Sub256<$S> = <B256 as PackedExtension<$S>>::cast_base(x);
					for i in 0..$expect_width {
						assert_eq!(
							packed.get(i),
							bases[i],
							"lane {} mismatch for {}bit subfield (PCS transpose would be WRONG)",
							i,
							<$S as BinaryField>::N_BITS
						);
					}
					// Round-trip: cast back up recovers the exact B256.
					let back: B256 = <B256 as PackedExtension<$S>>::cast_ext(packed);
					assert_eq!(back, x, "cast_base/cast_ext round-trip");
				}
			}};
		}
		check_bx!(B1, 256);
		check_bx!(B8, 32);
		check_bx!(B16, 16);
		check_bx!(B32, 8);
		check_bx!(B64, 4);
		println!(
			"b256_packed_extension_transpose_roundtrip: for S in B1/B8/B16/B32/B64, \
			 Sub256<S>::get(i) == <B256 as ExtensionField<S>>::iter_bases()[i] and cast round-trips; \
			 PackedSubfield widths 256/32/16/8/4 as required by square_transpose."
		);
	}
}
