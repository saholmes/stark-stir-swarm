// M3 (kappa_FS) — the PACKING machinery that lets Binius's
// `constraint_system::prove/verify` run over the 512-bit challenge field
// `B512TowerFamily` (tower level 9, NIST L5).
//
// THE WALL (same as b256_packed, one level up): `prove::<U, B512TowerFamily, ..>`
// requires `U: ProverTowerUnderlier<B512TowerFamily>`, i.e. ONE prover underlier `U`
// that `PackScalar`s EVERY tower subfield (B1,B8,B16,B32,B64 AND the 512-bit top B512)
// plus, on the top packed field, `RepackedExtension<PackedType<U,B_sub>>` for each
// subfield and `PackedTransformationFactory`, and `ProverTowerFamily for
// B512TowerFamily`.
//
// PATH TAKEN (NO Binius fork): we define LOCAL packed subfield types `Sub512<S>`
// (transparent over the local `U512` underlier) and implement `PackedField` for them
// with **element-wise** (scalar) arithmetic — trivially correct, and validated against
// scalar ops by `packed_subfield_ops_match_scalar_b512`. The heavy blanket traits
// (`PackedExtension`, `RepackedExtension`, `PackedFieldIndexable`, `PackedDivisible`)
// are derived by Binius for free once `PackScalar` + `WithUnderlier` + `Divisible`
// hold. No Binius file is touched.
//
// Layout invariant that makes the `PackedExtension` casts SEMANTICALLY correct: `U512`
// is little-endian `[u128;4]`, and `B512 = lo + hi*x` with `lo,hi` `B256` limbs (each
// itself `lo + hi*x` over `BinaryField128b`). `Sub512<S>::get(i)` reads the i-th
// `S::N_BITS`-bit little-endian chunk of the `U512`; because `B512`'s own tower basis
// over `S` (its `ExtensionField<S>::iter_bases`) enumerates exactly those same chunks
// in the same order, reinterpreting a `U512` between `PackedType<U512,B512>` (=B512,
// width 1) and `Sub512<S>` yields the tower-consistent subfield coordinates.

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

use crate::b512_field::{B512TowerFamily, B512, U512};

// ---------------------------------------------------------------------------
// U512 chunk get/set. `n_bits <= 128` and offsets are multiples of `n_bits`, and 128
// is a multiple of `n_bits`, so an `n_bits`-chunk NEVER straddles a 128-bit limb
// boundary — each chunk lies entirely within one `u128` limb (there are four).
// ---------------------------------------------------------------------------

#[inline]
fn chunk_mask(n_bits: usize) -> u128 {
	if n_bits >= 128 {
		u128::MAX
	} else {
		(1u128 << n_bits) - 1
	}
}

impl U512 {
	#[inline]
	fn get_chunk(self, bit_off: usize, n_bits: usize) -> u128 {
		let limb = bit_off >> 7; // bit_off / 128, in 0..4
		let pos = bit_off & 127;
		(self.0[limb] >> pos) & chunk_mask(n_bits)
	}

	#[inline]
	fn set_chunk(&mut self, bit_off: usize, n_bits: usize, v: u128) {
		let limb = bit_off >> 7;
		let pos = bit_off & 127;
		let m = chunk_mask(n_bits);
		self.0[limb] = (self.0[limb] & !(m << pos)) | ((v & m) << pos);
	}
}

// ---------------------------------------------------------------------------
// SubScalar: per-field bit read/write into a U512. One tiny impl per tower level.
// ---------------------------------------------------------------------------

/// A tower subfield that can be read from / written to an `n`-bit slot of a `U512`.
pub trait SubScalar:
	BinaryField + WithUnderlier + Square + InvertOrZero + Mul<Output = Self>
{
	/// Read the `i`-th `Self::N_BITS`-bit little-endian slot of `u` as a scalar.
	fn read(u: U512, i: usize) -> Self;
	/// Write scalar `v` into the `i`-th slot of `u`.
	fn write(u: &mut U512, i: usize, v: Self);
}

macro_rules! impl_sub_scalar_prim {
	($field:ty, $prim:ty) => {
		impl SubScalar for $field {
			#[inline]
			fn read(u: U512, i: usize) -> Self {
				let v = u.get_chunk(
					i * <$field as BinaryField>::N_BITS,
					<$field as BinaryField>::N_BITS,
				);
				<$field>::from_underlier(v as $prim)
			}
			#[inline]
			fn write(u: &mut U512, i: usize, v: Self) {
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
// The REAL BinaryField128b (NOT our B512): needed only so that our top field `B512` is
// a `PackedExtension<BinaryField128b>`, which binius_m3's
// `into_multilinear_extension_index` demands (it hard-codes the tower's 128-bit level
// to `BinaryField128b`). `n_bits == 128` chunks land exactly on a `u128` limb
// boundary, so `get_chunk`/`set_chunk` handle them.
impl_sub_scalar_prim!(RealB128, u128);

impl SubScalar for B1 {
	#[inline]
	fn read(u: U512, i: usize) -> Self {
		let bit = u.get_chunk(i, 1) as u8;
		B1::from_underlier(binius_field::underlier::U1::new(bit))
	}
	#[inline]
	fn write(u: &mut U512, i: usize, v: Self) {
		u.set_chunk(i, 1, u128::from(v.to_underlier().val()));
	}
}

// ---------------------------------------------------------------------------
// Sub512<S> — a packed field of `512/S::N_BITS` copies of `S`, transparent U512.
// ---------------------------------------------------------------------------

/// Packed tower subfield over the local 512-bit underlier. Element-wise arithmetic.
#[repr(transparent)]
pub struct Sub512<S: SubScalar>(pub U512, PhantomData<S>);

impl<S: SubScalar> Sub512<S> {
	#[inline]
	const fn new(u: U512) -> Self {
		Self(u, PhantomData)
	}
	#[inline]
	const fn width() -> usize {
		512 / S::N_BITS
	}
}

// Manual trait impls that must NOT carry an `S`-bound beyond `SubScalar`.
impl<S: SubScalar> Clone for Sub512<S> {
	#[inline]
	fn clone(&self) -> Self {
		*self
	}
}
impl<S: SubScalar> Copy for Sub512<S> {}
impl<S: SubScalar> PartialEq for Sub512<S> {
	#[inline]
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}
impl<S: SubScalar> Eq for Sub512<S> {}
impl<S: SubScalar> Default for Sub512<S> {
	#[inline]
	fn default() -> Self {
		Self::new(U512::default())
	}
}
impl<S: SubScalar> std::fmt::Debug for Sub512<S> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Sub512<{}bit>[", S::N_BITS)?;
		for i in 0..Self::width() {
			if i != 0 {
				write!(f, ",")?;
			}
			write!(f, "{}", S::read(self.0, i))?;
		}
		write!(f, "]")
	}
}

// SAFETY: repr(transparent) over U512, whose all-zero pattern is a valid (zero) value.
unsafe impl<S: SubScalar> Zeroable for Sub512<S> {}

// SAFETY: Sub512<S> is repr(transparent) over U512.
unsafe impl<S: SubScalar> WithUnderlier for Sub512<S> {
	type Underlier = U512;
	#[inline]
	fn to_underlier(self) -> U512 {
		self.0
	}
	#[inline]
	fn to_underlier_ref(&self) -> &U512 {
		&self.0
	}
	#[inline]
	fn to_underlier_ref_mut(&mut self) -> &mut U512 {
		&mut self.0
	}
	#[inline]
	fn to_underliers_ref(val: &[Self]) -> &[U512] {
		unsafe { std::slice::from_raw_parts(val.as_ptr().cast::<U512>(), val.len()) }
	}
	#[inline]
	fn to_underliers_ref_mut(val: &mut [Self]) -> &mut [U512] {
		unsafe { std::slice::from_raw_parts_mut(val.as_mut_ptr().cast::<U512>(), val.len()) }
	}
	#[inline]
	fn from_underlier(val: U512) -> Self {
		Self::new(val)
	}
	#[inline]
	fn from_underlier_ref(val: &U512) -> &Self {
		unsafe { &*(val as *const U512).cast::<Self>() }
	}
	#[inline]
	fn from_underlier_ref_mut(val: &mut U512) -> &mut Self {
		unsafe { &mut *(val as *mut U512).cast::<Self>() }
	}
	#[inline]
	fn from_underliers_ref(val: &[U512]) -> &[Self] {
		unsafe { std::slice::from_raw_parts(val.as_ptr().cast::<Self>(), val.len()) }
	}
	#[inline]
	fn from_underliers_ref_mut(val: &mut [U512]) -> &mut [Self] {
		unsafe { std::slice::from_raw_parts_mut(val.as_mut_ptr().cast::<Self>(), val.len()) }
	}
}

// --- Arithmetic (element-wise) ---------------------------------------------

#[inline]
fn xor512(a: U512, b: U512) -> U512 {
	U512([
		a.0[0] ^ b.0[0],
		a.0[1] ^ b.0[1],
		a.0[2] ^ b.0[2],
		a.0[3] ^ b.0[3],
	])
}

impl<S: SubScalar> Add for Sub512<S> {
	type Output = Self;
	#[inline]
	fn add(self, rhs: Self) -> Self {
		Self::new(xor512(self.0, rhs.0))
	}
}
impl<S: SubScalar> Sub for Sub512<S> {
	type Output = Self;
	#[inline]
	fn sub(self, rhs: Self) -> Self {
		self + rhs // characteristic 2
	}
}
impl<S: SubScalar> Mul for Sub512<S> {
	type Output = Self;
	#[inline]
	fn mul(self, rhs: Self) -> Self {
		<Self as PackedField>::from_fn(|i| S::read(self.0, i) * S::read(rhs.0, i))
	}
}
impl<S: SubScalar> AddAssign for Sub512<S> {
	#[inline]
	fn add_assign(&mut self, rhs: Self) {
		*self = *self + rhs;
	}
}
impl<S: SubScalar> SubAssign for Sub512<S> {
	#[inline]
	fn sub_assign(&mut self, rhs: Self) {
		*self = *self - rhs;
	}
}
impl<S: SubScalar> MulAssign for Sub512<S> {
	#[inline]
	fn mul_assign(&mut self, rhs: Self) {
		*self = *self * rhs;
	}
}

// Scalar-rhs ops (broadcast then op).
impl<S: SubScalar> Add<S> for Sub512<S> {
	type Output = Self;
	#[inline]
	fn add(self, rhs: S) -> Self {
		self + <Self as PackedField>::broadcast(rhs)
	}
}
impl<S: SubScalar> Sub<S> for Sub512<S> {
	type Output = Self;
	#[inline]
	fn sub(self, rhs: S) -> Self {
		self + <Self as PackedField>::broadcast(rhs)
	}
}
impl<S: SubScalar> Mul<S> for Sub512<S> {
	type Output = Self;
	#[inline]
	fn mul(self, rhs: S) -> Self {
		self * <Self as PackedField>::broadcast(rhs)
	}
}
impl<S: SubScalar> AddAssign<S> for Sub512<S> {
	#[inline]
	fn add_assign(&mut self, rhs: S) {
		*self = *self + rhs;
	}
}
impl<S: SubScalar> SubAssign<S> for Sub512<S> {
	#[inline]
	fn sub_assign(&mut self, rhs: S) {
		*self = *self - rhs;
	}
}
impl<S: SubScalar> MulAssign<S> for Sub512<S> {
	#[inline]
	fn mul_assign(&mut self, rhs: S) {
		*self = *self * rhs;
	}
}

impl<S: SubScalar> iter::Sum for Sub512<S> {
	fn sum<I: Iterator<Item = Self>>(it: I) -> Self {
		it.fold(Self::default(), |a, b| a + b)
	}
}
impl<S: SubScalar> iter::Product for Sub512<S> {
	fn product<I: Iterator<Item = Self>>(it: I) -> Self {
		it.fold(<Self as PackedField>::broadcast(S::ONE), |a, b| a * b)
	}
}

// --- PackedField ------------------------------------------------------------

impl<S: SubScalar> PackedField for Sub512<S> {
	type Scalar = S;
	const LOG_WIDTH: usize = {
		let w = 512 / S::N_BITS;
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
		let mk = |rng: &mut dyn RngCore| rng.next_u64() as u128 | ((rng.next_u64() as u128) << 64);
		Self::new(U512([mk(&mut rng), mk(&mut rng), mk(&mut rng), mk(&mut rng)]))
	}
	#[inline]
	fn broadcast(scalar: S) -> Self {
		let mut u = U512::default();
		for i in 0..Self::width() {
			S::write(&mut u, i, scalar);
		}
		Self::new(u)
	}
	#[inline]
	fn from_fn(mut f: impl FnMut(usize) -> S) -> Self {
		let mut u = U512::default();
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

// --- PackScalar wiring for U512 --------------------------------------------

macro_rules! impl_pack_scalar {
	($field:ty) => {
		impl PackScalar<$field> for U512 {
			type Packed = Sub512<$field>;
		}
	};
}
impl_pack_scalar!(B1);
impl_pack_scalar!(B8);
impl_pack_scalar!(B16);
impl_pack_scalar!(B32);
impl_pack_scalar!(B64);
impl_pack_scalar!(RealB128);

// --- Divisible<uN> for U512 (byte/word reinterpret; little-endian) ---------
// Enables Binius's blanket `PackedFieldIndexable`/`PackedDivisible` for the
// byte-aligned subfield packed types and for B512 itself.

macro_rules! impl_divisible {
	($prim:ty) => {
		unsafe impl Divisible<$prim> for U512 {
			type Array = [$prim; 512 / (8 * std::mem::size_of::<$prim>())];
			#[inline]
			fn split_val(self) -> Self::Array {
				bytemuck::must_cast(self.0)
			}
			#[inline]
			fn split_ref(&self) -> &[$prim] {
				bytemuck::must_cast_ref::<[u128; 4], [$prim; 512 / (8 * std::mem::size_of::<$prim>())]>(
					&self.0,
				)
			}
			#[inline]
			fn split_mut(&mut self) -> &mut [$prim] {
				bytemuck::must_cast_mut::<[u128; 4], [$prim; 512 / (8 * std::mem::size_of::<$prim>())]>(
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
// ProverTowerFamily: FastB128 = B512 (identity fast field; there is no polyval-512,
// and the prover only needs an isomorphism — identity is one).
// ===========================================================================

/// The identity F2-linear transformation on B512 (512 standard basis images).
fn b512_identity_transformation() -> FieldLinearTransformation<B512, Vec<B512>> {
	FieldLinearTransformation::new(
		(0..<B512 as ExtensionField<B1>>::DEGREE)
			.map(|i| <B512 as ExtensionField<B1>>::basis(i))
			.collect::<Vec<_>>(),
	)
}

// B512 is its own width-1 packed field (Binius blanket `impl<F:Field> PackedField for
// F`); make it a transformation factory to itself via the identity map.
impl PackedTransformationFactory<B512> for B512 {
	type PackedTransformation<Data: AsRef<[B512]> + Sync> = IDTransformation;
	fn make_packed_transformation<Data: AsRef<[B512]> + Sync>(
		_transformation: FieldLinearTransformation<B512, Data>,
	) -> Self::PackedTransformation<Data> {
		IDTransformation
	}
}

impl ProverTowerFamily for B512TowerFamily {
	type FastB128 = B512;

	fn packed_transformation_to_fast<Top, FastTop>() -> impl Transformation<Top, FastTop>
	where
		Top: PackedTop<Self> + PackedTransformationFactory<FastTop>,
		FastTop: PackedField<Scalar = Self::FastB128>,
	{
		Top::make_packed_transformation(b512_identity_transformation())
	}

	fn packed_transformation_from_fast<FastTop, Top>() -> impl Transformation<FastTop, Top>
	where
		FastTop: PackedTransformationFactory<Top>,
		Top: PackedField<Scalar = Self::B128>,
	{
		FastTop::make_packed_transformation(b512_identity_transformation())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_field::{
		PackedBinaryField16x32b, PackedBinaryField32x16b, PackedBinaryField512x1b,
		PackedBinaryField64x8b, PackedBinaryField8x64b, PackedField,
	};
	use rand::{rngs::StdRng, SeedableRng};

	fn seq<P: PackedField>(p: P) -> Vec<P::Scalar> {
		p.iter().collect()
	}

	// THE CORRECTNESS GATE (the landmine). For every packed subfield type `Sub512<S>`,
	// cross-check EVERY operation (add / mul / square / invert / broadcast / get-set /
	// interleave / unzip) against Binius's OWN canonical 512-bit packed type for the
	// same scalar (an independent, battle-tested implementation). Feeding both the same
	// scalar sequence and comparing the resulting scalar sequences validates BOTH the
	// packed bit-layout AND the arithmetic. A mismatch here would be a silent
	// soundness hole, so this MUST pass before any proof over B512 means anything.
	macro_rules! xcheck {
		($S:ty, $Ref:ty, $rng:expr) => {{
			type Mine = Sub512<$S>;
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
	fn packed_subfield_ops_match_scalar_b512() {
		let mut rng = StdRng::from_seed([11u8; 32]);
		xcheck!(B1, PackedBinaryField512x1b, &mut rng);
		xcheck!(B8, PackedBinaryField64x8b, &mut rng);
		xcheck!(B16, PackedBinaryField32x16b, &mut rng);
		xcheck!(B32, PackedBinaryField16x32b, &mut rng);
		xcheck!(B64, PackedBinaryField8x64b, &mut rng);
		println!(
			"packed_subfield_ops_match_scalar_b512: Sub512<B1/B8/B16/B32/B64> add/mul/square/\
			 invert/broadcast/interleave/unzip all agree with Binius canonical 512-bit packed types."
		);
	}

	// THE RING-SWITCH LANDMINE GATE at level 9.
	//
	// The ring-switch PCS transpose reinterprets a slice of the width-1 top field
	// `B512` as `PackedExtension::<S>::PackedSubfield = Sub512<S>` and treats lane `i`
	// of that packed subfield as the `i`-th tower-basis coordinate of the `B512`
	// scalar. For the transpose (hence the whole small-field opening) to be SOUND,
	// `Sub512<S>::get(i)` MUST equal `<B512 as ExtensionField<S>>::iter_bases()[i]` for
	// every subfield `S`. A width or byte-layout error here would make the transpose
	// silently emit a WRONG tensor element -> a proof that verifies a WRONG evaluation.
	#[test]
	fn b512_packed_extension_roundtrip() {
		use binius_field::{ExtensionField, Field, PackedExtension};
		let mut rng = StdRng::from_seed([29u8; 32]);
		macro_rules! check_bx {
			($S:ty, $expect_width:expr) => {{
				assert_eq!(
					<B512 as ExtensionField<$S>>::DEGREE,
					$expect_width,
					"ExtensionField degree (== PackedSubfield width) for {}bit subfield",
					<$S as BinaryField>::N_BITS
				);
				assert_eq!(
					<Sub512<$S>>::width(),
					$expect_width,
					"Sub512 packed width for {}bit subfield",
					<$S as BinaryField>::N_BITS
				);
				for _ in 0..500 {
					let x = <B512 as Field>::random(&mut rng);
					// Tower-basis subfield coordinates of the SCALAR B512.
					let bases: Vec<$S> = <B512 as ExtensionField<$S>>::iter_bases(&x).collect();
					assert_eq!(bases.len(), $expect_width);
					// The exact cast the PCS transpose uses: width-1 B512 -> Sub512<S>.
					let packed: Sub512<$S> = <B512 as PackedExtension<$S>>::cast_base(x);
					for i in 0..$expect_width {
						assert_eq!(
							packed.get(i),
							bases[i],
							"lane {} mismatch for {}bit subfield (PCS transpose would be WRONG)",
							i,
							<$S as BinaryField>::N_BITS
						);
					}
					// Round-trip: cast back up recovers the exact B512.
					let back: B512 = <B512 as PackedExtension<$S>>::cast_ext(packed);
					assert_eq!(back, x, "cast_base/cast_ext round-trip");
				}
			}};
		}
		check_bx!(B1, 512);
		check_bx!(B8, 64);
		check_bx!(B16, 32);
		check_bx!(B32, 16);
		check_bx!(B64, 8);
		println!(
			"b512_packed_extension_roundtrip: for S in B1/B8/B16/B32/B64, Sub512<S>::get(i) == \
			 <B512 as ExtensionField<S>>::iter_bases()[i] and cast round-trips; PackedSubfield \
			 widths 512/64/32/16/8 as required by square_transpose."
		);
	}
}
