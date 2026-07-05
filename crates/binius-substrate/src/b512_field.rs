// M3 (kappa_FS milestone) — a 512-bit binary tower field for Binius (NIST L5).
//
// GOAL (the FRI/sumcheck soundness lever, one tower level above b256_field): Binius's
// `constraint_system::prove` fixes the challenge/extension field to
// `FExt<Tower> = <Tower as TowerFamily>::B128`. At NIST L5 (`security_bits = 256`) the
// FRI query-count computation `calculate_n_test_queries::<F, FEncode>` FAILS with
// `ParameterError` for BOTH a 128-bit AND a 256-bit `F`, because the sumcheck /
// folding error terms `poly(N)/|F|` are not negligible against the `2^-256` budget
// (for a 256-bit field they land right at the boundary). Widening `F = FExt<Tower>` to
// a 512-bit field makes those terms `poly(N)/2^512` — negligible against `2^-256` — so
// `calculate_n_test_queries` SUCCEEDS at NIST L5, while `FEncode = Tower::B32` stays the
// real 32-bit Reed–Solomon alphabet.
//
// This module provides that 512-bit field. It is `T_9` in the canonical Fan–Paar
// tower: `T_9 = T_8[x] / (x^2 + alpha*x + 1)` with `T_8 = BinaryTowerField256b` (OUR
// B256, from `b256_field`) and `alpha = the tower generator of T_8` (the element `x`
// of the T_7 -> T_8 extension, i.e. `B256(U256([0,1]))`). Irreducibility of that
// reduction polynomial over GF(2^256) — `Tr_{GF(2^256)/GF(2)}(alpha^-2) = 1` — is
// verified against B256 arithmetic, so this is a REAL GF(2^512), not a stub. All
// arithmetic reuses `B256`'s multiply/invert through the SAME degree-2 tower recursion
// used in `b256_field` (which itself recurses to `BinaryField128b`).
//
// Everything here is ADDITIVE and lives in OUR crate: `B512` and its underlier are
// LOCAL structs, so implementing Binius's foreign traits for them is permitted by the
// orphan rule with NO change to the Binius checkout.

use std::{
	fmt,
	hash::Hash,
	iter,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use binius_field::{
	arithmetic_traits::{InvertOrZero, Square},
	as_packed_field::PackScalar,
	tower::TowerFamily,
	underlier::{UnderlierType, WithUnderlier},
	BinaryField, BinaryField128b as RealB128, BinaryField16b as B16, BinaryField1b as B1,
	BinaryField32b as B32, BinaryField64b as B64, BinaryField8b as B8, Error as FieldError,
	ExtensionField, Field, TowerField,
};
use binius_utils::{
	bytes::{Buf, BufMut},
	DeserializeBytes, SerializationError, SerializationMode, SerializeBytes,
};
use bytemuck::{NoUninit, Pod, Zeroable};
use rand::{
	distributions::{Distribution, Standard},
	Rng, RngCore,
};
use subtle::{Choice, ConstantTimeEq};

use crate::b256_field::{B256, U256};

// ===========================================================================
// 512-bit underlier (a LOCAL type, so it takes NO part in Binius's generic
// `PackScalar for ScaledUnderlier` impl — avoiding a coherence conflict).
// ===========================================================================

/// A 512-bit machine word: four little-endian `u128` limbs `[l0, l1, l2, l3]`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct U512(pub [u128; 4]);

unsafe impl Zeroable for U512 {}
// SAFETY: `[u128; 4]` is a plain-old-data array with no padding or uninit bytes.
unsafe impl NoUninit for U512 {}

impl ConstantTimeEq for U512 {
	fn ct_eq(&self, other: &Self) -> Choice {
		self.0[0].ct_eq(&other.0[0])
			& self.0[1].ct_eq(&other.0[1])
			& self.0[2].ct_eq(&other.0[2])
			& self.0[3].ct_eq(&other.0[3])
	}
}

// Gives `U512: Random` for free via Binius's blanket `impl<T: Standard> Random for T`.
impl Distribution<U512> for Standard {
	fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> U512 {
		U512([rng.gen(), rng.gen(), rng.gen(), rng.gen()])
	}
}

impl UnderlierType for U512 {
	const LOG_BITS: usize = 9; // 512 bits
}

impl U512 {
	/// The low 256-bit half (limbs 0..2) as a `U256`.
	#[inline]
	fn lo(self) -> U256 {
		U256([self.0[0], self.0[1]])
	}
	/// The high 256-bit half (limbs 2..4) as a `U256`.
	#[inline]
	fn hi(self) -> U256 {
		U256([self.0[2], self.0[3]])
	}
	#[inline]
	fn from_halves(lo: U256, hi: U256) -> Self {
		U512([lo.0[0], lo.0[1], hi.0[0], hi.0[1]])
	}
}

// ===========================================================================
// The 512-bit tower field T_9 = T_8[x]/(x^2 + alpha*x + 1), alpha = B256 tower gen.
// Represented as a pair of `B256` limbs (lo, hi) = lo + hi*x.
// ===========================================================================

/// `BinaryTowerField512b` — the canonical Fan–Paar tower field of order `2^512`.
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct BinaryTowerField512b(pub U512);

/// Convenient short alias used throughout the module and tests.
pub type B512 = BinaryTowerField512b;

/// The tower constant `alpha` of the T_8 -> T_9 extension (verified irreducible:
/// `Tr_{GF(2^256)/GF(2)}(alpha^-2) = 1`). It is the tower generator of T_8 = B256,
/// i.e. the element `x` of the T_7 -> T_8 extension: `B256(U256([0, 1]))`.
#[inline]
fn alpha() -> B256 {
	B256::from_underlier(U256([0, 1]))
}

impl B512 {
	#[inline]
	pub fn from_halves(lo: B256, hi: B256) -> Self {
		Self(U512::from_halves(lo.to_underlier(), hi.to_underlier()))
	}
	#[inline]
	pub fn lo(self) -> B256 {
		B256::from_underlier(self.0.lo())
	}
	#[inline]
	pub fn hi(self) -> B256 {
		B256::from_underlier(self.0.hi())
	}
}

// --- Field arithmetic via the degree-2 tower recursion over B256 -----------

#[inline]
fn b512_mul(a: B512, b: B512) -> B512 {
	let (a0, a1) = (a.lo(), a.hi());
	let (b0, b1) = (b.lo(), b.hi());
	let z0 = a0 * b0;
	let z2 = a1 * b1;
	let z0z2 = z0 + z2;
	let z1 = (a0 + a1) * (b0 + b1) - z0z2;
	let z2a = z2 * alpha();
	B512::from_halves(z0z2, z1 + z2a)
}

#[inline]
fn b512_square(a: B512) -> B512 {
	let (a0, a1) = (a.lo(), a.hi());
	let z0 = Square::square(a0);
	let z2 = Square::square(a1);
	let z2a = z2 * alpha();
	B512::from_halves(z0 + z2, z2a)
}

#[inline]
fn b512_invert_or_zero(a: B512) -> B512 {
	let (a0, a1) = (a.lo(), a.hi());
	let a0z1 = a0 + a1 * alpha();
	let delta = a0 * a0z1 + Square::square(a1);
	let delta_inv = InvertOrZero::invert_or_zero(delta);
	let inv0 = delta_inv * a0z1;
	let inv1 = delta_inv * a1;
	B512::from_halves(inv0, inv1)
}

impl Neg for B512 {
	type Output = Self;
	#[inline]
	fn neg(self) -> Self {
		self // characteristic 2
	}
}

#[inline]
fn xor512(a: U512, b: U512) -> U512 {
	U512([
		a.0[0] ^ b.0[0],
		a.0[1] ^ b.0[1],
		a.0[2] ^ b.0[2],
		a.0[3] ^ b.0[3],
	])
}

macro_rules! bin_op {
	($tr:ident, $m:ident, $rhs:ty, $body:expr) => {
		impl $tr<$rhs> for B512 {
			type Output = B512;
			#[inline]
			fn $m(self, rhs: $rhs) -> B512 {
				let f: &dyn Fn(B512, B512) -> B512 = &$body;
				f(self, rhs.into_b512())
			}
		}
	};
}

// Helper to normalise both `B512` and `&B512` rhs into a `B512`.
trait IntoB512 {
	fn into_b512(self) -> B512;
}
impl IntoB512 for B512 {
	#[inline]
	fn into_b512(self) -> B512 {
		self
	}
}
impl IntoB512 for &B512 {
	#[inline]
	fn into_b512(self) -> B512 {
		*self
	}
}

bin_op!(Add, add, B512, |a: B512, b: B512| BinaryTowerField512b(xor512(a.0, b.0)));
bin_op!(Add, add, &B512, |a: B512, b: B512| BinaryTowerField512b(xor512(a.0, b.0)));
bin_op!(Sub, sub, B512, |a: B512, b: B512| BinaryTowerField512b(xor512(a.0, b.0)));
bin_op!(Sub, sub, &B512, |a: B512, b: B512| BinaryTowerField512b(xor512(a.0, b.0)));
bin_op!(Mul, mul, B512, |a, b| b512_mul(a, b));
bin_op!(Mul, mul, &B512, |a, b| b512_mul(a, b));

macro_rules! assign_op {
	($tr:ident, $m:ident, $base:ident, $bm:ident, $rhs:ty) => {
		impl $tr<$rhs> for B512 {
			#[inline]
			fn $m(&mut self, rhs: $rhs) {
				*self = $base::$bm(*self, rhs);
			}
		}
	};
}
assign_op!(AddAssign, add_assign, Add, add, B512);
assign_op!(AddAssign, add_assign, Add, add, &B512);
assign_op!(SubAssign, sub_assign, Sub, sub, B512);
assign_op!(SubAssign, sub_assign, Sub, sub, &B512);
assign_op!(MulAssign, mul_assign, Mul, mul, B512);
assign_op!(MulAssign, mul_assign, Mul, mul, &B512);

impl iter::Sum for B512 {
	fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
		iter.fold(Self::ZERO, |a, b| a + b)
	}
}
impl<'a> iter::Sum<&'a Self> for B512 {
	fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
		iter.fold(Self::ZERO, |a, b| a + *b)
	}
}
impl iter::Product for B512 {
	fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
		iter.fold(Self::ONE, |a, b| a * b)
	}
}
impl<'a> iter::Product<&'a Self> for B512 {
	fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
		iter.fold(Self::ONE, |a, b| a * *b)
	}
}

impl Square for B512 {
	#[inline]
	fn square(self) -> Self {
		b512_square(self)
	}
}
impl InvertOrZero for B512 {
	#[inline]
	fn invert_or_zero(self) -> Self {
		b512_invert_or_zero(self)
	}
}

impl ConstantTimeEq for B512 {
	fn ct_eq(&self, other: &Self) -> Choice {
		self.0.ct_eq(&other.0)
	}
}

impl fmt::Debug for B512 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "B512({self})")
	}
}
impl fmt::Display for B512 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"0x{:032x}{:032x}{:032x}{:032x}",
			self.0 .0[3], self.0 .0[2], self.0 .0[1], self.0 .0[0]
		)
	}
}

// --- WithUnderlier (transparent over U512) ---------------------------------

// SAFETY: B512 is repr(transparent) over U512, whose all-zero bit pattern is ZERO.
unsafe impl Zeroable for B512 {}

// SAFETY: B512 is repr(transparent) over U512 = [u128; 4] — 64 contiguous bytes with
// no padding and no uninitialised bits, and EVERY 512-bit pattern is a valid field
// element (a binary tower field has no invalid encodings), so B512 is Pod. binius_m3's
// `TableWitnessSegment::get_mut_as::<u64,..>` (used by the Keccak-f gadget's
// `populate`) requires the top field `F` to be `Pod`.
unsafe impl Pod for B512 {}

unsafe impl WithUnderlier for B512 {
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
		// SAFETY: B512 is repr(transparent) over U512.
		unsafe { std::slice::from_raw_parts(val.as_ptr().cast::<U512>(), val.len()) }
	}
	#[inline]
	fn to_underliers_ref_mut(val: &mut [Self]) -> &mut [U512] {
		unsafe { std::slice::from_raw_parts_mut(val.as_mut_ptr().cast::<U512>(), val.len()) }
	}
	#[inline]
	fn from_underlier(val: U512) -> Self {
		Self(val)
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

// --- Serialization ----------------------------------------------------------

impl SerializeBytes for B512 {
	fn serialize(
		&self,
		mut write_buf: impl BufMut,
		_mode: SerializationMode,
	) -> Result<(), SerializationError> {
		if write_buf.remaining_mut() < 64 {
			return Err(SerializationError::WriteBufferFull);
		}
		for limb in self.0 .0 {
			write_buf.put_u128_le(limb);
		}
		Ok(())
	}
}
impl DeserializeBytes for B512 {
	fn deserialize(mut read_buf: impl Buf, _mode: SerializationMode) -> Result<Self, SerializationError>
	where
		Self: Sized,
	{
		if read_buf.remaining() < 64 {
			return Err(SerializationError::NotEnoughBytes);
		}
		let mut limbs = [0u128; 4];
		for limb in &mut limbs {
			*limb = read_buf.get_u128_le();
		}
		Ok(Self(U512(limbs)))
	}
}

// --- Field / BinaryField / TowerField --------------------------------------

impl Field for B512 {
	const ZERO: Self = Self(U512([0, 0, 0, 0]));
	const ONE: Self = Self(U512([1, 0, 0, 0])); // lo = B256::ONE (underlier [1,0]), hi = 0
	const CHARACTERISTIC: usize = 2;

	fn random(mut rng: impl RngCore) -> Self {
		Self::from_halves(
			<B256 as Field>::random(&mut rng),
			<B256 as Field>::random(&mut rng),
		)
	}

	fn double(&self) -> Self {
		Self::ZERO
	}
}

impl BinaryField for B512 {
	// Not on any soundness-critical path (challenges are sampled, not generated from a
	// fixed generator here). Chosen as the extension element `x` (lo=0, hi=B256::ONE);
	// not asserted to be a primitive root of the multiplicative group.
	const MULTIPLICATIVE_GENERATOR: Self = Self(U512([0, 0, 1, 0]));
}

impl TowerField for B512 {
	type Canonical = Self;

	fn min_tower_level(self) -> usize {
		if self.hi() == B256::ZERO {
			self.lo().min_tower_level()
		} else {
			9
		}
	}
}

// --- ExtensionField<Sub> + subfield scalar ops for every tower subfield -----
//
// Each B512 limb is a B256, so subfield coordinates are enumerated by recursing
// through `B256`'s own `ExtensionField<Sub>` on each of the two limbs. `K` is the
// number of `Sub`-coordinates per B256 limb (= `<B256 as ExtensionField<Sub>>::DEGREE`).

macro_rules! impl_ext {
	($sub:ty, $log_deg:expr, $k:expr) => {
		impl From<$sub> for B512 {
			#[inline]
			fn from(v: $sub) -> Self {
				Self::from_halves(B256::from(v), B256::ZERO)
			}
		}

		impl TryFrom<B512> for $sub {
			type Error = ();
			#[inline]
			fn try_from(x: B512) -> Result<Self, ()> {
				if x.hi() != B256::ZERO {
					return Err(());
				}
				<$sub as TryFrom<B256>>::try_from(x.lo()).map_err(|_| ())
			}
		}

		impl Add<$sub> for B512 {
			type Output = B512;
			#[inline]
			fn add(self, rhs: $sub) -> B512 {
				self + B512::from(rhs)
			}
		}
		impl Sub<$sub> for B512 {
			type Output = B512;
			#[inline]
			fn sub(self, rhs: $sub) -> B512 {
				self + B512::from(rhs)
			}
		}
		impl Mul<$sub> for B512 {
			type Output = B512;
			#[inline]
			fn mul(self, rhs: $sub) -> B512 {
				// multiplication by a subfield scalar is B256-linear on each limb
				B512::from_halves(self.lo() * rhs, self.hi() * rhs)
			}
		}
		impl AddAssign<$sub> for B512 {
			#[inline]
			fn add_assign(&mut self, rhs: $sub) {
				*self = *self + rhs;
			}
		}
		impl SubAssign<$sub> for B512 {
			#[inline]
			fn sub_assign(&mut self, rhs: $sub) {
				*self = *self - rhs;
			}
		}
		impl MulAssign<$sub> for B512 {
			#[inline]
			fn mul_assign(&mut self, rhs: $sub) {
				*self = *self * rhs;
			}
		}

		impl ExtensionField<$sub> for B512 {
			const LOG_DEGREE: usize = $log_deg;

			fn basis_checked(i: usize) -> Result<Self, FieldError> {
				if i >= (1usize << $log_deg) {
					return Err(FieldError::ExtensionDegreeMismatch);
				}
				Ok(if i < $k {
					Self::from_halves(<B256 as ExtensionField<$sub>>::basis(i), B256::ZERO)
				} else {
					Self::from_halves(B256::ZERO, <B256 as ExtensionField<$sub>>::basis(i - $k))
				})
			}

			fn from_bases_sparse(
				base_elems: impl IntoIterator<Item = $sub>,
				log_stride: usize,
			) -> Result<Self, FieldError> {
				let mut acc = Self::ZERO;
				for (m, e) in base_elems.into_iter().enumerate() {
					let idx = m << log_stride;
					if idx >= (1usize << $log_deg) {
						return Err(FieldError::ExtensionDegreeMismatch);
					}
					acc += <Self as ExtensionField<$sub>>::basis(idx) * e;
				}
				Ok(acc)
			}

			fn iter_bases(&self) -> impl Iterator<Item = $sub> {
				let (lo, hi) = (self.lo(), self.hi());
				<B256 as ExtensionField<$sub>>::into_iter_bases(lo)
					.chain(<B256 as ExtensionField<$sub>>::into_iter_bases(hi))
			}

			fn into_iter_bases(self) -> impl Iterator<Item = $sub> {
				<B256 as ExtensionField<$sub>>::into_iter_bases(self.lo())
					.chain(<B256 as ExtensionField<$sub>>::into_iter_bases(self.hi()))
			}

			#[inline]
			unsafe fn get_base_unchecked(&self, i: usize) -> $sub {
				if i < $k {
					<B256 as ExtensionField<$sub>>::get_base_unchecked(&self.lo(), i)
				} else {
					<B256 as ExtensionField<$sub>>::get_base_unchecked(&self.hi(), i - $k)
				}
			}
		}
	};
}

// (subfield, LOG_DEGREE over B512, K = #subfield-coords per B256 limb)
impl_ext!(B1, 9, 256);
impl_ext!(B8, 6, 32);
impl_ext!(B16, 5, 16);
impl_ext!(B32, 4, 8);
impl_ext!(B64, 3, 4);
impl_ext!(RealB128, 2, 2);
impl_ext!(B256, 1, 1);

// ===========================================================================
// PackScalar wiring. Binius blanket-implements `PackedField` for every `Field`
// (width 1), so `B512` IS its own width-1 packed field. We only need to name it as
// `U512`'s packed type; this satisfies the `Field: WithUnderlier<Underlier:
// PackScalar<Self>>` super-trait bound with no separate packed struct.
// ===========================================================================

impl PackScalar<B512> for U512 {
	type Packed = B512;
}

// ===========================================================================
// The tower family with the 512-bit challenge/extension field in the `B128` slot.
// `FExt<Tower> = <Tower as TowerFamily>::B128`, so putting `B512` in the `B128` slot
// makes the challenge/extension field 512-bit (tower level 9), while `FEncode<Tower> =
// Tower::B32` stays the real 32-bit Reed–Solomon alphabet and every other subfield
// stays a real Binius tower field.
// ===========================================================================

/// Tower family whose challenge/extension field (`FExt`) is the 512-bit `B512`, with
/// the standard 1/8/16/32/64-bit Binius subfields underneath.
#[derive(Debug, Default)]
pub struct B512TowerFamily;

impl TowerFamily for B512TowerFamily {
	type B1 = B1;
	type B8 = B8;
	type B16 = B16;
	type B32 = B32;
	type B64 = B64;
	type B128 = B512; // FExt slot := 512-bit field (tower level 9)
}

// ===========================================================================
// TESTS — the field-axiom + irreducibility + kappa_FS(L5) signal.
// ===========================================================================

#[cfg(test)]
mod tests {
	use super::*;
	use binius_core::{
		protocols::fri::{calculate_n_test_queries, Error as FriError},
		reed_solomon::reed_solomon::ReedSolomonCode,
	};
	use rand::{rngs::StdRng, SeedableRng};

	/// The reduction polynomial `x^2 + alpha*x + 1` is irreducible over GF(2^256):
	/// `Tr_{GF(2^256)/GF(2)}(alpha^-2) = 1`. This is the check that makes B512 a
	/// genuine field rather than a ring with zero divisors.
	#[test]
	fn alpha_makes_an_irreducible_extension() {
		let a = alpha();
		let inv2 = Square::square(InvertOrZero::invert_or_zero(a));
		let mut tr = B256::ZERO;
		let mut p = inv2;
		for _ in 0..256 {
			tr += p;
			p = Square::square(p);
		}
		assert_eq!(tr, B256::ONE, "Tr(alpha^-2) must be 1 for irreducibility over GF(2^256)");
	}

	/// B512 satisfies the field axioms on random inputs (commutativity + associativity
	/// of mul, distributivity, and — crucially — every nonzero element has an inverse,
	/// which fails iff the extension has zero divisors).
	#[test]
	fn b512_is_a_field() {
		let mut rng = StdRng::from_seed([3u8; 32]);
		assert_eq!(B512::ONE * B512::ONE, B512::ONE);
		assert_eq!(B512::ZERO * <B512 as Field>::random(&mut rng), B512::ZERO);
		for _ in 0..2000 {
			let a = <B512 as Field>::random(&mut rng);
			let b = <B512 as Field>::random(&mut rng);
			let c = <B512 as Field>::random(&mut rng);
			// commutativity + associativity
			assert_eq!(a * b, b * a);
			assert_eq!((a * b) * c, a * (b * c));
			// distributivity
			assert_eq!(a * (b + c), a * b + a * c);
			// inverse of every nonzero element
			if a != B512::ZERO {
				assert_eq!(a * InvertOrZero::invert_or_zero(a), B512::ONE);
			}
		}
	}

	/// The B256 subfield embeds correctly and DEGREE/N_BITS are 512-wide.
	#[test]
	fn b512_extension_shape() {
		assert_eq!(<B512 as ExtensionField<B1>>::DEGREE, 512);
		assert_eq!(<B512 as BinaryField>::N_BITS, 512);
		assert_eq!(<B512 as TowerField>::TOWER_LEVEL, 9);
		assert_eq!(<B512 as ExtensionField<B32>>::DEGREE, 16);
		assert_eq!(<B512 as ExtensionField<RealB128>>::DEGREE, 4);
		assert_eq!(<B512 as ExtensionField<B256>>::DEGREE, 2);
		// embedding B256 -> B512 is multiplicative
		let mut rng = StdRng::from_seed([71u8; 32]);
		let x = <B256 as Field>::random(&mut rng);
		let y = <B256 as Field>::random(&mut rng);
		assert_eq!(B512::from(x) * B512::from(y), B512::from(x * y));
	}

	/// The `TowerFamily` slot-swap is real: `FExt` (the `B128` associated type) is
	/// 512-bit while `FEncode` (the `B32` associated type) stays 32-bit.
	#[test]
	fn tower_family_slot_swap_shapes() {
		assert_eq!(
			<<B512TowerFamily as TowerFamily>::B128 as BinaryField>::N_BITS,
			512,
			"FExt must be the 512-bit challenge/extension field"
		);
		assert_eq!(
			<<B512TowerFamily as TowerFamily>::B32 as BinaryField>::N_BITS,
			32,
			"FEncode (Reed–Solomon alphabet) must stay 32-bit"
		);
		assert_eq!(<<B512TowerFamily as TowerFamily>::B1 as BinaryField>::N_BITS, 1);
	}

	/// THE CORE kappa_FS(L5) SIGNAL.
	///
	/// With Binius's 128-bit challenge field AND with our 256-bit B256 field,
	/// `calculate_n_test_queries` returns `ParameterError` at `security_bits = 256`
	/// (the folding/sumcheck error terms `poly(N)/|F|` exceed the `2^-256` budget).
	/// With our 512-bit field as `F`, those terms are `poly(N)/2^512` — negligible —
	/// so the computation SUCCEEDS at NIST L5 (256). FEncode stays `BinaryField32b`.
	#[test]
	fn calculate_n_test_queries_succeeds_at_l5_over_b512() {
		use crate::b256_field::B256 as OurB256;
		// A representative RS code: 2^20 dimension, blowup 2 (log_inv_rate = 1).
		let rs = ReedSolomonCode::<B32>::new(20, 1).unwrap();

		// 128-bit field: FAILS at 256.
		assert!(
			matches!(
				calculate_n_test_queries::<RealB128, B32>(256, &rs),
				Err(FriError::ParameterError)
			),
			"baseline: 128-bit F must fail at security_bits=256"
		);

		// 256-bit field: also FAILS at 256 (this is exactly why L5 needs level 9).
		assert!(
			matches!(
				calculate_n_test_queries::<OurB256, B32>(256, &rs),
				Err(FriError::ParameterError)
			),
			"baseline: 256-bit F must fail at security_bits=256 (motivates B512)"
		);

		// 512-bit field: SUCCEEDS at 256 (NIST L5).
		let n_l5 = calculate_n_test_queries::<B512, B32>(256, &rs)
			.expect("B512 must make calculate_n_test_queries succeed at NIST L5 (256)");
		assert!(n_l5 > 0);

		// Sanity: it also succeeds at the lower levels.
		let n_l1 = calculate_n_test_queries::<B512, B32>(128, &rs)
			.expect("B512 must also succeed at NIST L1 (128)");
		assert!(n_l5 >= n_l1);

		println!(
			"kappa_FS(L5) signal: over B512 (2^512), FRI test-queries = {n_l5} at L5(256), \
			 {n_l1} at L1(128); over B128 AND B256 the L5(256) computation is ParameterError. \
			 FEncode = B32."
		);
	}
}
