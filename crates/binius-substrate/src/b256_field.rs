// M3 (kappa_FS milestone, Phase 1) — a 256-bit binary tower field for Binius.
//
// GOAL (the FRI/sumcheck soundness lever): Binius's `constraint_system::prove`
// fixes the challenge/extension field to `FExt<Tower> = <Tower as TowerFamily>::B128`
// (see binius/crates/core/src/constraint_system/common.rs:6). At NIST L1
// (`security_bits = 128`) the FRI query-count computation
// `calculate_n_test_queries::<F, FEncode>` FAILS with `ParameterError`, because it
// subtracts the sumcheck error `2·log_dim/|F|` and the folding error `len/|F|` from
// the target `2^-128`; with a 128-bit `F` those terms already exceed `2^-128`, so
// `allowed_query_err <= 0`.
//
// The fix is purely to widen `F = FExt<Tower>` to a field larger than `2^128`, so
// those `poly(N)/|F|` terms become negligible against `2^-128` (and `2^-192`). The
// architectural trick (avoiding any change to binius_core) is that the *name* `B128`
// on `TowerFamily` is only a slot: whatever type sits in that slot IS the challenge
// field. So we define a NEW tower family whose `B128` associated type is a genuine
// 256-bit field, while `B32` (`FEncode`, the Reed–Solomon alphabet) stays 32-bit.
//
// This module provides that 256-bit field. It is `T_8` in the canonical Fan–Paar
// tower: `T_8 = T_7[x] / (x^2 + alpha*x + 1)` with `T_7 = BinaryField128b` and
// `alpha = the tower generator (underlier 1<<64)`. Irreducibility of that reduction
// polynomial over GF(2^128) — `Tr_{GF(2^128)/GF(2)}(alpha^-2) = 1` — was verified
// against Binius's own `BinaryField128b` arithmetic, so this is a REAL GF(2^256),
// not a stub. All arithmetic reuses `BinaryField128b`'s multiply/invert through the
// standard degree-2 tower recursion (the same recursion Binius uses in
// `arch/portable/pairwise_recursive_arithmetic.rs`).
//
// Everything here is ADDITIVE and lives in OUR crate: `B256` and its packed/underlier
// types are LOCAL structs, so implementing Binius's foreign traits (Field,
// BinaryField, ExtensionField, TowerField, PackedField, PackScalar, WithUnderlier,
// ...) for them is permitted by the orphan rule with NO change to the Binius checkout.

use std::{
	fmt,
	hash::Hash,
	iter,
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use binius_field::{
	arithmetic_traits::{InvertOrZero, Square},
	as_packed_field::PackScalar,
	underlier::{UnderlierType, WithUnderlier},
	tower::TowerFamily,
	BinaryField, BinaryField128b as B128, BinaryField16b as B16, BinaryField1b as B1,
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

// ===========================================================================
// 256-bit underlier (a LOCAL type, so it takes NO part in Binius's generic
// `PackScalar for ScaledUnderlier` impl — avoiding a coherence conflict).
// ===========================================================================

/// A 256-bit machine word: two little-endian `u128` limbs `[lo, hi]`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct U256(pub [u128; 2]);

unsafe impl Zeroable for U256 {}
// SAFETY: `[u128; 2]` is a plain-old-data array with no padding or uninit bytes.
unsafe impl NoUninit for U256 {}

impl ConstantTimeEq for U256 {
	fn ct_eq(&self, other: &Self) -> Choice {
		self.0[0].ct_eq(&other.0[0]) & self.0[1].ct_eq(&other.0[1])
	}
}

// Gives `U256: Random` for free via Binius's blanket `impl<T: Standard> Random for T`.
impl Distribution<U256> for Standard {
	fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> U256 {
		U256([rng.gen(), rng.gen()])
	}
}

impl UnderlierType for U256 {
	const LOG_BITS: usize = 8; // 256 bits
}

// ===========================================================================
// The 256-bit tower field T_8 = T_7[x]/(x^2 + alpha*x + 1), alpha = B128(1<<64).
// Represented as a pair of `BinaryField128b` limbs (lo, hi) = lo + hi*x.
// ===========================================================================

/// `BinaryTowerField256b` — the canonical Fan–Paar tower field of order `2^256`.
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct BinaryTowerField256b(pub U256);

/// Convenient short alias used throughout the module and tests.
pub type B256 = BinaryTowerField256b;

/// The tower constant `alpha` of the T_7 -> T_8 extension (verified irreducible:
/// `Tr_{GF(2^128)/GF(2)}(alpha^-2) = 1`). It is the tower generator of T_7.
#[inline]
fn alpha() -> B128 {
	B128::from_underlier(1u128 << 64)
}

impl B256 {
	#[inline]
	pub fn from_halves(lo: B128, hi: B128) -> Self {
		Self(U256([lo.to_underlier(), hi.to_underlier()]))
	}
	#[inline]
	pub fn lo(self) -> B128 {
		B128::from_underlier(self.0 .0[0])
	}
	#[inline]
	pub fn hi(self) -> B128 {
		B128::from_underlier(self.0 .0[1])
	}
}

// --- Field arithmetic via the degree-2 tower recursion over B128 -----------

#[inline]
fn b256_mul(a: B256, b: B256) -> B256 {
	let (a0, a1) = (a.lo(), a.hi());
	let (b0, b1) = (b.lo(), b.hi());
	let z0 = a0 * b0;
	let z2 = a1 * b1;
	let z0z2 = z0 + z2;
	let z1 = (a0 + a1) * (b0 + b1) - z0z2;
	let z2a = z2 * alpha();
	B256::from_halves(z0z2, z1 + z2a)
}

#[inline]
fn b256_square(a: B256) -> B256 {
	let (a0, a1) = (a.lo(), a.hi());
	let z0 = Square::square(a0);
	let z2 = Square::square(a1);
	let z2a = z2 * alpha();
	B256::from_halves(z0 + z2, z2a)
}

#[inline]
fn b256_invert_or_zero(a: B256) -> B256 {
	let (a0, a1) = (a.lo(), a.hi());
	let a0z1 = a0 + a1 * alpha();
	let delta = a0 * a0z1 + Square::square(a1);
	let delta_inv = InvertOrZero::invert_or_zero(delta);
	let inv0 = delta_inv * a0z1;
	let inv1 = delta_inv * a1;
	B256::from_halves(inv0, inv1)
}

impl Neg for B256 {
	type Output = Self;
	#[inline]
	fn neg(self) -> Self {
		self // characteristic 2
	}
}

macro_rules! bin_op {
	($tr:ident, $m:ident, $rhs:ty, $body:expr) => {
		impl $tr<$rhs> for B256 {
			type Output = B256;
			#[inline]
			fn $m(self, rhs: $rhs) -> B256 {
				let f: &dyn Fn(B256, B256) -> B256 = &$body;
				f(self, rhs.into_b256())
			}
		}
	};
}

// Helper to normalise both `B256` and `&B256` rhs into a `B256`.
trait IntoB256 {
	fn into_b256(self) -> B256;
}
impl IntoB256 for B256 {
	#[inline]
	fn into_b256(self) -> B256 {
		self
	}
}
impl IntoB256 for &B256 {
	#[inline]
	fn into_b256(self) -> B256 {
		*self
	}
}

bin_op!(Add, add, B256, |a: B256, b: B256| BinaryTowerField256b(U256([
	a.0 .0[0] ^ b.0 .0[0],
	a.0 .0[1] ^ b.0 .0[1]
])));
bin_op!(Add, add, &B256, |a: B256, b: B256| BinaryTowerField256b(U256([
	a.0 .0[0] ^ b.0 .0[0],
	a.0 .0[1] ^ b.0 .0[1]
])));
bin_op!(Sub, sub, B256, |a: B256, b: B256| BinaryTowerField256b(U256([
	a.0 .0[0] ^ b.0 .0[0],
	a.0 .0[1] ^ b.0 .0[1]
])));
bin_op!(Sub, sub, &B256, |a: B256, b: B256| BinaryTowerField256b(U256([
	a.0 .0[0] ^ b.0 .0[0],
	a.0 .0[1] ^ b.0 .0[1]
])));
bin_op!(Mul, mul, B256, |a, b| b256_mul(a, b));
bin_op!(Mul, mul, &B256, |a, b| b256_mul(a, b));

macro_rules! assign_op {
	($tr:ident, $m:ident, $base:ident, $bm:ident, $rhs:ty) => {
		impl $tr<$rhs> for B256 {
			#[inline]
			fn $m(&mut self, rhs: $rhs) {
				*self = $base::$bm(*self, rhs);
			}
		}
	};
}
assign_op!(AddAssign, add_assign, Add, add, B256);
assign_op!(AddAssign, add_assign, Add, add, &B256);
assign_op!(SubAssign, sub_assign, Sub, sub, B256);
assign_op!(SubAssign, sub_assign, Sub, sub, &B256);
assign_op!(MulAssign, mul_assign, Mul, mul, B256);
assign_op!(MulAssign, mul_assign, Mul, mul, &B256);

impl iter::Sum for B256 {
	fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
		iter.fold(Self::ZERO, |a, b| a + b)
	}
}
impl<'a> iter::Sum<&'a Self> for B256 {
	fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
		iter.fold(Self::ZERO, |a, b| a + *b)
	}
}
impl iter::Product for B256 {
	fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
		iter.fold(Self::ONE, |a, b| a * b)
	}
}
impl<'a> iter::Product<&'a Self> for B256 {
	fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
		iter.fold(Self::ONE, |a, b| a * *b)
	}
}

impl Square for B256 {
	#[inline]
	fn square(self) -> Self {
		b256_square(self)
	}
}
impl InvertOrZero for B256 {
	#[inline]
	fn invert_or_zero(self) -> Self {
		b256_invert_or_zero(self)
	}
}

impl ConstantTimeEq for B256 {
	fn ct_eq(&self, other: &Self) -> Choice {
		self.0.ct_eq(&other.0)
	}
}

impl fmt::Debug for B256 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "B256({self})")
	}
}
impl fmt::Display for B256 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "0x{:032x}{:032x}", self.0 .0[1], self.0 .0[0])
	}
}

// --- WithUnderlier (transparent over U256) ---------------------------------

// SAFETY: B256 is repr(transparent) over U256, whose all-zero bit pattern is the
// field ZERO. (Required: WithUnderlier: Zeroable.)
unsafe impl Zeroable for B256 {}

// SAFETY: B256 is repr(transparent) over U256 = [u128; 2] — 32 contiguous bytes
// with no padding and no uninitialised bits, and EVERY 256-bit pattern is a valid
// field element (a binary tower field has no invalid encodings), so B256 is Pod.
// binius_m3's `TableWitnessSegment::get_mut_as::<u64,..>` (used by the Keccak-f
// gadget's `populate`) requires the top field `F` to be `Pod`, because it
// reinterprets a column's `F`-scalar backing store as `u64` lanes via
// `must_cast_slice`. `Pod` also yields the `NoUninit`/`AnyBitPattern` that cast
// needs, via bytemuck's blanket impls.
unsafe impl Pod for B256 {}

unsafe impl WithUnderlier for B256 {
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
		// SAFETY: B256 is repr(transparent) over U256.
		unsafe { std::slice::from_raw_parts(val.as_ptr().cast::<U256>(), val.len()) }
	}
	#[inline]
	fn to_underliers_ref_mut(val: &mut [Self]) -> &mut [U256] {
		unsafe { std::slice::from_raw_parts_mut(val.as_mut_ptr().cast::<U256>(), val.len()) }
	}
	#[inline]
	fn from_underlier(val: U256) -> Self {
		Self(val)
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

// --- Serialization ----------------------------------------------------------

impl SerializeBytes for B256 {
	fn serialize(
		&self,
		mut write_buf: impl BufMut,
		_mode: SerializationMode,
	) -> Result<(), SerializationError> {
		if write_buf.remaining_mut() < 32 {
			return Err(SerializationError::WriteBufferFull);
		}
		write_buf.put_u128_le(self.0 .0[0]);
		write_buf.put_u128_le(self.0 .0[1]);
		Ok(())
	}
}
impl DeserializeBytes for B256 {
	fn deserialize(mut read_buf: impl Buf, _mode: SerializationMode) -> Result<Self, SerializationError>
	where
		Self: Sized,
	{
		if read_buf.remaining() < 32 {
			return Err(SerializationError::NotEnoughBytes);
		}
		let lo = read_buf.get_u128_le();
		let hi = read_buf.get_u128_le();
		Ok(Self(U256([lo, hi])))
	}
}

// --- Field / BinaryField / TowerField --------------------------------------

impl Field for B256 {
	const ZERO: Self = Self(U256([0, 0]));
	const ONE: Self = Self(U256([1, 0])); // lo = B128::ONE (underlier 1), hi = 0
	const CHARACTERISTIC: usize = 2;

	fn random(mut rng: impl RngCore) -> Self {
		Self::from_halves(
			<B128 as Field>::random(&mut rng),
			<B128 as Field>::random(&mut rng),
		)
	}

	fn double(&self) -> Self {
		Self::ZERO
	}
}

impl BinaryField for B256 {
	// Not on any soundness-critical path (challenges are sampled, not generated
	// from a fixed generator here). Chosen as a nonzero non-subfield element; not
	// asserted to be a primitive root of the multiplicative group.
	const MULTIPLICATIVE_GENERATOR: Self = Self(U256([0, 1])); // the extension element x
}

impl TowerField for B256 {
	type Canonical = Self;

	fn min_tower_level(self) -> usize {
		if self.hi() == B128::ZERO {
			self.lo().min_tower_level()
		} else {
			8
		}
	}
}

// --- ExtensionField<Sub> + subfield scalar ops for every tower subfield -----

macro_rules! impl_ext {
	($sub:ty, $log_deg:expr, $k:expr) => {
		impl From<$sub> for B256 {
			#[inline]
			fn from(v: $sub) -> Self {
				Self::from_halves(B128::from(v), B128::ZERO)
			}
		}

		impl TryFrom<B256> for $sub {
			type Error = ();
			#[inline]
			fn try_from(x: B256) -> Result<Self, ()> {
				if x.hi() != B128::ZERO {
					return Err(());
				}
				<$sub as TryFrom<B128>>::try_from(x.lo()).map_err(|_| ())
			}
		}

		impl Add<$sub> for B256 {
			type Output = B256;
			#[inline]
			fn add(self, rhs: $sub) -> B256 {
				self + B256::from(rhs)
			}
		}
		impl Sub<$sub> for B256 {
			type Output = B256;
			#[inline]
			fn sub(self, rhs: $sub) -> B256 {
				self + B256::from(rhs)
			}
		}
		impl Mul<$sub> for B256 {
			type Output = B256;
			#[inline]
			fn mul(self, rhs: $sub) -> B256 {
				// multiplication by a subfield scalar is B128-linear on each limb
				B256::from_halves(self.lo() * rhs, self.hi() * rhs)
			}
		}
		impl AddAssign<$sub> for B256 {
			#[inline]
			fn add_assign(&mut self, rhs: $sub) {
				*self = *self + rhs;
			}
		}
		impl SubAssign<$sub> for B256 {
			#[inline]
			fn sub_assign(&mut self, rhs: $sub) {
				*self = *self - rhs;
			}
		}
		impl MulAssign<$sub> for B256 {
			#[inline]
			fn mul_assign(&mut self, rhs: $sub) {
				*self = *self * rhs;
			}
		}

		impl ExtensionField<$sub> for B256 {
			const LOG_DEGREE: usize = $log_deg;

			fn basis_checked(i: usize) -> Result<Self, FieldError> {
				if i >= (1usize << $log_deg) {
					return Err(FieldError::ExtensionDegreeMismatch);
				}
				Ok(if i < $k {
					Self::from_halves(<B128 as ExtensionField<$sub>>::basis(i), B128::ZERO)
				} else {
					Self::from_halves(B128::ZERO, <B128 as ExtensionField<$sub>>::basis(i - $k))
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
				<B128 as ExtensionField<$sub>>::into_iter_bases(lo)
					.chain(<B128 as ExtensionField<$sub>>::into_iter_bases(hi))
			}

			fn into_iter_bases(self) -> impl Iterator<Item = $sub> {
				<B128 as ExtensionField<$sub>>::into_iter_bases(self.lo())
					.chain(<B128 as ExtensionField<$sub>>::into_iter_bases(self.hi()))
			}

			#[inline]
			unsafe fn get_base_unchecked(&self, i: usize) -> $sub {
				if i < $k {
					<B128 as ExtensionField<$sub>>::get_base_unchecked(&self.lo(), i)
				} else {
					<B128 as ExtensionField<$sub>>::get_base_unchecked(&self.hi(), i - $k)
				}
			}
		}
	};
}

// (subfield, LOG_DEGREE over B256, K = #subfield-coords per B128 limb)
impl_ext!(B1, 8, 128);
impl_ext!(B8, 5, 16);
impl_ext!(B16, 4, 8);
impl_ext!(B32, 3, 4);
impl_ext!(B64, 2, 2);
impl_ext!(B128, 1, 1);

// ===========================================================================
// PackScalar wiring. Binius already blanket-implements `PackedField` for every
// `Field` (packed.rs:562, width 1), so `B256` IS its own width-1 packed field.
// We therefore only need to name it as `U256`'s packed type; this satisfies the
// `Field: WithUnderlier<Underlier: PackScalar<Self>>` super-trait bound with no
// separate packed struct.
// ===========================================================================

impl PackScalar<B256> for U256 {
	type Packed = B256;
}

// ===========================================================================
// The tower family with the 256-bit challenge/extension field in the `B128`
// slot. THIS is the architectural trick: `FExt<Tower> = <Tower as TowerFamily>::B128`
// (binius_core common.rs:6), so putting `B256` in the `B128` slot makes the
// challenge/extension field 256-bit, while `FEncode<Tower> = Tower::B32` stays the
// real 32-bit Reed–Solomon alphabet and every other subfield stays a real Binius
// tower field. `TowerFamily` is satisfiable entirely in our crate.
// ===========================================================================

/// Tower family whose challenge/extension field (`FExt`) is the 256-bit `B256`,
/// with the standard 1/8/16/32/64-bit Binius subfields underneath.
#[derive(Debug, Default)]
pub struct B256TowerFamily;

impl TowerFamily for B256TowerFamily {
	type B1 = B1;
	type B8 = B8;
	type B16 = B16;
	type B32 = B32;
	type B64 = B64;
	type B128 = B256; // FExt slot := 256-bit field
}

// ---------------------------------------------------------------------------
// STATUS OF THE FULL prove/verify PATH (`prove_verify_keccak_b256`).
//
// `binius_core::constraint_system::prove::<U, B256TowerFamily, ..>` additionally
// requires `U: ProverTowerUnderlier<B256TowerFamily>`, i.e. the *single* prover
// underlier `U` must implement `PackScalar<F>` for EVERY tower subfield
// simultaneously — B1, B8, B16, B32, B64 AND the 256-bit top B256 — plus
// `RepackedExtension<PackedType<U, B_sub>>` and `PackedTransformationFactory` on the
// top packed field. This is the wall (verified by compile probe):
//
//   * A ready-made Binius 256-bit underlier cannot host B256: `impl PackScalar<B256>
//     for ScaledUnderlier<u128,2>` is E0119 (conflicts with Binius's blanket
//     `impl<U,F,N> PackScalar<F> for ScaledUnderlier<U,N> where U: PackScalar<F>`).
//     A 256-bit *scalar* also does not fit the `ScaledUnderlier<M128,N>` packing
//     mechanism, which only packs scalars of width <= 128.
//   * Our local `U256` compiles `PackScalar<B256>` fine, but `U256:
//     TowerUnderlier<B256TowerFamily>` is E0277: `PackScalar<B1/B8/B16/B32/B64>` are
//     not implemented for `U256`. Supplying them means writing five from-scratch
//     packed subfield types (B1x256, B8x32, B16x16, B32x8, B64x4) over U256, each a
//     full `PackedField` + `PackedExtension` + `RepackedExtension` +
//     `PackedTransformationFactory` implementation.
//
// So `prove_verify_keccak_b256` is NOT wired here: it cannot be satisfied externally
// without either (a) those five packed subfield implementations over U256, or (b) a
// (non-minimal) Binius patch adding a native 256-bit underlier + B256 tower level.
// This module delivers the kappa_FS *soundness* signal (the FRI query-count math over
// a 2^256 field, below) — which is the load-bearing claim — and leaves the packing
// engineering as the characterised remaining work.
// ---------------------------------------------------------------------------

// ===========================================================================
// TESTS — the kappa_FS signal.
// ===========================================================================

#[cfg(test)]
mod tests {
	use super::*;
	use binius_core::{
		protocols::fri::{calculate_n_test_queries, Error as FriError},
		reed_solomon::reed_solomon::ReedSolomonCode,
	};
	use rand::{rngs::StdRng, SeedableRng};

	/// The reduction polynomial `x^2 + alpha*x + 1` is irreducible over GF(2^128):
	/// `Tr_{GF(2^128)/GF(2)}(alpha^-2) = 1`. This is the check that makes B256 a
	/// genuine field rather than a ring with zero divisors.
	#[test]
	fn alpha_makes_an_irreducible_extension() {
		let a = alpha();
		let inv2 = Square::square(InvertOrZero::invert_or_zero(a));
		let mut tr = B128::ZERO;
		let mut p = inv2;
		for _ in 0..128 {
			tr += p;
			p = Square::square(p);
		}
		assert_eq!(tr, B128::ONE, "Tr(alpha^-2) must be 1 for irreducibility");
	}

	/// B256 satisfies the field axioms on random inputs (associativity of mul,
	/// distributivity, and — crucially — every nonzero element has an inverse,
	/// which fails iff the extension has zero divisors).
	#[test]
	fn b256_is_a_field() {
		let mut rng = StdRng::from_seed([3u8; 32]);
		assert_eq!(B256::ONE * B256::ONE, B256::ONE);
		assert_eq!(B256::ZERO * <B256 as Field>::random(&mut rng), B256::ZERO);
		for _ in 0..2000 {
			let a = <B256 as Field>::random(&mut rng);
			let b = <B256 as Field>::random(&mut rng);
			let c = <B256 as Field>::random(&mut rng);
			// commutativity + associativity
			assert_eq!(a * b, b * a);
			assert_eq!((a * b) * c, a * (b * c));
			// distributivity
			assert_eq!(a * (b + c), a * b + a * c);
			// inverse of every nonzero element
			if a != B256::ZERO {
				assert_eq!(a * InvertOrZero::invert_or_zero(a), B256::ONE);
			}
		}
	}

	/// The B128 subfield embeds correctly and DEGREE/N_BITS are 256-wide.
	#[test]
	fn b256_extension_shape() {
		assert_eq!(<B256 as ExtensionField<B1>>::DEGREE, 256);
		assert_eq!(<B256 as BinaryField>::N_BITS, 256);
		assert_eq!(<B256 as ExtensionField<B32>>::DEGREE, 8);
		assert_eq!(<B256 as ExtensionField<B128>>::DEGREE, 2);
		// embedding B128 -> B256 is multiplicative
		let x = B128::from_underlier(0x1234_5678_9abc_def0_1111_2222_3333_4444);
		let y = B128::from_underlier(0x0fed_cba9_8765_4321_5555_6666_7777_8888);
		assert_eq!(B256::from(x) * B256::from(y), B256::from(x * y));
	}

	/// The `TowerFamily` slot-swap is real: `FExt` (the `B128` associated type) is
	/// 256-bit while `FEncode` (the `B32` associated type) stays 32-bit.
	#[test]
	fn tower_family_slot_swap_shapes() {
		assert_eq!(
			<<B256TowerFamily as TowerFamily>::B128 as BinaryField>::N_BITS,
			256,
			"FExt must be the 256-bit challenge/extension field"
		);
		assert_eq!(
			<<B256TowerFamily as TowerFamily>::B32 as BinaryField>::N_BITS,
			32,
			"FEncode (Reed–Solomon alphabet) must stay 32-bit"
		);
		assert_eq!(<<B256TowerFamily as TowerFamily>::B1 as BinaryField>::N_BITS, 1);
	}

	/// THE CORE kappa_FS SIGNAL.
	///
	/// With Binius's 128-bit challenge field, `calculate_n_test_queries` returns
	/// `ParameterError` at `security_bits >= 128` (the folding/sumcheck error terms
	/// `poly(N)/2^128` already exceed the `2^-128` budget). With our 256-bit field
	/// as `F`, those terms are `poly(N)/2^256` — negligible — so the computation
	/// SUCCEEDS at NIST L1 (128) and L3 (192). FEncode stays `BinaryField32b`.
	#[test]
	fn calculate_n_test_queries_succeeds_at_l1_over_b256() {
		// A representative RS code: 2^20 dimension, blowup 2 (log_inv_rate = 1).
		let rs = ReedSolomonCode::<B32>::new(20, 1).unwrap();

		// 128-bit field: FAILS at 128 (the status quo this milestone must fix).
		let at_128_b128 = calculate_n_test_queries::<B128, B32>(128, &rs);
		assert!(
			matches!(at_128_b128, Err(FriError::ParameterError)),
			"baseline: 128-bit F must fail at security_bits=128, got {at_128_b128:?}"
		);

		// 256-bit field: SUCCEEDS at 128.
		let n_l1 = calculate_n_test_queries::<B256, B32>(128, &rs)
			.expect("B256 must make calculate_n_test_queries succeed at NIST L1 (128)");
		assert!(n_l1 > 0);

		// ... and at 192 (NIST L3), where 128-bit F is even more hopeless.
		let n_l3 = calculate_n_test_queries::<B256, B32>(192, &rs)
			.expect("B256 must make calculate_n_test_queries succeed at NIST L3 (192)");
		assert!(n_l3 >= n_l1);

		assert!(
			calculate_n_test_queries::<B128, B32>(192, &rs).is_err(),
			"baseline: 128-bit F must also fail at 192"
		);

		println!(
			"kappa_FS signal: over B256 (2^256), FRI test-queries = {n_l1} at L1(128), \
			 {n_l3} at L3(192); over B128 (2^128) both are ParameterError. FEncode = B32."
		);
	}
}
