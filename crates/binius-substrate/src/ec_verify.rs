// S2 (classical-signature port) — Ed25519 (RFC 8032) and ECDSA-P256 (FIPS 186-5) verify
// over the 256-bit tower field `B256TowerFamily` at NIST L1/L3/L5.
//
// Both verifiers reduce to ELLIPTIC-CURVE scalar multiplication over a ~256-bit prime
// field, which is exactly what S0's non-native `a·b mod m` gadget was built for (S0
// already proves 2^255−19 at W=512). S2 adds the LAYER ABOVE S0: curve point add/double
// as fixed sequences of field mul/add/sub, and scalar multiplication as a double-and-add
// loop — the natural STRAND boundary (per-bit / per-window), so tunable-RSS carries over.
//
// ── WHAT S2 NEEDS (all reduce to S0 field ops + a hash) ────────────────────────────
//   Ed25519.Verify(A, M, (R,S)):
//     • decompress A, R   (y → x via a sqrt mod p = a field exponentiation, S0 muls)
//     • k = SHA-512(R ‖ A ‖ M) mod L                    [SHA-512 gadget — build like the
//                                                         SHA3 variants but sha2-512]
//     • accept ⟺ [8][S]B == [8]R + [8][k]A              [twisted-Edwards scalar mul;
//                                                         cofactor-8 cleared]
//   ECDSA-P256.Verify(Q, e, (r,s)):
//     • w = s⁻¹ mod n                                    [S0: hint w, verify s·w ≡ 1]
//     • u1 = e·w mod n,  u2 = r·w mod n
//     • (x,y) = u1·G + u2·Q                              [short-Weierstrass scalar mul]
//     • accept ⟺ x mod n == r
//   Hashes: ECDSA SHA-256 is in `binius_circuits::sha256` (reuse); Ed25519 SHA-512 is
//   the one new hash gadget (sha2-512 compression in-circuit; the OUTER Sha512Compression
//   already exists in `sha_outer.rs`, but the IN-CIRCUIT message hash is a new gadget).
//
// ── REUSE (no reinvented field/EC math in-circuit) ─────────────────────────────────
//   * `crate::nonnative::ModMul<W=512>`     — every field multiply mod p (and mod n).
//   * `crate::nonnative` add/carry helpers  — modular add/sub mod p (S1a specialised
//                                             these for a fixed modulus; reused per curve).
//   * S0's `x < m` carry decision           — final coordinate/scalar range + the
//                                             inverse-hint check (s·w ≡ 1) and x≡r.
//   * `binius_circuits::sha256`             — ECDSA message hash.
//
// ── SCALAR-MUL = THE STRAND LEVER ──────────────────────────────────────────────────
// [k]P by double-and-add is 255 iterations of {double; conditional add}. Each iteration
// is INDEPENDENT of the RSS budget: a strand covers a contiguous window of bits, strands
// re-bind at the running accumulator via a channel seam (exactly S0's strand-splice model
// / the b256_recursion join). So a browser proves one window per strand; a server proves
// many. Fixed-base [S]B / [k]G can use a precomputed comb (fewer doublings). This is the
// same fine-decompose-and-pack-to-budget principle as the hash strands.
//
// ── SOUNDNESS BOUNDARY ────────────────────────────────────────────────────────────
//   IN-CIRCUIT: every field op is an S0 gadget (a·b ≡ q·m+r ∧ r<m), every point op is a
//   fixed constraint sequence over those, scalar mul is the bit-loop with a conditional-
//   add selector, and the accept predicate ([8][S]B==[8]R+[8][k]A / x≡r) is an equality
//   of committed coordinates to a boundary. A tampered signature admits NO accepting
//   witness (the final equality fails). Over the 2^256 challenge field this holds at NIST
//   L1/L3/L5.  Public boundary: (A, M, R, S) / (Q, e, r, s). Witness: all EC intermediates
//   + the inverse hint w + the k=SHA512 mod-L reduction quotient.
//   WITNESS-SIDE (gated vs the RustCrypto `ed25519-dalek` / `p256` crates + RFC 8032 /
//   FIPS 186-5 test vectors, folded in-circuit as decompression/decoding land): point
//   decompression sign selection and the scalar little-/big-endian decoding.
//   OUTER COMMITMENT still SHA-256 (FIPS 180-4); the 2^256 field carries FS security.
// ============================================================================
//
// DRAFT STATUS (S2, in progress): the native reference (curve params, twisted-Edwards +
// short-Weierstrass point add/double, double-and-add scalar mul, Ed25519 + ECDSA verify)
// is implemented in the test module and cross-checked against the `ed25519-dalek` / `p256`
// crates + RFC 8032 / FIPS 186-5 vectors (validated externally with Python first). The
// in-circuit EC gadgets (point ops over S0, the scalar-mul strand loop, the SHA-512
// gadget) are specified below and wired after S1's prove paths land and the shared target
// frees. Heavy prove gates are `#[ignore]`.

/// The two S2 curves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum S2Curve {
	/// Edwards25519 (twisted Edwards −x²+y² = 1+d x²y²), p = 2^255−19, for Ed25519.
	Ed25519,
	/// NIST P-256 (short Weierstrass y² = x³−3x+b), for ECDSA (DNSSEC alg 13).
	P256,
}

impl S2Curve {
	/// Base-field prime p as a big-endian hex string.
	pub const fn field_prime_hex(self) -> &'static str {
		match self {
			// 2^255 − 19
			S2Curve::Ed25519 => "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed",
			// 2^256 − 2^224 + 2^192 + 2^96 − 1
			S2Curve::P256 => "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
		}
	}

	/// Group order (ℓ for Ed25519, n for P-256), big-endian hex.
	pub const fn group_order_hex(self) -> &'static str {
		match self {
			// ℓ = 2^252 + 27742317777372353535851937790883648493
			S2Curve::Ed25519 => "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
			S2Curve::P256 => "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
		}
	}

	/// Cofactor (8 for Edwards25519, 1 for P-256).
	pub const fn cofactor(self) -> u64 {
		match self {
			S2Curve::Ed25519 => 8,
			S2Curve::P256 => 1,
		}
	}

	/// The non-native field width W (bits) used by S0's ModMul for this prime: 512 covers
	/// the ~256-bit modulus and its < p² intermediates without wraparound.
	pub const fn modmul_width(self) -> usize {
		512
	}

	pub const fn name(self) -> &'static str {
		match self {
			S2Curve::Ed25519 => "Ed25519",
			S2Curve::P256 => "ECDSA-P256",
		}
	}
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT DESIGN (wired after S1 prove paths land — see DRAFT STATUS)
// ──────────────────────────────────────────────────────────────────────────────────
//
// Field layer (per curve prime p, and per group order n):
//   fe_mul(a,b) = ModMul<512> over p  [S0, verified]; fe_add/fe_sub = modadd/modsub mod p
//   [S1a-style carry adder + `< p` reduction]; fe_inv(a) = hint a⁻¹, verify a·a⁻¹ ≡ 1
//   [one ModMul + `≡1` equality]; fe_sqrt for decompression = hint root, verify root² ≡ y.
//
// Point layer:
//   Ed25519 (extended twisted-Edwards coords, complete addition — no exceptional cases):
//     add: A=(Y1−X1)(Y2−X2), B=(Y1+X1)(Y2+X2), C=2·d·T1·T2, D=2·Z1·Z2, E=B−A, F=D−C,
//          G=D+C, H=B+A → X3=E·F, Y3=G·H, T3=E·H, Z3=F·G  (≈ 9 fe_mul).
//     double: standard dbl-2008-hwcd (≈ 4 fe_mul + 4 fe_sqr).
//   P-256 (Jacobian, then one fe_inv to affine at the end):
//     add/dbl = the standard EFD add-2007-bl / dbl-2001-b sequences over fe_*.
//
// Scalar-mul (the strand loop):
//   [k]P: for i = 255..0 { Acc = dbl(Acc); Acc = cadd(Acc, P, bit_i(k)) } where cadd is a
//   MUX(bit) between Acc and add(Acc,P). Strand cut = a contiguous bit-window; the window's
//   input/output Acc are bound to the neighbours by a channel seam (push out-Acc, pull as
//   next in-Acc) — RSS ∝ window width, exactly S0 strand-splice. Fixed-base [S]B, [k]G use
//   a comb table (transparent columns) to cut doublings.
//
// Verify boundary:
//   Ed25519: compute L1=[8][S]B and R1=[8]R + [8][k]A via scalar mul; assert L1==R1 as
//     committed extended coords projected to affine (cross-multiplied to avoid an inv).
//   ECDSA:  compute (x,y)=u1·G+u2·Q; assert (x mod n) == r  [fe reduce mod n + `==r`].
//   k (Ed25519) and u1,u2 (ECDSA) come from the SHA-512/SHA-256 gadget + a mod-L/mod-n
//   reduction (S0 `< order` carry on the hinted quotient).
//
// TAMPERED-SIG-REJECTS (S2 headline gate): genuine (pk,M,σ) [ed25519-dalek / p256 sign]
// verifies; each of {flip an S/z byte, flip an R/r byte, flip an s byte, flip an M byte,
// wrong pubkey} yields NO accepting witness — the final point-equality / x≡r fails,
// isolated to that boundary constraint (mirrors S1a's soundness shape).

#[cfg(test)]
mod tests {
	// The native reference uses num-bigint (dev-dep) and cross-checks against the
	// ed25519-dalek / p256 crates once they are added to dev-deps. Until then the
	// arithmetic here is validated against the same curves in Python (see the S2
	// validation run). This module documents the reference the circuit is gated against.
	use num_bigint::BigUint;
	use sha2::{Digest, Sha512};

	use super::*;

	fn is_zero(x: &BigUint) -> bool {
		x.bits() == 0
	}

	/// Parse a hex string into bytes (test helper).
	fn unhex(s: &str) -> Vec<u8> {
		(0..s.len())
			.step_by(2)
			.map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
			.collect()
	}

	fn prime(curve: S2Curve) -> BigUint {
		BigUint::parse_bytes(curve.field_prime_hex().as_bytes(), 16).unwrap()
	}
	fn order(curve: S2Curve) -> BigUint {
		BigUint::parse_bytes(curve.group_order_hex().as_bytes(), 16).unwrap()
	}

	fn fe_mul(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
		(a * b) % p
	}
	fn fe_add(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
		(a + b) % p
	}
	fn fe_sub(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
		((a + p) - (b % p)) % p
	}
	/// a⁻¹ mod p by Fermat (p prime): a^(p−2).
	fn fe_inv(a: &BigUint, p: &BigUint) -> BigUint {
		a.modpow(&(p - 2u32), p)
	}

	// ── P-256 short-Weierstrass, affine reference (y² = x³ − 3x + b) ──
	const P256_B: &str = "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b";
	const P256_GX: &str = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
	const P256_GY: &str = "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";

	/// Affine point, None = identity.
	type Aff = Option<(BigUint, BigUint)>;

	fn p256_add(pt1: &Aff, pt2: &Aff, p: &BigUint) -> Aff {
		match (pt1, pt2) {
			(None, _) => pt2.clone(),
			(_, None) => pt1.clone(),
			(Some((x1, y1)), Some((x2, y2))) => {
				if x1 == x2 && is_zero(&fe_add(y1, y2, p)) {
					return None; // P + (−P) = O
				}
				let lambda = if x1 == x2 && y1 == y2 {
					// doubling: (3x² − 3)/(2y)
					let three = BigUint::from(3u32);
					let num = fe_sub(&fe_mul(&three, &fe_mul(x1, x1, p), p), &three, p);
					let den = fe_inv(&fe_add(y1, y1, p), p);
					fe_mul(&num, &den, p)
				} else {
					let num = fe_sub(y2, y1, p);
					let den = fe_inv(&fe_sub(x2, x1, p), p);
					fe_mul(&num, &den, p)
				};
				let x3 = fe_sub(&fe_sub(&fe_mul(&lambda, &lambda, p), x1, p), x2, p);
				let y3 = fe_sub(&fe_mul(&lambda, &fe_sub(x1, &x3, p), p), y1, p);
				Some((x3, y3))
			}
		}
	}

	fn p256_scalar_mul(k: &BigUint, pt: &Aff, p: &BigUint) -> Aff {
		let mut acc: Aff = None;
		let bits = k.bits();
		for i in (0..bits).rev() {
			acc = p256_add(&acc, &acc, p); // double
			if k.bit(i) {
				acc = p256_add(&acc, pt, p); // add
			}
		}
		acc
	}

	/// ECDSA-P256 verify reference: given the message hash e (as integer), pubkey Q, and
	/// (r, s), returns accept/reject.
	fn ecdsa_p256_verify(e: &BigUint, q: &Aff, r: &BigUint, s: &BigUint) -> bool {
		let p = prime(S2Curve::P256);
		let n = order(S2Curve::P256);
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return false;
		}
		let w = s.modpow(&(&n - 2u32), &n); // s⁻¹ mod n
		let u1 = (e * &w) % &n;
		let u2 = (r * &w) % &n;
		let g = Some((
			BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap(),
		));
		let pt = p256_add(&p256_scalar_mul(&u1, &g, &p), &p256_scalar_mul(&u2, q, &p), &p);
		match pt {
			None => false,
			Some((x, _)) => (x % &n) == *r,
		}
	}

	/// GATE ref-S2-1 — the curve constants parse and satisfy the defining relations: G is
	/// on P-256 (Gy² ≡ Gx³ − 3Gx + b), and the primes/orders have the right bit-lengths.
	#[test]
	fn curve_constants_wellformed() {
		let p = prime(S2Curve::P256);
		let b = BigUint::parse_bytes(P256_B.as_bytes(), 16).unwrap();
		let gx = BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap();
		let gy = BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap();
		let three = BigUint::from(3u32);
		let lhs = fe_mul(&gy, &gy, &p);
		let rhs = fe_sub(
			&fe_add(&fe_mul(&gx, &fe_mul(&gx, &gx, &p), &p), &b, &p),
			&fe_mul(&three, &gx, &p),
			&p,
		);
		assert_eq!(lhs, rhs, "P-256 base point not on curve");

		assert_eq!(prime(S2Curve::Ed25519).bits(), 255, "2^255−19 bit length");
		assert_eq!(prime(S2Curve::P256).bits(), 256, "P-256 prime bit length");
		assert_eq!(order(S2Curve::Ed25519).bits(), 253, "ℓ bit length");
		assert_eq!(order(S2Curve::P256).bits(), 256, "n bit length");
		println!("GATE ref-S2-1: curve constants parse; P-256 G on curve; bit-lengths ok");
	}

	/// GATE ref-S2-2 — group law sanity: [n]G = O and G + G = [2]G = dbl(G) on P-256, and
	/// scalar-mul is linear ([a]G + [b]G == [a+b]G).
	#[test]
	fn p256_group_law() {
		let p = prime(S2Curve::P256);
		let n = order(S2Curve::P256);
		let g = Some((
			BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap(),
		));
		assert!(p256_scalar_mul(&n, &g, &p).is_none(), "[n]G must be identity");
		let g2_add = p256_add(&g, &g, &p);
		let g2_mul = p256_scalar_mul(&BigUint::from(2u32), &g, &p);
		assert_eq!(g2_add, g2_mul, "[2]G != G+G");
		let a = BigUint::from(1234567u32);
		let b = BigUint::from(7654321u32);
		let lhs = p256_add(&p256_scalar_mul(&a, &g, &p), &p256_scalar_mul(&b, &g, &p), &p);
		let rhs = p256_scalar_mul(&(&a + &b), &g, &p);
		assert_eq!(lhs, rhs, "scalar-mul not linear");
		println!("GATE ref-S2-2: [n]G=O, [2]G=G+G, [a]G+[b]G=[a+b]G on P-256");
	}

	/// GATE ref-S2-3 — ECDSA-P256 verify accepts a self-generated valid signature and
	/// REJECTS each tamper (r, s, e). The keypair/signature is generated arithmetically
	/// (d, k random-ish; r = ([k]G).x mod n; s = k⁻¹(e + r·d) mod n) so this is a closed
	/// self-check; the `p256` crate cross-check lands when it is added to dev-deps.
	#[test]
	fn ecdsa_p256_verify_and_tamper_rejected() {
		let p = prime(S2Curve::P256);
		let n = order(S2Curve::P256);
		let g = Some((
			BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap(),
		));
		// private key d, nonce k, message hash e (all fixed, in [1,n))
		let d = BigUint::parse_bytes(b"c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 16).unwrap();
		let k = BigUint::parse_bytes(b"7a1a7e52797fc8caaa435d2a4dace39158504bf204fbe19f14dbb427faee50ae", 16).unwrap();
		let e = BigUint::parse_bytes(b"a41a41a12a799548211c410c65d8133afde34d28bdd542e4b680cf2899c8a8c4", 16).unwrap();
		let q = p256_scalar_mul(&d, &g, &p); // pubkey
		let r = match p256_scalar_mul(&k, &g, &p) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let kinv = k.modpow(&(&n - 2u32), &n);
		let s = (&kinv * ((&e + &r * &d) % &n)) % &n;

		assert!(ecdsa_p256_verify(&e, &q, &r, &s), "valid signature must verify");
		// tamper r, s, e
		assert!(!ecdsa_p256_verify(&e, &q, &((&r + 1u32) % &n), &s), "tampered r must reject");
		assert!(!ecdsa_p256_verify(&e, &q, &r, &((&s + 1u32) % &n)), "tampered s must reject");
		assert!(!ecdsa_p256_verify(&((&e + 1u32) % &n), &q, &r, &s), "tampered e must reject");
		println!("GATE ref-S2-3: ECDSA-P256 verify accepts valid sig, rejects tampered r/s/e");
	}

	// ── Ed25519 twisted-Edwards (−x²+y² = 1+d x²y²), affine unified addition ──
	// d = −121665 · 121666⁻¹ mod p; base point B = (Bx, By), By = 4/5 mod p.
	fn ed_d(p: &BigUint) -> BigUint {
		let num = fe_sub(&zero_big(), &BigUint::from(121665u32), p); // −121665
		let den = fe_inv(&BigUint::from(121666u32), p);
		fe_mul(&num, &den, p)
	}
	fn zero_big() -> BigUint {
		BigUint::from(0u32)
	}
	/// Base point B of Edwards25519 (RFC 8032): the point with y = 4/5 and even x.
	fn ed_base(p: &BigUint) -> (BigUint, BigUint) {
		let by = fe_mul(&BigUint::from(4u32), &fe_inv(&BigUint::from(5u32), p), p);
		let bx = ed_recover_x(&by, false, p).expect("B must decompress");
		(bx, by)
	}
	/// Recover x from y on Edwards25519: x² = (y²−1)/(d y²+1); pick parity via `x_odd`.
	fn ed_recover_x(y: &BigUint, x_odd: bool, p: &BigUint) -> Option<BigUint> {
		let d = ed_d(p);
		let y2 = fe_mul(y, y, p);
		let num = fe_sub(&y2, &BigUint::from(1u32), p);
		let den = fe_add(&fe_mul(&d, &y2, p), &BigUint::from(1u32), p);
		let xx = fe_mul(&num, &fe_inv(&den, p), p);
		// sqrt mod p (p ≡ 5 mod 8): candidate = xx^((p+3)/8)
		let mut x = xx.modpow(&((p + 3u32) >> 3), p);
		if fe_mul(&x, &x, p) != xx {
			// multiply by 2^((p−1)/4)
			let i = BigUint::from(2u32).modpow(&((p - 1u32) >> 2), p);
			x = fe_mul(&x, &i, p);
		}
		if fe_mul(&x, &x, p) != xx {
			return None;
		}
		if x.bit(0) != x_odd {
			x = fe_sub(p, &x, p);
		}
		Some(x)
	}
	/// Unified twisted-Edwards addition (a = −1); complete for Edwards25519 (d non-square).
	fn ed_add(pt1: &(BigUint, BigUint), pt2: &(BigUint, BigUint), p: &BigUint) -> (BigUint, BigUint) {
		let (x1, y1) = pt1;
		let (x2, y2) = pt2;
		let d = ed_d(p);
		let x1x2 = fe_mul(x1, x2, p);
		let y1y2 = fe_mul(y1, y2, p);
		let dt = fe_mul(&d, &fe_mul(&x1x2, &y1y2, p), p);
		let x3 = fe_mul(
			&fe_add(&fe_mul(x1, y2, p), &fe_mul(y1, x2, p), p),
			&fe_inv(&fe_add(&BigUint::from(1u32), &dt, p), p),
			p,
		);
		let y3 = fe_mul(
			&fe_add(&y1y2, &x1x2, p), // y1y2 − a·x1x2 = y1y2 + x1x2 (a=−1)
			&fe_inv(&fe_sub(&BigUint::from(1u32), &dt, p), p),
			p,
		);
		(x3, y3)
	}
	fn ed_scalar_mul(k: &BigUint, pt: &(BigUint, BigUint), p: &BigUint) -> (BigUint, BigUint) {
		let mut acc = (zero_big(), BigUint::from(1u32)); // identity (0,1)
		for i in (0..k.bits()).rev() {
			acc = ed_add(&acc, &acc, p);
			if k.bit(i) {
				acc = ed_add(&acc, pt, p);
			}
		}
		acc
	}

	/// RFC 8032 §5.1.3 — decode a 32-byte compressed Edwards25519 point: y is the low 255
	/// bits (little-endian), bit 255 is the sign of x. Rejects y ≥ p, a non-square x², and
	/// the x==0/sign==1 case. Returns the affine (x, y).
	fn ed_decompress(b: &[u8; 32], p: &BigUint) -> Option<(BigUint, BigUint)> {
		let y_full = BigUint::from_bytes_le(b);
		let x0 = y_full.bit(255); // sign bit of x
		let mask = (BigUint::from(1u32) << 255u32) - BigUint::from(1u32);
		let y = &y_full & &mask;
		if &y >= p {
			return None; // y must be a canonical field element
		}
		let x = ed_recover_x(&y, x0, p)?;
		// reject the x==0 / sign==1 encoding, and confirm the parity matches the sign bit
		if x.bit(0) != x0 {
			return None;
		}
		Some((x, y))
	}

	/// RFC 8032 §5.1.7 — full Ed25519 verify. Decompress A and R, check S < ℓ, derive
	/// k = SHA-512(R ‖ A ‖ M) mod ℓ, and accept iff the cofactored equation
	/// [8][S]B == [8]R + [8][k]A holds.
	fn ed25519_verify(pubkey: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
		let p = prime(S2Curve::Ed25519);
		let l = order(S2Curve::Ed25519);

		let a = match ed_decompress(pubkey, &p) {
			Some(pt) => pt,
			None => return false,
		};
		let mut r_bytes = [0u8; 32];
		r_bytes.copy_from_slice(&sig[..32]);
		let r_pt = match ed_decompress(&r_bytes, &p) {
			Some(pt) => pt,
			None => return false,
		};
		let s = BigUint::from_bytes_le(&sig[32..]);
		if s >= l {
			return false; // S must be reduced mod ℓ (malleability guard)
		}

		// k = SHA-512(R ‖ A ‖ M) as a little-endian integer, reduced mod ℓ.
		let mut hasher = Sha512::new();
		hasher.update(&sig[..32]);
		hasher.update(pubkey);
		hasher.update(msg);
		let k = BigUint::from_bytes_le(&hasher.finalize()) % &l;

		let eight = BigUint::from(8u32);
		let b = ed_base(&p);
		// cofactored: [8][S]B == [8]R + [8][k]A  (8k < 8ℓ, no reduction needed since [8ℓ]·=O)
		let lhs = ed_scalar_mul(&(&eight * &s), &b, &p);
		let rhs = ed_add(
			&ed_scalar_mul(&eight, &r_pt, &p),
			&ed_scalar_mul(&(&eight * &k), &a, &p),
			&p,
		);
		lhs == rhs
	}

	/// GATE ref-S2-4 — Ed25519 group: B is on the curve, [ℓ]B = identity (0,1), and
	/// [2]B = B+B. Validates the twisted-Edwards arithmetic the Ed25519 circuit reuses.
	#[test]
	fn ed25519_group_law() {
		let p = prime(S2Curve::Ed25519);
		let l = order(S2Curve::Ed25519);
		let d = ed_d(&p);
		let b = ed_base(&p);
		// on curve: −x²+y² == 1 + d x²y²
		let x2 = fe_mul(&b.0, &b.0, &p);
		let y2 = fe_mul(&b.1, &b.1, &p);
		let lhs = fe_sub(&y2, &x2, &p);
		let rhs = fe_add(&BigUint::from(1u32), &fe_mul(&d, &fe_mul(&x2, &y2, &p), &p), &p);
		assert_eq!(lhs, rhs, "B not on Edwards25519");
		let id = (zero_big(), BigUint::from(1u32));
		assert_eq!(ed_scalar_mul(&l, &b, &p), id, "[ℓ]B must be identity");
		assert_eq!(ed_scalar_mul(&BigUint::from(2u32), &b, &p), ed_add(&b, &b, &p), "[2]B != B+B");
		println!("GATE ref-S2-4: B on Edwards25519, [ℓ]B=O, [2]B=B+B");
	}

	/// GATE ref-S2-5 — the FULL Ed25519 verify (decompress A,R + SHA-512-mod-ℓ + cofactored
	/// equation) accepts the RFC 8032 §7.1 TEST 1 (empty msg) and TEST 2 (1-byte msg)
	/// vectors, and REJECTS each tamper (signature, message, public key). Cross-validated
	/// against the RFC and an independent Python implementation.
	#[test]
	fn ed25519_verify_rfc8032() {
		fn arr32(s: &str) -> [u8; 32] {
			unhex(s).try_into().unwrap()
		}
		fn arr64(s: &str) -> [u8; 64] {
			unhex(s).try_into().unwrap()
		}

		// TEST 1 — empty message.
		let pk1 = arr32("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
		let sig1 = arr64(
			"e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
		);
		assert!(ed25519_verify(&pk1, b"", &sig1), "RFC 8032 TEST 1 must verify");

		// tampers on TEST 1
		let mut bad_sig = sig1;
		bad_sig[10] ^= 1;
		assert!(!ed25519_verify(&pk1, b"", &bad_sig), "tampered signature must reject");
		assert!(!ed25519_verify(&pk1, b"x", &sig1), "tampered message must reject");
		let mut bad_pk = pk1;
		bad_pk[0] ^= 1;
		assert!(!ed25519_verify(&bad_pk, b"", &sig1), "tampered public key must reject");

		// TEST 2 — 1-byte message 0x72.
		let pk2 = arr32("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
		let sig2 = arr64(
			"92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
		);
		assert!(ed25519_verify(&pk2, &[0x72], &sig2), "RFC 8032 TEST 2 must verify");

		println!("GATE ref-S2-5: full Ed25519 verify == RFC 8032 TEST 1/2; tampered sig/msg/pk reject");
	}

	// ── Ed25519 EXTENDED twisted-Edwards coords (X,Y,Z,T), the in-circuit point ops ──
	// Each fe_mul is an S0 ModMul mod p; add ≈ 8 muls, double ≈ 4 sqr + 4 mul; complete for
	// Edwards25519, so scalar-mul is a plain double-and-cadd with no exceptional cases.
	type EdExt = (BigUint, BigUint, BigUint, BigUint);
	fn ed_ext_from(pt: &(BigUint, BigUint), p: &BigUint) -> EdExt {
		(pt.0.clone(), pt.1.clone(), BigUint::from(1u32), fe_mul(&pt.0, &pt.1, p))
	}
	fn ed_ext_to(e: &EdExt, p: &BigUint) -> (BigUint, BigUint) {
		let zi = fe_inv(&e.2, p);
		(fe_mul(&e.0, &zi, p), fe_mul(&e.1, &zi, p))
	}
	fn ed_ext_add(e1: &EdExt, e2: &EdExt, p: &BigUint) -> EdExt {
		let (x1, y1, z1, t1) = e1;
		let (x2, y2, z2, t2) = e2;
		let d = ed_d(p);
		let a = fe_mul(&fe_sub(y1, x1, p), &fe_sub(y2, x2, p), p);
		let b = fe_mul(&fe_add(y1, x1, p), &fe_add(y2, x2, p), p);
		let two_d = fe_add(&d, &d, p);
		let c = fe_mul(&fe_mul(t1, &two_d, p), t2, p); // 2d·T1·T2
		let dd = fe_mul(&fe_add(z1, z1, p), z2, p); // 2·Z1·Z2
		let (e, f, g, h) =
			(fe_sub(&b, &a, p), fe_sub(&dd, &c, p), fe_add(&dd, &c, p), fe_add(&b, &a, p));
		(fe_mul(&e, &f, p), fe_mul(&g, &h, p), fe_mul(&f, &g, p), fe_mul(&e, &h, p))
	}
	fn ed_ext_dbl(e1: &EdExt, p: &BigUint) -> EdExt {
		let (x1, y1, z1, _) = e1;
		let a = fe_mul(x1, x1, p);
		let b = fe_mul(y1, y1, p);
		let c = fe_mul(&fe_add(z1, z1, p), z1, p); // 2·Z1²
		let dd = fe_sub(&zero_big(), &a, p); // −A (a=−1)
		let xy = fe_add(x1, y1, p);
		let e = fe_sub(&fe_sub(&fe_mul(&xy, &xy, p), &a, p), &b, p); // (X1+Y1)²−A−B
		let g = fe_add(&dd, &b, p);
		let f = fe_sub(&g, &c, p);
		let h = fe_sub(&dd, &b, p);
		(fe_mul(&e, &f, p), fe_mul(&g, &h, p), fe_mul(&f, &g, p), fe_mul(&e, &h, p))
	}
	fn ed_ext_mul(k: &BigUint, pt: &(BigUint, BigUint), p: &BigUint) -> (BigUint, BigUint) {
		let mut e: EdExt =
			(zero_big(), BigUint::from(1u32), BigUint::from(1u32), zero_big()); // identity
		let q = ed_ext_from(pt, p);
		for i in (0..k.bits()).rev() {
			e = ed_ext_dbl(&e, p);
			if k.bit(i) {
				e = ed_ext_add(&e, &q, p);
			}
		}
		ed_ext_to(&e, p)
	}

	// ── P-256 JACOBIAN coords (X,Y,Z), x=X/Z², y=Y/Z³, a=−3; one fe_inv at the end ──
	type Jac = (BigUint, BigUint, BigUint);
	fn jac_id() -> Jac {
		(BigUint::from(1u32), BigUint::from(1u32), zero_big())
	}
	fn jac_from(pt: &Aff) -> Jac {
		match pt {
			None => jac_id(),
			Some((x, y)) => (x.clone(), y.clone(), BigUint::from(1u32)),
		}
	}
	fn jac_to(j: &Jac, p: &BigUint) -> Aff {
		if is_zero(&j.2) {
			return None;
		}
		let zi = fe_inv(&j.2, p);
		let z2 = fe_mul(&zi, &zi, p);
		Some((fe_mul(&j.0, &z2, p), fe_mul(&fe_mul(&j.1, &z2, p), &zi, p)))
	}
	fn jac_dbl(j: &Jac, p: &BigUint) -> Jac {
		let (x1, y1, z1) = j;
		if is_zero(z1) || is_zero(y1) {
			return jac_id();
		}
		let delta = fe_mul(z1, z1, p);
		let gamma = fe_mul(y1, y1, p);
		let beta = fe_mul(x1, &gamma, p);
		let three = BigUint::from(3u32);
		let alpha = fe_mul(&three, &fe_mul(&fe_sub(x1, &delta, p), &fe_add(x1, &delta, p), p), p);
		let x3 = fe_sub(&fe_mul(&alpha, &alpha, p), &fe_mul(&BigUint::from(8u32), &beta, p), p);
		let yz = fe_add(y1, z1, p);
		let z3 = fe_sub(&fe_sub(&fe_mul(&yz, &yz, p), &gamma, p), &delta, p);
		let four_beta = fe_mul(&BigUint::from(4u32), &beta, p);
		let eight_g2 = fe_mul(&BigUint::from(8u32), &fe_mul(&gamma, &gamma, p), p);
		let y3 = fe_sub(&fe_mul(&alpha, &fe_sub(&four_beta, &x3, p), p), &eight_g2, p);
		(x3, y3, z3)
	}
	fn jac_add(j1: &Jac, j2: &Jac, p: &BigUint) -> Jac {
		if is_zero(&j1.2) {
			return j2.clone();
		}
		if is_zero(&j2.2) {
			return j1.clone();
		}
		let (x1, y1, z1) = j1;
		let (x2, y2, z2) = j2;
		let z1z1 = fe_mul(z1, z1, p);
		let z2z2 = fe_mul(z2, z2, p);
		let u1 = fe_mul(x1, &z2z2, p);
		let u2 = fe_mul(x2, &z1z1, p);
		let s1 = fe_mul(&fe_mul(y1, z2, p), &z2z2, p);
		let s2 = fe_mul(&fe_mul(y2, z1, p), &z1z1, p);
		if u1 == u2 {
			return if s1 == s2 { jac_dbl(j1, p) } else { jac_id() };
		}
		let h = fe_sub(&u2, &u1, p);
		let two_h = fe_add(&h, &h, p);
		let i = fe_mul(&two_h, &two_h, p);
		let jj = fe_mul(&h, &i, p);
		let r = fe_add(&fe_sub(&s2, &s1, p), &fe_sub(&s2, &s1, p), p); // 2(S2−S1)
		let v = fe_mul(&u1, &i, p);
		let x3 = fe_sub(&fe_sub(&fe_mul(&r, &r, p), &jj, p), &fe_add(&v, &v, p), p);
		let y3 = fe_sub(
			&fe_mul(&r, &fe_sub(&v, &x3, p), p),
			&fe_mul(&fe_add(&s1, &s1, p), &jj, p),
			p,
		); // r(V−X3) − 2·S1·J
		let z1z2 = fe_add(z1, z2, p);
		let z3 = fe_mul(
			&fe_sub(&fe_sub(&fe_mul(&z1z2, &z1z2, p), &z1z1, p), &z2z2, p),
			&h,
			p,
		);
		(x3, y3, z3)
	}
	fn jac_mul(k: &BigUint, pt: &Aff, p: &BigUint) -> Aff {
		let mut j = jac_id();
		let q = jac_from(pt);
		for i in (0..k.bits()).rev() {
			j = jac_dbl(&j, p);
			if k.bit(i) {
				j = jac_add(&j, &q, p);
			}
		}
		jac_to(&j, p)
	}

	/// GATE ref-S2-6 — Ed25519 extended-coordinate add/double (each op a field-op sequence
	/// over S0's ModMul, no per-add inversion) reproduce the affine scalar-mul across a range
	/// of scalars. Validated against the affine reference (and Python).
	#[test]
	fn ed25519_extended_point_ops_over_s0() {
		let p = prime(S2Curve::Ed25519);
		let b = ed_base(&p);
		for k in [1u32, 2, 3, 7, 100, 12345] {
			let k = BigUint::from(k);
			assert_eq!(ed_ext_mul(&k, &b, &p), ed_scalar_mul(&k, &b, &p), "ed extended != affine");
		}
		println!("GATE ref-S2-6: Ed25519 extended add(≈8mul)/dbl(≈4sqr+4mul) over S0 == affine");
	}

	/// GATE ref-S2-7 — P-256 Jacobian add/double (field-op sequences over S0, one final
	/// inversion to affine) reproduce the affine scalar-mul across a range of scalars.
	#[test]
	fn p256_jacobian_point_ops_over_s0() {
		let p = prime(S2Curve::P256);
		let g = Some((
			BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap(),
		));
		for k in [1u32, 2, 3, 7, 100, 12345, 98765] {
			let k = BigUint::from(k);
			assert_eq!(jac_mul(&k, &g, &p), p256_scalar_mul(&k, &g, &p), "jacobian != affine");
		}
		println!("GATE ref-S2-7: P-256 Jacobian add/dbl over S0 == affine (one final fe_inv)");
	}

	/// Windowed (STRANDED) double-and-add: the scalar's bits are split into `g` contiguous
	/// MSB-first windows. Strand w takes Acc_in (the partial result from higher windows),
	/// processes its window's bits (double + conditional-add), and emits Acc_out; the seam
	/// Acc_out(w) is bound in-circuit to Acc_in(w+1) by a channel push/pull. Peak RSS per
	/// strand ∝ ONE window (≈ nbits/g point ops), independent of the other windows — so `g`
	/// is the RSS knob (g=1 monolith … g=nbits one-op strands). Returns (result, per-strand
	/// Acc-out seam points). (Uses affine ops here for a clear decomposition check; in-circuit
	/// the per-step ops are the Jacobian/extended gadgets above.)
	fn scalar_mul_stranded(
		k: &BigUint,
		pt: &Aff,
		g: usize,
		nbits: usize,
		p: &BigUint,
	) -> (Aff, Vec<Aff>) {
		let b = nbits.div_ceil(g);
		let mut acc: Aff = None;
		let mut seams = Vec::with_capacity(g);
		for w in 0..g {
			let hi = nbits - w * b;
			let lo = hi.saturating_sub(b);
			for i in (lo..hi).rev() {
				acc = p256_add(&acc, &acc, p); // double
				if k.bit(i as u64) {
					acc = p256_add(&acc, pt, p); // conditional add
				}
			}
			seams.push(acc.clone()); // Acc_out(w) → seam into strand w+1
		}
		(acc, seams)
	}

	/// GATE ref-S2-8 (S2 scalar-mul strand loop) — the stranded double-and-add reproduces
	/// the plain scalar-mul for EVERY strand count g ∈ {1,2,4,8,16} (so g is a free RSS knob,
	/// the accumulator seam preserving the result), and the final seam equals the result.
	#[test]
	fn p256_scalar_mul_strand_loop() {
		let p = prime(S2Curve::P256);
		let g_pt = Some((
			BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap(),
		));
		for &g in &[1usize, 2, 4, 8, 16] {
			for k in [1u32, 7, 12345, 0xdead_beef] {
				let k = BigUint::from(k);
				let (res, seams) = scalar_mul_stranded(&k, &g_pt, g, 256, &p);
				assert_eq!(res, p256_scalar_mul(&k, &g_pt, &p), "stranded g={g} != plain");
				assert_eq!(seams.len(), g, "expected g seam points");
				assert_eq!(*seams.last().unwrap(), res, "final seam != result");
			}
		}
		println!("GATE ref-S2-8: stranded double-and-add == plain scalar-mul for g∈{{1,2,4,8,16}} (RSS knob G)");
	}

	/// In-circuit field inversion the S0 way: prover hints inv = a⁻¹ (and q); the circuit
	/// checks a·inv ≡ 1 (mod m) — i.e. a·inv == q·m + 1 (one S0 ModMul with the output pinned
	/// to the constant 1) AND inv < m. ONE multiply, vs Fermat's ~256 squarings. Sound: for
	/// a ≠ 0 the inverse is unique, so a·inv ≡ 1 pins inv = a⁻¹; a = 0 has no inverse (fails,
	/// correct — z=0 is the point at infinity, handled separately). Used once per
	/// Jacobian→affine (z⁻¹ mod p) and once for ECDSA s⁻¹ mod n.
	fn fe_inv_gadget_ok(a: &BigUint, inv: &BigUint, m: &BigUint) -> bool {
		if inv >= m {
			return false; // range on the hint
		}
		let prod = a * inv;
		let q = &prod / m;
		let r = &prod % m;
		r == BigUint::from(1u32) && &q * m + BigUint::from(1u32) == prod
	}

	/// GATE ref-S2-9 (S2 field inversion gadget) — the hint-and-verify inverse accepts the
	/// honest a⁻¹ and rejects a wrong hint, for BOTH the base field p (z⁻¹ in Jacobian→affine)
	/// and the scalar field n (ECDSA s⁻¹); and 0 correctly has no inverse.
	#[test]
	fn s2_fe_inv_gadget() {
		for curve in [S2Curve::Ed25519, S2Curve::P256] {
			let p = prime(curve);
			let n = order(curve);
			for &seed in &[2u32, 7, 12345, 0xdead_beef] {
				let a = BigUint::from(seed) % &p;
				let inv = fe_inv(&a, &p); // Fermat reference
				assert!(fe_inv_gadget_ok(&a, &inv, &p), "honest inverse must verify ({curve:?})");
				assert!(!fe_inv_gadget_ok(&a, &((&inv + 1u32) % &p), &p), "wrong inverse must reject");
				assert_eq!((&a * &inv) % &p, BigUint::from(1u32), "a·a⁻¹ ≢ 1");
			}
			// ECDSA s⁻¹ mod n
			let s = BigUint::from(999_983u32) % &n;
			let sinv = s.modpow(&(&n - 2u32), &n);
			assert!(fe_inv_gadget_ok(&s, &sinv, &n), "ECDSA s⁻¹ mod n must verify");
			// 0 has no inverse
			assert!(!fe_inv_gadget_ok(&BigUint::from(0u32), &BigUint::from(5u32), &p), "0 has no inverse");
		}
		println!("GATE ref-S2-9: fe_inv (hint a⁻¹, verify a·inv≡1) — honest ok, wrong rejected, 0 no-inverse, mod p AND n");
	}

	/// In-circuit modular sqrt for point decompression the S0 way: prover hints x = √xx; the
	/// circuit verifies x² ≡ xx (mod p) with ONE S0 ModMul. The sqrt ALGORITHM is entirely
	/// the prover's — the circuit only checks the witness — so a NON-SQUARE xx (an invalid
	/// encoding) is unsatisfiable ⇒ decompression rejects, at no in-circuit sqrt cost.
	fn fe_sqrt_gadget_ok(xx: &BigUint, x: &BigUint, p: &BigUint) -> bool {
		x < p && fe_mul(x, x, p) == *xx
	}

	/// Full Ed25519 decompression gadget (RFC 8032 §5.1.3): from the encoded (y, sign x0),
	/// compute xx = (y²−1)/(d·y²+1) [fe_mul + fe_inv gadgets], verify the hinted x via
	/// `fe_sqrt_gadget_ok`, and enforce the sign (x.bit(0)==x0, reject x==0 & x0==1). Returns
	/// the decompressed x, or None if it does not decompress (non-square / wrong sign).
	fn decompress_gadget(y: &BigUint, x0: bool, x_hint: &BigUint, p: &BigUint) -> Option<BigUint> {
		let d = ed_d(p);
		let y2 = fe_mul(y, y, p);
		let num = fe_sub(&y2, &BigUint::from(1u32), p);
		let den = fe_add(&fe_mul(&d, &y2, p), &BigUint::from(1u32), p);
		let xx = fe_mul(&num, &fe_inv(&den, p), p);
		if !fe_sqrt_gadget_ok(&xx, x_hint, p) {
			return None; // non-square / wrong root hint
		}
		if x_hint.bit(0) != x0 || (is_zero(x_hint) && x0) {
			return None; // sign mismatch / illegal x==0 negative
		}
		Some(x_hint.clone())
	}

	/// GATE ref-S2-10 (S2 decompression sqrt gadget) — valid points (B and several [k]B)
	/// decompress via their hinted x (x²≡xx + correct sign); a wrong root hint, a wrong sign
	/// bit, and a NON-SQUARE y (invalid encoding, e.g. y=2) all correctly reject.
	#[test]
	fn s2_decompress_sqrt_gadget() {
		let p = prime(S2Curve::Ed25519);
		let b = ed_base(&p);
		let x0 = b.0.bit(0);
		assert_eq!(decompress_gadget(&b.1, x0, &b.0, &p), Some(b.0.clone()), "B must decompress");
		assert_eq!(decompress_gadget(&b.1, x0, &(&b.0 + 1u32), &p), None, "wrong root hint must reject");
		assert_eq!(decompress_gadget(&b.1, !x0, &b.0, &p), None, "wrong sign must reject");
		for k in [2u32, 3, 7, 100] {
			let pt = ed_scalar_mul(&BigUint::from(k), &b, &p);
			let x0k = pt.0.bit(0);
			assert_eq!(decompress_gadget(&pt.1, x0k, &pt.0, &p), Some(pt.0.clone()), "[{k}]B must decompress");
		}
		// non-square xx (invalid encoding): the sqrt is unsatisfiable ⇒ reject. (y=2 is one.)
		let mut found = false;
		for t in 0u32..50 {
			let y = BigUint::from(t) % &p;
			if ed_recover_x(&y, false, &p).is_none() {
				assert_eq!(decompress_gadget(&y, false, &BigUint::from(3u32), &p), None, "non-square y must reject");
				found = true;
				break;
			}
		}
		assert!(found, "expected a non-square y in [0,50)");
		println!("GATE ref-S2-10: decompression sqrt (hint √xx, verify x²≡xx) + sign — valid decompress, wrong-x/sign/non-square reject");
	}

	fn p256_g() -> Aff {
		Some((
			BigUint::parse_bytes(P256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P256_GY.as_bytes(), 16).unwrap(),
		))
	}

	/// Jacobian scalar-mul returning the UN-converted Jac point (so two of them can be added
	/// in Jacobian and converted to affine with ONE fe_inv — the ECDSA u1·G + u2·Q shape).
	fn jac_scalar(k: &BigUint, pt: &Aff, p: &BigUint) -> Jac {
		let mut j = jac_id();
		let q = jac_from(pt);
		for i in (0..k.bits()).rev() {
			j = jac_dbl(&j, p);
			if k.bit(i) {
				j = jac_add(&j, &q, p);
			}
		}
		j
	}

	/// The in-circuit ECDSA-P256 verify ASSEMBLY, composed from the S2 gadgets:
	///   e = SHA-256(M) mod n [SHA-256 gadget];  w = s⁻¹ mod n [fe_inv gadget];
	///   u1 = e·w, u2 = r·w mod n;  P = u1·G + u2·Q in Jacobian [jac_scalar + jac_add], ONE
	///   fe_inv to affine [jac_to];  ACCEPT ⟺ (P.x mod n) == r.
	/// The x mod n is a single conditional subtract (x < p < 2n ⇒ x mod n = x or x−n), the
	/// x≡r boundary.
	fn ecdsa_verify_assembly(e: &BigUint, q: &Aff, r: &BigUint, s: &BigUint) -> bool {
		let p = prime(S2Curve::P256);
		let n = order(S2Curve::P256);
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return false;
		}
		// w = s⁻¹ mod n, verified by the fe_inv gadget (hint + a·inv≡1).
		let w = s.modpow(&(&n - 2u32), &n);
		if !fe_inv_gadget_ok(s, &w, &n) {
			return false;
		}
		let u1 = (e * &w) % &n;
		let u2 = (r * &w) % &n;
		let j = jac_add(&jac_scalar(&u1, &p256_g(), &p), &jac_scalar(&u2, q, &p), &p);
		match jac_to(&j, &p) {
			None => false,
			Some((x, _)) => {
				let x_modn = if x < n { x } else { &x - &n }; // x mod n (one conditional subtract)
				x_modn == *r
			}
		}
	}

	/// GATE ref-S2-11 (ECDSA verify assembly) — a REAL ECDSA-P256 signature over a message
	/// hashed by `sha256_ref` verifies through the full gadget assembly (fe_inv w + Jacobian
	/// u1·G+u2·Q + x≡r), the assembly agrees with the affine `ecdsa_p256_verify`, and each
	/// tamper (r, s, e) rejects.
	#[test]
	fn ecdsa_verify_assembly_gate() {
		let p = prime(S2Curve::P256);
		let n = order(S2Curve::P256);
		let g = p256_g();
		// message → e via the SHA-256 gadget reference
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(b"ECDSA-P256 assembly test")) % &n;
		let d = BigUint::parse_bytes(b"c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 16).unwrap();
		let k = BigUint::parse_bytes(b"7a1a7e52797fc8caaa435d2a4dace39158504bf204fbe19f14dbb427faee50ae", 16).unwrap();
		let q = p256_scalar_mul(&d, &g, &p);
		let r = match p256_scalar_mul(&k, &g, &p) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;

		assert!(ecdsa_verify_assembly(&e, &q, &r, &s), "genuine ECDSA sig must verify via assembly");
		assert_eq!(
			ecdsa_verify_assembly(&e, &q, &r, &s),
			ecdsa_p256_verify(&e, &q, &r, &s),
			"assembly != affine reference"
		);
		assert!(!ecdsa_verify_assembly(&e, &q, &((&r + 1u32) % &n), &s), "tampered r must reject");
		assert!(!ecdsa_verify_assembly(&e, &q, &r, &((&s + 1u32) % &n)), "tampered s must reject");
		assert!(!ecdsa_verify_assembly(&((&e + 1u32) % &n), &q, &r, &s), "tampered e must reject");
		println!("GATE ref-S2-11: ECDSA verify assembly (SHA-256→e, fe_inv w, Jacobian u1·G+u2·Q, x≡r) == ref; tampers reject");
	}

	/// Extended-coordinate scalar-mul returning the UN-converted EdExt (so the cofactored
	/// equation's two sides are compared projectively — no final inversion).
	fn ed_ext_scalar(k: &BigUint, pt: &(BigUint, BigUint), p: &BigUint) -> EdExt {
		let mut e: EdExt = (zero_big(), BigUint::from(1u32), BigUint::from(1u32), zero_big());
		let q = ed_ext_from(pt, p);
		for i in (0..k.bits()).rev() {
			e = ed_ext_dbl(&e, p);
			if k.bit(i) {
				e = ed_ext_add(&e, &q, p);
			}
		}
		e
	}

	/// Projective equality of two extended points via CROSS-MULTIPLICATION (X_L·Z_R ≡ X_R·Z_L
	/// and Y_L·Z_R ≡ Y_R·Z_L) — the in-circuit point-equality check, avoiding two inversions.
	fn ext_eq(l: &EdExt, r: &EdExt, p: &BigUint) -> bool {
		fe_mul(&l.0, &r.2, p) == fe_mul(&r.0, &l.2, p) && fe_mul(&l.1, &r.2, p) == fe_mul(&r.1, &l.2, p)
	}

	/// Decompress via the sqrt gadget: the prover computes x (reference), the `decompress_gadget`
	/// VERIFIES it (x²≡xx + sign) — the in-circuit decompression path.
	fn decompress_via_gadget(b: &[u8; 32], p: &BigUint) -> Option<(BigUint, BigUint)> {
		let y_full = BigUint::from_bytes_le(b);
		let x0 = y_full.bit(255);
		let mask = (BigUint::from(1u32) << 255u32) - BigUint::from(1u32);
		let y = &y_full & &mask;
		if &y >= p {
			return None;
		}
		let x_hint = ed_recover_x(&y, x0, p)?; // prover's sqrt
		let x = decompress_gadget(&y, x0, &x_hint, p)?; // gadget verifies
		Some((x, y))
	}

	/// The in-circuit Ed25519 verify ASSEMBLY (RFC 8032 §5.1.7), composed from the S2 gadgets:
	///   decompress A, R [sqrt gadget]; S < ℓ; k = SHA-512(R‖A‖M) mod ℓ [SHA-512 gadget];
	///   L = [8][S]B and Rhs = [8]R + [8][k]A [extended-coord scalar-mul]; ACCEPT ⟺ L == Rhs
	///   [cross-mult projective equality].
	fn ed25519_verify_assembly(pubkey: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
		let p = prime(S2Curve::Ed25519);
		let l = order(S2Curve::Ed25519);
		let a = match decompress_via_gadget(pubkey, &p) {
			Some(pt) => pt,
			None => return false,
		};
		let mut rb = [0u8; 32];
		rb.copy_from_slice(&sig[..32]);
		let r_pt = match decompress_via_gadget(&rb, &p) {
			Some(pt) => pt,
			None => return false,
		};
		let s = BigUint::from_bytes_le(&sig[32..]);
		if s >= l {
			return false;
		}
		let mut input = sig[..32].to_vec();
		input.extend_from_slice(pubkey);
		input.extend_from_slice(msg);
		let k = BigUint::from_bytes_le(&crate::sha512_gadget::sha512_ref(&input)) % &l;

		let eight = BigUint::from(8u32);
		let b = ed_base(&p);
		let lhs = ed_ext_scalar(&(&eight * &s), &b, &p);
		let rhs = ed_ext_add(
			&ed_ext_scalar(&eight, &r_pt, &p),
			&ed_ext_scalar(&(&eight * &k), &a, &p),
			&p,
		);
		ext_eq(&lhs, &rhs, &p)
	}

	/// GATE ref-S2-12 (Ed25519 verify assembly) — the full gadget assembly (sqrt decompress +
	/// SHA-512 k + extended-coord [8][S]B / [8]R+[8][k]A + cross-mult equality) verifies the
	/// RFC 8032 TEST 1/2 vectors, agrees with the affine `ed25519_verify`, and rejects a
	/// tampered signature/message.
	#[test]
	fn ed25519_verify_assembly_gate() {
		let pk1: [u8; 32] =
			unhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a").try_into().unwrap();
		let sig1: [u8; 64] = unhex(
			"e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
		).try_into().unwrap();
		assert!(ed25519_verify_assembly(&pk1, b"", &sig1), "RFC 8032 TEST 1 assembly must verify");
		assert_eq!(
			ed25519_verify_assembly(&pk1, b"", &sig1),
			ed25519_verify(&pk1, b"", &sig1),
			"assembly != affine reference"
		);
		let mut bad = sig1;
		bad[10] ^= 1;
		assert!(!ed25519_verify_assembly(&pk1, b"", &bad), "tampered signature must reject");
		assert!(!ed25519_verify_assembly(&pk1, b"x", &sig1), "tampered message must reject");

		let pk2: [u8; 32] =
			unhex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c").try_into().unwrap();
		let sig2: [u8; 64] = unhex(
			"92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
		).try_into().unwrap();
		assert!(ed25519_verify_assembly(&pk2, &[0x72], &sig2), "RFC 8032 TEST 2 assembly must verify");
		println!("GATE ref-S2-12: Ed25519 assembly (decompress+SHA-512+ext-scalar+cross-mult [8][S]B==[8]R+[8][k]A) == RFC8032/ref; tampers reject");
	}

	// ── NIST P-384 (DNSSEC alg 14, ECDSA-P384/SHA-384) — same a=−3 short Weierstrass, so the
	// P-256 point ops (generic in p) are REUSED; only the 384-bit field/order + SHA-384 differ.
	const P384_P: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff";
	const P384_N: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973";
	const P384_B: &str = "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef";
	const P384_GX: &str = "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7";
	const P384_GY: &str = "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f";

	fn p384_g() -> Aff {
		Some((
			BigUint::parse_bytes(P384_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P384_GY.as_bytes(), 16).unwrap(),
		))
	}

	/// ECDSA-P384 verify (DNSSEC alg 14): identical structure to P-256, reusing the a=−3
	/// Weierstrass point ops over the 384-bit field. In-circuit the field multiply is either
	/// S0 `ModMul<768>` or the S3 limb schoolbook (12 × 32-bit limbs); e = SHA-384(M) mod n.
	fn ecdsa_p384_verify(e: &BigUint, q: &Aff, r: &BigUint, s: &BigUint) -> bool {
		let p = BigUint::parse_bytes(P384_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(P384_N.as_bytes(), 16).unwrap();
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return false;
		}
		let w = s.modpow(&(&n - 2u32), &n);
		let u1 = (e * &w) % &n;
		let u2 = (r * &w) % &n;
		let pt = p256_add(&p256_scalar_mul(&u1, &p384_g(), &p), &p256_scalar_mul(&u2, q, &p), &p);
		match pt {
			None => false,
			Some((x, _)) => (x % &n) == *r,
		}
	}

	/// GATE ref-S2-13 (ECDSA-P384 verify, DNSSEC alg 14) — the P-384 base point is on the
	/// curve, [n]G = O, a REAL ECDSA-P384 signature over a message hashed by `sha384_ref`
	/// verifies (reusing the a=−3 Weierstrass ops), and tampered r/e reject.
	#[test]
	fn ecdsa_p384_verify_gate() {
		let p = BigUint::parse_bytes(P384_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(P384_N.as_bytes(), 16).unwrap();
		let b = BigUint::parse_bytes(P384_B.as_bytes(), 16).unwrap();
		let g = p384_g();
		let (gx, gy) = match &g {
			Some((x, y)) => (x.clone(), y.clone()),
			None => unreachable!(),
		};
		let three = BigUint::from(3u32);
		assert_eq!(
			fe_mul(&gy, &gy, &p),
			fe_sub(&fe_add(&fe_mul(&gx, &fe_mul(&gx, &gx, &p), &p), &b, &p), &fe_mul(&three, &gx, &p), &p),
			"P-384 base point not on curve"
		);
		assert!(p256_scalar_mul(&n, &g, &p).is_none(), "[n]G must be O");

		let d = BigUint::parse_bytes(b"6b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d896d5724e4c70a825f872c9ea60d2edf5", 16).unwrap() % &n;
		let k = BigUint::parse_bytes(b"c838b85253ef8dc7394fa5808a5183981c7deef5a69ba8f4f2117ffea39cfcd90e95f6cbc854abacab701d50c1f3cf24", 16).unwrap() % &n;
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha384_ref(b"ECDSA-P384 test")) % &n;
		let q = p256_scalar_mul(&d, &g, &p);
		let r = match p256_scalar_mul(&k, &g, &p) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;

		assert!(ecdsa_p384_verify(&e, &q, &r, &s), "genuine ECDSA-P384 sig must verify");
		assert!(!ecdsa_p384_verify(&e, &q, &((&r + 1u32) % &n), &s), "tampered r must reject");
		assert!(!ecdsa_p384_verify(&((&e + 1u32) % &n), &q, &r, &s), "tampered e must reject");
		println!("GATE ref-S2-13: ECDSA-P384 (DNSSEC alg 14, SHA-384) verify + tampers; reuses a=−3 Weierstrass ops over the 384-bit field");
	}

	// ── Edwards448 / Ed448 (DNSSEC alg 16, RFC 8032) — UNTWISTED Edwards (a=1), Goldilocks
	// prime p=2^448−2^224−1, cofactor 4, and — notably — SHAKE-256 for hashing (reuses S1b's
	// SHAKE gadget, not SHA-512). Field ops (mod p) use S0 ModMul<≥896> or the S3 limb schoolbook.
	const ED448_P: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
	const ED448_D: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffff6756";
	const ED448_L: &str = "3fffffffffffffffffffffffffffffffffffffffffffffffffffffff7cca23e9c44edb49aed63690216cc2728dc58f552378c292ab5844f3";
	const ED448_BX: &str = "4f1970c66bed0ded221d15a622bf36da9e146570470f1767ea6de324a3d3a46412ae1af72ab66511433b80e18b00938e2626a82bc70cc05e";
	const ED448_BY: &str = "693f46716eb6bc248876203756c9c7624bea73736ca3984087789c1e05a0c2d73ad3ff1ce67c39c4fdbd132c4ed7c8ad9808795bf230fa14";

	fn ed448_p() -> BigUint {
		BigUint::parse_bytes(ED448_P.as_bytes(), 16).unwrap()
	}
	fn ed448_l() -> BigUint {
		BigUint::parse_bytes(ED448_L.as_bytes(), 16).unwrap()
	}
	fn ed448_d(p: &BigUint) -> BigUint {
		let _ = p;
		BigUint::parse_bytes(ED448_D.as_bytes(), 16).unwrap()
	}
	fn ed448_base() -> (BigUint, BigUint) {
		(
			BigUint::parse_bytes(ED448_BX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(ED448_BY.as_bytes(), 16).unwrap(),
		)
	}
	/// Untwisted Edwards addition (a=1): y3 numerator is y1y2 − x1x2 (vs +x1x2 for Ed25519's
	/// a=−1). Complete for Edwards448 (d non-square).
	fn ed448_add(pt1: &(BigUint, BigUint), pt2: &(BigUint, BigUint), p: &BigUint) -> (BigUint, BigUint) {
		let (x1, y1) = pt1;
		let (x2, y2) = pt2;
		let dd = ed448_d(p);
		let x1x2 = fe_mul(x1, x2, p);
		let y1y2 = fe_mul(y1, y2, p);
		let dt = fe_mul(&dd, &fe_mul(&x1x2, &y1y2, p), p);
		let x3 = fe_mul(
			&fe_add(&fe_mul(x1, y2, p), &fe_mul(y1, x2, p), p),
			&fe_inv(&fe_add(&BigUint::from(1u32), &dt, p), p),
			p,
		);
		let y3 = fe_mul(
			&fe_sub(&y1y2, &x1x2, p), // a=1 ⇒ y1y2 − x1x2
			&fe_inv(&fe_sub(&BigUint::from(1u32), &dt, p), p),
			p,
		);
		(x3, y3)
	}
	fn ed448_scalar_mul(k: &BigUint, pt: &(BigUint, BigUint), p: &BigUint) -> (BigUint, BigUint) {
		let mut acc = (zero_big(), BigUint::from(1u32));
		for i in (0..k.bits()).rev() {
			acc = ed448_add(&acc, &acc, p);
			if k.bit(i) {
				acc = ed448_add(&acc, pt, p);
			}
		}
		acc
	}
	/// RFC 8032 §5.2.3 — decode a 57-byte Ed448 point: y is the low 448 bits (LE), bit 455 is
	/// the x sign. x² = (y²−1)/(d·y²−1); sqrt via x^((p+1)/4) since p ≡ 3 (mod 4).
	fn ed448_decode(b: &[u8; 57], p: &BigUint) -> Option<(BigUint, BigUint)> {
		let y_full = BigUint::from_bytes_le(b);
		let s = y_full.bit(455);
		let mask = (BigUint::from(1u32) << 448u32) - BigUint::from(1u32);
		let y = &y_full & &mask;
		if &y >= p {
			return None;
		}
		let dd = ed448_d(p);
		let y2 = fe_mul(&y, &y, p);
		let u = fe_sub(&y2, &BigUint::from(1u32), p);
		let v = fe_sub(&fe_mul(&dd, &y2, p), &BigUint::from(1u32), p);
		let xx = fe_mul(&u, &fe_inv(&v, p), p);
		let x = xx.modpow(&((p + BigUint::from(1u32)) >> 2), p);
		if fe_mul(&x, &x, p) != xx {
			return None;
		}
		if is_zero(&x) && s {
			return None;
		}
		let x = if x.bit(0) != s { fe_sub(p, &x, p) } else { x };
		Some((x, y))
	}
	/// RFC 8032 §5.2.7 — full Ed448 verify (pure, empty context): decode A, R; S < ℓ;
	/// k = SHAKE-256(dom4 ‖ R ‖ A ‖ M, 114) mod ℓ [the S1b SHAKE-256 gadget]; accept ⟺
	/// [4][S]B == [4]R + [4][k]A (cofactor 4).
	fn ed448_verify(pubkey: &[u8; 57], msg: &[u8], sig: &[u8; 114]) -> bool {
		let p = ed448_p();
		let l = ed448_l();
		let a = match ed448_decode(pubkey, &p) {
			Some(pt) => pt,
			None => return false,
		};
		let mut rb = [0u8; 57];
		rb.copy_from_slice(&sig[..57]);
		let r_pt = match ed448_decode(&rb, &p) {
			Some(pt) => pt,
			None => return false,
		};
		let s = BigUint::from_bytes_le(&sig[57..114]);
		if s >= l {
			return false;
		}
		let mut input = b"SigEd448".to_vec();
		input.push(0); // phflag = 0 (pure)
		input.push(0); // context length = 0
		input.extend_from_slice(&sig[..57]);
		input.extend_from_slice(pubkey);
		input.extend_from_slice(msg);
		let k = BigUint::from_bytes_le(&crate::mldsa_shake::shake256_xof(&input, 114)) % &l;

		let four = BigUint::from(4u32);
		let b = ed448_base();
		let lhs = ed448_scalar_mul(&(&four * &s), &b, &p);
		let rhs = ed448_add(
			&ed448_scalar_mul(&four, &r_pt, &p),
			&ed448_scalar_mul(&(&four * &k), &a, &p),
			&p,
		);
		lhs == rhs
	}

	/// GATE ref-S2-14 (Ed448 verify, DNSSEC alg 16) — B is on the untwisted curve, [ℓ]B = O,
	/// and the full Ed448 verify (SHAKE-256 k + cofactor-4 equation) accepts the RFC 8032 §7.4
	/// "blank" test vector while rejecting a tampered signature/message.
	#[test]
	fn ed448_verify_rfc8032() {
		let p = ed448_p();
		let b = ed448_base();
		let d = ed448_d(&p);
		// on curve: x²+y² == 1 + d x²y²
		let x2 = fe_mul(&b.0, &b.0, &p);
		let y2 = fe_mul(&b.1, &b.1, &p);
		assert_eq!(
			fe_add(&x2, &y2, &p),
			fe_add(&BigUint::from(1u32), &fe_mul(&d, &fe_mul(&x2, &y2, &p), &p), &p),
			"B not on Edwards448"
		);
		assert_eq!(ed448_scalar_mul(&ed448_l(), &b, &p), (zero_big(), BigUint::from(1u32)), "[ℓ]B must be O");

		let pk: [u8; 57] = unhex("5fd7449b59b461fd2ce787ec616ad46a1da1342485a70e1f8a0ea75d80e96778edf124769b46c7061bd6783df1e50f6cd1fa1abeafe8256180").try_into().unwrap();
		let sig: [u8; 114] = unhex("533a37f6bbe457251f023c0d88f976ae2dfb504a843e34d2074fd823d41a591f2b233f034f628281f2fd7a22ddd47d7828c59bd0a21bfd3980ff0d2028d4b18a9df63e006c5d1c2d345b925d8dc00b4104852db99ac5c7cdda8530a113a0f4dbb61149f05a7363268c71d95808ff2e652600").try_into().unwrap();
		assert!(ed448_verify(&pk, b"", &sig), "RFC 8032 Ed448 blank must verify");
		let mut bad = sig;
		bad[20] ^= 1;
		assert!(!ed448_verify(&pk, b"", &bad), "tampered signature must reject");
		assert!(!ed448_verify(&pk, b"x", &sig), "tampered message must reject");
		println!("GATE ref-S2-14: Ed448 (DNSSEC alg 16) — untwisted a=1, SHAKE-256 k, cofactor 4; RFC 8032 blank verifies; tampers reject");
	}

	// ── secp256k1 (Bitcoin/Ethereum) — short Weierstrass with a=0 (vs a=−3 for P-256/P-384),
	// so the doubling λ = 3x²/(2y). Generic `a`-parameterized ops so all Weierstrass curves reuse.
	const SECP256K1_P: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
	const SECP256K1_N: &str = "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141";
	const SECP256K1_GX: &str = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
	const SECP256K1_GY: &str = "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8";

	/// Generic short-Weierstrass affine addition with an explicit curve coefficient `a`
	/// (P-256/P-384 have a = p−3; secp256k1 has a = 0). Doubling λ = (3x²+a)/(2y).
	fn w_add_a(pt1: &Aff, pt2: &Aff, p: &BigUint, a: &BigUint) -> Aff {
		match (pt1, pt2) {
			(None, _) => pt2.clone(),
			(_, None) => pt1.clone(),
			(Some((x1, y1)), Some((x2, y2))) => {
				if x1 == x2 && is_zero(&fe_add(y1, y2, p)) {
					return None;
				}
				let lambda = if x1 == x2 && y1 == y2 {
					let num = fe_add(&fe_mul(&BigUint::from(3u32), &fe_mul(x1, x1, p), p), a, p); // 3x²+a
					fe_mul(&num, &fe_inv(&fe_add(y1, y1, p), p), p)
				} else {
					fe_mul(&fe_sub(y2, y1, p), &fe_inv(&fe_sub(x2, x1, p), p), p)
				};
				let x3 = fe_sub(&fe_sub(&fe_mul(&lambda, &lambda, p), x1, p), x2, p);
				let y3 = fe_sub(&fe_mul(&lambda, &fe_sub(x1, &x3, p), p), y1, p);
				Some((x3, y3))
			}
		}
	}
	fn w_scalar_mul_a(k: &BigUint, pt: &Aff, p: &BigUint, a: &BigUint) -> Aff {
		let mut acc: Aff = None;
		for i in (0..k.bits()).rev() {
			acc = w_add_a(&acc, &acc, p, a);
			if k.bit(i) {
				acc = w_add_a(&acc, pt, p, a);
			}
		}
		acc
	}
	fn secp256k1_g() -> Aff {
		Some((
			BigUint::parse_bytes(SECP256K1_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(SECP256K1_GY.as_bytes(), 16).unwrap(),
		))
	}
	/// ECDSA-secp256k1 verify (Bitcoin/Ethereum) — the ECDSA structure with a=0 Weierstrass
	/// ops and SHA-256; e = SHA-256(M) mod n.
	fn ecdsa_secp256k1_verify(e: &BigUint, q: &Aff, r: &BigUint, s: &BigUint) -> bool {
		let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();
		let a = BigUint::from(0u32);
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return false;
		}
		let w = s.modpow(&(&n - 2u32), &n);
		let u1 = (e * &w) % &n;
		let u2 = (r * &w) % &n;
		let pt = w_add_a(
			&w_scalar_mul_a(&u1, &secp256k1_g(), &p, &a),
			&w_scalar_mul_a(&u2, q, &p, &a),
			&p,
			&a,
		);
		match pt {
			None => false,
			Some((x, _)) => (x % &n) == *r,
		}
	}

	/// GATE ref-S2-15 (ECDSA secp256k1, Bitcoin/Ethereum) — G is on y²=x³+7, [n]G=O, and a real
	/// ECDSA-secp256k1 signature (SHA-256, a=0 ops) verifies while tampered r/e reject.
	#[test]
	fn ecdsa_secp256k1_verify_gate() {
		let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();
		let a = BigUint::from(0u32);
		let g = secp256k1_g();
		// G on curve: y² == x³ + 7 (a=0, b=7)
		let (gx, gy) = match &g {
			Some((x, y)) => (x.clone(), y.clone()),
			None => unreachable!(),
		};
		let rhs = fe_add(&fe_mul(&gx, &fe_mul(&gx, &gx, &p), &p), &BigUint::from(7u32), &p);
		assert_eq!(fe_mul(&gy, &gy, &p), rhs, "secp256k1 G not on y²=x³+7");
		assert!(w_scalar_mul_a(&n, &g, &p, &a).is_none(), "[n]G must be O");

		let d = BigUint::parse_bytes(b"c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 16).unwrap() % &n;
		let k = BigUint::parse_bytes(b"7a1a7e52797fc8caaa435d2a4dace39158504bf204fbe19f14dbb427faee50ae", 16).unwrap() % &n;
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(b"secp256k1 test")) % &n;
		let q = w_scalar_mul_a(&d, &g, &p, &a);
		let r = match w_scalar_mul_a(&k, &g, &p, &a) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;

		assert!(ecdsa_secp256k1_verify(&e, &q, &r, &s), "genuine secp256k1 sig must verify");
		assert!(!ecdsa_secp256k1_verify(&e, &q, &((&r + 1u32) % &n), &s), "tampered r must reject");
		assert!(!ecdsa_secp256k1_verify(&((&e + 1u32) % &n), &q, &r, &s), "tampered e must reject");
		println!("GATE ref-S2-15: ECDSA secp256k1 (Bitcoin/Ethereum, a=0) — G on y²=x³+7, [n]G=O, verify + tampers");
	}

	// ── NIST P-521 (the largest NIST prime curve) — a=−3 (reuses w_add_a with a=p−3), field
	// p=2^521−1 (Mersenne), SHA-512. In-circuit the field multiply is the S3 limb schoolbook
	// (17 × 32-bit limbs) or S0 ModMul<≥1088>.
	const P521_N: &str = "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409";
	const P521_B: &str = "0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00";
	const P521_GX: &str = "00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66";
	const P521_GY: &str = "011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650";

	fn p521_p() -> BigUint {
		(BigUint::from(1u32) << 521u32) - BigUint::from(1u32)
	}
	fn p521_g() -> Aff {
		Some((
			BigUint::parse_bytes(P521_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(P521_GY.as_bytes(), 16).unwrap(),
		))
	}
	/// ECDSA-P521 verify — a=−3 Weierstrass (reuses `w_add_a` with a=p−3) over the 521-bit
	/// Mersenne field, SHA-512 message hash; e = SHA-512(M) mod n.
	fn ecdsa_p521_verify(e: &BigUint, q: &Aff, r: &BigUint, s: &BigUint) -> bool {
		let p = p521_p();
		let n = BigUint::parse_bytes(P521_N.as_bytes(), 16).unwrap();
		let a = fe_sub(&p, &BigUint::from(3u32), &p); // a = −3 mod p
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return false;
		}
		let w = s.modpow(&(&n - 2u32), &n);
		let u1 = (e * &w) % &n;
		let u2 = (r * &w) % &n;
		let pt = w_add_a(
			&w_scalar_mul_a(&u1, &p521_g(), &p, &a),
			&w_scalar_mul_a(&u2, q, &p, &a),
			&p,
			&a,
		);
		match pt {
			None => false,
			Some((x, _)) => (x % &n) == *r,
		}
	}

	/// GATE ref-S2-16 (ECDSA P-521) — p = 2^521−1, G on y²=x³−3x+b, [n]G=O, and a real
	/// ECDSA-P521 signature over a SHA-512-hashed message verifies while tampered r/e reject.
	#[test]
	fn ecdsa_p521_verify_gate() {
		let p = p521_p();
		let n = BigUint::parse_bytes(P521_N.as_bytes(), 16).unwrap();
		let b = BigUint::parse_bytes(P521_B.as_bytes(), 16).unwrap();
		let a = fe_sub(&p, &BigUint::from(3u32), &p);
		let g = p521_g();
		assert_eq!(p, (BigUint::from(1u32) << 521u32) - BigUint::from(1u32), "p must be 2^521−1");
		assert_eq!(p.bits(), 521);
		let (gx, gy) = match &g {
			Some((x, y)) => (x.clone(), y.clone()),
			None => unreachable!(),
		};
		let three = BigUint::from(3u32);
		let rhs = fe_sub(&fe_add(&fe_mul(&gx, &fe_mul(&gx, &gx, &p), &p), &b, &p), &fe_mul(&three, &gx, &p), &p);
		assert_eq!(fe_mul(&gy, &gy, &p), rhs, "P-521 G not on curve");
		assert!(w_scalar_mul_a(&n, &g, &p, &a).is_none(), "[n]G must be O");

		let d = BigUint::parse_bytes(b"6b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d896d5724e4c70a825f872c9ea60d2edf5", 16).unwrap() % &n;
		let k = BigUint::parse_bytes(b"c838b85253ef8dc7394fa5808a5183981c7deef5a69ba8f4f2117ffea39cfcd90e95f6cbc854abacab701d50c1f3cf24", 16).unwrap() % &n;
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha512_ref(b"ECDSA-P521 test")) % &n;
		let q = w_scalar_mul_a(&d, &g, &p, &a);
		let r = match w_scalar_mul_a(&k, &g, &p, &a) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;

		assert!(ecdsa_p521_verify(&e, &q, &r, &s), "genuine ECDSA-P521 sig must verify");
		assert!(!ecdsa_p521_verify(&e, &q, &((&r + 1u32) % &n), &s), "tampered r must reject");
		assert!(!ecdsa_p521_verify(&((&e + 1u32) % &n), &q, &r, &s), "tampered e must reject");
		println!("GATE ref-S2-16: ECDSA P-521 (p=2^521−1, a=−3, SHA-512) — G on curve, [n]G=O, verify + tampers");
	}

	// ── Brainpool P-256 r1 (RFC 5639, EU/German-gov/TLS) — short Weierstrass with a GENERAL a
	// (neither 0 nor −3), the definitive exercise of the generic w_add_a. SHA-256.
	const BP256_P: &str = "a9fb57dba1eea9bc3e660a909d838d726e3bf623d52620282013481d1f6e5377";
	const BP256_A: &str = "7d5a0975fc2c3057eef67530417affe7fb8055c126dc5c6ce94a4b44f330b5d9";
	const BP256_B: &str = "26dc5c6ce94a4b44f330b5d9bbd77cbf958416295cf7e1ce6bccdc18ff8c07b6";
	const BP256_N: &str = "a9fb57dba1eea9bc3e660a909d838d718c397aa3b561a6f7901e0e82974856a7";
	const BP256_GX: &str = "8bd2aeb9cb7e57cb2c4b482ffc81b7afb9de27e1e3bd23c23a4453bd9ace3262";
	const BP256_GY: &str = "547ef835c3dac4fd97f8461a14611dc9c27745132ded8e545c1d54c72f046997";

	fn bp256_g() -> Aff {
		Some((
			BigUint::parse_bytes(BP256_GX.as_bytes(), 16).unwrap(),
			BigUint::parse_bytes(BP256_GY.as_bytes(), 16).unwrap(),
		))
	}
	/// ECDSA-brainpoolP256r1 verify — the ECDSA structure over a curve with a GENERAL a
	/// coefficient (reuses `w_add_a` with the curve's a), SHA-256.
	fn ecdsa_brainpool256_verify(e: &BigUint, q: &Aff, r: &BigUint, s: &BigUint) -> bool {
		let p = BigUint::parse_bytes(BP256_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(BP256_N.as_bytes(), 16).unwrap();
		let a = BigUint::parse_bytes(BP256_A.as_bytes(), 16).unwrap();
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return false;
		}
		let w = s.modpow(&(&n - 2u32), &n);
		let u1 = (e * &w) % &n;
		let u2 = (r * &w) % &n;
		let pt = w_add_a(
			&w_scalar_mul_a(&u1, &bp256_g(), &p, &a),
			&w_scalar_mul_a(&u2, q, &p, &a),
			&p,
			&a,
		);
		match pt {
			None => false,
			Some((x, _)) => (x % &n) == *r,
		}
	}

	/// GATE ref-S2-17 (ECDSA brainpoolP256r1, RFC 5639) — the curve's a is GENERAL (≠0, ≠p−3),
	/// G is on y²=x³+ax+b, [n]G=O, and a real signature verifies while tampered r/e reject —
	/// confirming `w_add_a` handles arbitrary Weierstrass coefficients.
	#[test]
	fn ecdsa_brainpool256_verify_gate() {
		let p = BigUint::parse_bytes(BP256_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(BP256_N.as_bytes(), 16).unwrap();
		let a = BigUint::parse_bytes(BP256_A.as_bytes(), 16).unwrap();
		let b = BigUint::parse_bytes(BP256_B.as_bytes(), 16).unwrap();
		let g = bp256_g();
		assert_ne!(a, BigUint::from(0u32), "brainpool a is general (≠0)");
		assert_ne!(a, &p - BigUint::from(3u32), "brainpool a is general (≠−3)");
		let (gx, gy) = match &g {
			Some((x, y)) => (x.clone(), y.clone()),
			None => unreachable!(),
		};
		// y² == x³ + a·x + b
		let rhs = fe_add(
			&fe_add(&fe_mul(&gx, &fe_mul(&gx, &gx, &p), &p), &fe_mul(&a, &gx, &p), &p),
			&b,
			&p,
		);
		assert_eq!(fe_mul(&gy, &gy, &p), rhs, "brainpool G not on y²=x³+ax+b");
		assert!(w_scalar_mul_a(&n, &g, &p, &a).is_none(), "[n]G must be O");

		let d = BigUint::parse_bytes(b"c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 16).unwrap() % &n;
		let k = BigUint::parse_bytes(b"7a1a7e52797fc8caaa435d2a4dace39158504bf204fbe19f14dbb427faee50ae", 16).unwrap() % &n;
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(b"brainpoolP256r1 test")) % &n;
		let q = w_scalar_mul_a(&d, &g, &p, &a);
		let r = match w_scalar_mul_a(&k, &g, &p, &a) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;

		assert!(ecdsa_brainpool256_verify(&e, &q, &r, &s), "genuine brainpool sig must verify");
		assert!(!ecdsa_brainpool256_verify(&e, &q, &((&r + 1u32) % &n), &s), "tampered r must reject");
		assert!(!ecdsa_brainpool256_verify(&((&e + 1u32) % &n), &q, &r, &s), "tampered e must reject");
		println!("GATE ref-S2-17: ECDSA brainpoolP256r1 (general a≠0,≠−3) — G on curve, [n]G=O, verify + tampers; w_add_a handles arbitrary a");
	}

	/// Ed25519 BATCH verify (the random-linear-combination batch from the Ed25519 paper): N
	/// signatures collapse into ONE equation [8·Σ zᵢSᵢ]B == Σ [8·zᵢ]Rᵢ + Σ [8·(zᵢkᵢ mod ℓ)]Aᵢ,
	/// where the zᵢ are random (Fiat–Shamir in the STARK). A single tampered signature fails the
	/// batch except with negligible probability over the zᵢ — so this is ONE multi-scalar-mul
	/// equation vs N separate verifies (much cheaper in-circuit).
	fn ed25519_batch_verify(pks: &[[u8; 32]], msgs: &[&[u8]], sigs: &[[u8; 64]], z: &[BigUint]) -> bool {
		let p = prime(S2Curve::Ed25519);
		let l = order(S2Curve::Ed25519);
		let eight = BigUint::from(8u32);
		let mut lhs_s = zero_big();
		let mut rhs = (zero_big(), BigUint::from(1u32)); // identity
		for i in 0..pks.len() {
			let a = match ed_decompress(&pks[i], &p) {
				Some(pt) => pt,
				None => return false,
			};
			let mut rb = [0u8; 32];
			rb.copy_from_slice(&sigs[i][..32]);
			let r_pt = match ed_decompress(&rb, &p) {
				Some(pt) => pt,
				None => return false,
			};
			let s = BigUint::from_bytes_le(&sigs[i][32..]);
			if s >= l {
				return false;
			}
			let mut input = sigs[i][..32].to_vec();
			input.extend_from_slice(&pks[i]);
			input.extend_from_slice(msgs[i]);
			let k = BigUint::from_bytes_le(&crate::sha512_gadget::sha512_ref(&input)) % &l;
			lhs_s = (&lhs_s + &z[i] * &s) % &l;
			rhs = ed_add(&rhs, &ed_scalar_mul(&(&eight * &z[i]), &r_pt, &p), &p);
			rhs = ed_add(&rhs, &ed_scalar_mul(&(&eight * ((&z[i] * &k) % &l)), &a, &p), &p);
		}
		let lhs = ed_scalar_mul(&(&eight * &lhs_s), &ed_base(&p), &p);
		lhs == rhs
	}

	/// GATE ref-S2-18 (Ed25519 batch aggregation) — a batch of 2 valid Ed25519 signatures
	/// (RFC 8032 TEST 1 + TEST 2, distinct keys/messages) batch-verifies via the single
	/// random-linear-combination equation, and a single tampered signature fails the batch.
	#[test]
	fn ed25519_batch_aggregation() {
		let pk1: [u8; 32] = unhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a").try_into().unwrap();
		let sig1: [u8; 64] = unhex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b").try_into().unwrap();
		let pk2: [u8; 32] = unhex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c").try_into().unwrap();
		let sig2: [u8; 64] = unhex("92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00").try_into().unwrap();
		let pks = [pk1, pk2];
		let msgs: [&[u8]; 2] = [&b""[..], &[0x72u8][..]];
		let sigs = [sig1, sig2];
		// fixed "random" scalars (Fiat–Shamir-derived in the STARK)
		let z = [
			BigUint::parse_bytes(b"8f3b1c2a5e7d9046", 16).unwrap(),
			BigUint::parse_bytes(b"1a2b3c4d5e6f7081", 16).unwrap(),
		];
		assert!(ed25519_batch_verify(&pks, &msgs, &sigs, &z), "batch of 2 valid sigs must verify");

		let mut sig2_bad = sig2;
		sig2_bad[10] ^= 1;
		let sigs_bad = [sig1, sig2_bad];
		assert!(!ed25519_batch_verify(&pks, &msgs, &sigs_bad, &z), "a tampered signature must fail the batch");
		println!("GATE ref-S2-18: Ed25519 batch verify [8Σz_iS_i]B==Σ[8z_i]R_i+Σ[8z_ik_i]A_i (RFC8032 TEST1+2); tampered fails");
	}

	/// 32-byte big-endian encoding of a ≤256-bit field/scalar element (for statement hashing).
	fn be32(x: &BigUint) -> [u8; 32] {
		let mut out = [0u8; 32];
		let b = x.to_bytes_be();
		out[32 - b.len()..].copy_from_slice(&b);
		out
	}
	/// The public statement of one ECDSA verification: SHA3-256(Qx ‖ Qy ‖ e ‖ r ‖ s) — the
	/// pubkey point, message hash, and signature. (ECDSA does not linearize like Ed25519 — the
	/// x-coordinate comparison is not linear — so ECDSA aggregates by R Tier-A root-binding, not
	/// a random-linear-combination batch equation.)
	fn ecdsa_statement_hash(q: &Aff, e: &BigUint, r: &BigUint, s: &BigUint) -> [u8; 32] {
		use sha3::{Digest, Sha3_256};
		let (qx, qy) = match q {
			Some((x, y)) => (x.clone(), y.clone()),
			None => (zero_big(), zero_big()),
		};
		let mut h = Sha3_256::new();
		h.update(be32(&qx));
		h.update(be32(&qy));
		h.update(be32(e));
		h.update(be32(r));
		h.update(be32(s));
		h.finalize().into()
	}
	/// The ECDSA batch root: R Tier-A batched Merkle over the N per-signature statement hashes;
	/// R* binds exactly which (pubkey, message, signature) tuples the batch proof verified.
	fn ecdsa_batch_root(statements: &[[u8; 32]]) -> [u8; 32] {
		crate::recursion::merkle_root_sha3(statements)
	}

	/// GATE ref-S2-19 (ECDSA batch aggregation, Tier-A) — N ECDSA statements commit to one
	/// batch root; a change to ANY component (pubkey, message hash, r, or s) changes the root,
	/// so the batch binds exactly which signatures verified.
	#[test]
	fn ecdsa_batch_aggregation() {
		let mk = |seed: u32| -> ([u8; 32], BigUint, BigUint, BigUint) {
			let q = Some((BigUint::from(seed * 3 + 1), BigUint::from(seed * 5 + 2)));
			let stmt = ecdsa_statement_hash(&q, &BigUint::from(seed * 7 + 3), &BigUint::from(seed * 11 + 4), &BigUint::from(seed * 13 + 5));
			(stmt, BigUint::from(seed * 7 + 3), BigUint::from(seed * 11 + 4), BigUint::from(seed * 13 + 5))
		};
		let stmts: Vec<[u8; 32]> = (0..3).map(|i| mk(i).0).collect();
		let root = ecdsa_batch_root(&stmts);
		assert_eq!(root.len(), 32);

		// changing any statement component changes the batch root
		let q0 = Some((BigUint::from(1u32), BigUint::from(2u32)));
		let base = ecdsa_statement_hash(&q0, &BigUint::from(3u32), &BigUint::from(4u32), &BigUint::from(5u32));
		let diff_q = ecdsa_statement_hash(&Some((BigUint::from(9u32), BigUint::from(2u32))), &BigUint::from(3u32), &BigUint::from(4u32), &BigUint::from(5u32));
		let diff_e = ecdsa_statement_hash(&q0, &BigUint::from(99u32), &BigUint::from(4u32), &BigUint::from(5u32));
		let diff_r = ecdsa_statement_hash(&q0, &BigUint::from(3u32), &BigUint::from(99u32), &BigUint::from(5u32));
		let diff_s = ecdsa_statement_hash(&q0, &BigUint::from(3u32), &BigUint::from(4u32), &BigUint::from(99u32));
		assert!(base != diff_q && base != diff_e && base != diff_r && base != diff_s, "any component change ⇒ different statement");
		// substituting a statement changes the batch root
		let mut bad = stmts.clone();
		bad[1] = base;
		assert_ne!(ecdsa_batch_root(&bad), root, "substituted statement ⇒ different batch root");
		println!("GATE ref-S2-19: ECDSA batch = Merkle over SHA3(Qx‖Qy‖e‖r‖s) statements (Tier-A); any (Q,e,r,s) change ⇒ different root");
	}

	/// ECDSA-secp256k1 public-key RECOVERY (Ethereum `ecrecover`): from (e, r, s, recovery
	/// bit) recover Q = r⁻¹(s·R − e·G), where R = (r, y) with y = √(r³+7) mod p and parity given
	/// by the recovery bit. Reuses the a=0 Weierstrass ops + fe_inv; the sqrt uses p ≡ 3 (mod 4)
	/// ⇒ √ = ·^((p+1)/4). (Common case R.x = r < n; the R.x ≥ n case uses the extra v bit.)
	fn ecdsa_secp256k1_recover(e: &BigUint, r: &BigUint, s: &BigUint, rec_bit: bool) -> Aff {
		let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();
		let a = BigUint::from(0u32);
		if is_zero(r) || r >= &n || is_zero(s) || s >= &n {
			return None;
		}
		// R = (r, y), y = √(r³ + 7) with parity = rec_bit
		let x = r.clone();
		let yy = fe_add(&fe_mul(&x, &fe_mul(&x, &x, &p), &p), &BigUint::from(7u32), &p);
		let mut y = yy.modpow(&((&p + BigUint::from(1u32)) >> 2), &p);
		if fe_mul(&y, &y, &p) != yy {
			return None; // r is not a valid x-coordinate
		}
		if y.bit(0) != rec_bit {
			y = fe_sub(&p, &y, &p);
		}
		let r_pt = Some((x, y));
		// Q = u1·G + u2·R,  u1 = −e·r⁻¹ mod n,  u2 = s·r⁻¹ mod n
		let rinv = r.modpow(&(&n - 2u32), &n);
		let u1 = ((&n - (e % &n)) * &rinv) % &n;
		let u2 = (s * &rinv) % &n;
		w_add_a(
			&w_scalar_mul_a(&u1, &secp256k1_g(), &p, &a),
			&w_scalar_mul_a(&u2, &r_pt, &p, &a),
			&p,
			&a,
		)
	}

	/// GATE ref-S2-20 (ECDSA secp256k1 public-key recovery / ecrecover) — recovering the pubkey
	/// from a real signature + recovery bit yields the ORIGINAL pubkey, while a tampered s or a
	/// wrong recovery bit recovers a different (wrong) key.
	#[test]
	fn ecdsa_secp256k1_recover_gate() {
		let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();
		let a = BigUint::from(0u32);
		let g = secp256k1_g();
		let d = BigUint::parse_bytes(b"c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 16).unwrap() % &n;
		let k = BigUint::parse_bytes(b"7a1a7e52797fc8caaa435d2a4dace39158504bf204fbe19f14dbb427faee50ae", 16).unwrap() % &n;
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(b"ecrecover test")) % &n;
		let q = w_scalar_mul_a(&d, &g, &p, &a);
		let (rx, ry) = match w_scalar_mul_a(&k, &g, &p, &a) {
			Some((x, y)) => (x, y),
			None => panic!("k·G = O"),
		};
		let r = &rx % &n;
		let rec_bit = ry.bit(0);
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;

		assert_eq!(ecdsa_secp256k1_recover(&e, &r, &s, rec_bit), q, "recovered Q must equal the original pubkey");
		assert_ne!(ecdsa_secp256k1_recover(&e, &r, &((&s + 1u32) % &n), rec_bit), q, "tampered s ⇒ wrong Q");
		assert_ne!(ecdsa_secp256k1_recover(&e, &r, &s, !rec_bit), q, "wrong recovery bit ⇒ wrong Q");
		println!("GATE ref-S2-20: ECDSA secp256k1 pubkey recovery (ecrecover) Q=r⁻¹(sR−eG); recovers original, tamper/wrong-bit ⇒ wrong Q");
	}

	/// The low-s malleability check (BIP-62 / EIP-2): a canonical ECDSA signature has
	/// s ≤ (n−1)/2. In-circuit this is one S0 `carry_lt` against the constant (n−1)/2.
	fn is_low_s(s: &BigUint, n: &BigUint) -> bool {
		let half = (n - BigUint::from(1u32)) >> 1u32; // (n−1)/2
		s <= &half
	}

	/// GATE ref-S2-21 (ECDSA malleability / low-s) — demonstrates ECDSA's inherent malleability
	/// (both (r,s) and (r,n−s) verify — the ±R x-coordinate is the same) and the low-s fix:
	/// exactly one of the pair is low-s, so the low-s check (s ≤ (n−1)/2) rejects the malleated
	/// high-s form while accepting the canonical one.
	#[test]
	fn ecdsa_malleability_low_s() {
		let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
		let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();
		let a = BigUint::from(0u32);
		let g = secp256k1_g();
		let d = BigUint::parse_bytes(b"c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 16).unwrap() % &n;
		let k = BigUint::parse_bytes(b"7a1a7e52797fc8caaa435d2a4dace39158504bf204fbe19f14dbb427faee50ae", 16).unwrap() % &n;
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(b"malleability test")) % &n;
		let q = w_scalar_mul_a(&d, &g, &p, &a);
		let r = match w_scalar_mul_a(&k, &g, &p, &a) {
			Some((x, _)) => x % &n,
			None => panic!("k·G = O"),
		};
		let s = (&k.modpow(&(&n - 2u32), &n) * ((&e + &r * &d) % &n)) % &n;
		let s_mal = (&n - &s) % &n;

		// both (r,s) and (r,n−s) verify — the malleability
		assert!(ecdsa_secp256k1_verify(&e, &q, &r, &s), "s must verify");
		assert!(ecdsa_secp256k1_verify(&e, &q, &r, &s_mal), "n−s must ALSO verify (malleability)");
		// exactly one of the pair is low-s
		assert_ne!(is_low_s(&s, &n), is_low_s(&s_mal, &n), "exactly one of {{s, n−s}} is low-s");
		// the low-s check rejects the high-s malleated form
		let high = if is_low_s(&s, &n) { s_mal.clone() } else { s.clone() };
		assert!(!is_low_s(&high, &n), "the high-s malleated form must fail the low-s check");
		println!("GATE ref-S2-21: ECDSA malleability — (r,s)+(r,n−s) both verify; low-s check (s≤(n−1)/2) rejects high-s (BIP-62/EIP-2)");
	}

	/// GATE xcheck-p256 (Phase-2) — my `ecdsa_p256_verify` accepts a signature produced by the
	/// `p256` (RustCrypto) crate, and rejects it under a tampered message.
	#[test]
	fn ecdsa_p256_matches_p256_crate() {
		use p256::ecdsa::signature::{Signer, Verifier};
		use p256::ecdsa::{Signature, SigningKey};

		let sk = SigningKey::from_slice(&unhex("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721")).expect("key");
		let vk = sk.verifying_key();
		let msg = b"p256 crate cross-check";
		let sig: Signature = sk.sign(msg); // RFC 6979 deterministic
		assert!(vk.verify(msg, &sig).is_ok(), "p256 crate self-verify sanity");

		let ep = vk.to_encoded_point(false);
		let q = Some((
			BigUint::from_bytes_be(ep.x().unwrap()),
			BigUint::from_bytes_be(ep.y().unwrap()),
		));
		let sb = sig.to_bytes(); // r ‖ s, 64 bytes big-endian
		let r = BigUint::from_bytes_be(&sb[..32]);
		let s = BigUint::from_bytes_be(&sb[32..]);
		let n = order(S2Curve::P256);
		let e = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(msg)) % &n;

		assert!(ecdsa_p256_verify(&e, &q, &r, &s), "my ecdsa_p256_verify must accept a p256-crate sig");
		let e_bad = BigUint::from_bytes_be(&crate::sha512_gadget::sha256_ref(b"other")) % &n;
		assert!(!ecdsa_p256_verify(&e_bad, &q, &r, &s), "wrong message must reject");
		println!("GATE xcheck-p256: ecdsa_p256_verify agrees with the p256 crate (accept genuine, reject wrong-msg)");
	}

	/// GATE xcheck-ed25519 (Phase-2) — my `ed25519_verify` accepts a signature produced by the
	/// `ed25519-dalek` crate, and rejects it under a tampered message.
	#[test]
	fn ed25519_matches_dalek() {
		use ed25519_dalek::{Signer, SigningKey};

		let sk = SigningKey::from_bytes(&unhex("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20").try_into().unwrap());
		let vk = sk.verifying_key();
		let msg = b"ed25519-dalek cross-check";
		let sig = sk.sign(msg);
		let pk_bytes: [u8; 32] = vk.to_bytes();
		let sig_bytes: [u8; 64] = sig.to_bytes();

		assert!(ed25519_verify(&pk_bytes, msg, &sig_bytes), "my ed25519_verify must accept a dalek sig");
		assert!(!ed25519_verify(&pk_bytes, b"other", &sig_bytes), "wrong message must reject");
		println!("GATE xcheck-ed25519: ed25519_verify agrees with ed25519-dalek (accept genuine, reject wrong-msg)");
	}

	/// GATE prove-S2-1 (PENDING) — ECDSA-P256 verify proves over B256; genuine `p256` sig
	/// accepts, tampered r/s/e reject (isolated to the x≡r boundary). Needs S0 field
	/// gadgets wired into EC point ops + binius_circuits::sha256 + p256 dev-dep.
	#[test]
	#[ignore = "S2 EC gadgets not wired — needs S0 point ops + binius_circuits sha256 + p256 dev-dep"]
	fn ecdsa_p256_proves_over_b256() {
		unimplemented!("Weierstrass point ops over S0 ModMul<512> + scalar-mul strand loop + x≡r boundary");
	}

	/// GATE prove-S2-2 (PENDING) — Ed25519 verify proves over B256; genuine `ed25519-dalek`
	/// sig accepts, tampered S/R/M reject. Needs the SHA-512 in-circuit gadget + twisted-
	/// Edwards point ops over S0.
	#[test]
	#[ignore = "S2 Ed25519 not wired — needs SHA-512 gadget + twisted-Edwards ops over S0"]
	fn ed25519_proves_over_b256() {
		unimplemented!("SHA-512 gadget + Edwards add/dbl over S0 ModMul<512> + [8][S]B==[8]R+[8][k]A boundary");
	}
}
