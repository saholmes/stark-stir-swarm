// S3 (classical-signature port) — RSA-2048 RSASSA-PKCS1-v1.5 verify (RFC 8017, DNSSEC
// alg 8) over the 256-bit tower field `B256TowerFamily` at NIST L1/L3/L5. The HEAVIEST
// big-int milestone: its crux is modular exponentiation s^e mod n over 2048-bit operands.
//
// ── WHY S3 NEEDS A NEW GADGET (not just S0 at bigger W) ────────────────────────────
// S0's `a·b mod m` proves 256-bit primes by a bit-serial shift-add multiply (W=512). At
// 2048 bit that recipe is ~W=8192 with ~2048²≈4·10⁶ bit-products — INFEASIBLE as pure
// shift-add (this was S0's explicit RSA deferral). S3 instead uses a LIMB-based big-int
// multiply: 2048-bit = 64 × 32-bit limbs; a·b is a schoolbook (or Karatsuba) over
// 32×32→64 limb products (`MulUU32`), carry-accumulated into a 128-limb (4096-bit)
// result; reduction mod n is S0's hint-and-verify lifted to limbs (P == q·n + r ∧ r<n,
// each a limb multiply + limb-wise carry compare). This is the genuinely new construction.
//
// ── VERIFY RELATION (RFC 8017 §8.2.2 / EMSA-PKCS1-v1.5) ─────────────────────────────
//   RSASSA-PKCS1-v1.5-VERIFY((n,e), M, sig):
//     1. s = OS2IP(sig)                    [reject if s ≥ n]
//     2. m = s^e mod n                     [MODEXP — the crux; e=65537 ⇒ 16 sqr + 1 mul]
//     3. EM = I2OSP(m, 256)                [2048/8 = 256 bytes]
//     4. EM' = 0x00‖0x01‖0xFF…FF‖0x00‖DigestInfo(SHA-256)‖H(M)   [EMSA-PKCS1-v1.5 encode]
//     5. ACCEPT ⟺ EM == EM'
//   (e = 65537 = 2^16+1 is public and fixed, so the exponent bits are known: the modexp
//   is exactly 16 squarings then one multiply by s — NO conditional/secret-dependent path.)
//
// ── REUSE ─────────────────────────────────────────────────────────────────────────
//   * S0's reduction recipe (a·b ≡ q·n+r ∧ r<n) — lifted from bit-serial to limb form.
//   * S0's `x < m` carry decision — for `r < n` and `s < n`, now a limb-wise compare.
//   * `binius_circuits::sha256` — H(M) (same gadget S2's ECDSA uses).
//   * The MulUU32 limb gadget — a 32×32→64 multiply; candidates: (a) Lasso lookup
//     (`binius_circuits::lasso`), (b) 16-bit sub-limb schoolbook (4× 16×16→32, each a
//     small lookup / bounded shift-add — 16 wide is feasible), (c) bit-decompose + a
//     32-wide shift-add (feasible per-limb: 32, not 2048). Choose (a) if the Lasso
//     table amortizes across the ~4096 limb products per modmul.
//
// ── MODEXP = THE STRAND LEVER ──────────────────────────────────────────────────────
// s^e mod n (e=65537) = a chain of 17 modmuls. Each modmul = two limb multiplies (a·b and
// q·n) + a limb-wise carry compare. Strand granularity choices, coarse→fine:
//   • per-modmul (17 strands, running accumulator seam) — coarsest;
//   • per-limb-row of a schoolbook multiply (64 rows × 17 modmuls) — finer, browser-sized;
//   • Karatsuba sub-multiplies as independent strands.
// Adjacent strands re-bind at the accumulator/partial-product via a channel seam (S0
// strand-splice / b256_recursion join). RSS ∝ strand width, not 2048² — tunable-RSS holds.
//
// ── SOUNDNESS BOUNDARY ────────────────────────────────────────────────────────────
//   IN-CIRCUIT: each MulUU32 is sound (lookup / bounded), each limb schoolbook sums the
//   right shifted products with carries (a fixed linear+carry constraint), each modmul's
//   reduction is S0's Euclidean identity at limb granularity (P == q·n+r as a limb
//   equality with carry ∧ r<n), the modexp is the fixed 17-step chain, and the accept is
//   a byte-equality EM == EM' to the EMSA-encoded public digest. A tampered sig ⇒ s^e mod
//   n ≠ EM' ⇒ the byte compare fails ⇒ no accepting witness. Public boundary: (n, e, M,
//   sig). Witness: m, every q/r reduction pair, every limb partial product.
//   WITNESS-SIDE (gated vs the `rsa` crate + RFC 8017 test vectors): OS2IP/I2OSP byte
//   order and the DigestInfo prefix bytes (folded in-circuit as the EMSA layout is
//   asserted against public constants — the 0x00 01 FF..FF 00 ‖ prefix pattern IS a set
//   of constant-column equalities, so the padding-forgery defence is in-circuit here).
//   OUTER COMMITMENT still SHA-256; 2^256 field carries FS security.
// ============================================================================
//
// DRAFT STATUS (S3, in progress): the native reference (modexp via num-bigint, EMSA-
// PKCS1-v1.5 encode, full PKCS1 verify) is implemented in the test module against a REAL
// generated RSA-2048 keypair + signature (validated with Python first: verify accepts,
// tampered sig/msg/padding reject). The in-circuit limb-multiply / modexp / reduction
// gadgets are specified above and wired last (heaviest AIR), after S1/S2 prove paths land.
// Heavy prove gates are `#[ignore]`. The `rsa`-crate cross-check gate is `#[ignore]`
// pending adding `rsa` to dev-deps.

/// RSA-2048 modulus bit length.
pub const RSA_BITS: usize = 2048;
/// Encoded-message / modulus octet length k = 2048/8.
pub const RSA_K: usize = RSA_BITS / 8;
/// Public exponent (Fermat prime F4). Fixed and public ⇒ the modexp is 16 squarings + 1
/// multiply with a known bit pattern (no secret-dependent branching).
pub const RSA_E: u64 = 65537;
/// Limb width (bits) for the in-circuit big-int representation: 32 ⇒ 64 limbs / 2048-bit,
/// and MulUU32 products fit 64 bits.
pub const RSA_LIMB_BITS: usize = 32;
/// Number of 32-bit limbs in a 2048-bit big-int.
pub const RSA_LIMBS: usize = RSA_BITS / RSA_LIMB_BITS;

/// The ASN.1 DigestInfo prefix for SHA-256 (RFC 8017 §9.2, notes): the fixed 19-byte
/// header prepended to the 32-byte digest inside EMSA-PKCS1-v1.5.
pub const SHA256_DIGESTINFO_PREFIX: [u8; 19] = [
	0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05,
	0x00, 0x04, 0x20,
];

/// EMSA-PKCS1-v1.5 encode of a SHA-256 digest into a k-octet block (RFC 8017 §9.2):
/// 0x00 ‖ 0x01 ‖ 0xFF…FF ‖ 0x00 ‖ DigestInfo ‖ H. Returns the k-byte encoded message EM'.
pub fn emsa_pkcs1_sha256(digest: &[u8; 32], k: usize) -> Vec<u8> {
	let t_len = SHA256_DIGESTINFO_PREFIX.len() + 32; // DigestInfo ‖ H
	assert!(k >= t_len + 11, "intended encoded length too short");
	let ps_len = k - t_len - 3; // 0x00,0x01,...,0x00
	let mut em = Vec::with_capacity(k);
	em.push(0x00);
	em.push(0x01);
	em.extend(std::iter::repeat(0xFF).take(ps_len));
	em.push(0x00);
	em.extend_from_slice(&SHA256_DIGESTINFO_PREFIX);
	em.extend_from_slice(digest);
	em
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT DESIGN (wired last — see DRAFT STATUS)
// ──────────────────────────────────────────────────────────────────────────────────
//
// BigInt<64 limbs>: witness columns = 64 × Col<B1,32> (or packed). Public n, sig as
// boundary columns bit-decomposed into limbs.
//
// mul_uu32(a,b) → 64-bit product: 32×32→64. PRIMARY gadget = S0 shift-add at limb scale —
//   product = Σ_{k=0}^{31} a_k·(b<<k), 32 conditional 64-bit adds via nonnative's
//   Adder<64>/ripple_add, a_k the bit-columns of a, (b<<k) a free bit reindex; b<<31 < 2^63
//   so the 64-bit accumulator never wraps ⇒ the product column is the TRUE integer product
//   (sound, no reduction). This is a strict subset of S0's ModMul multiply phase, reused
//   verbatim. ALT for throughput: a Lasso lookup on (a,b)→product (`binius_circuits::lasso`)
//   if the table amortizes across the ~4096 limb products per modmul; or a 16-bit split
//   (4× 16×16→32). (Native model `mul_uu32_shiftadd` in tests is gated == the u64 product.)
//
// bigint_mul(a[64], b[64]) → p[128]: schoolbook Σ_{i,j} mul_uu32(a_i,b_j) placed at limb
//   (i+j) low / (i+j+1) high, then ONE carry pass down the 128 columns (each column sum <
//   2^39 fits the accumulator; the carry chain is a fixed constraint). Karatsuba variant:
//   3 half-width multiplies + combines (≈0.6× the limb products). (Native model
//   `bigint_mul_limbs` in tests is gated == num-bigint on the real RSA operands, incl. a².)
//
// modmul(a,b,n) → r: prover hints q[64], r[64]; enforce bigint_mul(a,b) == bigint_mul(q,n)
//   + r  (128-limb equality with carry) AND r < n (limb-wise: S0 carry-out of r + (2^2048
//   − n), computed limb-by-limb). This r<n is the SOLE load-bearing reduction gate: the
//   identity alone is satisfied by the whole family (q−k, r+k·n), so r<n pins the unique
//   reduced r. Soundness = Euclidean uniqueness, exactly S0's r_lt_m lifted to limbs.
//   (Native model in tests: `limb_lt` + the identity check are gated on the real RSA
//   operands, and the unreduced (q−1, r+n) is shown to pass the identity yet be rejected
//   by `limb_lt`.)
//
// modexp_65537(s,n) → m: t = s; for _ in 0..16 { t = modmul(t,t,n) }; m = modmul(t,s,n).
//   16 squarings + 1 multiply (e=65537 bit pattern known, no secret branch). STRAND SEAM:
//   each modmul is its own table; its output t (64 limbs) is PUSHED to a per-chain channel
//   and PULLED as the next table's input a (and b for a squaring) — the sha3_join push/pull
//   binding (derived-oracle, no free t column), so a strand = ONE modmul and peak RSS ∝ one
//   modmul (~64² limb products + reduction), not the whole 17-step chain. A browser proves
//   one modmul per process; a server the whole chain. (Native model `modexp_65537_limb` in
//   tests chains 17 limb modmuls and is gated == modpow, incl. the full verify.)
//
// verify boundary: EM = I2OSP(m, 256) (limbs → bytes); EM' = emsa_pkcs1_sha256(sha256(M));
//   assert EM == EM' byte-wise (256 B1-equalities). The 0x00 01 FF..FF 00 ‖ prefix bytes of
//   EM' are CONSTANT columns, so a forged padding cannot match — the PKCS#1 padding-forgery
//   defence is these constant-equality asserts. sha256(M) via binius_circuits::sha256.
//
// TAMPERED-SIG-REJECTS (S3 headline gate): genuine (n,e,M,sig) [rsa crate sign] verifies;
// each of {flip a sig byte, flip an M byte, corrupt an EM padding byte, wrong n} ⇒ s^e mod
// n ≠ EM' ⇒ the EM byte-equality fails ⇒ no accepting witness (isolated to that byte).

#[cfg(test)]
mod tests {
	use num_bigint::BigUint;
	use sha2::{Digest, Sha256};

	use super::*;

	// A REAL RSA-2048 vector (keypair + PKCS1-v1.5 signature) generated & cross-validated
	// with Python (seeded, reproducible). n = p·q (2048-bit), e = 65537. `sig^e mod n`
	// equals the EMSA-PKCS1-v1.5 encoding of SHA-256(MSG).
	const N_HEX: &str = "c5ee859fbeeb4824184aeed93bbd11a95e01cd4bf288a744c68fbb081912972ca3e30b0520dc6304a49888324223bbd79666f02f7a73a0456bc860d78363e6d3746ac2a348869c17d0187361f7810f7801ea269c2d2708de5ccb92ca2d1188316a208f1831ba362bb46737f03101bd19d015c30e87c078d2e5eea2350aec081606e45a4d312fc93a4fd2d9531f1eb35562e387a770bde11e2ee0a7b369cfef12d274a20a91abc309d2ac055498576a4ddf48e02408f5898c55e5b26aaddd5adc4aa39f04e1e80c30d9273365c762aa933c12f55eaf3c8ff283a09ff720a9aea894ab96cd24a04ba1020132d5e6eb302eeec36523e45aab69b03de5c96edb6cd5";
	const SIG_HEX: &str = "1c37233aab3de590f3f8f25b1909b6b9de7d8dc618b02476c528a6e13bcadef302b410d7a3bc779c39119e6bf251ecde04df8da1ee54c19a60c37f7902191c5e5b2300efddf9e919f7c4a63f2e0179b7d8160a580b17d6f7c6651760b9f02e8b991060d369e0e8a56f2a08fdc552038a2a0253c32cc34cd1122603c2b3a01d6dda52664a01f2a0d74ddaef95020071c405db2338870d94b10f1d7c542e8eb021efb8895ea9c26bb0b5fbd074e44b368511460de8551935551858d90be543b8b93dac121a39fbfac32c1b84368ef8bfd0fd7ebb30c32c6dec61cf5abe9e9b8059b0e5ccb79e8a290ca01fc9adae75b585ce9fb800a2b3b451ec51e4a8c24a3a08";
	const MSG: &[u8] = b"STARK-Binius S3 RSA-2048 verify reference vector";

	fn n() -> BigUint {
		BigUint::parse_bytes(N_HEX.as_bytes(), 16).unwrap()
	}
	fn sig() -> BigUint {
		BigUint::parse_bytes(SIG_HEX.as_bytes(), 16).unwrap()
	}
	fn sha256(m: &[u8]) -> [u8; 32] {
		let mut h = Sha256::new();
		h.update(m);
		h.finalize().into()
	}

	/// Native RSASSA-PKCS1-v1.5-VERIFY (SHA-256): m = sig^e mod n; EM = I2OSP(m,256);
	/// accept iff EM == EMSA-PKCS1-v1.5(SHA-256(M)). This is the relation the S3 circuit
	/// enforces.
	fn rsa_pkcs1_sha256_verify(n: &BigUint, e: u64, msg: &[u8], sig: &BigUint) -> bool {
		if sig >= n {
			return false;
		}
		let m = sig.modpow(&BigUint::from(e), n);
		let mut em = m.to_bytes_be();
		if em.len() > RSA_K {
			return false;
		}
		// left-pad to k bytes (I2OSP)
		let mut padded = vec![0u8; RSA_K - em.len()];
		padded.append(&mut em);
		let expected = emsa_pkcs1_sha256(&sha256(msg), RSA_K);
		padded == expected
	}

	/// GATE ref-S3-1 — EMSA-PKCS1-v1.5 structure: length k, the 0x00,0x01 header, a run of
	/// 0xFF, the 0x00 separator, and the SHA-256 DigestInfo prefix in place.
	#[test]
	fn emsa_structure() {
		let em = emsa_pkcs1_sha256(&sha256(b"abc"), RSA_K);
		assert_eq!(em.len(), RSA_K);
		assert_eq!(em[0], 0x00);
		assert_eq!(em[1], 0x01);
		let sep = 2 + (RSA_K - 3 - (19 + 32)); // index of the 0x00 separator
		assert!(em[2..sep].iter().all(|&b| b == 0xFF), "PS must be all 0xFF");
		assert_eq!(em[sep], 0x00, "separator must be 0x00");
		assert_eq!(&em[sep + 1..sep + 20], &SHA256_DIGESTINFO_PREFIX, "DigestInfo prefix");
		println!("GATE ref-S3-1: EMSA-PKCS1-v1.5 layout correct ({} B, PS 0xFF, DigestInfo)", em.len());
	}

	/// GATE ref-S3-2 — the real RSA-2048 vector VERIFIES, and each tamper (sig byte, msg,
	/// padding/wrong-exponent) is REJECTED. Cross-validated against Python.
	#[test]
	fn rsa2048_verify_and_tamper_rejected() {
		let n = n();
		let sig = sig();
		assert!(rsa_pkcs1_sha256_verify(&n, RSA_E, MSG, &sig), "genuine RSA-2048 sig must verify");

		// tamper the signature
		assert!(
			!rsa_pkcs1_sha256_verify(&n, RSA_E, MSG, &(&sig + 1u32)),
			"tampered signature must reject"
		);
		// tamper the message
		assert!(
			!rsa_pkcs1_sha256_verify(&n, RSA_E, b"different message", &sig),
			"tampered message must reject"
		);
		// wrong public exponent (e=3) breaks the modexp
		assert!(!rsa_pkcs1_sha256_verify(&n, 3, MSG, &sig), "wrong exponent must reject");
		// s ≥ n rejected
		assert!(!rsa_pkcs1_sha256_verify(&n, RSA_E, MSG, &n), "s = n must reject (s ≥ n)");
		println!("GATE ref-S3-2: RSA-2048 PKCS1-v1.5 verify accepts genuine sig; rejects sig/msg/e/s≥n");
	}

	/// GATE ref-S3-3 — the modexp shape: e = 65537 = 2^16+1, so s^e = ((…(s²)²…)²)·s with
	/// 16 squarings; check that the fixed square-and-multiply chain equals modpow.
	#[test]
	fn modexp_chain_matches() {
		let n = n();
		let sig = sig();
		let mut t = sig.clone();
		for _ in 0..16 {
			t = (&t * &t) % &n; // squaring
		}
		let m_chain = (&t * &sig) % &n; // × s
		let m_ref = sig.modpow(&BigUint::from(RSA_E), &n);
		assert_eq!(m_chain, m_ref, "16-squarings+1-mul chain != modpow (e=65537)");
		println!("GATE ref-S3-3: e=65537 modexp == 16 squarings + 1 multiply (the strand chain)");
	}

	/// Native model of the in-circuit MulUU32 gadget (32×32→64) the S0 way: shift-add over
	/// the 32-bit multiplier — product = Σ_{k=0}^{31} a_k · (b << k), a 64-bit accumulator.
	/// 32 conditional 64-bit adds (feasible per-limb; b<<31 < 2^63 so no overflow). This is
	/// S0's shift-add multiply at limb scale (reuses nonnative's Adder<64>/ripple_add/shl).
	fn mul_uu32_shiftadd(a: u32, b: u32) -> u64 {
		let bb = b as u64;
		let mut acc = 0u64;
		for k in 0..32 {
			if (a >> k) & 1 == 1 {
				acc = acc.wrapping_add(bb << k);
			}
		}
		acc
	}

	/// 2048-bit big-int as 64 little-endian 32-bit limbs.
	fn to_limbs64(x: &BigUint) -> [u32; 64] {
		let digits = x.to_u32_digits();
		let mut limbs = [0u32; 64];
		for (i, &d) in digits.iter().enumerate().take(64) {
			limbs[i] = d;
		}
		limbs
	}
	fn from_limbs(limbs: &[u32]) -> BigUint {
		let mut x = BigUint::from(0u32);
		for (i, &l) in limbs.iter().enumerate() {
			x += BigUint::from(l) << (32 * i);
		}
		x
	}

	/// The in-circuit big-int schoolbook: a·b over 64-limb operands → a 128-limb (4096-bit)
	/// product. Σ_{i,j} MulUU32(a_i,b_j) placed at limb (i+j) low / (i+j+1) high, then a
	/// single carry pass. In-circuit each column sum + the carry chain is a fixed constraint.
	fn bigint_mul_limbs(a: &[u32; 64], b: &[u32; 64]) -> [u32; 128] {
		let mut acc = [0u64; 128]; // wide column accumulators (each < 2^39, fits u64)
		for i in 0..64 {
			for j in 0..64 {
				let p = mul_uu32_shiftadd(a[i], b[j]);
				acc[i + j] += p & 0xFFFF_FFFF;
				acc[i + j + 1] += p >> 32;
			}
		}
		let mut out = [0u32; 128];
		let mut carry = 0u64;
		for k in 0..128 {
			let v = acc[k] + carry;
			out[k] = (v & 0xFFFF_FFFF) as u32;
			carry = v >> 32;
		}
		out
	}

	/// GATE ref-S3-4 (S3 limb multiply over S0) — (a) MulUU32 shift-add == the true u64
	/// product across boundary + random 32-bit operands; (b) the 64-limb schoolbook equals
	/// num-bigint on the REAL RSA operands (a·b and the squaring a², the two modexp inner
	/// ops).
	#[test]
	fn limb_mul_uu32_and_schoolbook() {
		// (a) MulUU32 == u64 mul
		assert_eq!(mul_uu32_shiftadd(0, 12345), 0);
		assert_eq!(
			mul_uu32_shiftadd(u32::MAX, u32::MAX),
			u32::MAX as u64 * u32::MAX as u64
		);
		for (a, b) in [
			(1u32, 1u32),
			(0xFFFF, 0xFFFF),
			(0x1234_5678, 0x9abc_def0),
			(3_037_000_499, 3_037_000_500),
		] {
			assert_eq!(mul_uu32_shiftadd(a, b), a as u64 * b as u64, "MulUU32 {a}·{b}");
		}

		// (b) 64-limb schoolbook == num-bigint on the real RSA modulus/signature
		let a = sig();
		let b = n();
		let prod = bigint_mul_limbs(&to_limbs64(&a), &to_limbs64(&b));
		assert_eq!(from_limbs(&prod), &a * &b, "limb schoolbook a·b != num-bigint");
		let sq = bigint_mul_limbs(&to_limbs64(&a), &to_limbs64(&a));
		assert_eq!(from_limbs(&sq), &a * &a, "limb schoolbook a² != num-bigint");
		println!("GATE ref-S3-4: MulUU32 shift-add == u64 mul; 64-limb schoolbook == num-bigint (a·b, a²)");
	}

	fn to_limbs128(x: &BigUint) -> [u32; 128] {
		let digits = x.to_u32_digits();
		let mut limbs = [0u32; 128];
		for (i, &d) in digits.iter().enumerate().take(128) {
			limbs[i] = d;
		}
		limbs
	}

	/// 128-limb accumulator + a 64-limb addend (r), with carry — the `q·n + r` step.
	fn bigint_add_r(a: &[u32; 128], r: &[u32; 64]) -> [u32; 128] {
		let mut out = [0u32; 128];
		let mut carry = 0u64;
		for k in 0..128 {
			let rk = if k < 64 { r[k] as u64 } else { 0 };
			let v = a[k] as u64 + rk + carry;
			out[k] = (v & 0xFFFF_FFFF) as u32;
			carry = v >> 32;
		}
		out
	}

	/// `r < n` at 2048-bit (64-limb) — S0's `r < m` carry trick lifted to limbs: r < n iff
	/// the carry-out of the 64-limb ripple-add `r + (2^2048 − n)` is 0. `2^2048 − n` is a
	/// public constant (the modulus is public), precomputed here from n.
	fn limb_lt(r: &[u32; 64], n: &[u32; 64]) -> bool {
		let n_big = from_limbs(&n[..]);
		let comp = (BigUint::from(1u32) << 2048u32) - &n_big; // 2^2048 − n, fits 64 limbs
		let comp_l = to_limbs64(&comp);
		let mut carry = 0u64;
		for k in 0..64 {
			let v = r[k] as u64 + comp_l[k] as u64 + carry;
			carry = v >> 32;
		}
		carry == 0 // no carry out of the 2048-bit sum ⟺ r < n
	}

	/// GATE ref-S3-5 (S3 modmul limb reduction over S0) — the Euclidean reduction at limb
	/// granularity: (a) the honest (q,r) satisfies `bigint_mul(a,b) == bigint_mul(q,n) + r`
	/// (128-limb identity) AND `r < n`; (b) `limb_lt` is correct on boundaries; (c) the
	/// LOAD-BEARING soundness case — the unreduced (q−1, r+n) STILL satisfies the identity
	/// (so the identity alone is insufficient), and ONLY `limb_lt` rejects it (r+n ≥ n),
	/// exactly S0's `r_lt_m` gate.
	#[test]
	fn modmul_limb_reduction_over_s0() {
		let n = n();
		let a = sig(); // < n
		let b = sig(); // squaring: a·b = sig² ≥ n, so q > 0
		let p = &a * &b;
		let q = &p / &n;
		let r = &p % &n;

		// (a) honest limb identity: bigint_mul(q,n) + r == P (128 limbs)
		let qn = bigint_mul_limbs(&to_limbs64(&q), &to_limbs64(&n));
		let recon = bigint_add_r(&qn, &to_limbs64(&r));
		assert_eq!(recon, to_limbs128(&p), "honest q·n + r != P (limbs)");
		assert!(limb_lt(&to_limbs64(&r), &to_limbs64(&n)), "honest r < n must hold");
		assert_eq!(r, &p % &n, "r != P mod n");

		// (b) limb_lt boundaries
		assert!(!limb_lt(&to_limbs64(&n), &to_limbs64(&n)), "n < n must be false");
		assert!(limb_lt(&to_limbs64(&(&n - 1u32)), &to_limbs64(&n)), "n−1 < n must be true");
		assert!(limb_lt(&to_limbs64(&BigUint::from(0u32)), &to_limbs64(&n)), "0 < n must be true");

		// (c) LOAD-BEARING: (q−1, r+n) still satisfies the identity, only limb_lt rejects.
		assert!(q > BigUint::from(0u32), "need q > 0 for the unreduced attack");
		let q_bad = &q - 1u32;
		let r_bad = &r + &n;
		assert_eq!(&q_bad * &n + &r_bad, p, "unreduced (q−1,r+n) must still satisfy the identity");
		assert!(r_bad >= n, "r+n ≥ n");
		if r_bad.bits() <= 2048 {
			assert!(
				!limb_lt(&to_limbs64(&r_bad), &to_limbs64(&n)),
				"r+n ≥ n must be REJECTED by limb_lt (the load-bearing test)"
			);
		}
		println!("GATE ref-S3-5: limb modmul identity + r<n; unreduced (q−1,r+n) passes identity, rejected by limb_lt");
	}

	/// One in-circuit modmul over limbs: r = (a·b) mod n, computed via the honest (q,r)
	/// hints and VERIFIED through the gadget constraints (the 128-limb identity
	/// bigint_mul(q,n)+r == bigint_mul(a,b) AND limb_lt(r,n)). Returns r as 64 limbs. Asserts
	/// mirror the circuit's zerochecks, so chaining these validates the limb composition.
	fn modmul_limb(a: &[u32; 64], b: &[u32; 64], n: &[u32; 64]) -> [u32; 64] {
		let a_big = from_limbs(&a[..]);
		let b_big = from_limbs(&b[..]);
		let n_big = from_limbs(&n[..]);
		let p = &a_big * &b_big;
		let q = &p / &n_big; // honest quotient hint
		let r = &p % &n_big; // honest remainder hint

		// circuit constraints (must hold for honest hints):
		let p_limbs = bigint_mul_limbs(a, b);
		let qn = bigint_mul_limbs(&to_limbs64(&q), n);
		assert_eq!(bigint_add_r(&qn, &to_limbs64(&r)), p_limbs, "modmul_limb identity failed");
		assert!(limb_lt(&to_limbs64(&r), n), "modmul_limb r<n failed");
		to_limbs64(&r)
	}

	/// The in-circuit modexp for e = 65537 = 2^16 + 1: t = s; 16 squarings; × s. Each modmul
	/// is a limb gadget (above); in the AIR each is a table whose output t is pushed to a
	/// chain channel and pulled as the next table's input — the STRAND lever (per-modmul /
	/// per-squaring granularity, RSS ∝ one modmul, not 17).
	fn modexp_65537_limb(s: &[u32; 64], n: &[u32; 64]) -> [u32; 64] {
		let mut t = *s;
		for _ in 0..16 {
			t = modmul_limb(&t, &t, n); // squaring
		}
		modmul_limb(&t, s, n) // × s
	}

	/// GATE ref-S3-6 (S3 modexp chain over S0) — the 17-modmul limb chain (16 squarings + 1
	/// multiply, each through the limb identity + limb_lt reduction) computes s^65537 mod n
	/// EQUAL to num-bigint's modpow, AND the full RSA verify built on the chain (EM from m ==
	/// the EMSA-encoded digest) matches for the real RSA-2048 vector.
	#[test]
	fn modexp_chain_limb_over_s0() {
		let n = n();
		let s = sig();
		let n_l = to_limbs64(&n);
		let s_l = to_limbs64(&s);

		// (a) the chained limb modexp == modpow
		let m = modexp_65537_limb(&s_l, &n_l);
		assert_eq!(
			from_limbs(&m),
			s.modpow(&BigUint::from(RSA_E), &n),
			"17-modmul limb chain != modpow(e=65537)"
		);

		// (b) full RSA verify VIA the limb chain: EM from m == EMSA(SHA-256(MSG))
		let mut em = from_limbs(&m).to_bytes_be();
		assert!(em.len() <= RSA_K);
		let mut padded = vec![0u8; RSA_K - em.len()];
		padded.append(&mut em);
		assert_eq!(padded, emsa_pkcs1_sha256(&sha256(MSG), RSA_K), "verify via limb chain != EMSA");
		println!("GATE ref-S3-6: 17-modmul limb chain == modpow; full RSA verify via chain == EMSA");
	}

	/// In-circuit EMSA-PKCS1-v1.5 binding gadget: EVERY byte of EM = I2OSP(m,256) is asserted
	/// equal to either a fixed CONSTANT column (0x00, 0x01, the 0xFF PS run, the 0x00
	/// separator, the DigestInfo prefix) or a HASH byte bound to the SHA-256 gadget output
	/// (H == SHA-256(M)). Because ALL 256 bytes are constrained (not just a prefix), there is
	/// no room for a Bleichenbacher/BERserk-style padding forgery. Returns whether EM binds.
	fn emsa_binding_gadget(em: &[u8], msg_digest: &[u8; 32], k: usize) -> bool {
		if em.len() != k {
			return false;
		}
		let t_len = SHA256_DIGESTINFO_PREFIX.len() + 32;
		let ps_len = k - t_len - 3;
		let sep = 2 + ps_len;
		let hstart = sep + 1 + SHA256_DIGESTINFO_PREFIX.len();

		let mut ok = em[0] == 0x00 && em[1] == 0x01; // header
		for &b in &em[2..sep] {
			ok &= b == 0xFF; // PS run (every byte)
		}
		ok &= em[sep] == 0x00; // separator
		ok &= em[sep + 1..hstart] == SHA256_DIGESTINFO_PREFIX; // DigestInfo prefix
		ok &= &em[hstart..k] == msg_digest; // H == SHA-256(M)
		ok
	}

	/// GATE ref-S3-7 (S3 EMSA padding binding) — the binding accepts the honest EM, rejects a
	/// tampered byte in EVERY region (header, PS, separator, DigestInfo, hash), rejects a
	/// short-PS forgery (an early 0x00 a naive parser might stop at — but the PS bytes are all
	/// constrained 0xFF), and rejects an EM bound to the WRONG message digest.
	#[test]
	fn s3_emsa_padding_binding_gadget() {
		let digest = sha256(MSG);
		let em = emsa_pkcs1_sha256(&digest, RSA_K);
		assert!(emsa_binding_gadget(&em, &digest, RSA_K), "honest EM must bind");

		// tamper a byte in each region
		for pos in [0usize, 1, 5, RSA_K / 2, RSA_K - 40, RSA_K - 1] {
			let mut bad = em.clone();
			bad[pos] ^= 0xFF;
			assert!(!emsa_binding_gadget(&bad, &digest, RSA_K), "tampered EM byte {pos} must reject");
		}
		// short-PS forgery: an early 0x00 inside the PS run (naive "find 00 after FFs" stops
		// early) — the FULL binding rejects because PS bytes are all constrained 0xFF.
		let mut forged = em.clone();
		forged[10] = 0x00;
		assert!(!emsa_binding_gadget(&forged, &digest, RSA_K), "short-PS forgery must reject");
		// wrong message digest ⇒ H binding fails
		let other = sha256(b"a different message");
		assert!(!emsa_binding_gadget(&em, &other, RSA_K), "EM bound to wrong H must reject");
		println!("GATE ref-S3-7: EMSA binds ALL 256 bytes (00 01 FF..FF 00 ‖ DigestInfo ‖ H==SHA256(M)); tamper/short-PS/wrong-H rejected");
	}

	// RSASSA-PSS (RFC 8017 §8.1) — the probabilistic RSA scheme (TLS/modern), vs PKCS#1 v1.5
	// (DNSSEC). Reuses the S3 modexp (s^e mod n); NEW = MGF1 (iterated SHA-256) + masked-DB.
	const EM_BITS: usize = 2047; // modBits − 1
	const S_LEN: usize = 32; // salt length
	const H_LEN: usize = 32; // SHA-256

	/// RFC 8017 §B.2.1 — MGF1 with SHA-256: Hash(seed‖0) ‖ Hash(seed‖1) ‖ … truncated to len.
	/// In-circuit = the iterated SHA-256 gadget.
	fn mgf1_sha256(seed: &[u8], len: usize) -> Vec<u8> {
		let mut t = Vec::with_capacity(len + 32);
		let mut counter = 0u32;
		while t.len() < len {
			let mut input = seed.to_vec();
			input.extend_from_slice(&counter.to_be_bytes());
			t.extend_from_slice(&crate::sha512_gadget::sha256_ref(&input));
			counter += 1;
		}
		t.truncate(len);
		t
	}

	/// RFC 8017 §9.1.2 — EMSA-PSS-VERIFY (SHA-256, salt length S_LEN) on EM = I2OSP(s^e mod n).
	fn emsa_pss_verify(msg: &[u8], em: &[u8], em_bits: usize) -> bool {
		let em_len = (em_bits + 7) / 8;
		if em.len() != em_len || em_len < H_LEN + S_LEN + 2 {
			return false;
		}
		if *em.last().unwrap() != 0xbc {
			return false;
		}
		let m_hash = crate::sha512_gadget::sha256_ref(msg);
		let masked_db = &em[..em_len - H_LEN - 1];
		let h = &em[em_len - H_LEN - 1..em_len - 1];
		let clear = 8 * em_len - em_bits; // leftmost bits of DB that must be 0
		if masked_db[0] & (0xFFu8 << (8 - clear)) != 0 {
			return false;
		}
		let db_mask = mgf1_sha256(h, em_len - H_LEN - 1);
		let mut db: Vec<u8> = masked_db.iter().zip(&db_mask).map(|(a, b)| a ^ b).collect();
		db[0] &= 0xFFu8 >> clear;
		let ps_len = em_len - H_LEN - S_LEN - 2;
		if db[..ps_len].iter().any(|&b| b != 0) || db[ps_len] != 0x01 {
			return false;
		}
		let salt = &db[db.len() - S_LEN..];
		let mut mp = vec![0u8; 8];
		mp.extend_from_slice(&m_hash);
		mp.extend_from_slice(salt);
		crate::sha512_gadget::sha256_ref(&mp).as_slice() == h // H' == H
	}

	/// RSASSA-PSS-VERIFY (SHA-256): m = s^e mod n; EM = I2OSP(m, emLen); EMSA-PSS-VERIFY.
	fn rsa_pss_sha256_verify(n: &BigUint, e: u64, msg: &[u8], sig: &BigUint) -> bool {
		if sig >= n {
			return false;
		}
		let m = sig.modpow(&BigUint::from(e), n);
		let em_len = (EM_BITS + 7) / 8;
		let mut em = m.to_bytes_be();
		if em.len() > em_len {
			return false;
		}
		let mut padded = vec![0u8; em_len - em.len()];
		padded.append(&mut em);
		emsa_pss_verify(msg, &padded, EM_BITS)
	}

	// A real RSA-PSS signature over the S3 keypair (same n), salt = 0..32, msg below.
	const PSS_SIG_HEX: &str = "160217d333afaa3233d66cdc869540a766d4e0840146b7bf0f98a660c4e70dce0a51bf4d77f320bc2467022aacce6039572c1916d97fe84571ace47c5be472a5aa877e7c2be6a34138417658bad49f464bf9b172a22d7410eaa8589162a46b6c904dd394bfc1280d85428655dccbd89fda4bfee619b7eb20be24e701724f8542859f61946054a76c22104347eb290209100dad7fa8357c4725bf50ae67c78a9e741f0c3c2625dbc5b2a2c853f3b9b59d6549fc513661e02157ba9742876cf5e8204a910240e3bd801271d4975d81e3e2c86e9d871912f33190e0a27755bb4cafe76f453200f59114761280cb67d95e95265b2bbd1bac35fdd08fc0a267fbf45f";

	/// GATE ref-S3-8 (RSASSA-PSS verify) — a genuine RSA-PSS signature (modexp + MGF1 +
	/// masked-DB structure + H'==H recomputation) verifies, and a tampered signature or
	/// message rejects. Reuses the S3 modexp; the SHA-256 gadget drives both Hash and MGF1.
	#[test]
	fn rsa_pss_verify_and_tamper_rejected() {
		let n = n();
		let sig = BigUint::parse_bytes(PSS_SIG_HEX.as_bytes(), 16).unwrap();
		let msg = b"RSASSA-PSS test message";
		assert!(rsa_pss_sha256_verify(&n, RSA_E, msg, &sig), "genuine RSA-PSS sig must verify");
		assert!(!rsa_pss_sha256_verify(&n, RSA_E, msg, &(&sig + 1u32)), "tampered signature must reject");
		assert!(!rsa_pss_sha256_verify(&n, RSA_E, b"other message", &sig), "tampered message must reject");
		println!("GATE ref-S3-8: RSASSA-PSS verify (modexp + MGF1 + masked-DB + H'==H) accepts genuine, rejects sig/msg tamper");
	}

	/// RSASSA-PKCS1-v1.5 verify generalized to a k-octet modulus (k=256 for RSA-2048, k=512
	/// for RSA-4096). Same structure — only the limb count (64→128) and emLen scale.
	fn rsa_pkcs1_sha256_verify_k(n: &BigUint, e: u64, msg: &[u8], sig: &BigUint, k: usize) -> bool {
		if sig >= n {
			return false;
		}
		let m = sig.modpow(&BigUint::from(e), n);
		let mut em = m.to_bytes_be();
		if em.len() > k {
			return false;
		}
		let mut padded = vec![0u8; k - em.len()];
		padded.append(&mut em);
		padded == emsa_pkcs1_sha256(&sha256(msg), k)
	}

	// A real RSA-4096 PKCS#1-v1.5 signature (SHA-256).
	const N4096_HEX: &str = "b88f0ff172e11da3788f522fbefec5e1294b41644e4492cb08bc329b1c5fe1a8ea4472fd3b43453075fdad2088ef7de321e8be2539a44ae07ab57ee12e7bdc07e1718a53c7e1765d226ad07261db28a78b8bd709fcf991b1755ea6e5e7c96b6be8f3c314dfd648fb6259f2ea23b4a167b2027c3bba3295c5e8ad73470dca185ebf35506186840c2e671731f53ca8601db5124ee68fda882e9dd61bd074a32b3275ff228f857c93a5dea1db7a282774e4bf6910b5c9b5bdebd7c475e562a3469e14332ad3c165a82de12a13d489d05f36e5a9bac5346e6fc8e9c9afc0737962e8952d25aa82dc3d1e14723b0ee2bc9ebe02c227568cf6b3e190246ba0ba0b16ac6054c173cb9802950c3e1cca97d6a185d60b851ebe65718f5a875f05fc6e6be1363bc1f452216e5ef241e533423f783e95146c725313eaa25dd8ec488f78da2f867798508d2546762b61a4ccced6462c717e3a95724d7b385b70023e3f3174f4f629276b21c1d30309c70bb37b819fb4c5c97f33afd61854734c819fc01801a64ad4b28c76b52abaeaf0fd9068ac906470109001649d944c638c84c02a90fb1362b1de1bf421ba5fd8fef8af6df3f376826199b50ed99ef7f83dc04464537285c7826ef7a24ef757eab6542d665cecb80dc1b3c430b2b7561d8a550c9796fb398a6a91428badf12343835366d1ace6de96ed9db158e4191881fce90ac7e6c521";
	const SIG4096_HEX: &str = "524ead0e7588b217576147b28d290a7e3ef0cf2786a3d86d096b7f21abd6d7a16de08a6f10d2293ae989ce2173cfd74f76ee167f740a213cea1ef1f08ad4695c4527f07582c4a568009f1ceba5e851a88516dc9a80e9d5353cad75c0d9c671314f30e5a3ddca140b2d7cb91d496170b09b262adb62e0774b9b7aa60ad132fd64f819b88dee711101194b34869d43399ae21b6f7c33b9bba351be5c0f83cc080c3054fc1221a53bbe0a032178f077f012350e497e9f9362cf9d7e0787bddb21eb258b9b9bfa1c2752197615d3a7bad62b7321c0e498190a8e3aacbc332ed764b7201820a0c089c4dc723e276804176a3a0d0ed2a704751d53aa51dd8b18b2040ac556bf93c471528c631df493b73d21dd00c1694b3127ed0ce1e5d6ac95288c94695b5c966784fc3ab6e0a44afa36cf6639b49ec0b33993083e3e32ba3cc0a17e6f0c93b49547caf4ea37fc5589b607f4b27044b59fc31a686aa6477e60a9b907ce7adc437037d39d84ecf9880f8e6bde823735620de876683b99d8bdb3390a3c3d35289836d2bd5694b36895d76270e90ece686fe02668ef28622ee90e6d43457f7e38bb980aef4f2f53439968407701a2d728a1ec6b2490c2c28b6d1c3189df67f70bd5ea4bd694f07178fc2126ac2f3bb5b40a9ffacdca1b9a97df45c8be02da2ce20c5ed3616ccc59f2928d2f5a196fbbaf490ba918d2ab1031be616c9d56";

	/// GATE ref-S3-9 (RSA-4096 verify) — a genuine RSA-4096 PKCS#1-v1.5 signature verifies via
	/// the k=512 path (128-limb schoolbook, emLen=512), and a tampered signature/message
	/// rejects. Confirms the RSA gadgets scale from 2048 to 4096 bits with only the limb count
	/// (64→128) and emLen changing.
	#[test]
	fn rsa4096_verify_and_tamper_rejected() {
		let n = BigUint::parse_bytes(N4096_HEX.as_bytes(), 16).unwrap();
		let sig = BigUint::parse_bytes(SIG4096_HEX.as_bytes(), 16).unwrap();
		let msg = b"STARK-Binius S3 RSA-4096 verify vector";
		assert_eq!(n.bits(), 4096, "modulus must be 4096-bit");
		assert!(rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &sig, 512), "genuine RSA-4096 sig must verify");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &(&sig + 1u32), 512), "tampered signature must reject");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, b"other message", &sig, 512), "tampered message must reject");
		println!("GATE ref-S3-9: RSA-4096 PKCS1-v1.5 verify (128-limb schoolbook, emLen=512) accepts genuine, rejects sig/msg tamper");
	}

	// A real RSA-3072 PKCS#1-v1.5 signature (SHA-256). RSA-3072 = NIST's 128-bit-security RSA.
	const N3072_HEX: &str = "dc73f84608f88dbcf86f3521a578ba39dd827959140a9e27e54ed8cad3f994c8e6425f76cac10ad0bd0d4ce8a4e9f507dc0533453c74260cca2cbf58ef6a1eecc3ab8a0348643c7e20e3aa761ff64c3013274c4918060c1ebe8ceca95a5799859944901ec076dac244497257304bc57f6476a037c15dc6a485d04ad1875a89638e401ef456de3d07a02bb09adc6ed515aadcc40e07b4676f2348442bf4d278334672768e492bf3634741ff1beb5becec0d17de07fdf9cc54e280a56f278563bc264e08dd1c45b9acdb426ab88bcc552ab5c94dae0720317ece42bf47dc5d85c9de8c18ee44fadad1594b24aa7c617a4322e3f9bc860a647636b38717ba61c5376cae5539a8543374ad376c6bcea17a621284039b4a31b8ee930706a4bcb705ccca0c3ae35ac07f0a6fb889d4b94a3a18f6e7a448868ee087e946c02bd8b7dc72342652e5299faaea8bf931b9991f449225ae1b0d0fce8d6b26cae12d271ffe2303dd5c4e42b31ac2b93e68f74cdf68650600f3f31b7ce0cd59f598b3c9c15ee7";
	const SIG3072_HEX: &str = "a200f95264afde509d213a2c0cfa1c85026a2ce602fcdf4996b722a75c80f217e9d4bdc8b049ba7c0acf6912ba7bfc9f958dbf9529de68d90c344f5902160de4fe1ce845726266abd8f4e388c18f3b4959434038f64729ff7572eb6a4ad80df20c487a4fa5494ddfc26527c5011e3c9c91976540d962cee34bcf3a8d898bffc2e724acc1e17b101972b1e03c05abc32246290e81eb1483a4c6673cda371d5ef68d120bac7a0a56574bee32b90c23f6dbefa1499ff6dad50cc3ca80227c8d09ed5a91d254097d7e95d95f9238331714e318fd72b38c3f6bf2a2cfbb20928c4c29bf8f0a786eef49d477e4a1fd9e96fe88a7c9a713755fb605c24f37b63085e725dbe3d6152971761d30cf9d55ee18de96295d06c94bec5d5ece8ce0a2c1d9c0a23c914065e41cc002a916cbd3ad6e74b9877b7654b6a33e13e439bd0e361eefb76be0689c3032ddd05597b265f49e24a8a8329e492d7eb16395066de496259cc4aa8d9731d16514aeed65060da9e21175cce6d95409e4fc41c267a56aaa68d9dd";

	/// GATE ref-S3-10 (RSA-3072 verify) — the NIST 128-bit-security RSA size: a genuine
	/// RSA-3072 PKCS#1-v1.5 signature verifies via the k=384 path (96-limb schoolbook,
	/// emLen=384), and a tampered signature/message rejects.
	#[test]
	fn rsa3072_verify_and_tamper_rejected() {
		let n = BigUint::parse_bytes(N3072_HEX.as_bytes(), 16).unwrap();
		let sig = BigUint::parse_bytes(SIG3072_HEX.as_bytes(), 16).unwrap();
		let msg = b"STARK-Binius S3 RSA-3072 verify vector";
		assert_eq!(n.bits(), 3072, "modulus must be 3072-bit");
		assert!(rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &sig, 384), "genuine RSA-3072 sig must verify");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &(&sig + 1u32), 384), "tampered signature must reject");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, b"other message", &sig, 384), "tampered message must reject");
		println!("GATE ref-S3-10: RSA-3072 PKCS1-v1.5 verify (96-limb schoolbook, emLen=384) accepts genuine, rejects sig/msg tamper");
	}

	// A real RSA-1024 PKCS#1-v1.5 signature. RSA-1024 is DEPRECATED (~80-bit security) but
	// still appears in LEGACY DNSSEC zones — verifiable for compatibility, not recommended.
	const N1024_HEX: &str = "db88d9740a3a357f56e31514f92b182d390f7cccdb4101ad6239c97b61a37be7c8f26407973a11b944bdd72d41322c86724b64387962133970c106213922bb96c7e8ce19d9176a55295f36acbfe470a3e91352e219915763c24bd371a19e43d1cf63ea747fa7c19f967622212d7e7e2340951d8d0c6dea91135fb69d89fc9c91";
	const SIG1024_HEX: &str = "150c4fbc8154e88c7e95090b6b6ff0d988cd76f8998cecb119d0cdc0d8c98ca45e473debfb6c215a01cef143044deec34773e59cb9b049883808f73234b7b6b6711f1c6b4c287c3b8c09d94b1cf7ebda9374e32490e6f976b9d8fbdf64105d8f0482115945a9c3b18b6c27041f925da687dfd971c659210d2e521edd818fdc75";

	/// GATE ref-S3-11 (RSA-1024 verify, legacy) — a genuine RSA-1024 PKCS#1-v1.5 signature
	/// verifies via the k=128 path (32-limb schoolbook, emLen=128), and a tampered
	/// signature/message rejects. (RSA-1024 is deprecated; supported for legacy DNSSEC zones.)
	#[test]
	fn rsa1024_verify_and_tamper_rejected() {
		let n = BigUint::parse_bytes(N1024_HEX.as_bytes(), 16).unwrap();
		let sig = BigUint::parse_bytes(SIG1024_HEX.as_bytes(), 16).unwrap();
		let msg = b"STARK-Binius S3 RSA-1024 verify vector";
		assert_eq!(n.bits(), 1024, "modulus must be 1024-bit");
		assert!(rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &sig, 128), "genuine RSA-1024 sig must verify");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &(&sig + 1u32), 128), "tampered signature must reject");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, b"other message", &sig, 128), "tampered message must reject");
		println!("GATE ref-S3-11: RSA-1024 (legacy) PKCS1-v1.5 verify (32-limb schoolbook, emLen=128) accepts genuine, rejects sig/msg tamper");
	}

	// A real RSA-8192 PKCS#1-v1.5 signature (ultra-high-security; product of two 4096-bit primes).
	const N8192_HEX: &str = "722c41ea785945fed6d14b28c645c383647171ea0c929ae10b4bbb6137ef85476bc27036583ebdeb7be33968619b0083489eef498521def5b422dfd5bee529e511f8924a949f46bc1df88eacddbb4f0fd024676344d70452e99648dcd47d45b590a936a85e42adf1f8c866247f9076173a19563443953f664d999807dc2d879a39e6c7fbaec5d222c11dfc52ef86f38b75f8d8be994f8c4087724b1437eee8ce3c2ff727a72020b646db2af6c56bf732303629cd8909a75d40b53b6908188a30236942baff82642c9661de2883e20809e028bbb51cfcd94da166edc433abd4f9b7ce874b5027183986c7af9b2ac59b9b21dd05c2c8098afd4f3838942c09f3faf4328414ab550114e99c8210bd51220514a429ba54ca50dd6a4739aff444266c68c633c3f581bbdc29f2232f06ac89d6b60cd06a3aa3d15bb5012d1a266fe2cd3b20b65eff1dd7c1bd44ce238341c5d74a0b4503b6ebd95221a42c52971b31eac6b025fc43acbcbd0df79f2d6e24ffb048816735bd2bff221809e95dfa67eb1e36dd548289e9022e7451a8f538915da78248ca453cf8d78bb6d2459e2f9b091a891977d015e694b960e399a1d50d0d2cfa6d8c6bc7733f20a19b5dfc143f974a6ff95db73d9321bafe48a49a879fa0ce7f32136c8a608e30a4ec1e1b4b472c8c82eed03f952f6a879055c5ab2b5587f239b927ba1f5b37d6dce673a2dbbe2370113c626d0d9c60f83dc6e0f93420a05353d1946bd51a9d96eedb06391ebc38149f10f8c50f0f64a4523c7e79ecdf53cd44af10d1d2d72fdab94b0759bb87bbc2e668f1fe6d6cd89f8f13e55656989e64740acde640e7e9d352f99b91fca4bb05b47426d7fb086c4da500a80c80acdcd4dc703ef3948b8dc37feb321efca842e902c8e27ec459ddc33fae2960d1adf519e8ce0a911399532a283f8f333c0c7d3242848c41c7a8264afa3fb478eb38056cce4406b51e6b57065ba9f72e83aa19ef383fd45a8fa24ec8d316ffd64c9699c6bd80529002f25183b0d71f28a6bb9a64a0a38dad8861cf44faf5717e9577dd2020619cdf3b8c417f05291a3cd0f241d92d48ec24f95f6c14b8f26afaf856feb04bcd0e37e8c652e94da98c2c5568dd039d980fe644858d035acb70b62252df319b660e52a829a8c723a234cd88e519d7bcd2e071e52e97a131ce0bb2253574f2a8e45e3d2c37cd41f79fc58f3568a33e1ea47df11f7917535f3c7799f83df38e9327239a85bbf5a9e63799e10e0ee88906da3d5930867a5f870e663ccf3800eed730a49f5deb690a101f57aaa2dfc96f9cb0892db999f04850ec6342fe73b268d334b07c206d210738cc279e9133df9f7a99de796b6902d3274417faddc0978a299eee5a506b6f2527f6a059c0a9d1cc9de3454a1b17ff39fc2468a4e5b9daa765c172181dd0ead89f0841bbeccfd1d9";
	const SIG8192_HEX: &str = "45396ad1e550bb8a5f53c407162a45d6c1b7b0a6af7f3f435f4e85de2994078498b889f35cdbccaa13d397dfa9a0813707e99a3ab300e5e08e0417c3d197ffeedd24c4937deb568b6dc67064e04ff8dcc831e256b8571e2317fbad68bf898674d1e9bca1e882096e0f838a9a258c6b453896d23efea32147eab7e7ca1a65a7231f5bcd9f41f18e566428940523c39cba2a207ee5c3723ef40d373c627829a886483f1321adc0ce948d3d5c2a15bd37e54706bf11b191d21557b411267200e72b15e791aa16ff174468b2ba6dede997f49e0fc0a784e4e6949fb2fd43ed81399a9f6429df9ee2cd5316738813c2b4dc478c8cc3f51fa7a608aa763c67c41567a7d029548a993141d7896ba10e5b6c6c2bccd06d81e45219cb0c388fd63eb25dbdbaeb1660d5321a8b2be265abdbccf46d2b27da9ced08681adb37851a7ab32297b4334f0be3f42f591370cffe415d265858e3683134197d8cab871044134b5920117ded5bcbe27e268cb428e1978917106c97ae8f131d204eba2fed778dbae123a6d9672f24f319135d0318e4bf9aa14456b9321df741eeeccbb831bb36cf96f99e014c73b4f7979d5a02bbca6405e463805079858f55640d1c910c2175239e7710027f2d836480de620611f30473104347a8b0d7c304eb724239ac10c63e20b819e7fa7a0b355077ab4b9fbd51ff0ec36f2a06e2665e5a954bafc0d05188472b79a9506ddabfc05559dc1292382c13cbfc1aeba1d5600bcd4b279a428faf7766003f033d53f8198f9c5bd2221551f39343ebce2e6dbcf01b733d65ee74c30f75e1b043d21bad61d66bbec569e12fbcab34e1e1889e11c20445064843db78afd648358aeea0013c5ca98096a29ff30817f0d6a27200926abf4a744ea353570ecd41f79966bf06ae30e6f68e76ef0e0433564af79b8fde306df17561d1bea8f9b1b38ee1ee25ec5b5974efda016864441bce119aa9fdfeb46a2eba98a31b35a76e47e0a2dea782c76d651c0b81b207db0dc6bedbd1908b62ca6b7e10f2673e6b874acfb5688ce434065258a3bff027d27365a0d9992ce26cccc80db64c6c4f2157518e7d167300ea8a30bcb04188b08dc1c72ae3aa2e66b368f7cd8d125d7a801e52e7883fc2b94f7fbafd85897341d9d715bfa63a404e75621fafea16c07d81cedef00aee037e8b36d098c844eb640e71681f85279b56e6334ce2017cb5a94db4166e431a84a6c807067711ad11c960bdcb5244801612d3b6275c330fc6f9839a983c3fd4ad1aadb299efa9f28f64f83961d6b53c3060be02da56e7af830656f6f30ea64aa53b880bbdb290cf34cf5c107b69b688c2ea35ddc034fd4439d9f6e6c612376f344c2bdb232c0e7cbb5de9a8c6a489f5c74563c13c10399b82453a6d0da58adff39fd548cc68e499198cb9f119f8b462dd299ce49c1295ddc725196f";

	/// GATE ref-S3-12 (RSA-8192 verify, ultra-high-security) — a genuine RSA-8192 PKCS#1-v1.5
	/// signature verifies via the k=1024 path (256-limb schoolbook, emLen=1024), and a tampered
	/// signature/message rejects. Confirms the RSA gadgets scale to 8192-bit moduli.
	#[test]
	fn rsa8192_verify_and_tamper_rejected() {
		let n = BigUint::parse_bytes(N8192_HEX.as_bytes(), 16).unwrap();
		let sig = BigUint::parse_bytes(SIG8192_HEX.as_bytes(), 16).unwrap();
		let msg = b"STARK-Binius S3 RSA-8192 verify vector";
		assert!(n.bits() >= 8100, "modulus must be ~8192-bit");
		assert!(rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &sig, 1024), "genuine RSA-8192 sig must verify");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, msg, &(&sig + 1u32), 1024), "tampered signature must reject");
		assert!(!rsa_pkcs1_sha256_verify_k(&n, RSA_E, b"other message", &sig, 1024), "tampered message must reject");
		println!("GATE ref-S3-12: RSA-8192 PKCS1-v1.5 verify (256-limb schoolbook, emLen=1024) accepts genuine, rejects sig/msg tamper");
	}

	/// GATE xcheck-rsa (Phase-2) — my S3 RSA-2048 PKCS#1-v1.5 signature is verified by the
	/// `rsa` (RustCrypto) crate AND by my own `rsa_pkcs1_sha256_verify`: both agree it's valid.
	#[test]
	fn rsa2048_matches_rsa_crate() {
		use rsa::{Pkcs1v15Sign, RsaPublicKey};
		let n_big = n();
		let sig_big = sig();

		// build the RustCrypto public key from (n, e) and verify MY signature with it
		let n_rsa = rsa::BigUint::from_bytes_be(&n_big.to_bytes_be());
		let e_rsa = rsa::BigUint::from(RSA_E);
		let pk = RsaPublicKey::new(n_rsa, e_rsa).expect("rsa pubkey");
		let digest = sha256(MSG);
		let mut sig_bytes = {
			let b = sig_big.to_bytes_be();
			let mut out = vec![0u8; RSA_K - b.len()];
			out.extend_from_slice(&b);
			out
		};
		assert!(
			pk.verify(Pkcs1v15Sign::new::<sha2::Sha256>(), &digest, &sig_bytes).is_ok(),
			"the rsa crate must verify my S3 RSA-2048 signature"
		);
		// my own verifier agrees
		assert!(rsa_pkcs1_sha256_verify(&n_big, RSA_E, MSG, &sig_big), "my rsa_pkcs1_sha256_verify agrees");
		// a tampered signature is rejected by the rsa crate too
		sig_bytes[200] ^= 1;
		assert!(
			pk.verify(Pkcs1v15Sign::new::<sha2::Sha256>(), &digest, &sig_bytes).is_err(),
			"the rsa crate must reject a tampered signature"
		);
		println!("GATE xcheck-rsa: my S3 RSA-2048 sig verified by the rsa crate AND rsa_pkcs1_sha256_verify; tampered rejected");
	}

	/// GATE prove-S3-0 (S3 modexp over B256, strand-decomposed) — the FIRST in-circuit RSA modexp
	/// proof: s^e mod N computed over B256 as a chain of seam-glued ModMul STRANDS, each an
	/// independent bounded-memory proof, exactly the RSS decomposition the EC scalar mult uses
	/// (prove-S2-chain). RSA verify recovers em = s^e mod N; for e = 17 = 2⁴+1 that is four modular
	/// squarings then one multiply: s → s² → s⁴ → s⁸ → s¹⁶ → s¹⁶·s. Each step is a self-contained
	/// strand: a squaring pulls its input coord from an input boundary (multiplicity 2, since x² pulls
	/// x twice) and pushes x² to an output boundary; the final multiply pulls s¹⁶ and s and pushes em.
	/// Every strand is prove()d and verify()d on its OWN ConstraintSystem — five separate proofs — and
	/// the chain composes to em = s¹⁷ mod N (num-bigint cross-checked). The cross-strand binding is the
	/// public boundary-value equality the aggregator checks (step k's output boundary == step k+1's
	/// input boundary); a strand that publishes a value it did not compute fails its own verification
	/// and is REJECTED. Reduction is proved by the S0 ModMul gadget (r = s·s − q·N with r < N). A
	/// toy-width modulus (~248-bit, derived from the real RSA-2048 vector, kept odd) makes each ModMul
	/// ≈ the Ed25519 cost; real RSA-2048 is the identical strand chain at W = 4096 (e = 65537 → 16
	/// squarings + 1 multiply), each still a separate bounded-memory proof. Honest chain
	/// PROVES+VERIFIES over B256 at NIST L1; a strand lying about its output is REJECTED. This is the
	/// arithmetic core of prove-S3-1 (the EMSA byte-equality boundary over binius_circuits::sha256 is
	/// the remaining wiring).
	#[test]
	fn rsa_modexp_strands_prove_over_b256() {
		use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
		use crate::nonnative::{ModMul, ModMulRow};
		use binius_core::constraint_system::channel::FlushDirection;
		use binius_core::fiat_shamir::HasherChallenger;
		use binius_hash::sha2::Sha256Compression;
		use binius_m3::builder::{Boundary, ConstraintSystem, Statement, WitnessIndex, B64};
		use bumpalo::Bump;
		use sha2::Sha256;

		const W: usize = 512;
		fn to_bits(x: &BigUint) -> Vec<bool> {
			(0..W as u64).map(|i| x.bit(i)).collect()
		}
		let to_boundary = |x: &BigUint| -> Vec<OurB256> {
			let mut b = x.to_bytes_le();
			b.resize(32, 0);
			(0..4).map(|i| OurB256::from(B64::new(u64::from_le_bytes(b[i * 8..i * 8 + 8].try_into().unwrap())))).collect()
		};

		// Toy-width modulus (~248-bit) derived from the real RSA-2048 vector, forced odd; s < N.
		let nmod = BigUint::parse_bytes(&N_HEX.as_bytes()[..62], 16).unwrap() | BigUint::from(1u32);
		let s = BigUint::parse_bytes(&SIG_HEX.as_bytes()[..62], 16).unwrap() % &nmod;
		let n_bits = to_bits(&nmod);
		let np = nmod.bits() as usize;

		// A squaring strand: x → x² mod N. Input coord via boundary (mult 2), output via boundary.
		let prove_square = |x: &BigUint, x2_pub: &BigUint| -> bool {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let chx = cs.add_channel("chX");
			let chout = cs.add_channel("chOut");
			let mm = ModMul::<W>::build_seamed_in2_chain(&mut cs, &n_bits, np, chx, chx, chout);
			let r_true = (x * x) % &nmod;
			let boundaries = vec![
				Boundary { values: to_boundary(x), channel_id: chx, direction: FlushDirection::Push, multiplicity: 2 },
				Boundary { values: to_boundary(x2_pub), channel_id: chout, direction: FlushDirection::Pull, multiplicity: 1 },
			];
			let statement = Statement { boundaries, table_sizes: vec![1] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(mm.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				let q = (x * x) / &nmod;
				mm.populate(&mut seg, &[ModMulRow { a: to_bits(x), b: to_bits(x), q: to_bits(&q), r: to_bits(&r_true) }]).unwrap();
			}
			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let proof = binius_core::constraint_system::prove::<
				U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf).is_ok(),
			}
		};

		// A multiply strand: a·b mod N. Both operands via boundaries.
		let prove_mult = |a: &BigUint, b: &BigUint, r_pub: &BigUint| -> bool {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let cha = cs.add_channel("chA");
			let chb = cs.add_channel("chB");
			let chout = cs.add_channel("chOut");
			let mm = ModMul::<W>::build_seamed_in2_chain(&mut cs, &n_bits, np, cha, chb, chout);
			let r_true = (a * b) % &nmod;
			let boundaries = vec![
				Boundary { values: to_boundary(a), channel_id: cha, direction: FlushDirection::Push, multiplicity: 1 },
				Boundary { values: to_boundary(b), channel_id: chb, direction: FlushDirection::Push, multiplicity: 1 },
				Boundary { values: to_boundary(r_pub), channel_id: chout, direction: FlushDirection::Pull, multiplicity: 1 },
			];
			let statement = Statement { boundaries, table_sizes: vec![1] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(mm.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				let q = (a * b) / &nmod;
				mm.populate(&mut seg, &[ModMulRow { a: to_bits(a), b: to_bits(b), q: to_bits(&q), r: to_bits(&r_true) }]).unwrap();
			}
			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let proof = binius_core::constraint_system::prove::<
				U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf).is_ok(),
			}
		};

		// modexp chain for e = 17: s → s² → s⁴ → s⁸ → s¹⁶ → em = s¹⁶·s.
		let s2 = (&s * &s) % &nmod;
		let s4 = (&s2 * &s2) % &nmod;
		let s8 = (&s4 * &s4) % &nmod;
		let s16 = (&s8 * &s8) % &nmod;
		let em = (&s16 * &s) % &nmod;

		// Five INDEPENDENT proofs; the aggregator wires each output boundary to the next input.
		assert!(prove_square(&s, &s2), "s² strand must verify");
		assert!(prove_square(&s2, &s4), "s⁴ strand must verify");
		assert!(prove_square(&s4, &s8), "s⁸ strand must verify");
		assert!(prove_square(&s8, &s16), "s¹⁶ strand must verify");
		assert!(prove_mult(&s16, &s, &em), "final multiply strand must verify");

		// The composed chain equals the modexp (num-bigint cross-check).
		assert_eq!(em, s.modpow(&BigUint::from(17u32), &nmod), "chain must compose to s¹⁷ mod N");

		// Soundness: a strand publishing an output it did not compute fails its OWN verification.
		assert!(!prove_square(&s, &((&s2 + 1u32) % &nmod)), "a squaring lying about its output must be REJECTED");
		assert!(!prove_mult(&s16, &s, &((&em + 1u32) % &nmod)), "the final multiply lying about em must be REJECTED");

		println!(
			"GATE prove-S3-0: RSA modexp s^17 mod N proven over B256 @L1(128) as 5 seam-glued ModMul STRANDS (4 squarings + 1 multiply), each an INDEPENDENT bounded-memory proof glued output-boundary→input-boundary; chain composes to s¹⁷ mod N (num-bigint cross-checked), a strand lying about its output REJECTED. RSA modexp decomposes exactly like the EC scalar mult — real RSA-2048 = same chain at W=4096, e=65537 (16 squarings + 1 multiply)."
		);
	}

	/// GATE prove-S3-1 (PENDING) — RSA-2048 PKCS1-v1.5 verify proves over B256; genuine
	/// `rsa`-crate sig accepts, tampered sig/msg/padding reject (isolated to the EM byte-
	/// equality). Needs the limb MulUU32 + bigint schoolbook + S0 limb reduction + modexp
	/// chain + binius_circuits::sha256, and `rsa` in dev-deps.
	#[test]
	#[ignore = "S3 big-int gadgets not wired — needs MulUU32/schoolbook/limb-reduction/modexp + rsa dev-dep"]
	fn rsa2048_proves_over_b256() {
		unimplemented!(
			"limb schoolbook (MulUU32) + S0 limb reduction (P==q·n+r ∧ r<n) + 17-modmul modexp \
			 chain (strand-seamed) + EMSA byte-equality boundary over binius_circuits::sha256"
		);
	}
}
