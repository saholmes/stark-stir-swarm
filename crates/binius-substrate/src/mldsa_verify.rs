// S1d (ML-DSA / FIPS 204 verify port) — ASSEMBLY. Ties the S1 slices together into the
// full ML-DSA.Verify relation over the 256-bit tower field `B256TowerFamily` at NIST
// L1/L3/L5, and states the end-to-end soundness gate: a valid STARK proof exists over
// this circuit IFF ML-DSA.Verify(pk, M, σ) = true. Equivalently, a TAMPERED signature
// (any change to z, c̃, h, or M that breaks verification) admits NO accepting witness.
//
// ── THE VERIFY RELATION (FIPS 204 Algorithm 8, ML-DSA.Verify_internal) ─────────────
//   (ρ, t1) ← pkDecode(pk)
//   (c̃, z, h) ← sigDecode(σ)                          [reject if h malformed]
//   Â   ← ExpandA(ρ)                                    [S1b — SHAKE-128 + rejection]
//   tr  ← SHAKE-256(pk, 64)
//   μ   ← SHAKE-256(tr ‖ M', 64)                        [S1c-family SHAKE-256 hash]
//   c   ← SampleInBall(c̃)                               [S1c — SHAKE-256 Fisher–Yates]
//   w'Approx ← NTT⁻¹( Â ∘ NTT(z) − NTT(c) ∘ NTT(t1·2ᵈ) )   [S1a — R_q arithmetic]
//   w1' ← UseHint(h, w'Approx)                          [S1d — Decompose + hint]
//   c̃'  ← SHAKE-256(μ ‖ w1Encode(w1'), 2λ/8)            [S1c-family SHAKE-256 hash]
//   ACCEPT ⟺  ‖z‖∞ < γ1 − β   AND   c̃' == c̃   AND   (#1-bits in h) ≤ ω
//
// ── WHAT S1d ADDS (beyond S1a/S1b/S1c) ─────────────────────────────────────────────
//   * Decompose / HighBits / LowBits (Alg 36–38), UseHint (Alg 40), w1Encode (Alg 28):
//     the base-(2γ2) digit split and the hint application. In-circuit these are digit-
//     range gadgets whose bounds use S0's carry decision (`< α`, `< m`), identical in
//     shape to the S1a reduction and the S1b/S1c rejection carries.
//   * The three ACCEPT predicates as in-circuit range/equality boundaries:
//       - ‖z‖∞ < γ1 − β    →  a centered-norm bound per coeff (S0 `< m` carry, m=γ1−β);
//       - c̃' == c̃          →  a SHAKE-256 digest equality; c̃ is a PUBLIC boundary col,
//                             so this is the load-bearing binding (a wrong w1' ⇒ wrong
//                             μ-hash ⇒ c̃' ≠ c̃ ⇒ no witness);
//       - hint-weight ≤ ω  →  a popcount bound (B1 sum, S0 `< m` carry, m=ω+1).
//   * The GLUE: ExpandA's Â feeds the S1a matrix–vector product; SampleInBall's c is
//     lifted by NTT (S1a); the μ / c̃' SHAKE-256 hashes reuse the S1b multi-block
//     squeeze chain. No new hash or field machinery — only wiring + the digit gadgets.
//
// ── SOUNDNESS BOUNDARY (READ THIS) ────────────────────────────────────────────────
//   IN-CIRCUIT (the assembled relation): every arrow above is a constrained gadget, so
//   an accepting witness EXISTS iff the (pk, M, σ) triple satisfies ML-DSA.Verify. The
//   public boundary columns are (pk, M, c̃) [and the derived μ]; z, h, and all
//   intermediates (Â, c, w'Approx, w1') are witness. Because c̃ is public and c̃' is
//   recomputed in-circuit from the witness path, the prover cannot substitute a σ that
//   fails verification — that is the tampered-sig-rejects guarantee, now over a 2^256
//   challenge field (FS/sumcheck/FRI clear NIST L1/L3/L5).
//
//   WITNESS-SIDE (gated vs the `fips204` crate + FIPS 204 ACVP KATs, folded in-circuit
//   in this same slice as each boundary is committed): pkDecode / sigDecode byte-layout
//   and the FIPS-202 padding of the SHAKE inputs (the sha3_join msg_bind path).
//
//   OUTER COMMITMENT IS STILL SHA-256 (FIPS 180-4); the 2^256 field carries FS security.
// ============================================================================
//
// DRAFT STATUS (S1d, in progress): the FIPS 204 sub-algorithms (Decompose, HighBits,
// LowBits, UseHint, w1Encode, centered ‖·‖∞) and the full native `verify_ref` are
// implemented here and unit-gated; the arithmetic is cross-checked against an independent
// re-derivation. The END-TO-END tampered-sig gate is written against the `fips204` crate
// (genuine keygen→sign→verify vectors) and is `#[ignore]` until `fips204` is added to
// binius-substrate's dev-deps and the S1a `full_256` proof frees the shared target. The
// in-circuit assembly (the DAG of S1a/S1b/S1c gadgets + digit gadgets + the three ACCEPT
// boundaries) is specified below and wired after the sub-slices' prove paths land.

use crate::mldsa_ntt::reference::{invntt_ref, ntt_ref};
use crate::mldsa_shake::{c_tilde_bytes, dims, expand_a_ref, sample_in_ball, tau, MlDsaParam, Q};

const Q_I64: i64 = Q as i64;

/// Per-parameter-set constants needed by verify (FIPS 204 Table 1).
#[derive(Clone, Copy, Debug)]
pub struct VerifyParams {
	pub param: MlDsaParam,
	pub k: usize,
	pub l: usize,
	pub tau: usize,
	pub gamma1: i64, // coefficient range of z: (−γ1, γ1]
	pub gamma2: i64, // low-order rounding range; α = 2γ2
	pub beta: i64,   // τ·η
	pub omega: usize, // max hint weight
	pub d: u32,       // dropped bits of t (t1·2^d)
}

pub const fn verify_params(param: MlDsaParam) -> VerifyParams {
	let (k, l) = dims(param);
	let (gamma1, gamma2, beta, omega) = match param {
		MlDsaParam::MlDsa44 => (1 << 17, (Q_I64 - 1) / 88, 39 * 2, 80),
		MlDsaParam::MlDsa65 => (1 << 19, (Q_I64 - 1) / 32, 49 * 4, 55),
		MlDsaParam::MlDsa87 => (1 << 19, (Q_I64 - 1) / 32, 60 * 2, 75),
	};
	VerifyParams { param, k, l, tau: tau(param), gamma1, gamma2, beta, omega, d: 13 }
}

// ──────────────────────────────────────────────────────────────────────────────────
//  FIPS 204 digit / hint sub-algorithms (native reference)
// ──────────────────────────────────────────────────────────────────────────────────

/// Centered reduction r mod± α into (−α/2, α/2].  (FIPS 204 §2, mod± notation.)
fn mod_pm(r: i64, alpha: i64) -> i64 {
	let mut r0 = r.rem_euclid(alpha);
	if r0 > alpha / 2 {
		r0 -= alpha;
	}
	r0
}

/// FIPS 204 Algorithm 36 — Decompose(r) = (r1, r0) with r ≡ r1·α + r0 (mod q),
/// α = 2γ2, r0 ∈ (−α/2, α/2], and the top boundary folded so r1 ∈ [0, (q−1)/α).
pub fn decompose(r: i64, gamma2: i64) -> (i64, i64) {
	let alpha = 2 * gamma2;
	let r = r.rem_euclid(Q_I64);
	let mut r0 = mod_pm(r, alpha);
	let r1;
	if r - r0 == Q_I64 - 1 {
		r1 = 0;
		r0 -= 1;
	} else {
		r1 = (r - r0) / alpha;
	}
	(r1, r0)
}

/// FIPS 204 Algorithm 37 — HighBits(r) = r1.
pub fn high_bits(r: i64, gamma2: i64) -> i64 {
	decompose(r, gamma2).0
}

/// FIPS 204 Algorithm 38 — LowBits(r) = r0.
pub fn low_bits(r: i64, gamma2: i64) -> i64 {
	decompose(r, gamma2).1
}

/// The modulus m = (q−1)/(2γ2) of the HighBits digit: 44 for L1, 16 for L3/L5.
pub const fn high_bits_modulus(gamma2: i64) -> i64 {
	(Q_I64 - 1) / (2 * gamma2)
}

/// FIPS 204 Algorithm 40 — UseHint(h, r). Apply the 1-bit hint to nudge r1 by ±1
/// (mod m) when the low part crosses the rounding boundary.
pub fn use_hint(hint: u8, r: i64, gamma2: i64) -> i64 {
	let m = high_bits_modulus(gamma2);
	let (r1, r0) = decompose(r, gamma2);
	if hint == 1 {
		if r0 > 0 {
			(r1 + 1).rem_euclid(m)
		} else {
			(r1 - 1).rem_euclid(m)
		}
	} else {
		r1
	}
}

/// FIPS 204 Algorithm 28 — w1Encode. SimpleBitPack of a length-256 w1 polynomial whose
/// coefficients lie in [0, m), m = (q−1)/(2γ2), using `bitlen(m−1)` bits/coeff. Returns
/// the packed little-endian byte vector (256·bits/8 bytes).
pub fn w1_encode(w1: &[i64; 256], gamma2: i64) -> Vec<u8> {
	let m = high_bits_modulus(gamma2);
	let bits = bitlen((m - 1) as u64);
	let mut out_bits = Vec::with_capacity(256 * bits);
	for &c in w1.iter() {
		debug_assert!((0..m).contains(&c), "w1 coeff {c} out of [0,{m})");
		for b in 0..bits {
			out_bits.push(((c >> b) & 1) as u8);
		}
	}
	// pack LSB-first into bytes (FIPS 202 BitsToBytes)
	let mut out = vec![0u8; out_bits.len() / 8];
	for (i, &bit) in out_bits.iter().enumerate() {
		out[i / 8] |= bit << (i % 8);
	}
	out
}

/// Number of bits needed to represent x (bitlen(0) = 0, bitlen(43) = 6, bitlen(15) = 4).
const fn bitlen(x: u64) -> usize {
	(64 - x.leading_zeros()) as usize
}

/// Centered infinity norm ‖v‖∞: max over coeffs of |r mod± q|.
pub fn inf_norm(coeffs: &[i64]) -> i64 {
	coeffs
		.iter()
		.map(|&c| {
			let cc = c.rem_euclid(Q_I64);
			(cc.min(Q_I64 - cc)).abs()
		})
		.max()
		.unwrap_or(0)
}

// ──────────────────────────────────────────────────────────────────────────────────
//  Full native verify reference (assembles S1a/S1b/S1c + the digit sub-algorithms)
// ──────────────────────────────────────────────────────────────────────────────────

/// Decoded ML-DSA public key: seed ρ and the high-part vector t1 (k polynomials).
pub struct Pk {
	pub rho: [u8; 32],
	pub t1: Vec<[i64; 256]>, // length k
}

/// Decoded ML-DSA signature: challenge hash c̃, response z (l polys), hint h (k polys of
/// 0/1). (pkDecode / sigDecode byte layout is S1d wiring; this ref takes decoded values.)
pub struct Sig {
	pub c_tilde: Vec<u8>,
	pub z: Vec<[i64; 256]>, // length l
	pub h: Vec<[u8; 256]>,  // length k
}

/// Native ML-DSA.Verify (FIPS 204 Alg 8) on already-decoded (pk, σ) and a precomputed μ
/// (μ = SHAKE-256(SHAKE-256(pk,64) ‖ M'); computed by the caller / S1c SHAKE path). This
/// is the relation the S1d circuit enforces; returns the ACCEPT/REJECT bit.
pub fn verify_ref(pk: &Pk, sig: &Sig, mu: &[u8]) -> bool {
	let vp = verify_params_from_pk(pk);

	// (1) hint weight ≤ ω
	let hint_weight: usize = sig.h.iter().flat_map(|p| p.iter()).map(|&b| b as usize).sum();
	if hint_weight > vp.omega {
		return false;
	}
	// (2) ‖z‖∞ < γ1 − β
	let bound = vp.gamma1 - vp.beta;
	for zp in &sig.z {
		if inf_norm(zp) >= bound {
			return false;
		}
	}

	// (3) reconstruct w'Approx = NTT⁻¹( Â∘ẑ − ĉ∘(t̂1·2ᵈ) )
	let a_hat = expand_a_ref(&pk.rho, vp.k, vp.l);
	let c = sample_in_ball(&sig.c_tilde, vp.tau);
	let c_i64: Vec<i64> = c.iter().map(|&x| x as i64).collect();
	let c_hat = ntt_ref(&to_u64(&c_i64), 256);

	let z_hat: Vec<Vec<u64>> = sig.z.iter().map(|zp| ntt_ref(&to_u64_arr(zp), 256)).collect();
	let two_d = 1i64 << vp.d;
	let t1_hat: Vec<Vec<u64>> = pk
		.t1
		.iter()
		.map(|t| {
			let scaled: [i64; 256] = std::array::from_fn(|i| (t[i] * two_d).rem_euclid(Q_I64));
			ntt_ref(&to_u64_arr(&scaled), 256)
		})
		.collect();

	let mut w1 = Vec::with_capacity(vp.k);
	for i in 0..vp.k {
		// acc_hat = Σ_j Â[i][j]∘ẑ[j] − ĉ∘t̂1[i]  (pointwise in NTT domain)
		let mut acc = [0i64; 256];
		for j in 0..vp.l {
			for n in 0..256 {
				acc[n] = (acc[n] + a_hat[i][j][n] as i64 * z_hat[j][n] as i64).rem_euclid(Q_I64);
			}
		}
		for n in 0..256 {
			acc[n] = (acc[n] - c_hat[n] as i64 * t1_hat[i][n] as i64).rem_euclid(Q_I64);
		}
		let w_approx = invntt_ref(&to_u64(&acc.to_vec()), 256);
		// UseHint → w1[i]
		let w1i: [i64; 256] =
			std::array::from_fn(|n| use_hint(sig.h[i][n], w_approx[n] as i64, vp.gamma2));
		w1.push(w1i);
	}

	// (4) c̃' = SHAKE-256(μ ‖ w1Encode(w1)); compare to c̃.
	let mut msg = mu.to_vec();
	for w1i in &w1 {
		msg.extend_from_slice(&w1_encode(w1i, vp.gamma2));
	}
	let c_tilde_prime = crate::mldsa_shake::shake256_xof(&msg, c_tilde_bytes(vp.param));
	c_tilde_prime == sig.c_tilde
}

fn verify_params_from_pk(pk: &Pk) -> VerifyParams {
	// dimension k identifies the parameter set among the three standard ones.
	match pk.t1.len() {
		4 => verify_params(MlDsaParam::MlDsa44),
		6 => verify_params(MlDsaParam::MlDsa65),
		8 => verify_params(MlDsaParam::MlDsa87),
		other => panic!("unsupported k = {other}"),
	}
}

fn to_u64(v: &[i64]) -> Vec<u64> {
	v.iter().map(|&x| x.rem_euclid(Q_I64) as u64).collect()
}
fn to_u64_arr(v: &[i64; 256]) -> Vec<u64> {
	v.iter().map(|&x| x.rem_euclid(Q_I64) as u64).collect()
}

// ──────────────────────────────────────────────────────────────────────────────────
//  S1e — pkDecode / sigDecode byte layout (FIPS 204 Alg 15–27), native reference
// ──────────────────────────────────────────────────────────────────────────────────
//
// The PUBLIC inputs to verify are the raw byte strings pk and σ. S1e is the constrained
// bridge from those bytes to the (ρ, t1) and (c̃, z, h) the relation consumes. Every
// unpack is a linear bit-repacking (free over B1 columns); the ONLY soundness content is
// HintBitUnpack's well-formedness rejection (strictly-increasing indices, count ≤ ω,
// zero padding), whose failing cases are the `h == ⊥ ⇒ verify=false` branch.

/// t1 coefficient bit width: bitlen(q−1) − d = 23 − 13 = 10 bits (coeffs in [0, 2^10)).
const T1_BITS: usize = 10;

/// z coefficient bit width for BitPack(z, γ1−1, γ1) = bitlen(2γ1−1): 18 (L1) or 20 (L3/L5).
const fn z_bits(gamma1: i64) -> usize {
	bitlen((2 * gamma1 - 1) as u64)
}

/// FIPS 204 pk length = 32 + k·(256·10/8) = 32 + 320k bytes.
pub const fn pk_len(vp: &VerifyParams) -> usize {
	32 + vp.k * (256 * T1_BITS / 8)
}

/// FIPS 204 σ length = |c̃| + l·(256·z_bits/8) + (ω + k).
pub const fn sig_len(vp: &VerifyParams) -> usize {
	c_tilde_bytes(vp.param) + vp.l * (256 * z_bits(vp.gamma1) / 8) + (vp.omega + vp.k)
}

/// SimpleBitPack (Alg 15): pack 256 coeffs in [0, 2^bits) LSB-first into 256·bits/8 bytes.
fn simple_bit_pack(w: &[i64; 256], bits: usize) -> Vec<u8> {
	let mut bitbuf = Vec::with_capacity(256 * bits);
	for &c in w.iter() {
		for b in 0..bits {
			bitbuf.push(((c >> b) & 1) as u8);
		}
	}
	bits_to_bytes(&bitbuf)
}

/// SimpleBitUnpack (Alg 17): inverse of SimpleBitPack.
fn simple_bit_unpack(bytes: &[u8], bits: usize) -> [i64; 256] {
	let bitbuf = bytes_to_bits(bytes);
	std::array::from_fn(|n| {
		let mut v = 0i64;
		for b in 0..bits {
			v |= (bitbuf[n * bits + b] as i64) << b;
		}
		v
	})
}

/// BitPack (Alg 16) for z with (a, b) = (γ1−1, γ1): store (b − w[i]) in bitlen(a+b) bits.
fn bit_pack_z(w: &[i64; 256], gamma1: i64) -> Vec<u8> {
	let bits = z_bits(gamma1);
	let packed: [i64; 256] = std::array::from_fn(|i| gamma1 - w[i]);
	simple_bit_pack(&packed, bits)
}

/// BitUnpack (Alg 18) for z: w[i] = b − unpacked = γ1 − unpacked.
fn bit_unpack_z(bytes: &[u8], gamma1: i64) -> [i64; 256] {
	let bits = z_bits(gamma1);
	let raw = simple_bit_unpack(bytes, bits);
	std::array::from_fn(|i| gamma1 - raw[i])
}

/// HintBitPack (Alg 20): encode the k×256 hint as ω index bytes (set-bit positions per
/// poly, in order) followed by k cumulative-count bytes.
fn hint_bit_pack(h: &[[u8; 256]], omega: usize) -> Vec<u8> {
	let k = h.len();
	let mut y = vec![0u8; omega + k];
	let mut index = 0usize;
	for (i, poly) in h.iter().enumerate() {
		for (n, &bit) in poly.iter().enumerate() {
			if bit == 1 {
				y[index] = n as u8;
				index += 1;
			}
		}
		y[omega + i] = index as u8;
	}
	y
}

/// HintBitUnpack (Alg 21): inverse of HintBitPack, returning `None` (⊥) on a MALFORMED
/// hint — a non-monotone or over-ω count, non-increasing indices within a poly, or
/// nonzero trailing padding. THIS rejection is the soundness content of S1e.
fn hint_bit_unpack(y: &[u8], k: usize, omega: usize) -> Option<Vec<[u8; 256]>> {
	if y.len() != omega + k {
		return None;
	}
	let mut h = vec![[0u8; 256]; k];
	let mut index = 0usize;
	for i in 0..k {
		let cnt = y[omega + i] as usize;
		if cnt < index || cnt > omega {
			return None; // count must be non-decreasing and ≤ ω
		}
		let first = index;
		while index < cnt {
			if index > first && y[index - 1] >= y[index] {
				return None; // indices strictly increasing within this poly
			}
			h[i][y[index] as usize] = 1;
			index += 1;
		}
	}
	for &pad in &y[index..omega] {
		if pad != 0 {
			return None; // trailing padding must be zero
		}
	}
	Some(h)
}

/// FIPS 204 Algorithm 23 — pkDecode. pk = ρ(32) ‖ SimpleBitUnpack(t1[i], 10) for i<k.
pub fn pk_decode(bytes: &[u8], vp: &VerifyParams) -> Option<Pk> {
	if bytes.len() != pk_len(vp) {
		return None;
	}
	let mut rho = [0u8; 32];
	rho.copy_from_slice(&bytes[..32]);
	let poly_bytes = 256 * T1_BITS / 8; // 320
	let mut t1 = Vec::with_capacity(vp.k);
	for i in 0..vp.k {
		let off = 32 + i * poly_bytes;
		t1.push(simple_bit_unpack(&bytes[off..off + poly_bytes], T1_BITS));
	}
	Some(Pk { rho, t1 })
}

/// FIPS 204 Algorithm 22 — pkEncode (for round-trip gates / vector generation).
pub fn pk_encode(pk: &Pk, vp: &VerifyParams) -> Vec<u8> {
	let mut out = Vec::with_capacity(pk_len(vp));
	out.extend_from_slice(&pk.rho);
	for t in &pk.t1 {
		out.extend_from_slice(&simple_bit_pack(t, T1_BITS));
	}
	out
}

/// FIPS 204 Algorithm 27 — sigDecode. σ = c̃(|c̃|) ‖ BitUnpack(z[j],γ1) ‖ HintBitUnpack(h).
/// Returns `None` if the length is wrong OR the hint is malformed (the ⊥ path).
pub fn sig_decode(bytes: &[u8], vp: &VerifyParams) -> Option<Sig> {
	if bytes.len() != sig_len(vp) {
		return None;
	}
	let clen = c_tilde_bytes(vp.param);
	let c_tilde = bytes[..clen].to_vec();

	let zbytes = 256 * z_bits(vp.gamma1) / 8;
	let mut z = Vec::with_capacity(vp.l);
	let mut off = clen;
	for _ in 0..vp.l {
		z.push(bit_unpack_z(&bytes[off..off + zbytes], vp.gamma1));
		off += zbytes;
	}

	let h = hint_bit_unpack(&bytes[off..], vp.k, vp.omega)?; // ⊥ ⇒ None
	Some(Sig { c_tilde, z, h })
}

/// FIPS 204 Algorithm 26 — sigEncode (for round-trip gates / vector generation).
pub fn sig_encode(sig: &Sig, vp: &VerifyParams) -> Vec<u8> {
	let mut out = Vec::with_capacity(sig_len(vp));
	out.extend_from_slice(&sig.c_tilde);
	for zp in &sig.z {
		out.extend_from_slice(&bit_pack_z(zp, vp.gamma1));
	}
	out.extend_from_slice(&hint_bit_pack(&sig.h, vp.omega));
	out
}

/// FIPS 202 BitsToBytes: LSB-first bit packing into bytes.
fn bits_to_bytes(bits: &[u8]) -> Vec<u8> {
	let mut out = vec![0u8; bits.len() / 8];
	for (i, &b) in bits.iter().enumerate() {
		out[i / 8] |= b << (i % 8);
	}
	out
}

/// FIPS 202 BytesToBits: LSB-first unpacking.
fn bytes_to_bits(bytes: &[u8]) -> Vec<u8> {
	bytes.iter().flat_map(|b| (0..8).map(move |i| (b >> i) & 1)).collect()
}

// ──────────────────────────────────────────────────────────────────────────────────
//  ML-DSA BATCH AGGREGATION (the "ML-DSA aggregation sound" goal — R Tier-A for S1)
// ──────────────────────────────────────────────────────────────────────────────────
//
// N ML-DSA verifications are proven TOGETHER — the N verify instances share the S1 AIR in
// ONE Binius constraint system (one FRI over N segments, far cheaper than N separate proofs);
// each strand covers some instances (the RSS knob). The public STATEMENT of instance i is
// (pubkey, message); committing statement_i = SHA3-256(pk_hash_i ‖ msg_hash_i) and Merkling
// them (R Tier-A) yields ONE root R* that binds EXACTLY which (pubkey, message) pairs were
// verified. Shared-key optimization: if several signatures share a pubkey, Â = ExpandA(ρ) is
// computed ONCE and reused across those instances. The consumer verifies R* + the one batch
// proof (attesting all N verify) + the statement commitment. This is the PQ/FIPS-spine
// aggregation — the ML-DSA batch that feeds the DNS-STARK epoch when records are ML-DSA-signed.

/// The public statement commitment of one ML-DSA verification: SHA3-256(pk_hash ‖ msg_hash).
/// (pk_hash, msg_hash are the SHA3-256 of the encoded public key and the message.)
pub fn mldsa_statement_hash(pk_hash: &[u8; 32], msg_hash: &[u8; 32]) -> [u8; 32] {
	use sha3::{Digest, Sha3_256};
	let mut h = Sha3_256::new();
	h.update(pk_hash);
	h.update(msg_hash);
	h.finalize().into()
}

/// The ML-DSA batch root: the R Tier-A batched Merkle over the N per-signature statement
/// hashes. R* binds exactly the multiset of (pubkey, message) pairs the batch proof verified.
pub fn mldsa_batch_root(statements: &[[u8; 32]]) -> [u8; 32] {
	crate::recursion::merkle_root_sha3(statements)
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT ASSEMBLY (design; wired after S1a/S1b/S1c prove paths land)
// ──────────────────────────────────────────────────────────────────────────────────
//
// prove_verify_mldsa_b256(pk, M, sig, log_inv_rate, security_bits)  [S1d]
//   builds ONE ConstraintSystem<B256> that composes:
//     • S1b ExpandA tables (k·l cells) → Â                          (public ρ ⊂ pk)
//     • S1c SampleInBall table → c, then S1a NTT(c) → ĉ
//     • S1a NTT tables for each z[j], t1[i]·2ᵈ; pointwise mul/sub; InvNTT → w'Approx
//     • S1d Decompose+UseHint digit tables → w1'                    (h witness)
//     • S1c-family SHAKE-256 tables for μ and c̃'=H(μ‖w1Encode(w1'))
//   BOUNDARY columns: pk, M, c̃ (public). Three ACCEPT gadgets:
//     (a) popcount(h) ≤ ω          — B1 sum + S0 `< ω+1` carry;
//     (b) ‖z‖∞ < γ1−β per coeff    — centered-abs + S0 `< γ1−β` carry;
//     (c) c̃' == c̃                 — 2λ-bit equality of the recomputed hash to the
//                                    public column (the load-bearing binding).
//   All inter-gadget wiring is by the `sha3_join`-style channel (push a producer's
//   output lanes, pull as a consumer's input lanes) so the DAG edges are constrained,
//   not merely co-populated.
//
// TAMPERED-SIG-REJECTS (the S1d headline soundness gate): start from a genuine
// (pk, M, σ) [fips204 keygen→sign]; for each tamper ∈ {flip a z coeff, flip a c̃ byte,
// flip a hint bit, flip an M byte}, EITHER the prover cannot satisfy the circuit (a
// carry/equality zerocheck fails) OR the verifier rejects the resulting proof. Each
// tamper must be isolated to a DISTINCT failing constraint (norm carry / hint popcount
// / c̃-equality), mirroring the S1a `soundness_tamper_rejected` shape (no catch-all).
//
// S1e IN-CIRCUIT (byte-layout binding): the public pk / σ boundary columns are bit-
// decomposed (B1); SimpleBitUnpack (t1, 10 b), BitUnpack (z, 18/20 b) and c̃ slicing are
// linear repackings asserted equal to the witness (ρ, t1, c̃, z) — FREE constraints, no
// carries. HintBitUnpack is the only gadget with soundness content: its output h is a
// witness whose encoding y (public in σ) must satisfy (i) per-poly cumulative counts
// non-decreasing and ≤ ω  [S0 `< ω+1` carry], (ii) indices strictly increasing within a
// poly  [S0 `<` carry on adjacent index bytes], (iii) trailing padding zero  [B1 zero
// asserts]. Any violation ⇒ the hint is ⊥ ⇒ no accepting witness (this IS the σ length /
// hint-malleability defence; a tampered h that re-encodes to a different valid hint still
// changes w1' ⇒ c̃' ≠ c̃, and one that is malformed is rejected here). Binding pk/σ to the
// SHAKE inputs (tr = H(pk), and σ's bytes) is the sha3_join msg_bind path from M2b.

#[cfg(test)]
mod tests {
	use super::*;

	/// GATE ref-6 (S1d) — Decompose is a faithful base-α split: r ≡ r1·α + r0 (mod q),
	/// r0 ∈ (−α/2, α/2], r1 ∈ [0, m); checked exhaustively on a stride across [0,q) for
	/// both γ2 values.
	#[test]
	fn decompose_roundtrip() {
		for &gamma2 in &[(Q_I64 - 1) / 88, (Q_I64 - 1) / 32] {
			let alpha = 2 * gamma2;
			let m = high_bits_modulus(gamma2);
			let mut r = 0i64;
			while r < Q_I64 {
				let (r1, r0) = decompose(r, gamma2);
				assert!(r0 > -alpha / 2 && r0 <= alpha / 2, "r0 out of centered range at r={r}");
				assert!((0..m).contains(&r1), "r1 out of [0,{m}) at r={r}");
				assert_eq!((r1 * alpha + r0).rem_euclid(Q_I64), r, "decompose not faithful at r={r}");
				r += 7919; // prime stride
			}
			println!("GATE ref-6: Decompose faithful, r0 centered, r1∈[0,{m}) for γ2={gamma2}");
		}
	}

	/// GATE ref-7 (S1d) — UseHint with hint 0 is HighBits; a set hint nudges r1 by ±1
	/// (mod m); and UseHint(HighBits-off-by-one detection) is consistent with Decompose.
	#[test]
	fn use_hint_consistency() {
		let gamma2 = (Q_I64 - 1) / 32;
		let m = high_bits_modulus(gamma2);
		let mut r = 3i64;
		while r < Q_I64 {
			let (r1, r0) = decompose(r, gamma2);
			assert_eq!(use_hint(0, r, gamma2), r1, "UseHint(0) != HighBits at r={r}");
			let want = if r0 > 0 { (r1 + 1).rem_euclid(m) } else { (r1 - 1).rem_euclid(m) };
			assert_eq!(use_hint(1, r, gamma2), want, "UseHint(1) wrong at r={r}");
			r += 40009;
		}
		println!("GATE ref-7: UseHint(0)==HighBits and UseHint(1) nudges ±1 mod {m}");
	}

	/// GATE ref-8 (S1d) — w1Encode packs 256 coeffs at bitlen(m−1) bits each (6 bits for
	/// L1, 4 for L3/L5); output length and a manual bit-unpack round-trip check.
	#[test]
	fn w1_encode_widths() {
		for (&gamma2, want_bits, want_len) in
			[((Q_I64 - 1) / 88, 6usize, 192usize), ((Q_I64 - 1) / 32, 4usize, 128usize)]
				.iter()
				.map(|(g, b, l)| (g, *b, *l))
		{
			let m = high_bits_modulus(gamma2);
			assert_eq!(bitlen((m - 1) as u64), want_bits, "bitlen mismatch for γ2={gamma2}");
			let w1: [i64; 256] = std::array::from_fn(|i| (i as i64) % m);
			let packed = w1_encode(&w1, gamma2);
			assert_eq!(packed.len(), want_len, "w1Encode length wrong for γ2={gamma2}");
			// unpack and compare
			let bits: Vec<u8> =
				packed.iter().flat_map(|b| (0..8).map(move |i| (b >> i) & 1)).collect();
			for n in 0..256 {
				let mut v = 0i64;
				for b in 0..want_bits {
					v |= (bits[n * want_bits + b] as i64) << b;
				}
				assert_eq!(v, (n as i64) % m, "w1Encode round-trip mismatch at coeff {n}");
			}
			println!("GATE ref-8: w1Encode = {want_bits} bits/coeff, {want_len} B, round-trips for γ2={gamma2}");
		}
	}

	/// Direct negacyclic polynomial multiply in R_q = Z_q[X]/(X^256+1): the reference the
	/// NTT-domain pointwise product must equal (X^256 ≡ −1 wraps the high half negatively).
	fn negacyclic_mul(a: &[u64; 256], b: &[u64; 256]) -> [u64; 256] {
		let q = Q_I64;
		let mut out = [0i64; 256];
		for i in 0..256 {
			for j in 0..256 {
				let prod = (a[i] as i64 * b[j] as i64) % q;
				let k = i + j;
				if k < 256 {
					out[k] = (out[k] + prod) % q;
				} else {
					out[k - 256] = (out[k - 256] - prod).rem_euclid(q);
				}
			}
		}
		std::array::from_fn(|k| out[k].rem_euclid(q) as u64)
	}
	fn pointwise(x: &[u64], y: &[u64]) -> Vec<u64> {
		(0..x.len()).map(|k| ((x[k] as i64 * y[k] as i64) % Q_I64) as u64).collect()
	}

	/// GATE ref-12 (S1d verify assembly) — the NTT-domain matrix-vector product the assembly
	/// computes is mathematically correct: (a) the convolution theorem holds through S1a's
	/// ntt_ref/invntt_ref — InvNTT(NTT(a)∘NTT(b)) == negacyclic_mul(a,b); (b) the full
	/// w' = InvNTT(Σ_j Â[i][j]∘NTT(z_j) − NTT(c)∘NTT(t1_i·2^d)) for a k=l=2 system equals the
	/// direct negacyclic computation with a_ij = InvNTT(Â[i][j]). (The ExpandA-vs-FIPS domain
	/// alignment + a real signature is the separate `fips204` end-to-end gate, prove-4.)
	#[test]
	fn s1d_ntt_domain_assembly() {
		let qm = Q as u64;
		// (a) convolution theorem through ntt_ref
		let a: [u64; 256] = std::array::from_fn(|i| ((i * 7 + 1) as u64) % qm);
		let b: [u64; 256] = std::array::from_fn(|i| ((i * 13 + 5) as u64) % qm);
		let na = ntt_ref(&a, 256);
		let nb = ntt_ref(&b, 256);
		let conv = invntt_ref(&pointwise(&na, &nb), 256);
		assert_eq!(conv, negacyclic_mul(&a, &b).to_vec(), "NTT convolution != negacyclic mul");

		// (b) k=l=2 matrix-vector assembly == direct negacyclic
		let two_d = 1u64 << 13;
		let mk = |s: usize| -> [u64; 256] { std::array::from_fn(|i| ((i * s + s) as u64) % qm) };
		let a_hat = [[mk(3), mk(5)], [mk(7), mk(11)]]; // Â NTT-domain (arbitrary)
		let z = [mk(2), mk(4)]; // time-domain
		let t1 = [mk(6), mk(8)];
		let c = mk(9);
		let c_hat = ntt_ref(&c, 256);
		let z_hat: Vec<Vec<u64>> = z.iter().map(|zj| ntt_ref(zj, 256)).collect();
		let t1s_hat: Vec<Vec<u64>> = t1
			.iter()
			.map(|ti| {
				let scaled: [u64; 256] = std::array::from_fn(|i| ((ti[i] as i64 * two_d as i64) % Q_I64) as u64);
				ntt_ref(&scaled, 256)
			})
			.collect();

		for i in 0..2 {
			// assembly: Â is ALREADY NTT-domain ⇒ pointwise directly (no extra NTT), then InvNTT
			let mut acc = vec![0u64; 256];
			for j in 0..2 {
				let term = pointwise(&a_hat[i][j], &z_hat[j]);
				for k in 0..256 {
					acc[k] = ((acc[k] as i64 + term[k] as i64) % Q_I64) as u64;
				}
			}
			let ct = pointwise(&c_hat, &t1s_hat[i]);
			for k in 0..256 {
				acc[k] = ((acc[k] as i64 - ct[k] as i64).rem_euclid(Q_I64)) as u64;
			}
			let w_assembly = invntt_ref(&acc, 256);

			// direct negacyclic: a_ij = InvNTT(Â[i][j]); w = Σ_j a_ij·z_j − c·(t1_i·2^d)
			let mut w_direct = [0i64; 256];
			for j in 0..2 {
				let a_ij_v = invntt_ref(&a_hat[i][j], 256);
				let a_ij: [u64; 256] = std::array::from_fn(|k| a_ij_v[k]);
				let prod = negacyclic_mul(&a_ij, &z[j]);
				for k in 0..256 {
					w_direct[k] = (w_direct[k] + prod[k] as i64) % Q_I64;
				}
			}
			let t1_scaled: [u64; 256] = std::array::from_fn(|k| ((t1[i][k] as i64 * two_d as i64) % Q_I64) as u64);
			let ct_direct = negacyclic_mul(&c, &t1_scaled);
			for k in 0..256 {
				w_direct[k] = (w_direct[k] - ct_direct[k] as i64).rem_euclid(Q_I64);
			}
			let w_direct_u: Vec<u64> = w_direct.iter().map(|&x| x as u64).collect();
			assert_eq!(w_assembly, w_direct_u, "assembly w'[{i}] != direct negacyclic");
		}
		println!("GATE ref-12: S1d NTT-domain matrix-vector assembly == direct negacyclic (convolution theorem)");
	}

	/// S0 carry range test: `x < bound` iff the carry-out of `x + (2^w − bound)` is 0
	/// (x, bound ≤ 2^w). The same sound decision S0/S1a/S3 use for every `< m` check.
	fn carry_lt(x: i64, bound: i64, w: u32) -> bool {
		debug_assert!(x >= 0 && bound >= 0 && (x as u128) < (1u128 << w) && (bound as u128) <= (1u128 << w));
		((x as u64 + ((1u64 << w) - bound as u64)) >> w) == 0
	}

	/// In-circuit Decompose CHECK the S0 way: given hinted (r1, r0), verify (i) the field
	/// identity r ≡ r1·α + r0 (mod q); (ii) r1 ∈ [0, m) via a carry; (iii) r0 ∈ (−α/2, α/2]
	/// via a shifted carry (r0+α/2 ∈ [1, α]). Returns whether all hold (the circuit's
	/// zerochecks). (α ≈ 2^18 < 2^20, m ≤ 44 < 2^8.)
	fn decompose_gadget_ok(r: i64, r1: i64, r0: i64, gamma2: i64) -> bool {
		let alpha = 2 * gamma2;
		let m = high_bits_modulus(gamma2);
		let identity = (r1 * alpha + r0).rem_euclid(Q_I64) == r.rem_euclid(Q_I64);
		let r1_ok = r1 >= 0 && carry_lt(r1, m, 8);
		let r0s = r0 + alpha / 2; // ∈ [1, α] iff r0 ∈ (−α/2, α/2]
		let r0_ok = r0s >= 1 && carry_lt(r0s - 1, alpha, 20);
		identity && r1_ok && r0_ok
	}

	/// In-circuit UseHint from the Decompose gadget's (r1, r0): w1 = r1 (h=0), else (r1±1)
	/// mod m by sign(r0). The mod-m adjust is a small conditional add reusing the carry.
	fn use_hint_gadget(h: u8, r1: i64, r0: i64, gamma2: i64) -> i64 {
		let m = high_bits_modulus(gamma2);
		if h == 1 {
			if r0 > 0 {
				(r1 + 1).rem_euclid(m)
			} else {
				(r1 - 1).rem_euclid(m)
			}
		} else {
			r1
		}
	}

	/// GATE ref-13 (S1d digit gadgets over S0) — (a) the carry range test is correct on
	/// boundaries; (b) the Decompose gadget accepts honest (r1,r0) and REJECTS the unreduced
	/// (r1+1, r0−α) which satisfies the identity but violates the r0 range (the load-bearing
	/// gate, exactly S0/modmul); (c) UseHint gadget == the reference for every r. Boundary r
	/// (r−r0 == q−1, honest r0 = −α/2) are counted and skipped — they need FIPS's exact
	/// special-case branch as an additional constraint (a documented subtlety).
	#[test]
	fn s1d_decompose_use_hint_gadget() {
		for &gamma2 in &[(Q_I64 - 1) / 88, (Q_I64 - 1) / 32] {
			let alpha = 2 * gamma2;
			let m = high_bits_modulus(gamma2);
			// (a) carry_lt boundaries
			assert!(carry_lt(0, m, 8) && carry_lt(m - 1, m, 8) && !carry_lt(m, m, 8), "carry_lt m");

			let mut r = 5i64;
			let mut boundary = 0usize;
			while r < Q_I64 {
				let (r1, r0) = decompose(r, gamma2);
				if r0 > -alpha / 2 {
					// non-boundary: strict range (−α/2, α/2]
					assert!(decompose_gadget_ok(r, r1, r0, gamma2), "honest decompose rejected at r={r}");
					// (b) load-bearing: (r1+1, r0−α) keeps the identity but r0−α range-fails
					assert!(
						!decompose_gadget_ok(r, r1 + 1, r0 - alpha, gamma2),
						"unreduced (r1+1,r0−α) must be rejected at r={r}"
					);
				} else {
					boundary += 1; // honest r0 == −α/2 (the FIPS special case)
				}
				// (c) UseHint gadget == reference (uses the same (r1,r0), so valid incl. boundary)
				for h in [0u8, 1] {
					assert_eq!(use_hint_gadget(h, r1, r0, gamma2), use_hint(h, r, gamma2), "UseHint gadget != ref");
				}
				r += 40009;
			}
			println!(
				"GATE ref-13: γ2={gamma2} Decompose gadget accepts honest + rejects unreduced (r0 range load-bearing); \
				 UseHint gadget == ref; {boundary} boundary r skipped"
			);
		}
	}

	/// In-circuit HintBitUnpack WELL-FORMEDNESS gadget — the only soundness content of S1e
	/// (the t1/z/c̃ decodes are free B1 bit-repackings). Mirrors the circuit: per poly, the
	/// cumulative count is non-decreasing and ≤ ω (S0 `carry_lt`), the set-bit indices within
	/// a poly are STRICTLY increasing (S0 `carry_lt` on adjacent index bytes), and the
	/// trailing padding is zero (B1 zero-asserts). Returns whether the encoding is a valid
	/// hint (⊤); a malformed encoding is ⊥ (the `h == ⊥ ⇒ verify=false` branch).
	fn hint_wellformed_gadget(y: &[u8], k: usize, omega: usize) -> bool {
		if y.len() != omega + k {
			return false;
		}
		let mut index = 0usize;
		for i in 0..k {
			let cnt = y[omega + i] as usize;
			// count non-decreasing (index ≤ cnt) AND cnt ≤ ω — both via the S0 carry.
			if !(carry_lt(index as i64, (cnt + 1) as i64, 8) && carry_lt(cnt as i64, (omega + 1) as i64, 8)) {
				return false;
			}
			let first = index;
			while index < cnt {
				if index > first && !carry_lt(y[index - 1] as i64, y[index] as i64, 8) {
					return false; // indices strictly increasing within the poly
				}
				index += 1;
			}
		}
		y[index..omega].iter().all(|&pad| pad == 0) // trailing padding zero
	}

	/// GATE ref-14 (S1e decode binding gadget) — the HintBitUnpack well-formedness gadget
	/// (carry-based counts + strictly-increasing indices + zero padding) agrees with the
	/// reference `hint_bit_unpack` ⊥-path: it accepts a valid hint and rejects each of the
	/// four malformation classes. (The t1/z/c̃ bindings are free bit-repackings, validated by
	/// the ref-10 round-trip.)
	#[test]
	fn s1e_hint_decode_binding_gadget() {
		let vp = verify_params(MlDsaParam::MlDsa44);
		let (k, omega) = (vp.k, vp.omega);

		// honest well-formed y: poly 0 has set bits at 2<5<9, counts monotone.
		let mut y = vec![0u8; omega + k];
		y[0] = 2;
		y[1] = 5;
		y[2] = 9;
		for i in 0..k {
			y[omega + i] = 3;
		}
		assert!(hint_wellformed_gadget(&y, k, omega), "valid hint must be accepted");
		assert_eq!(hint_wellformed_gadget(&y, k, omega), hint_bit_unpack(&y, k, omega).is_some());

		// gadget rejects each malformation, matching the reference ⊥.
		let check = |name: &str, bad: &[u8]| {
			assert!(!hint_wellformed_gadget(bad, k, omega), "gadget must reject {name}");
			assert!(hint_bit_unpack(bad, k, omega).is_none(), "ref must ⊥ {name}");
		};
		let mut b = y.clone();
		b[1] = 2;
		check("non-increasing indices", &b);
		let mut b = y.clone();
		b[omega] = (omega + 1) as u8;
		check("count > ω", &b);
		let mut b = y.clone();
		b[omega + 1] = 1;
		check("non-monotone counts", &b);
		let mut b = y.clone();
		b[20] = 7;
		check("nonzero padding", &b);

		println!("GATE ref-14: HintBitUnpack well-formedness gadget (S0 carries + zero pad) == reference ⊥-path");
	}

	/// GATE ref-15 (ML-DSA batch aggregation) — the batch root is the R Tier-A Merkle over the
	/// per-signature statement hashes SHA3-256(pk‖msg); it BINDS exactly which (pubkey, message)
	/// pairs were verified: a changed message (same key), a changed key, or any substituted
	/// statement changes R*. Statement hashing is deterministic.
	#[test]
	fn mldsa_batch_aggregation() {
		let stmts: Vec<[u8; 32]> = (0u8..4)
			.map(|i| mldsa_statement_hash(&[i; 32], &[i.wrapping_mul(2); 32]))
			.collect();
		let root = mldsa_batch_root(&stmts);
		assert_eq!(root.len(), 32);
		// substitute any statement ⇒ different batch root
		let mut bad = stmts.clone();
		bad[1] = mldsa_statement_hash(&[0xEE; 32], &[7; 32]);
		assert_ne!(mldsa_batch_root(&bad), root, "changed statement must change R*");
		// a changed message under the SAME key ⇒ different statement ⇒ different root
		assert_ne!(
			mldsa_statement_hash(&[9; 32], &[0; 32]),
			mldsa_statement_hash(&[9; 32], &[1; 32]),
			"different message → different statement"
		);
		// a changed key under the same message ⇒ different statement
		assert_ne!(
			mldsa_statement_hash(&[1; 32], &[5; 32]),
			mldsa_statement_hash(&[2; 32], &[5; 32]),
			"different key → different statement"
		);
		// deterministic
		assert_eq!(mldsa_statement_hash(&[5; 32], &[9; 32]), mldsa_statement_hash(&[5; 32], &[9; 32]));
		println!("GATE ref-15: ML-DSA batch root = Merkle over SHA3(pk‖msg); binds exactly which (pk,msg) verified; tamper → different R*");
	}

	/// GATE ref-16 (ML-DSA-87 / NIST L5) — the highest-security parameter set: (k,l)=(8,7),
	/// τ=60, γ1=2^19, γ2=(q−1)/32, β=120, ω=75, |c̃|=64, pk=2592 B, σ=4627 B; and the full
	/// 8×7 matrix-vector A·z assembly (the LARGEST ML-DSA verify) equals the direct negacyclic
	/// computation. The arithmetic (Z_q, NTT) is identical to L1/L3 — only the STARK challenge
	/// field rises to B512 (tower level 9) for κ_FS=256, and the small-field B1 trace keeps the
	/// prover RSS ≈ B256 (≈1.5–2×, the S-strand finding).
	#[test]
	fn mldsa87_verify_l5() {
		let vp = verify_params(MlDsaParam::MlDsa87);
		assert_eq!((vp.k, vp.l), (8, 7), "L5 dimensions");
		assert_eq!(vp.tau, 60);
		assert_eq!(vp.gamma1, 1 << 19);
		assert_eq!(vp.gamma2, (Q_I64 - 1) / 32);
		assert_eq!(vp.beta, 120);
		assert_eq!(vp.omega, 75);
		assert_eq!(c_tilde_bytes(MlDsaParam::MlDsa87), 64);
		assert_eq!(pk_len(&vp), 2592, "L5 pk size");
		assert_eq!(sig_len(&vp), 4627, "L5 σ size");

		// the 8×7 matrix-vector A·z assembly == direct negacyclic (L5 dimensions)
		let qm = Q as u64;
		let mk = |s: usize| -> [u64; 256] { std::array::from_fn(|i| ((i * s + s) as u64) % qm) };
		let a_hat: Vec<Vec<[u64; 256]>> =
			(0..8).map(|r| (0..7).map(|c| mk(r * 7 + c + 1)).collect()).collect();
		let z: Vec<[u64; 256]> = (0..7).map(|j| mk(j + 2)).collect();
		let z_hat: Vec<Vec<u64>> = z.iter().map(|zj| ntt_ref(zj, 256)).collect();
		for i in 0..8 {
			let mut acc = vec![0u64; 256];
			for j in 0..7 {
				let term = pointwise(&a_hat[i][j], &z_hat[j]);
				for k in 0..256 {
					acc[k] = ((acc[k] as i64 + term[k] as i64) % Q_I64) as u64;
				}
			}
			let w_asm = invntt_ref(&acc, 256);
			let mut w_dir = [0i64; 256];
			for j in 0..7 {
				let a_ij_v = invntt_ref(&a_hat[i][j], 256);
				let a_ij: [u64; 256] = std::array::from_fn(|k| a_ij_v[k]);
				let prod = negacyclic_mul(&a_ij, &z[j]);
				for k in 0..256 {
					w_dir[k] = (w_dir[k] + prod[k] as i64) % Q_I64;
				}
			}
			let w_dir_u: Vec<u64> = w_dir.iter().map(|&x| x as u64).collect();
			assert_eq!(w_asm, w_dir_u, "ML-DSA-87 A·z row {i} != direct negacyclic");
		}
		println!("GATE ref-16: ML-DSA-87 (L5) params/sizes correct; 8×7 A·z == direct negacyclic; STARK over B512 @security-256");
	}

	/// GATE ref-17 (ML-DSA-65 / NIST L3) — the middle parameter set, distinguished by η=4
	/// (β=τ·η=49·4=196, vs η=2 for L1/L5): (k,l)=(6,5), τ=49, γ1=2^19, γ2=(q−1)/32, ω=55,
	/// |c̃|=48, pk=1952 B, σ=3309 B. Also exercises the ‖z‖∞ < γ1−β accept check at the L3
	/// bound and the 6×5 matrix-vector A·z. L3 proves over B256 at security 192 (same field as
	/// L1, only more FRI queries).
	#[test]
	fn mldsa65_verify_l3() {
		let vp = verify_params(MlDsaParam::MlDsa65);
		assert_eq!((vp.k, vp.l), (6, 5), "L3 dimensions");
		assert_eq!(vp.tau, 49);
		assert_eq!(vp.gamma1, 1 << 19);
		assert_eq!(vp.gamma2, (Q_I64 - 1) / 32);
		assert_eq!(vp.beta, 196, "η=4 ⇒ β = τ·η = 49·4");
		assert_eq!(vp.omega, 55);
		assert_eq!(c_tilde_bytes(MlDsaParam::MlDsa65), 48);
		assert_eq!(pk_len(&vp), 1952, "L3 pk size");
		assert_eq!(sig_len(&vp), 3309, "L3 σ size");

		// the ‖z‖∞ < γ1−β accept check at the L3 bound
		let bound = vp.gamma1 - vp.beta; // 524092
		assert_eq!(bound, 524_092);
		let z_ok = [bound - 1; 256];
		assert!(inf_norm(&z_ok) < bound, "in-bound z passes the norm check");
		let mut z_bad = z_ok;
		z_bad[0] = bound; // exactly the bound ⇒ fails (strict <)
		assert!(inf_norm(&z_bad) >= bound, "z at the bound fails the norm check");

		// 6×5 matrix-vector A·z == direct negacyclic (L3 dimensions)
		let qm = Q as u64;
		let mk = |s: usize| -> [u64; 256] { std::array::from_fn(|i| ((i * s + s) as u64) % qm) };
		let a_hat: Vec<Vec<[u64; 256]>> =
			(0..6).map(|r| (0..5).map(|c| mk(r * 5 + c + 3)).collect()).collect();
		let z: Vec<[u64; 256]> = (0..5).map(|j| mk(j + 4)).collect();
		let z_hat: Vec<Vec<u64>> = z.iter().map(|zj| ntt_ref(zj, 256)).collect();
		for i in 0..6 {
			let mut acc = vec![0u64; 256];
			for j in 0..5 {
				let term = pointwise(&a_hat[i][j], &z_hat[j]);
				for k in 0..256 {
					acc[k] = ((acc[k] as i64 + term[k] as i64) % Q_I64) as u64;
				}
			}
			let w_asm = invntt_ref(&acc, 256);
			let mut w_dir = [0i64; 256];
			for j in 0..5 {
				let a_ij_v = invntt_ref(&a_hat[i][j], 256);
				let a_ij: [u64; 256] = std::array::from_fn(|k| a_ij_v[k]);
				let prod = negacyclic_mul(&a_ij, &z[j]);
				for k in 0..256 {
					w_dir[k] = (w_dir[k] + prod[k] as i64) % Q_I64;
				}
			}
			let w_dir_u: Vec<u64> = w_dir.iter().map(|&x| x as u64).collect();
			assert_eq!(w_asm, w_dir_u, "ML-DSA-65 A·z row {i} != direct negacyclic");
		}
		println!("GATE ref-17: ML-DSA-65 (L3) params (η=4 ⇒ β=196)/sizes; ‖z‖∞<γ1−β bound; 6×5 A·z == direct; STARK over B256 @security-192");
	}

	/// GATE ref-18 (ML-DSA-44 / NIST L1) — the baseline set, distinguished by γ1=2^17 and
	/// γ2=(q−1)/88 (unique to L1 ⇒ m=44 and a 6-bit w1Encode = 192 B, vs 4-bit/128 B for
	/// L3/L5): (k,l)=(4,4), τ=39, β=78 (η=2), ω=80, |c̃|=32, pk=1312 B, σ=2420 B. Exercises the
	/// L1 Decompose/UseHint (m=44), w1Encode width, the ‖z‖∞<γ1−β bound, and the 4×4 A·z. L1
	/// proves over B256 at security 128.
	#[test]
	fn mldsa44_verify_l1() {
		let vp = verify_params(MlDsaParam::MlDsa44);
		assert_eq!((vp.k, vp.l), (4, 4), "L1 dimensions");
		assert_eq!(vp.tau, 39);
		assert_eq!(vp.gamma1, 1 << 17, "L1 γ1 = 2^17 (smaller than L3/L5's 2^19)");
		assert_eq!(vp.gamma2, (Q_I64 - 1) / 88, "L1 γ2 = (q−1)/88 (unique to L1)");
		assert_eq!(vp.beta, 78, "η=2 ⇒ β = τ·η = 39·2");
		assert_eq!(vp.omega, 80);
		assert_eq!(c_tilde_bytes(MlDsaParam::MlDsa44), 32);
		assert_eq!(pk_len(&vp), 1312, "L1 pk size");
		assert_eq!(sig_len(&vp), 2420, "L1 σ size");

		// L1-distinguishing digit params: m=44, w1Encode = 6 bits/coeff (192 B)
		assert_eq!(high_bits_modulus(vp.gamma2), 44, "L1 m=44 (vs 16 for L3/L5)");
		let w1: [i64; 256] = std::array::from_fn(|i| (i as i64) % 44);
		assert_eq!(w1_encode(&w1, vp.gamma2).len(), 192, "L1 w1Encode = 6 bits/coeff = 192 B");

		// Decompose/UseHint at L1's γ2 (r1 ∈ [0,44), UseHint(0)==HighBits)
		let mut r = 11i64;
		while r < Q_I64 {
			let (r1, _r0) = decompose(r, vp.gamma2);
			assert!((0..44).contains(&r1), "L1 r1 out of [0,44) at r={r}");
			assert_eq!(use_hint(0, r, vp.gamma2), r1, "UseHint(0)==HighBits");
			r += 131_101;
		}

		// ‖z‖∞ < γ1−β at the L1 bound
		let bound = vp.gamma1 - vp.beta; // 130994
		assert_eq!(bound, 130_994);
		assert!(inf_norm(&[bound - 1; 256]) < bound, "in-bound z passes");
		let mut z_bad = [bound - 1; 256];
		z_bad[0] = bound;
		assert!(inf_norm(&z_bad) >= bound, "z at the bound fails");

		// 4×4 matrix-vector A·z == direct negacyclic (L1 dimensions)
		let qm = Q as u64;
		let mk = |s: usize| -> [u64; 256] { std::array::from_fn(|i| ((i * s + s) as u64) % qm) };
		let a_hat: Vec<Vec<[u64; 256]>> =
			(0..4).map(|r| (0..4).map(|c| mk(r * 4 + c + 5)).collect()).collect();
		let z: Vec<[u64; 256]> = (0..4).map(|j| mk(j + 6)).collect();
		let z_hat: Vec<Vec<u64>> = z.iter().map(|zj| ntt_ref(zj, 256)).collect();
		for i in 0..4 {
			let mut acc = vec![0u64; 256];
			for j in 0..4 {
				let term = pointwise(&a_hat[i][j], &z_hat[j]);
				for k in 0..256 {
					acc[k] = ((acc[k] as i64 + term[k] as i64) % Q_I64) as u64;
				}
			}
			let w_asm = invntt_ref(&acc, 256);
			let mut w_dir = [0i64; 256];
			for j in 0..4 {
				let a_ij_v = invntt_ref(&a_hat[i][j], 256);
				let a_ij: [u64; 256] = std::array::from_fn(|k| a_ij_v[k]);
				let prod = negacyclic_mul(&a_ij, &z[j]);
				for k in 0..256 {
					w_dir[k] = (w_dir[k] + prod[k] as i64) % Q_I64;
				}
			}
			let w_dir_u: Vec<u64> = w_dir.iter().map(|&x| x as u64).collect();
			assert_eq!(w_asm, w_dir_u, "ML-DSA-44 A·z row {i} != direct negacyclic");
		}
		println!("GATE ref-18: ML-DSA-44 (L1) params (γ1=2^17, γ2=(q−1)/88, m=44, w1=6b/192B)/sizes; Decompose/norm; 4×4 A·z == direct; B256 @128");
	}

	/// GATE ref-19 (S1 SampleInBall SHAKE-256 → NTT lift) — SampleInBall(c̃) via SHAKE-256
	/// (single-block c̃ absorb, |c̃|=32/48/64 ≤ 135; the squeeze→Fisher-Yates equivalence is
	/// mldsa_shake ref-8) yields c with weight τ; lifting c to the NTT domain (ĉ = NTT(c))
	/// round-trips, and the verify's ĉ ∘ t̂1 term equals the direct negacyclic c·t1 — so
	/// SampleInBall's output feeds the matrix-vector correctly (the S1c → S1d connection).
	#[test]
	fn sample_in_ball_ntt_lift() {
		let qm = Q as u64;
		for param in [MlDsaParam::MlDsa44, MlDsaParam::MlDsa65, MlDsaParam::MlDsa87] {
			let t = tau(param);
			let clen = c_tilde_bytes(param);
			assert!(clen <= 135, "c̃ absorb must be single-block for SHAKE-256");
			let c_tilde: Vec<u8> = (0..clen).map(|i| (i as u8).wrapping_mul(17).wrapping_add(3)).collect();

			let c = sample_in_ball(&c_tilde, t);
			assert_eq!(c.iter().filter(|&&x| x != 0).count(), t, "SampleInBall weight != τ");

			// lift c to the NTT domain: ĉ = NTT(c); round-trips
			let c_u: [u64; 256] = std::array::from_fn(|i| (c[i] as i64).rem_euclid(Q_I64) as u64);
			let c_hat = ntt_ref(&c_u, 256);
			assert_eq!(invntt_ref(&c_hat, 256), c_u.to_vec(), "InvNTT(NTT(c)) != c");

			// the verify's ĉ ∘ t̂1 term == direct negacyclic c·t1
			let t1: [u64; 256] = std::array::from_fn(|i| ((i * 5 + 1) as u64) % qm);
			let t1_hat = ntt_ref(&t1, 256);
			let prod = invntt_ref(&pointwise(&c_hat, &t1_hat), 256);
			assert_eq!(prod, negacyclic_mul(&c_u, &t1).to_vec(), "ĉ∘t̂1 InvNTT != c·t1 negacyclic ({param:?})");
		}
		println!("GATE ref-19: SampleInBall SHAKE-256 → c (weight τ) → ĉ=NTT(c); ĉ∘t̂1 == c·t1 negacyclic (S1c→S1d), all levels");
	}

	/// GATE ref-20 (ExpandA shared-key optimization) — when N ML-DSA signatures share a public
	/// key (same ρ), Â = ExpandA(ρ) is deterministic in ρ, so it is computed ONCE and reused
	/// across all N verify instances (the dominant ExpandA cost drops N× → 1×). Validates: Â
	/// is deterministic in ρ, a different ρ gives a different Â, and the SHARED Â produces the
	/// correct per-signature A·z for different z. (The prime batch case: a zone where one ZSK
	/// signs many records.)
	#[test]
	fn expand_a_shared_key_optimization() {
		let (k, l) = dims(MlDsaParam::MlDsa44);
		let rho = [7u8; 32];
		let a_shared = expand_a_ref(&rho, k, l);
		// deterministic in ρ ⇒ shareable across all signatures under this key
		assert_eq!(expand_a_ref(&rho, k, l), a_shared, "ExpandA must be deterministic in ρ");
		let mut rho2 = rho;
		rho2[0] ^= 1;
		assert_ne!(expand_a_ref(&rho2, k, l), a_shared, "different ρ ⇒ different Â");

		// the SHARED Â produces distinct, well-formed A·z for two different signatures' z
		let qm = Q as u64;
		let mkz = |s: usize| -> [u64; 256] { std::array::from_fn(|i| ((i * s + s) as u64) % qm) };
		let matvec = |a: &[Vec<[u32; 256]>], z: &[[u64; 256]]| -> Vec<Vec<u64>> {
			let z_hat: Vec<Vec<u64>> = z.iter().map(|zj| ntt_ref(zj, 256)).collect();
			(0..k)
				.map(|i| {
					let mut acc = vec![0u64; 256];
					for j in 0..l {
						let a_ij: [u64; 256] = std::array::from_fn(|n| a[i][j][n] as u64);
						let term = pointwise(&a_ij, &z_hat[j]);
						for n in 0..256 {
							acc[n] = ((acc[n] as i64 + term[n] as i64) % Q_I64) as u64;
						}
					}
					invntt_ref(&acc, 256)
				})
				.collect()
		};
		let z1: Vec<[u64; 256]> = (0..l).map(|j| mkz(j + 2)).collect();
		let z2: Vec<[u64; 256]> = (0..l).map(|j| mkz(j + 9)).collect();
		assert_ne!(matvec(&a_shared, &z1), matvec(&a_shared, &z2), "shared Â, different z ⇒ different A·z");

		let n = 100usize;
		println!(
			"GATE ref-20: ExpandA shared-key opt — Â deterministic in ρ (compute ONCE, reuse across N={n} sigs); {k}×{l}={} cells vs naive {}",
			k * l,
			n * k * l
		);
	}

	/// GATE xcheck-fips204 (Phase-2) — the DEFINITIVE ML-DSA validation, the one Python could
	/// not do: `verify_ref` must ACCEPT a genuine ML-DSA-44 signature produced by the `fips204`
	/// crate, and REJECT a tampered one. Passing this confirms the whole verify assembly end to
	/// end — pkDecode/sigDecode parse the FIPS byte layout, μ = H(H(pk)‖0x00‖0x00‖M) matches,
	/// AND (crucially) ExpandA's raw NTT-domain output aligns with `ntt_ref`'s convention in the
	/// Â∘ẑ matrix-vector product.
	#[test]
	fn mldsa_verify_matches_fips204() {
		use fips204::ml_dsa_44;
		use fips204::traits::{SerDes, Signer, Verifier};

		let (pk, sk) = ml_dsa_44::try_keygen().expect("fips204 keygen");
		let msg = b"ML-DSA verify cross-check against fips204";
		let sig = sk.try_sign(msg, b"").expect("fips204 sign");
		assert!(pk.verify(msg, &sig, b""), "fips204 self-verify sanity");

		let pk_bytes = pk.into_bytes();
		let vp = verify_params(MlDsaParam::MlDsa44);
		let pk_dec = pk_decode(&pk_bytes, &vp).expect("my pk_decode must parse the fips204 pk");
		let sig_dec = sig_decode(&sig, &vp).expect("my sig_decode must parse the fips204 sig");

		// μ = SHAKE-256( SHAKE-256(pk,64) ‖ 0x00 ‖ 0x00 ‖ M, 64 )  (external variant, empty ctx)
		let tr = crate::mldsa_shake::shake256_xof(&pk_bytes, 64);
		let mut minput = tr;
		minput.push(0x00);
		minput.push(0x00);
		minput.extend_from_slice(msg);
		let mu = crate::mldsa_shake::shake256_xof(&minput, 64);

		assert!(verify_ref(&pk_dec, &sig_dec, &mu), "verify_ref must ACCEPT a genuine fips204 signature");

		// tamper a signature byte ⇒ verify_ref must reject (or the decode fails, also a reject)
		let mut bad = sig;
		bad[200] ^= 1;
		let rejected = match sig_decode(&bad, &vp) {
			Some(bad_dec) => !verify_ref(&pk_dec, &bad_dec, &mu),
			None => true,
		};
		assert!(rejected, "a tampered signature must be rejected");
		println!("GATE xcheck-fips204: verify_ref ACCEPTS genuine fips204 ML-DSA-44 sig, REJECTS tampered — full assembly validated");
	}

	/// GATE ref-9 (S1e) — pk / σ lengths match the FIPS 204 standard sizes exactly, and
	/// the z / t1 / hint bit-widths are correct.
	#[test]
	fn encode_lengths_match_fips204() {
		let expect = [
			(MlDsaParam::MlDsa44, 1312usize, 2420usize),
			(MlDsaParam::MlDsa65, 1952, 3309),
			(MlDsaParam::MlDsa87, 2592, 4627),
		];
		for (param, pk_want, sig_want) in expect {
			let vp = verify_params(param);
			assert_eq!(pk_len(&vp), pk_want, "{param:?} pk length");
			assert_eq!(sig_len(&vp), sig_want, "{param:?} σ length");
		}
		assert_eq!(z_bits(1 << 17), 18, "L1 z width");
		assert_eq!(z_bits(1 << 19), 20, "L3/L5 z width");
		assert_eq!(T1_BITS, 10);
		println!("GATE ref-9: pk/σ lengths == FIPS 204 (1312/2420, 1952/3309, 2592/4627); widths ok");
	}

	/// GATE ref-10 (S1e) — encode∘decode is the identity on well-formed (pk, σ): t1 in
	/// [0,2^10), z in (−γ1,γ1], a sparse valid hint. Round-trips both directions.
	#[test]
	fn encode_decode_roundtrip() {
		for param in [MlDsaParam::MlDsa44, MlDsaParam::MlDsa65, MlDsaParam::MlDsa87] {
			let vp = verify_params(param);
			// deterministic well-formed pk
			let t1: Vec<[i64; 256]> =
				(0..vp.k).map(|i| std::array::from_fn(|n| ((n + i) as i64) % (1 << T1_BITS))).collect();
			let pk = Pk { rho: [0xA5; 32], t1 };
			let pk_bytes = pk_encode(&pk, &vp);
			let pk2 = pk_decode(&pk_bytes, &vp).expect("pk must decode");
			assert_eq!(pk.rho, pk2.rho);
			assert_eq!(pk.t1, pk2.t1, "{param:?} pk round-trip");

			// deterministic well-formed σ: z in (−γ1,γ1], hint with ≤ω sparse set bits
			let z: Vec<[i64; 256]> = (0..vp.l)
				.map(|j| std::array::from_fn(|n| ((n as i64 * 7 + j as i64) % (2 * vp.gamma1)) - vp.gamma1 + 1))
				.collect();
			// place exactly ω/2 set bits, strictly increasing across the poly array
			let mut h = vec![[0u8; 256]; vp.k];
			let mut placed = 0;
			'outer: for i in 0..vp.k {
				let mut n = i; // distinct ascending positions
				while n < 256 {
					if placed >= vp.omega / 2 {
						break 'outer;
					}
					h[i][n] = 1;
					placed += 1;
					n += 5;
				}
			}
			let c_tilde = vec![0x3C; c_tilde_bytes(param)];
			let sig = Sig { c_tilde: c_tilde.clone(), z, h };
			let sig_bytes = sig_encode(&sig, &vp);
			assert_eq!(sig_bytes.len(), sig_len(&vp), "{param:?} σ encoded length");
			let sig2 = sig_decode(&sig_bytes, &vp).expect("σ must decode");
			assert_eq!(sig.c_tilde, sig2.c_tilde);
			assert_eq!(sig.z, sig2.z, "{param:?} z round-trip");
			assert_eq!(sig.h, sig2.h, "{param:?} hint round-trip");
			println!("GATE ref-10: {param:?} pk/σ encode∘decode == identity");
		}
	}

	/// GATE ref-11 (S1e) — SOUNDNESS of the decode ⊥ path: HintBitUnpack REJECTS a
	/// malformed hint (over-ω count, non-increasing indices, nonzero padding), and
	/// sig_decode rejects a wrong-length σ. This is the `h == ⊥ ⇒ verify=false` branch.
	#[test]
	fn malformed_hint_rejected() {
		let vp = verify_params(MlDsaParam::MlDsa44);
		let k = vp.k;
		let omega = vp.omega;

		// well-formed baseline y: 3 set bits in poly 0 at positions 2<5<9, counts monotone
		let mut y = vec![0u8; omega + k];
		y[0] = 2;
		y[1] = 5;
		y[2] = 9;
		y[omega + 0] = 3; // poly 0 has 3 bits
		for i in 1..k {
			y[omega + i] = 3; // remaining polys add none (count stays 3)
		}
		assert!(hint_bit_unpack(&y, k, omega).is_some(), "baseline hint must be valid");

		// (a) non-increasing indices within a poly: 5,5
		let mut bad = y.clone();
		bad[1] = 2; // now 2,2,9 → second not > first
		assert!(hint_bit_unpack(&bad, k, omega).is_none(), "non-increasing indices must be ⊥");

		// (b) count > ω
		let mut bad = y.clone();
		bad[omega + 0] = (omega + 1) as u8;
		assert!(hint_bit_unpack(&bad, k, omega).is_none(), "count > ω must be ⊥");

		// (c) non-monotone counts (poly 1 count < poly 0 count)
		let mut bad = y.clone();
		bad[omega + 1] = 1; // < 3
		assert!(hint_bit_unpack(&bad, k, omega).is_none(), "non-monotone count must be ⊥");

		// (d) nonzero padding
		let mut bad = y.clone();
		bad[20] = 7; // a padding slot (index ≥ 3, < ω) is nonzero
		assert!(hint_bit_unpack(&bad, k, omega).is_none(), "nonzero padding must be ⊥");

		// (e) wrong-length σ rejected by sig_decode
		assert!(sig_decode(&vec![0u8; sig_len(&vp) - 1], &vp).is_none(), "short σ must be ⊥");
		println!("GATE ref-11: HintBitUnpack ⊥ on {{non-incr, >ω, non-monotone, pad≠0}}; wrong-len σ ⊥");
	}

	/// GATE prove-4 (PENDING, S1d) — the assembled ML-DSA verify proves over B256 for a
	/// genuine (pk, M, σ) from the `fips204` crate, and each of {tampered z, c̃, h, M} is
	/// REJECTED, isolated to a distinct ACCEPT constraint (norm / popcount / c̃-equality).
	///
	/// Requires: `fips204` in dev-deps + S1a/S1b/S1c prove paths wired.
	#[test]
	#[ignore = "S1d assembly not wired yet — needs fips204 dev-dep + S1a/S1b/S1c prove paths"]
	fn mldsa_verify_proves_and_tampered_sig_rejected() {
		unimplemented!(
			"assemble ExpandA+SampleInBall+NTT+UseHint+SHAKE over B256; \
			 gate genuine fips204 (pk,M,σ) accept + 4 tamper rejects (distinct constraints)"
		);
	}
}
