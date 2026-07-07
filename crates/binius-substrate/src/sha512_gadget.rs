// S2-support — SHA-512 (FIPS 180-4) in-circuit gadget for Ed25519 verify (k = SHA-512(R‖A‖M)).
// The ONE new hash S2 needs: ECDSA reuses `binius_circuits::sha256`, but there is no
// SHA-512 gadget in Binius, and `sha_outer.rs`'s `Sha512Compression` is the OUTER Merkle/FS
// compression (a hash-based commitment), NOT an in-circuit AIR that proves the SHA-512
// computation as constraints. SHA-512 is sha2 / Merkle–Damgård (64-bit words, 80 rounds) —
// a different construction from the Keccak gadgets — so this is genuinely new.
//
// ── ARITHMETIZATION (all over B1/B64 columns; reuses S0/S1a + m3 primitives) ────────
//   words are 64-bit (B64, or 64×B1). The round function needs only:
//     • mod-2^64 ADD  — the width-64 carry adder from `crate::nonnative` (Adder<64> /
//       ripple_add), taking the LOW 64 bits (drop carry-out) = natural wraparound. This is
//       the SAME sound adder S0/S1a use; SHA needs no reduction, just truncation.
//     • ROTR / SHR   — bit reindexing: free over B1 columns (S1a's shl/shr, or m3
//       add_shifted) — a rotation/shift is a wiring permutation, no constraints.
//     • XOR / AND    — B1 column algebra: XOR = B1 add, AND = B1 mul; Ch/Maj/Σ/σ are fixed
//       combinations of these.
//     • K, H constants — transparent `add_constant` columns.
//   80 rounds (a repeated row structure or unrolled), a 16→80 message schedule, and
//   MULTI-BLOCK chaining (block i+1's input H = block i's output H) bound by a channel seam
//   (the `sha3_join` push/pull mechanism, already proven over B256/B512) or an in-table row
//   dependency. Proven over `B256TowerFamily` (L1/L3) / `B512` (L5), SHA-256 outer commit.
//
// ── REUSE ─────────────────────────────────────────────────────────────────────────
//   * `crate::nonnative` width-64 adder (mod-2^64 add), shl/shr (rotations/shifts).
//   * m3 B1 add/mul (XOR/AND), add_shifted (rotations), add_constant (K/H).
//   * `crate::sha3_join` channel (multi-block H-chaining seam).
//   * `sha2::Sha512` + NIST FIPS 180-4 KATs (the reference the witness is gated against).
//
// ── SOUNDNESS BOUNDARY ────────────────────────────────────────────────────────────
//   IN-CIRCUIT: every round output is a constrained function of its inputs (the adds are
//   the sound carry adder; the bit ops are B1 algebra; the constants are transparent), the
//   message schedule is constrained, and the block chaining binds H across blocks. So the
//   committed digest equals SHA-512 of the committed (padded) message. A tampered message /
//   digest ⇒ a round constraint fails ⇒ no witness. Over the 2^256/2^512 challenge field at
//   NIST L1/L3/L5.
//   WITNESS-SIDE (gated vs sha2 + NIST KATs, folded in-circuit as the padding is asserted
//   against the length): the FIPS 180-4 padding (0x80 ‖ 0*‖ 128-bit big-endian length) —
//   same padding-binding pattern as the SHA-3 gadgets (sha3_binding).
//   OUTER COMMITMENT SHA-256; challenge field carries FS security.
// ============================================================================
//
// DRAFT STATUS: the from-scratch SHA-512 (FIPS 180-4 constants, padding, message schedule,
// 80-round compression) is implemented as the witness-generation REFERENCE the AIR mirrors
// lane-for-lane, and gated against the `sha2` crate + NIST KATs (validated with Python
// first). The in-circuit AIR (round rows + schedule + multi-block chaining over B256/B512)
// is specified above and wired in Phase 3 with the Ed25519 EC ops. Heavy prove gate `#[ignore]`.

/// FIPS 180-4 SHA-512 initial hash value (first 64 bits of the fractional parts of the
/// square roots of the first 8 primes).
pub const SHA512_H: [u64; 8] = [
	0x6a09e667f3bcc908,
	0xbb67ae8584caa73b,
	0x3c6ef372fe94f82b,
	0xa54ff53a5f1d36f1,
	0x510e527fade682d1,
	0x9b05688c2b3e6c1f,
	0x1f83d9abfb41bd6b,
	0x5be0cd19137e2179,
];

/// FIPS 180-4 SHA-512 round constants (first 64 bits of the fractional parts of the cube
/// roots of the first 80 primes).
pub const SHA512_K: [u64; 80] = [
	0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
	0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
	0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
	0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
	0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
	0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
	0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
	0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
	0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
	0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
	0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
	0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
	0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
	0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
	0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
	0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
	0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
	0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
	0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
	0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

#[inline]
fn ch(x: u64, y: u64, z: u64) -> u64 {
	(x & y) ^ (!x & z)
}
#[inline]
fn maj(x: u64, y: u64, z: u64) -> u64 {
	(x & y) ^ (x & z) ^ (y & z)
}
#[inline]
fn big_sigma0(x: u64) -> u64 {
	x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}
#[inline]
fn big_sigma1(x: u64) -> u64 {
	x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}
#[inline]
fn small_sigma0(x: u64) -> u64 {
	x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}
#[inline]
fn small_sigma1(x: u64) -> u64 {
	x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}

/// FIPS 180-4 SHA-512, from scratch. This is the witness-generation reference the in-circuit
/// AIR mirrors constraint-for-constraint: the mod-2^64 `wrapping_add`s are the width-64
/// carry adder, the `rotate_right`/`>>` are bit reindexing, and `ch`/`maj`/`Σ`/`σ` are the
/// B1 algebra. Gated against the `sha2` crate + NIST KATs.
pub fn sha512_ref(msg: &[u8]) -> [u8; 64] {
	let mut h = SHA512_H;

	// FIPS 180-4 padding: msg ‖ 0x80 ‖ 0x00… ‖ 128-bit big-endian bit length, to a 128-byte
	// multiple.
	let bit_len = (msg.len() as u128) * 8;
	let mut m = msg.to_vec();
	m.push(0x80);
	while m.len() % 128 != 112 {
		m.push(0x00);
	}
	m.extend_from_slice(&bit_len.to_be_bytes()); // 16 bytes

	for block in m.chunks(128) {
		let mut w = [0u64; 80];
		for (i, wi) in w.iter_mut().enumerate().take(16) {
			*wi = u64::from_be_bytes(block[i * 8..i * 8 + 8].try_into().unwrap());
		}
		for t in 16..80 {
			w[t] = small_sigma1(w[t - 2])
				.wrapping_add(w[t - 7])
				.wrapping_add(small_sigma0(w[t - 15]))
				.wrapping_add(w[t - 16]);
		}

		let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
		for t in 0..80 {
			let t1 = hh
				.wrapping_add(big_sigma1(e))
				.wrapping_add(ch(e, f, g))
				.wrapping_add(SHA512_K[t])
				.wrapping_add(w[t]);
			let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
			hh = g;
			g = f;
			f = e;
			e = d.wrapping_add(t1);
			d = c;
			c = b;
			b = a;
			a = t1.wrapping_add(t2);
		}
		for (hi, vi) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
			*hi = hi.wrapping_add(vi);
		}
	}

	let mut out = [0u8; 64];
	for (i, hi) in h.iter().enumerate() {
		out[i * 8..i * 8 + 8].copy_from_slice(&hi.to_be_bytes());
	}
	out
}

/// FIPS 180-4 SHA-384 initial hash values (the "second 64 bits" IV). SHA-384 shares the
/// SHA-512 compression and round constants; only the IV and the 48-byte truncation differ.
pub const SHA384_H: [u64; 8] = [
	0xcbbb9d5dc1059ed8,
	0x629a292a367cd507,
	0x9159015a3070dd17,
	0x152fecd8f70e5939,
	0x67332667ffc00b31,
	0x8eb44a8768581511,
	0xdb0c2e0d64f98fa7,
	0x47b5481dbefa4fa4,
];

/// FIPS 180-4 SHA-384 — the SHA-512 compression with the SHA-384 IV, output truncated to the
/// first 6 words (48 bytes). The witness-gen reference for the ECDSA-P384 (DNSSEC alg 14)
/// message hash; in-circuit it is the SHA-512 gadget with a different IV constant + truncation.
pub fn sha384_ref(msg: &[u8]) -> [u8; 48] {
	let mut h = SHA384_H;
	let bit_len = (msg.len() as u128) * 8;
	let mut m = msg.to_vec();
	m.push(0x80);
	while m.len() % 128 != 112 {
		m.push(0x00);
	}
	m.extend_from_slice(&bit_len.to_be_bytes());

	for block in m.chunks(128) {
		let mut w = [0u64; 80];
		for (i, wi) in w.iter_mut().enumerate().take(16) {
			*wi = u64::from_be_bytes(block[i * 8..i * 8 + 8].try_into().unwrap());
		}
		for t in 16..80 {
			w[t] = small_sigma1(w[t - 2])
				.wrapping_add(w[t - 7])
				.wrapping_add(small_sigma0(w[t - 15]))
				.wrapping_add(w[t - 16]);
		}
		let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
		for t in 0..80 {
			let t1 = hh
				.wrapping_add(big_sigma1(e))
				.wrapping_add(ch(e, f, g))
				.wrapping_add(SHA512_K[t])
				.wrapping_add(w[t]);
			let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
			hh = g;
			g = f;
			f = e;
			e = d.wrapping_add(t1);
			d = c;
			c = b;
			b = a;
			a = t1.wrapping_add(t2);
		}
		for (hi, vi) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
			*hi = hi.wrapping_add(vi);
		}
	}

	let mut out = [0u8; 48];
	for (i, hi) in h.iter().take(6).enumerate() {
		out[i * 8..i * 8 + 8].copy_from_slice(&hi.to_be_bytes());
	}
	out
}

/// FIPS 180-4 SHA-256 initial hash values (sqrt of the first 8 primes).
pub const SHA256_H: [u32; 8] = [
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// FIPS 180-4 SHA-256 round constants (cbrt of the first 64 primes).
pub const SHA256_K: [u32; 64] = [
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// FIPS 180-4 SHA-256, from scratch — the witness-generation reference for the S2 ECDSA /
/// S3 RSA message hash. In-circuit the AIR REUSES `binius_circuits::sha256` (it already
/// exists, unlike SHA-512); if that gadget is not field-generic over B256/B512 it is built
/// from scratch exactly like `sha512_ref`'s AIR (32-bit words, 64 rounds, the width-32 carry
/// adder + B1 Σ/σ/Ch/Maj). Gated against the `sha2` crate + NIST KATs.
pub fn sha256_ref(msg: &[u8]) -> [u8; 32] {
	let mut h = SHA256_H;
	let bit_len = (msg.len() as u64) * 8;
	let mut m = msg.to_vec();
	m.push(0x80);
	while m.len() % 64 != 56 {
		m.push(0x00);
	}
	m.extend_from_slice(&bit_len.to_be_bytes()); // 8 bytes

	for block in m.chunks(64) {
		let mut w = [0u32; 64];
		for (i, wi) in w.iter_mut().enumerate().take(16) {
			*wi = u32::from_be_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
		}
		for t in 16..64 {
			let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
			let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
			w[t] = w[t - 16].wrapping_add(s0).wrapping_add(w[t - 7]).wrapping_add(s1);
		}
		let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
		for t in 0..64 {
			let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
			let ch = (e & f) ^ (!e & g);
			let t1 = hh
				.wrapping_add(s1)
				.wrapping_add(ch)
				.wrapping_add(SHA256_K[t])
				.wrapping_add(w[t]);
			let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
			let maj = (a & b) ^ (a & c) ^ (b & c);
			let t2 = s0.wrapping_add(maj);
			hh = g;
			g = f;
			f = e;
			e = d.wrapping_add(t1);
			d = c;
			c = b;
			b = a;
			a = t1.wrapping_add(t2);
		}
		for (hi, vi) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
			*hi = hi.wrapping_add(vi);
		}
	}

	let mut out = [0u8; 32];
	for (i, hi) in h.iter().enumerate() {
		out[i * 4..i * 4 + 4].copy_from_slice(&hi.to_be_bytes());
	}
	out
}

/// FIPS 180-4 SHA-1 initial hash values. (SHA-1 is used ONLY for the DNSSEC NSEC3 owner-name
/// hash — RFC 5155 mandates it there; it is NOT on any signature-verify path.)
pub const SHA1_H: [u32; 5] = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];

/// SHA-1 from scratch — the witness-generation reference for the NSEC3 iterated hash. Same
/// Merkle–Damgård shape as SHA-256 (32-bit words) but 80 rounds with the 5-var round function.
pub fn sha1_ref(msg: &[u8]) -> [u8; 20] {
	let mut h = SHA1_H;
	let bit_len = (msg.len() as u64) * 8;
	let mut m = msg.to_vec();
	m.push(0x80);
	while m.len() % 64 != 56 {
		m.push(0x00);
	}
	m.extend_from_slice(&bit_len.to_be_bytes());

	for block in m.chunks(64) {
		let mut w = [0u32; 80];
		for (i, wi) in w.iter_mut().enumerate().take(16) {
			*wi = u32::from_be_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
		}
		for t in 16..80 {
			w[t] = (w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16]).rotate_left(1);
		}
		let [mut a, mut b, mut c, mut d, mut e] = h;
		for (t, &wt) in w.iter().enumerate() {
			let (f, k) = if t < 20 {
				((b & c) | (!b & d), 0x5A827999u32)
			} else if t < 40 {
				(b ^ c ^ d, 0x6ED9EBA1)
			} else if t < 60 {
				((b & c) | (b & d) | (c & d), 0x8F1BBCDC)
			} else {
				(b ^ c ^ d, 0xCA62C1D6)
			};
			let t2 = a.rotate_left(5).wrapping_add(f).wrapping_add(e).wrapping_add(k).wrapping_add(wt);
			e = d;
			d = c;
			c = b.rotate_left(30);
			b = a;
			a = t2;
		}
		for (hi, vi) in h.iter_mut().zip([a, b, c, d, e]) {
			*hi = hi.wrapping_add(vi);
		}
	}

	let mut out = [0u8; 20];
	for (i, hi) in h.iter().enumerate() {
		out[i * 4..i * 4 + 4].copy_from_slice(&hi.to_be_bytes());
	}
	out
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT AIR DESIGN (wired Phase 3 with the Ed25519 EC ops)
// ──────────────────────────────────────────────────────────────────────────────────
//
// columns per block: 16 committed message words W[0..16] (B64), the derived W[16..80] as
//   add-chains of the schedule, and the 8 working vars a..h across 80 round rows.
// round row t: e_new = d ⊞ (h ⊞ Σ1(e) ⊞ Ch(e,f,g) ⊞ K[t] ⊞ W[t]); a_new = T1 ⊞ Σ0(a) ⊞
//   Maj(a,b,c); the rest a shift-register (⊞ = width-64 carry adder, truncated). Σ/σ are
//   XOR (B1 add) of rotations (add_shifted / bit reindex); Ch/Maj are B1 add/mul. K[t]/H are
//   add_constant columns.
// message schedule: W[t] = σ1(W[t-2]) ⊞ W[t-7] ⊞ σ0(W[t-15]) ⊞ W[t-16], each a constrained
//   add of derived-oracle rotations of committed words.
// multi-block: H_out(block i) pushed to a chain channel, pulled as H_in(block i+1); final
//   block's H_out = the digest (a Boundary, or fed into Ed25519's k = digest mod ℓ). This is
//   the sha3_join seam, reused. Ed25519 hashes R‖A‖M ⇒ 1–2 blocks for short M.
//
// GATE prove (PENDING): SHA-512 of "abc"/"" proves over B256; the committed digest equals
//   the NIST KAT; a tampered message word or a flipped round output is REJECTED.

#[cfg(test)]
mod tests {
	use sha2::{Digest, Sha256, Sha512};

	use super::*;

	fn unhex(s: &str) -> Vec<u8> {
		(0..s.len())
			.step_by(2)
			.map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
			.collect()
	}

	// NIST FIPS 180-4 SHA-256 known-answer vectors.
	const KAT256_EMPTY: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
	const KAT256_ABC: &str = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";

	/// GATE ref-sha256-1 — the from-scratch SHA-256 (the S2/S3 message-hash witness gen)
	/// matches the NIST KATs and the `sha2` crate across empty, "abc", and a MULTI-BLOCK
	/// message (200 B ⇒ 4 blocks — the RSA/ECDSA arbitrary-length case).
	#[test]
	fn sha256_reference_matches_nist_and_sha2() {
		assert_eq!(sha256_ref(b"").to_vec(), unhex(KAT256_EMPTY), "SHA-256(\"\") != NIST KAT");
		assert_eq!(sha256_ref(b"abc").to_vec(), unhex(KAT256_ABC), "SHA-256(\"abc\") != NIST KAT");
		for msg in [&b""[..], &b"abc"[..], &[0x61u8; 200][..]] {
			let mut hasher = Sha256::new();
			hasher.update(msg);
			let expect: [u8; 32] = hasher.finalize().into();
			assert_eq!(sha256_ref(msg), expect, "sha256_ref != sha2 crate for len {}", msg.len());
		}
		assert_eq!(SHA256_H[0], 0x6a09e667);
		assert_eq!(SHA256_K[0], 0x428a2f98);
		assert_eq!(SHA256_K[63], 0xc67178f2);
		println!("GATE ref-sha256-1: from-scratch SHA-256 == NIST KATs + sha2 crate (incl. 4-block)");
	}

	/// GATE ref-sha384-1 — SHA-384 (SHA-512 compression + SHA-384 IV, 48-byte output) matches
	/// the NIST KAT and the `sha2` crate (the ECDSA-P384 message hash).
	#[test]
	fn sha384_reference_matches_kat() {
		use sha2::Sha384;
		let kat_abc = "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7";
		assert_eq!(sha384_ref(b"abc").to_vec(), unhex(kat_abc), "SHA-384(abc) != NIST KAT");
		let mut hasher = Sha384::new();
		hasher.update(&[0x61u8; 200][..]);
		let expect: [u8; 48] = hasher.finalize().into();
		assert_eq!(sha384_ref(&[0x61u8; 200]), expect, "SHA-384 != sha2 crate (2-block)");
		println!("GATE ref-sha384-1: SHA-384 (SHA-512 core + SHA-384 IV) == NIST KAT + sha2 crate");
	}

	/// GATE ref-sha1-1 — the from-scratch SHA-1 (the NSEC3 owner-name hash witness gen)
	/// matches the FIPS 180-4 KATs for empty and "abc".
	#[test]
	fn sha1_reference_matches_kat() {
		assert_eq!(sha1_ref(b"abc").to_vec(), unhex("a9993e364706816aba3e25717850c26c9cd0d89d"), "SHA-1(abc)");
		assert_eq!(sha1_ref(b"").to_vec(), unhex("da39a3ee5e6b4b0d3255bfef95601890afd80709"), "SHA-1(\"\")");
		assert_eq!(SHA1_H[0], 0x67452301);
		println!("GATE ref-sha1-1: from-scratch SHA-1 == FIPS 180-4 KATs (empty, abc)");
	}

	// NIST FIPS 180-4 SHA-512 known-answer vectors.
	const KAT_EMPTY: &str = "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e";
	const KAT_ABC: &str = "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";

	/// GATE ref-sha512-1 — the from-scratch reference matches the NIST KATs and the `sha2`
	/// crate across empty, "abc", a one-block message, and a MULTI-BLOCK message (>112 B,
	/// forcing a second block — exactly the Ed25519 R‖A‖M case for longer M).
	#[test]
	fn sha512_reference_matches_nist_and_sha2() {
		assert_eq!(sha512_ref(b"").to_vec(), unhex(KAT_EMPTY), "SHA-512(\"\") != NIST KAT");
		assert_eq!(sha512_ref(b"abc").to_vec(), unhex(KAT_ABC), "SHA-512(\"abc\") != NIST KAT");

		// cross-check against the sha2 crate on several lengths, incl. a 2-block message.
		for msg in [
			&b""[..],
			&b"abc"[..],
			&b"The quick brown fox jumps over the lazy dog"[..],
			&[0x61u8; 200][..], // 200 bytes ⇒ 2 SHA-512 blocks
		] {
			let mut hasher = Sha512::new();
			hasher.update(msg);
			let expect: [u8; 64] = hasher.finalize().into();
			assert_eq!(sha512_ref(msg), expect, "sha512_ref != sha2 crate for len {}", msg.len());
		}
		println!("GATE ref-sha512-1: from-scratch SHA-512 == NIST KATs + sha2 crate (incl. 2-block)");
	}

	/// GATE ref-sha512-2 — the FIPS 180-4 constants are correct (H0, K0, and the array
	/// lengths), and the round primitives satisfy their defining identities.
	#[test]
	fn constants_and_primitives() {
		assert_eq!(SHA512_H.len(), 8);
		assert_eq!(SHA512_K.len(), 80);
		assert_eq!(SHA512_H[0], 0x6a09e667f3bcc908, "H0");
		assert_eq!(SHA512_K[0], 0x428a2f98d728ae22, "K0");
		assert_eq!(SHA512_K[79], 0x6c44198c4a475817, "K79");
		// rotation is a bijection: rotr∘rotl == id
		let x = 0x0123456789abcdefu64;
		assert_eq!(x.rotate_right(28).rotate_left(28), x);
		// Ch/Maj boolean identities on a couple of bit patterns
		assert_eq!(ch(!0, 0xAA, 0x55), 0xAA, "Ch(1..,y,z)=y");
		assert_eq!(ch(0, 0xAA, 0x55), 0x55, "Ch(0,y,z)=z");
		assert_eq!(maj(0xFF, 0xFF, 0x00), 0xFF, "Maj majority");
		println!("GATE ref-sha512-2: FIPS 180-4 H/K constants + Ch/Maj/rotation primitives correct");
	}

	/// GATE ref-sha512-3 — SHA-512 exactly reproduces the hash used by Ed25519 (k input):
	/// SHA-512(R ‖ A ‖ M) matches the `sha2` crate for the RFC 8032 TEST 1 (R, A) with an
	/// empty M, confirming the gadget will compute the right challenge scalar pre-image.
	#[test]
	fn matches_ed25519_k_preimage() {
		let sig_r = unhex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155");
		let pk_a = unhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
		let mut input = sig_r.clone();
		input.extend_from_slice(&pk_a);
		// empty message M
		let mut hasher = Sha512::new();
		hasher.update(&input);
		let expect: [u8; 64] = hasher.finalize().into();
		assert_eq!(sha512_ref(&input), expect, "SHA-512(R‖A‖M) reference != sha2 (Ed25519 k pre-image)");
		println!("GATE ref-sha512-3: SHA-512(R‖A‖M) == sha2 (the Ed25519 k = H(R‖A‖M) pre-image)");
	}

	/// GATE prove-sha512-1 (PENDING) — SHA-512 proves over B256; the committed digest == the
	/// NIST KAT; a tampered message word / flipped round output is REJECTED. Needs the round-
	/// row AIR (width-64 adder + B1 Σ/σ/Ch/Maj) + multi-block chaining wired.
	#[test]
	#[ignore = "SHA-512 AIR not wired — needs round rows over the width-64 adder + B1 ops + block chaining"]
	fn sha512_proves_over_b256() {
		unimplemented!("80-round SHA-512 compression AIR (nonnative adder + B1 Σ/σ/Ch/Maj) + block-chain seam");
	}
}
