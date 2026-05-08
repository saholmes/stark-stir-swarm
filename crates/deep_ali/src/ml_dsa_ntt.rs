//! Native NTT for ML-DSA-44 (FIPS 204 §3.7, §3.8).
//!
//! The negacyclic NTT for R_q = Z_q[X] / (X^256 + 1).
//! Reference: FIPS 204 §3.8.4 Algorithm 35 (NTT) and §3.8.5
//! Algorithm 36 (NTT⁻¹).
//!
//! The primitive 256th root of unity ζ such that ζ^256 = -1
//! (i.e., a primitive 512th root of unity) is **ζ = 1753** (mod
//! 8_380_417), per FIPS 204 §C — the "ZETAS" table is generated
//! from this root in bit-reversed index order.
//!
//! Used as the reference against `ml_dsa_ntt_air`.

#![allow(dead_code)]

use crate::ml_dsa::params::{N, Q};
use crate::ml_dsa_field::{add_q, mul_q, sub_q};

/// Primitive 512th root of unity in Z_q.  ζ^512 = 1, ζ^256 = -1.
pub const ZETA: u32 = 1753;

/// Pre-computed table of ζ powers in bit-reversed order.  256
/// entries: `zetas[k] = ζ^{br_8(k)}` where `br_8` is the 8-bit
/// reversal of `k`.  Entry 0 is unused; the FIPS 204 NTT (Alg. 35)
/// pre-increments `k`, consuming entries 1..=255 across the layers.
pub fn compute_zetas() -> [u32; N] {
    fn br8(mut x: u32) -> u32 {
        let mut r = 0u32;
        for _ in 0..8 {
            r = (r << 1) | (x & 1);
            x >>= 1;
        }
        r
    }
    let mut out = [0u32; N];
    for i in 0..N as u32 {
        let exp = br8(i) as u64;
        let mut acc: u64 = 1;
        let mut base: u64 = ZETA as u64;
        let mut e = exp;
        while e > 0 {
            if e & 1 == 1 { acc = (acc * base) % Q as u64; }
            base = (base * base) % Q as u64;
            e >>= 1;
        }
        out[i as usize] = acc as u32;
    }
    out
}

/// Forward NTT, in-place.  Maps `[a_0, a_1, ..., a_255]` from the
/// coefficient domain to the NTT domain.  FIPS 204 §3.8.4 Alg. 35.
pub fn ntt(a: &mut [u32; N]) {
    let zetas = compute_zetas();
    let mut k = 0usize;
    let mut len = 128usize;
    while len > 0 {
        let mut start = 0usize;
        while start < N {
            k += 1;
            let zeta = zetas[k];
            for j in start..start + len {
                let t = mul_q(zeta, a[j + len]);
                a[j + len] = sub_q(a[j], t);
                a[j]       = add_q(a[j], t);
            }
            start += 2 * len;
        }
        len >>= 1;
    }
}

/// Inverse NTT, in-place.  Maps NTT-domain → coefficient domain.
/// FIPS 204 §3.8.5 Alg. 36.  Walks the same `zetas` table in
/// reverse, using `q - zetas[k]` for the inverse twiddle factor.
pub fn ntt_inv(a: &mut [u32; N]) {
    let zetas = compute_zetas();
    let mut k = 256usize;
    let mut len = 1usize;
    while len < N {
        let mut start = 0usize;
        while start < N {
            k -= 1;
            let zeta = Q - zetas[k];
            for j in start..start + len {
                let t = a[j];
                a[j]       = add_q(t, a[j + len]);
                a[j + len] = mul_q(zeta, sub_q(t, a[j + len]));
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    // Final scaling by N⁻¹ mod q (FIPS 204 §C).  256⁻¹ mod q is
    // computed once via Fermat's little theorem; for q = 8 380 417,
    // 256⁻¹ ≡ 8 347 681 (mod q).
    const N_INV: u32 = 8_347_681;
    for v in a.iter_mut() {
        *v = mul_q(*v, N_INV);
    }
}

/// Pointwise multiplication in NTT domain.  Used by the
/// polynomial-multiplication path: `c = NTT⁻¹(NTT(a) ⊙ NTT(b))`.
pub fn ntt_pointwise_mul(a: &[u32; N], b: &[u32; N]) -> [u32; N] {
    let mut out = [0u32; N];
    for i in 0..N {
        out[i] = mul_q(a[i], b[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ntt_round_trip() {
        let mut a = [0u32; N];
        // Some non-trivial input
        for i in 0..N {
            a[i] = (i as u32 * 12345) % Q;
        }
        let original = a;
        ntt(&mut a);
        ntt_inv(&mut a);
        assert_eq!(a, original, "NTT⁻¹ ∘ NTT must be the identity");
    }

    #[test]
    fn pointwise_mul_matches_schoolbook_polymul() {
        // Polynomial multiplication in R_q via NTT round-trip should
        // agree with negacyclic schoolbook multiplication.
        let mut a = [0u32; N];
        let mut b = [0u32; N];
        a[0] = 3;  a[1] = 5;  a[2] = 7;
        b[0] = 2;  b[1] = 11; b[3] = 4;

        // Schoolbook negacyclic: c[k] = Σ a[i]·b[j] with i+j ≡ k (mod 256),
        // negating when i+j ≥ 256.
        let mut expected = [0u32; N];
        for i in 0..N {
            for j in 0..N {
                let p = mul_q(a[i], b[j]);
                let k = (i + j) % N;
                if i + j < N {
                    expected[k] = add_q(expected[k], p);
                } else {
                    expected[k] = sub_q(expected[k], p);
                }
            }
        }

        let mut a_ntt = a;  ntt(&mut a_ntt);
        let mut b_ntt = b;  ntt(&mut b_ntt);
        let prod_ntt = ntt_pointwise_mul(&a_ntt, &b_ntt);
        let mut prod = prod_ntt;
        ntt_inv(&mut prod);
        assert_eq!(prod, expected,
            "NTT-domain pointwise product must equal negacyclic polymul");
    }

    #[test]
    fn zeta_has_correct_order() {
        // ζ^256 ≡ −1 (mod q), ζ^512 ≡ 1.
        let mut acc: u64 = 1;
        let mut z = ZETA as u64;
        for _ in 0..256 {
            acc = (acc * z) % Q as u64;
        }
        assert_eq!(acc, (Q as u64) - 1, "ζ^256 must equal q − 1 (i.e., −1 mod q)");
        // Square again: ζ^512 = 1.
        acc = (acc * acc) % Q as u64;
        // (q−1)·(q−1) ≡ 1 (mod q) — so this should be 1, but watch
        // for the squaring formulation: we want ζ^512.
        let _ = z;
        let mut acc2: u64 = 1;
        z = ZETA as u64;
        for _ in 0..512 {
            acc2 = (acc2 * z) % Q as u64;
        }
        assert_eq!(acc2, 1, "ζ^512 must equal 1");
    }
}
