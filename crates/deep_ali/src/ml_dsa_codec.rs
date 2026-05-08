//! FIPS 204 byte-level encoders / decoders + ExpandA — multi-level.
//!
//! Supports the "real ML-DSA signature PoK" path for ALL THREE
//! parameter sets ML-DSA-44 / ML-DSA-65 / ML-DSA-87, selected by
//! the active `mldsa-N` Cargo feature.  All sizes and bit widths
//! auto-derive from `ml_dsa::params`.
//!
//! Conventions:
//!   * All polynomial coefficients are returned in canonical
//!     `[0, q)` form (lifted from any centred or signed encoding).
//!   * `A_hat` from `ExpandA` is already in NTT domain (it's
//!     constructed there directly via `RejNTTPoly`); no separate
//!     NTT step is needed.

#![allow(non_snake_case, dead_code)]

use crate::ml_dsa::params::{
    D, GAMMA1, K, L, N, Q, OMEGA, Z_BITS_PER_COEF,
    C_TILDE_BYTES as PARAM_C_TILDE_BYTES,
    PUBLIC_KEY_BYTES as PARAM_PK_BYTES,
    SIGNATURE_BYTES as PARAM_SIG_BYTES,
};

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake128,
};

/// Encoded sizes — auto-derived from active `mldsa-N` feature.
pub const PUBLIC_KEY_BYTES: usize = PARAM_PK_BYTES;
pub const SIGNATURE_BYTES:  usize = PARAM_SIG_BYTES;
pub const C_TILDE_BYTES:    usize = PARAM_C_TILDE_BYTES;
pub const T1_BYTES_PER_POLY: usize = N * 10 / 8;            // 320 (same all levels)
pub const Z_BYTES_PER_POLY:  usize = N * Z_BITS_PER_COEF / 8;  // 576 (L1) / 640 (L3,L5)
pub const HINT_BYTES:        usize = OMEGA + K;             // ω + K, level-dependent

// Z-decode group structure: 4 coefs × Z_BITS_PER_COEF bits per group.
// L1: 4 × 18 = 72 bits = 9 bytes per group.
// L3/L5: 4 × 20 = 80 bits = 10 bytes per group.
const Z_BYTES_PER_GROUP: usize = 4 * Z_BITS_PER_COEF / 8;
const Z_GROUPS: usize = N / 4;  // 64 groups

/// Decode `pk_bytes` per FIPS 204 §3.5.4 pkDecode.
/// Returns `(rho, t1)` where `t1[k][i] ∈ [0, 2^10)`.
pub fn decode_pk(pk: &[u8]) -> Option<([u8; 32], Box<[[u32; N]; K]>)> {
    if pk.len() != PUBLIC_KEY_BYTES { return None; }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&pk[0..32]);

    let mut t1 = Box::new([[0u32; N]; K]);
    for k in 0..K {
        let off = 32 + k * T1_BYTES_PER_POLY;
        decode_t1_poly(&pk[off..off + T1_BYTES_PER_POLY], &mut t1[k]);
    }
    Some((rho, t1))
}

/// Decode `signature_bytes` per FIPS 204 §3.5.5 sigDecode.
/// Returns `(c_tilde, z, h)`.  `z[l][i]` is in canonical `[0, q)`
/// (lifted from the centred residue in `(−γ_1, γ_1]`).
pub fn decode_signature(sig: &[u8])
    -> Option<([u8; C_TILDE_BYTES], Box<[[u32; N]; L]>, Box<[[bool; N]; K]>)>
{
    if sig.len() != SIGNATURE_BYTES { return None; }

    let mut c_tilde = [0u8; C_TILDE_BYTES];
    c_tilde.copy_from_slice(&sig[0..C_TILDE_BYTES]);

    let z_off = C_TILDE_BYTES;
    let mut z = Box::new([[0u32; N]; L]);
    for l in 0..L {
        let off = z_off + l * Z_BYTES_PER_POLY;
        decode_z_poly(&sig[off..off + Z_BYTES_PER_POLY], &mut z[l]);
    }

    let h_off = z_off + L * Z_BYTES_PER_POLY;
    let h = decode_hint(&sig[h_off..h_off + HINT_BYTES])?;

    Some((c_tilde, z, h))
}

fn decode_t1_poly(packed: &[u8], out: &mut [u32; N]) {
    debug_assert_eq!(packed.len(), T1_BYTES_PER_POLY);
    // 4 coefficients × 10 bits = 40 bits = 5 bytes per group; 64 groups.
    for g in 0..64 {
        let c = &packed[g * 5..(g + 1) * 5];
        let bits: u64 = (c[0] as u64)
            | ((c[1] as u64) << 8)
            | ((c[2] as u64) << 16)
            | ((c[3] as u64) << 24)
            | ((c[4] as u64) << 32);
        for j in 0..4 {
            out[g * 4 + j] = ((bits >> (j * 10)) & 0x3FF) as u32;
        }
    }
}

fn decode_z_poly(packed: &[u8], out: &mut [u32; N]) {
    debug_assert_eq!(packed.len(), Z_BYTES_PER_POLY);
    // 4 coefficients × Z_BITS_PER_COEF bits per group; N/4 groups.
    // L1 (γ_1=2¹⁷): 4 × 18 = 72 bits = 9 bytes per group.
    // L3/L5 (γ_1=2¹⁹): 4 × 20 = 80 bits = 10 bytes per group.
    let mask: u32 = (1u32 << Z_BITS_PER_COEF) - 1;
    for g in 0..Z_GROUPS {
        let c = &packed[g * Z_BYTES_PER_GROUP..(g + 1) * Z_BYTES_PER_GROUP];
        let mut bits: u128 = 0;
        for i in 0..Z_BYTES_PER_GROUP {
            bits |= (c[i] as u128) << (i * 8);
        }
        for j in 0..4 {
            let raw = ((bits >> (j * Z_BITS_PER_COEF)) & (mask as u128)) as u32;
            // FIPS 204 §3.5.5 zDecode: z = γ_1 − raw  (centred residue),
            // then lift into [0, q).
            let z_signed = (GAMMA1 as i32) - (raw as i32);
            out[g * 4 + j] = if z_signed >= 0 {
                z_signed as u32
            } else {
                (z_signed + Q as i32) as u32
            };
        }
    }
}

fn decode_hint(packed: &[u8]) -> Option<Box<[[bool; N]; K]>> {
    // FIPS 204 §3.5.5 Algorithm 18 (hintBitUnpack).  Auto-adapts to
    // the active param set's ω: 80 (L1) / 55 (L3) / 75 (L5).
    debug_assert_eq!(packed.len(), HINT_BYTES);
    let mut h = Box::new([[false; N]; K]);
    let mut idx = 0usize;
    for k in 0..K {
        let upper = packed[OMEGA + k] as usize;
        if upper < idx || upper > OMEGA { return None; }
        let mut prev = -1i32;
        for i in idx..upper {
            let pos = packed[i] as i32;
            if pos <= prev { return None; }
            h[k][pos as usize] = true;
            prev = pos;
        }
        idx = upper;
    }
    for b in &packed[idx..OMEGA] {
        if *b != 0 { return None; }
    }
    Some(h)
}

/// Multiply each coefficient of `t1` by `2^D` (= 2^13).  Coefficients
/// are in `[0, 2^10)` so the result fits in 23 bits, well below q.
pub fn t1_times_2d(t1: &[[u32; N]; K]) -> Box<[[u32; N]; K]> {
    let mut out = Box::new([[0u32; N]; K]);
    for k in 0..K {
        for i in 0..N {
            out[k][i] = t1[k][i] << D;
        }
    }
    out
}

/// FIPS 204 §3.4 ExpandA + Algorithm 32.  Expands `ρ` into a
/// `K × L` matrix of polynomials in NTT domain via SHAKE-128 with
/// rejection sampling.
pub fn expand_a(rho: &[u8; 32]) -> Box<[[[u32; N]; L]; K]> {
    let mut a_hat = Box::new([[[0u32; N]; L]; K]);
    for r in 0..K {
        for c in 0..L {
            rej_ntt_poly(rho, c as u8, r as u8, &mut a_hat[r][c]);
        }
    }
    a_hat
}

fn rej_ntt_poly(rho: &[u8; 32], col: u8, row: u8, out: &mut [u32; N]) {
    let mut shake = Shake128::default();
    shake.update(rho);
    shake.update(&[col]);
    shake.update(&[row]);
    let mut reader = shake.finalize_xof();

    let mut ctr = 0usize;
    let mut buf = [0u8; 3];
    while ctr < N {
        reader.read(&mut buf);
        // Algorithm 14 CoeffFromThreeBytes.
        let b2 = buf[2] & 0x7F;
        let z = (b2 as u32) << 16 | (buf[1] as u32) << 8 | (buf[0] as u32);
        if z < Q {
            out[ctr] = z;
            ctr += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `decode_t1_poly` should round-trip values in `[0, 1024)` —
    /// reconstruct from a synthetic packed buffer and compare.
    #[test]
    fn t1_decode_round_trip_known_values() {
        let mut original = [0u32; N];
        for i in 0..N {
            original[i] = (i as u32 * 73) & 0x3FF;
        }
        let mut packed = [0u8; T1_BYTES_PER_POLY];
        for g in 0..64 {
            let mut bits: u64 = 0;
            for j in 0..4 {
                bits |= (original[g * 4 + j] as u64) << (j * 10);
            }
            for i in 0..5 {
                packed[g * 5 + i] = ((bits >> (i * 8)) & 0xFF) as u8;
            }
        }
        let mut decoded = [0u32; N];
        decode_t1_poly(&packed, &mut decoded);
        assert_eq!(decoded, original);
    }

    /// `decode_z_poly` should recover the centred residue lifted into
    /// `[0, q)`.  Test with values both inside and outside the
    /// positive range.
    #[test]
    fn z_decode_round_trip_known_values() {
        // Build z values in canonical [0, q) that come from
        // centred-residues in (−γ_1, γ_1].
        let mut original = [0u32; N];
        for i in 0..N {
            let signed: i32 = ((i as i32) - 100) * 31;  // mix of positive and negative
            original[i] = if signed >= 0 { signed as u32 } else { (signed + Q as i32) as u32 };
        }
        // Encode to packed form (auto-adapts to Z_BITS_PER_COEF and
        // Z_BYTES_PER_GROUP per active mldsa-N feature).
        let mut packed = vec![0u8; Z_BYTES_PER_POLY];
        let mask: u128 = (1u128 << Z_BITS_PER_COEF) - 1;
        for g in 0..Z_GROUPS {
            let mut bits: u128 = 0;
            for j in 0..4 {
                let z = original[g * 4 + j];
                let z_signed = if z > Q / 2 { (z as i64) - (Q as i64) } else { z as i64 };
                let raw = (GAMMA1 as i64) - z_signed;
                debug_assert!((0..=2 * GAMMA1 as i64).contains(&raw),
                    "test setup: z out of (-γ_1, γ_1]: {z_signed}");
                bits |= ((raw as u128) & mask) << (j * Z_BITS_PER_COEF);
            }
            for i in 0..Z_BYTES_PER_GROUP {
                packed[g * Z_BYTES_PER_GROUP + i] = ((bits >> (i * 8)) & 0xFF) as u8;
            }
        }
        let mut decoded = [0u32; N];
        decode_z_poly(&packed, &mut decoded);
        assert_eq!(decoded, original);
    }

    /// ExpandA must be deterministic in `ρ`: same input → identical
    /// matrix.  Different ρ → different matrix.
    #[test]
    fn expand_a_is_deterministic() {
        let rho = [0x42u8; 32];
        let a1 = expand_a(&rho);
        let a2 = expand_a(&rho);
        assert_eq!(*a1, *a2);
        let mut rho2 = rho;
        rho2[0] ^= 0xFF;
        let a3 = expand_a(&rho2);
        assert_ne!(*a1, *a3);
    }

    /// All `A_hat` coefficients must be in `[0, q)`.
    #[test]
    fn expand_a_outputs_canonical_zq() {
        let rho = [0x07u8; 32];
        let a = expand_a(&rho);
        for r in 0..K {
            for c in 0..L {
                for i in 0..N {
                    assert!(a[r][c][i] < Q,
                        "A_hat[{r}][{c}][{i}] = {} not in [0, {Q})", a[r][c][i]);
                }
            }
        }
    }

    /// `t1_times_2d` is a pure bit-shift; sanity-check.
    #[test]
    fn t1_times_2d_correct() {
        let mut t1 = Box::new([[0u32; N]; K]);
        for k in 0..K { for i in 0..N { t1[k][i] = (i as u32) & 0x3FF; } }
        let scaled = t1_times_2d(&t1);
        for k in 0..K {
            for i in 0..N {
                assert_eq!(scaled[k][i], t1[k][i] << D);
            }
        }
    }
}
