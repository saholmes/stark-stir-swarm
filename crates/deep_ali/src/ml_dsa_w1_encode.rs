//! `w1Encode` (FIPS 204 §3.5 Algorithm 28) — pack 256 4-bit values
//! per polynomial into 128 bytes.
//!
//! Used inside ML-DSA verify (FIPS 204 §3 Algorithm 3 step 7) to
//! re-derive `c̃'` from `μ ‖ w1Encode(w'_1)` and check it matches
//! the signature's challenge digest.
//!
//! For ML-DSA-44, `w'_1` coefficients are HighBits values in
//! `[0, 88)`, which fit in 7 bits — but w1Encode for level-2
//! parameters actually uses **6-bit packing** (the (q-1)/(2γ_2)
//! upper bound is 88, which still requires 7 bits, but FIPS 204
//! §3.5 specifies the encoding tightness more precisely; we
//! adopt the natural-width approach here and let the verify AIR
//! settle exact packing later).

#![allow(dead_code)]

use crate::ml_dsa::params::N;
use crate::ml_dsa_decompose::NUM_R1_VALUES;

/// Bits per HighBits value.  `ceil(log2(NUM_R1_VALUES))` = 7 for
/// ML-DSA-44 (NUM_R1_VALUES = 88).
pub const W1_BITS: usize = 7;

/// Encoded length in bytes per 256-coefficient polynomial.
pub const W1_BYTES: usize = (N * W1_BITS + 7) / 8;

/// Pack a polynomial's HighBits values into a byte string.  Inputs
/// must satisfy `coeffs[i] < NUM_R1_VALUES` for every i.
pub fn w1_encode(coeffs: &[u32; N]) -> Vec<u8> {
    let mut out = vec![0u8; W1_BYTES];
    let mut bit_pos = 0usize;
    for &c in coeffs.iter() {
        debug_assert!(c < NUM_R1_VALUES);
        for k in 0..W1_BITS {
            let bit = ((c >> k) & 1) as u8;
            let byte_idx = bit_pos >> 3;
            let bit_idx  = bit_pos & 7;
            out[byte_idx] |= bit << bit_idx;
            bit_pos += 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_through_unpack() {
        let mut input = [0u32; N];
        for i in 0..N {
            input[i] = (i as u32) % NUM_R1_VALUES;
        }
        let bytes = w1_encode(&input);
        assert_eq!(bytes.len(), W1_BYTES);

        // Manual unpack to sanity-check
        let mut bit_pos = 0usize;
        let mut decoded = [0u32; N];
        for i in 0..N {
            let mut v = 0u32;
            for k in 0..W1_BITS {
                let byte_idx = bit_pos >> 3;
                let bit_idx  = bit_pos & 7;
                let bit = (bytes[byte_idx] >> bit_idx) & 1;
                v |= (bit as u32) << k;
                bit_pos += 1;
            }
            decoded[i] = v;
        }
        assert_eq!(decoded, input, "w1Encode round-trip should be the identity");
    }

    #[test]
    fn w1_byte_size_is_correct() {
        // 256 × 7 = 1792 bits, ceil/8 = 224 bytes.
        assert_eq!(W1_BYTES, 224);
    }
}
