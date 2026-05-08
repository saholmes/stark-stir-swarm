//! `SampleInBall` — FIPS 204 §3.7 Algorithm 23.
//!
//! Hashes a 32-byte challenge digest `c̃` into a sparse polynomial
//! `c` ∈ R_q with exactly `τ` coefficients in {±1} and the rest
//! zero (τ = 39 for ML-DSA-44).  Uses SHAKE-256 with rejection
//! sampling for the position selection.
//!
//! Reference for the AIR.  The in-circuit version requires
//! `keccak_f1600_air` orchestration: SHAKE-256 absorbs `c̃` (32 B)
//! and squeezes one byte at a time, with rejection logic on each
//! squeezed byte.  Implementing that in-circuit is left for a
//! follow-up; the v1 verify AIR treats `c` as a public input and
//! the verifier recomputes it natively from `c̃`.

#![allow(dead_code)]

use crate::ml_dsa::params::{C_TILDE_BYTES, N, TAU};

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

/// Output of SampleInBall: a polynomial in R_q with exactly τ
/// non-zero coefficients in {q-1, 1} (the centred ±1).  We
/// represent it as `[u32; N]` with values in {0, 1, q−1}.
pub fn sample_in_ball(c_tilde: &[u8; C_TILDE_BYTES]) -> [u32; N] {
    use crate::ml_dsa::params::Q;

    let mut shake = Shake256::default();
    shake.update(c_tilde);
    let mut reader = shake.finalize_xof();

    // Read 8 bytes for the sign mask (lowest TAU bits used).
    let mut sign_buf = [0u8; 8];
    reader.read(&mut sign_buf);
    let mut signs = u64::from_le_bytes(sign_buf);

    let mut c = [0u32; N];
    for i in (N - TAU)..N {
        // Rejection sampling: read bytes until we get one ≤ i.
        let j = loop {
            let mut byte = [0u8; 1];
            reader.read(&mut byte);
            let b = byte[0] as usize;
            if b <= i { break b; }
        };
        c[i] = c[j];
        c[j] = if signs & 1 == 0 { 1 } else { Q - 1 };
        signs >>= 1;
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::Q;

    /// SampleInBall produces exactly τ non-zero coefficients,
    /// each ±1 (lifted into Z_q as 1 or q − 1).
    #[test]
    fn output_has_exactly_tau_nonzero_pm1() {
        let c_tilde = [0x42u8; C_TILDE_BYTES];
        let c = sample_in_ball(&c_tilde);
        let nonzero: Vec<u32> = c.iter().copied().filter(|&v| v != 0).collect();
        assert_eq!(nonzero.len(), TAU);
        for &v in &nonzero {
            assert!(v == 1 || v == Q - 1, "non-±1 coefficient: {v}");
        }
    }

    /// Same input ⇒ same output; different input ⇒ (with overwhelming
    /// probability) different output.
    #[test]
    fn deterministic_on_input() {
        let c_tilde = [0x07u8; C_TILDE_BYTES];
        let a = sample_in_ball(&c_tilde);
        let b = sample_in_ball(&c_tilde);
        assert_eq!(a, b);

        let mut other = c_tilde;
        other[0] ^= 0xFF;
        let d = sample_in_ball(&other);
        assert_ne!(a, d);
    }
}
