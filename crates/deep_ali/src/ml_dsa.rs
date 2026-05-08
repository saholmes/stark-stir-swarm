//! ML-DSA-44 native reference implementation (FIPS 204).
//!
//! Out-of-circuit verifier matching FIPS 204 §3 Algorithm~3.  Used as
//! the reference against which the in-circuit AIR (this module's
//! sibling files: `ml_dsa_field_air`, `ml_dsa_ntt_air`,
//! `keccak_f1600_air`, `ml_dsa_verify_air`) is validated.
//!
//! Mirrors the pattern used for `rsa2048.rs` (RSA-PKCS#1 v1.5 native
//! verifier) and `ed25519_verify.rs` (Ed25519 native verifier).
//!
//! For the demo's signing/keygen we reuse the upstream `ml-dsa` crate
//! (RustCrypto, FIPS 204 conformant) at the
//! `mmiyc_server::ml_dsa` layer.  This module is purely the
//! *constraint-targeting* native reference used by AIR tests.

#![allow(non_snake_case, non_upper_case_globals)]
#![allow(dead_code)]

/// FIPS 204 §4 Table 1 parameters for ML-DSA-44 (security category 2).
pub mod params {
    /// Modulus q = 2^23 - 2^13 + 1.
    pub const Q: u32 = 8_380_417;
    /// Polynomial degree (R_q = Z_q[X] / (X^N + 1)).
    pub const N: usize = 256;
    /// Module rank — number of polynomials in the response vector z.
    pub const L: usize = 4;
    /// Module dimension — number of polynomials in t1 / w.
    pub const K: usize = 4;
    /// Bound on s1, s2 coefficients.
    pub const ETA: i32 = 2;
    /// Number of ±1 entries in the challenge polynomial c.
    pub const TAU: usize = 39;
    /// Bound β = τ · η used in z's norm check.
    pub const BETA: i32 = (TAU as i32) * ETA; // 78
    /// γ_1 = 2^17 (response masking range).
    pub const GAMMA1: u32 = 1 << 17;
    /// γ_2 = (q − 1) / 88.
    pub const GAMMA2: u32 = (Q - 1) / 88;
    /// Hint Hamming-weight bound.
    pub const OMEGA: usize = 80;
    /// Low-bits drop in t.
    pub const D: u32 = 13;

    /// Size of the encoded public key (FIPS 204 §3.5 Table 1).
    pub const PUBLIC_KEY_BYTES: usize = 1_312;
    /// Size of the encoded signing key.
    pub const SIGNING_KEY_BYTES: usize = 2_560;
    /// Size of the encoded signature.
    pub const SIGNATURE_BYTES: usize = 2_420;
}

/// 256-coefficient polynomial in Z_q.  Coefficients are stored
/// canonically in [0, q).  Hidden behind a struct so we can switch
/// to NTT-domain or Montgomery-form internal representations
/// without churning callers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolyZq {
    pub coeffs: [u32; params::N],
}

impl PolyZq {
    pub const fn zero() -> Self {
        Self { coeffs: [0u32; params::N] }
    }
}

// TODO (phase 6): native verify implementation.  Mirror FIPS 204 §3
// Algorithm 3 step-by-step.  Defer until the supporting AIRs are in
// place — we cross-validate by running native + AIR on the same
// inputs and comparing every intermediate trace cell.
