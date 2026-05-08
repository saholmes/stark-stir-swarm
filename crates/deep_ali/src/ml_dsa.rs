//! ML-DSA native reference implementation (FIPS 204).
//!
//! Out-of-circuit verifier matching FIPS 204 §3 Algorithm 3.  Used as
//! the reference against which the in-circuit AIR (this module's
//! sibling files: `ml_dsa_field_air`, `ml_dsa_ntt_air`,
//! `keccak_f1600_air`, `ml_dsa_verify_air`, etc.) is validated.
//!
//! ## Multi-level support (Cargo features)
//!
//! Exactly one of the mutually-exclusive features `mldsa-44`,
//! `mldsa-65`, `mldsa-87` must be enabled.  These select the FIPS
//! 204 §4 Table 1 parameter set:
//!
//! | Feature   | Scheme     | NIST PQ Level | λ_sig | K | L | τ  | β   | γ_1   | γ_2/q-shift | ω  | c̃ B | pk B | sig B |
//! |-----------|------------|---------------|-------|---|---|----|----|-------|-------------|----|------|------|-------|
//! | mldsa-44  | ML-DSA-44  | 1             | 128   | 4 | 4 | 39 | 78  | 2¹⁷   | (q-1)/88   | 80 | 32   | 1312 | 2420 |
//! | mldsa-65  | ML-DSA-65  | 3             | 192   | 6 | 5 | 49 | 196 | 2¹⁹   | (q-1)/32   | 55 | 48   | 1952 | 3293 |
//! | mldsa-87  | ML-DSA-87  | 5             | 256   | 8 | 7 | 60 | 120 | 2¹⁹   | (q-1)/32   | 75 | 64   | 2592 | 4627 |
//!
//! The STARK calibration is independent: pair with `sha3-256` /
//! `sha3-384` / `sha3-512` plus the matching unconditional Johnson-
//! regime query count (r = 54 / 79 / 105) for Levels 1 / 3 / 5.
//! The STARK level may exceed the signature level (over-provisioning
//! is fine; under-provisioning leaves the gate sig-bottlenecked
//! below STARK soundness, which is unsafe to claim as Level k).

#![allow(non_snake_case, non_upper_case_globals)]
#![allow(dead_code)]

// ─── Compile-time mutual exclusion ───────────────────────────────────

#[cfg(all(feature = "mldsa-44", feature = "mldsa-65"))]
compile_error!("Cannot enable both `mldsa-44` and `mldsa-65` features simultaneously");
#[cfg(all(feature = "mldsa-44", feature = "mldsa-87"))]
compile_error!("Cannot enable both `mldsa-44` and `mldsa-87` features simultaneously");
#[cfg(all(feature = "mldsa-65", feature = "mldsa-87"))]
compile_error!("Cannot enable both `mldsa-65` and `mldsa-87` features simultaneously");
#[cfg(not(any(feature = "mldsa-44", feature = "mldsa-65", feature = "mldsa-87")))]
compile_error!("Must enable exactly one of `mldsa-44`, `mldsa-65`, `mldsa-87` features");

// ─── STARK-level ≥ signature-level compile-time constraint ───────────
//
// Calibrating the STARK below the signature scheme leaves the gate
// "STARK-bottlenecked" at a lower bit-strength than the sig the
// gate purports to certify.  Enforce STARK ≥ sig at compile time.

#[cfg(all(feature = "sha3-256", feature = "mldsa-65"))]
compile_error!(
    "STARK at Level 1 (sha3-256, λ_col=128) cannot back ML-DSA-65 (Level 3, λ_sig=192). \
     Enable `sha3-384` (or higher) for the deep_ali dep."
);
#[cfg(all(feature = "sha3-256", feature = "mldsa-87"))]
compile_error!(
    "STARK at Level 1 (sha3-256, λ_col=128) cannot back ML-DSA-87 (Level 5, λ_sig=256). \
     Enable `sha3-512` for the deep_ali dep."
);
#[cfg(all(feature = "sha3-384", feature = "mldsa-87"))]
compile_error!(
    "STARK at Level 3 (sha3-384, λ_col=192) cannot back ML-DSA-87 (Level 5, λ_sig=256). \
     Enable `sha3-512` for the deep_ali dep."
);

/// FIPS 204 §4 Table 1 parameters.  The active set is selected by
/// the `mldsa-44` / `mldsa-65` / `mldsa-87` Cargo features.
pub mod params {
    /// Modulus q = 2^23 − 2^13 + 1.  Same across all three parameter sets.
    pub const Q: u32 = 8_380_417;
    /// Polynomial degree (R_q = Z_q[X] / (X^N + 1)).  Same.
    pub const N: usize = 256;
    /// Low-bits drop in t.  Same.
    pub const D: u32 = 13;

    // ── Per-parameter-set values (cfg-conditional) ─────────────────

    #[cfg(feature = "mldsa-44")]
    pub const L: usize = 4;
    #[cfg(feature = "mldsa-65")]
    pub const L: usize = 5;
    #[cfg(feature = "mldsa-87")]
    pub const L: usize = 7;

    #[cfg(feature = "mldsa-44")]
    pub const K: usize = 4;
    #[cfg(feature = "mldsa-65")]
    pub const K: usize = 6;
    #[cfg(feature = "mldsa-87")]
    pub const K: usize = 8;

    /// Bound on s1, s2 coefficients.
    #[cfg(feature = "mldsa-44")]
    pub const ETA: i32 = 2;
    #[cfg(feature = "mldsa-65")]
    pub const ETA: i32 = 4;
    #[cfg(feature = "mldsa-87")]
    pub const ETA: i32 = 2;

    /// Number of ±1 entries in the challenge polynomial c.
    #[cfg(feature = "mldsa-44")]
    pub const TAU: usize = 39;
    #[cfg(feature = "mldsa-65")]
    pub const TAU: usize = 49;
    #[cfg(feature = "mldsa-87")]
    pub const TAU: usize = 60;

    /// Bound β = τ · η used in z's norm check.
    pub const BETA: i32 = (TAU as i32) * ETA;

    /// γ_1 (response masking range).  ML-DSA-44 = 2^17, ML-DSA-65/87 = 2^19.
    #[cfg(feature = "mldsa-44")]
    pub const GAMMA1: u32 = 1 << 17;
    #[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
    pub const GAMMA1: u32 = 1 << 19;

    /// γ_2 = (q − 1) / γ_2_DIV.  ML-DSA-44 uses /88; ML-DSA-65/87 use /32.
    #[cfg(feature = "mldsa-44")]
    pub const GAMMA2_DIV: u32 = 88;
    #[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
    pub const GAMMA2_DIV: u32 = 32;
    pub const GAMMA2: u32 = (Q - 1) / GAMMA2_DIV;

    /// Hint Hamming-weight bound.
    #[cfg(feature = "mldsa-44")]
    pub const OMEGA: usize = 80;
    #[cfg(feature = "mldsa-65")]
    pub const OMEGA: usize = 55;
    #[cfg(feature = "mldsa-87")]
    pub const OMEGA: usize = 75;

    /// c̃ length in bytes (= λ_sig / 4 = 2 · λ_sig / 8).  ML-DSA-44 = 32,
    /// ML-DSA-65 = 48, ML-DSA-87 = 64.
    #[cfg(feature = "mldsa-44")]
    pub const C_TILDE_BYTES: usize = 32;
    #[cfg(feature = "mldsa-65")]
    pub const C_TILDE_BYTES: usize = 48;
    #[cfg(feature = "mldsa-87")]
    pub const C_TILDE_BYTES: usize = 64;

    /// Size of the encoded public key (FIPS 204 §3.5 Table 1).
    #[cfg(feature = "mldsa-44")]
    pub const PUBLIC_KEY_BYTES: usize = 1_312;
    #[cfg(feature = "mldsa-65")]
    pub const PUBLIC_KEY_BYTES: usize = 1_952;
    #[cfg(feature = "mldsa-87")]
    pub const PUBLIC_KEY_BYTES: usize = 2_592;

    /// Size of the encoded signing key.
    #[cfg(feature = "mldsa-44")]
    pub const SIGNING_KEY_BYTES: usize = 2_560;
    #[cfg(feature = "mldsa-65")]
    pub const SIGNING_KEY_BYTES: usize = 4_032;
    #[cfg(feature = "mldsa-87")]
    pub const SIGNING_KEY_BYTES: usize = 4_896;

    /// Size of the encoded signature (FIPS 204 §3.5.5 sigEncode).
    /// Verified against rustcrypto ml-dsa crate.
    #[cfg(feature = "mldsa-44")]
    pub const SIGNATURE_BYTES: usize = 2_420;
    #[cfg(feature = "mldsa-65")]
    pub const SIGNATURE_BYTES: usize = 3_309;
    #[cfg(feature = "mldsa-87")]
    pub const SIGNATURE_BYTES: usize = 4_627;

    /// Bits per coefficient in z encoding: bitlen(2γ_1) = 18 for L1
    /// (γ_1=2¹⁷), 20 for L3/L5 (γ_1=2¹⁹).
    #[cfg(feature = "mldsa-44")]
    pub const Z_BITS_PER_COEF: usize = 18;
    #[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
    pub const Z_BITS_PER_COEF: usize = 20;

    /// Bits per coefficient in w1Encode (FIPS 204 §3.5.7 BitPack):
    /// bitlen(m − 1) where m = (q−1)/(2γ_2).
    /// L1: m = 44 ⇒ 6 bits.  L3/L5: m = 16 ⇒ 4 bits.
    #[cfg(feature = "mldsa-44")]
    pub const W1_BITS_PER_COEF: usize = 6;
    #[cfg(any(feature = "mldsa-65", feature = "mldsa-87"))]
    pub const W1_BITS_PER_COEF: usize = 4;

    /// NIST PQ level of this parameter set (for runtime introspection).
    #[cfg(feature = "mldsa-44")]
    pub const NIST_LEVEL: u8 = 1;
    #[cfg(feature = "mldsa-65")]
    pub const NIST_LEVEL: u8 = 3;
    #[cfg(feature = "mldsa-87")]
    pub const NIST_LEVEL: u8 = 5;

    /// Human-readable name of the active parameter set.
    #[cfg(feature = "mldsa-44")]
    pub const SCHEME_NAME: &str = "ML-DSA-44";
    #[cfg(feature = "mldsa-65")]
    pub const SCHEME_NAME: &str = "ML-DSA-65";
    #[cfg(feature = "mldsa-87")]
    pub const SCHEME_NAME: &str = "ML-DSA-87";
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
