//! Recursive STARK wrapper for `deep_ali_merge` proofs.
//!
//! # Purpose
//!
//! Take a "fat" inner STARK proof (e.g. our modular ML-DSA-65 v2 proof at
//! ~18 MiB / 154 ms verify) and produce a "skinny" outer proof
//! (~200-500 KiB / ~5-15 ms verify) by expressing the inner verifier as
//! an AIR and proving its acceptance inside a single outer FRI/STIR STARK.
//!
//! End-to-end soundness story (paper §8 + Theorem 6):
//!
//! - **Inner**:           unconditional NIST PQ L1/L3/L5 via SHA-3 CR + FRI IT
//! - **Wrapper prover**:  Poseidon-internal Merkle (cheap to express as
//!                        polynomial constraints, ~300 vs ~5000 for SHA-3)
//! - **Wrapper verifier**: SHA-3-only commitments (FIPS 202, CMVP-validatable)
//! - **Composed**:        unconditional NIST PQ at the same level as inner
//!
//! # Status
//!
//! WIP on `feature/recursive-stark`.  Do not consume from `main` paths.
//!
//! The production stacked-AIR path (`crates/swarm-dns`) remains the
//! canonical STARK-DNS solution today; this wrapper is the per-signature
//! compression layer being engineered for future per-sig edge profile
//! parity with RSA-2048.

#![allow(dead_code)]
#![allow(clippy::module_inception)]

// Note: the crate has no default features so it compiles to an empty
// stub under `cargo check --workspace` (avoids Cargo feature-unification
// pulling in conflicting mldsa-* features on `deep_ali`).  Real
// implementation modules below MUST be `#[cfg(feature = "sha3-*")]`-gated
// once they reference deep_ali types that require those features.

// ─── Public API: types that pin the wrapper's contract ───────────────

/// The statement the wrapper STARK attests to: the inner proof's
/// `pi_hash` and `c_tilde_prime` are bound to a specific ML-DSA verify
/// invocation, i.e. there exists a valid witness for `ml_dsa_verify(pk,
/// msg, sig) → ACCEPT` whose Fiat-Shamir transcript hashes to `pi_hash`.
///
/// The cross-shape attestation pattern (future) requires the wrapper's
/// public inputs to be byte-identical across both AIR shapes (modular
/// and monolithic), so we keep the shape narrow: just the public-input
/// commitments + the level identifier.  Anything shape-specific stays
/// inside the wrapper proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrapperPublicInputs {
    /// SHA3-(256/384/512) of the FS-bound public input vector
    /// `(pk || mu || sig || c_tilde_prime || pp_vector)`.  Variable
    /// length to track the active SHA-3 variant.
    pub pi_hash: Vec<u8>,
    /// SHAKE256 challenge digest `c̃'` from the ML-DSA signature
    /// (FIPS 204 §8.3 / §Algorithm 8 output[0..C_TILDE_BYTES]).
    /// Bound into `pi_hash` and re-exported for direct verifier
    /// access (binding-wall analysis at FIPS 140-3 boundary).
    pub c_tilde_prime: Vec<u8>,
    /// NIST PQ Level this wrapper attests at: 1, 3, or 5.  Must equal
    /// the inner proof's level; composed soundness is min(inner, outer).
    pub nist_level: u8,
}

/// Wrapper STARK proof — opaque envelope around the outer FRI/STIR proof.
///
/// The internal representation is intentionally NOT exposed: this is
/// the FIPS-202 verifier-path artefact that downstream consumers
/// (edge resolvers, CMVP-validated modules) deserialise and pass to
/// [`verify`] without inspection.
#[derive(Clone, Debug)]
pub struct WrapperProof {
    /// Serialised outer FRI/STIR proof bytes.  Encoded with
    /// `ark_serialize::CanonicalSerialize` for cross-implementation
    /// portability.
    bytes: Vec<u8>,
    /// Public-input commitment header — duplicates `WrapperPublicInputs`
    /// for self-contained verifier dispatch.  Wire serialisation puts
    /// this before the proof body so verifiers can early-reject on
    /// level/pi_hash mismatch before parsing the FRI proof.
    public_header: WrapperPublicInputs,
}

impl WrapperProof {
    /// Size of the on-wire proof artefact (bytes).  Used for paper-grade
    /// reporting and bandwidth-budget enforcement.
    pub fn size_bytes(&self) -> usize {
        self.bytes.len() + self.public_header.pi_hash.len()
            + self.public_header.c_tilde_prime.len() + 1 /* nist_level */
    }

    /// Construct from raw bytes + header.  Used by the serialiser; do
    /// NOT construct ad-hoc in consumer code.
    pub fn from_parts(bytes: Vec<u8>, public_header: WrapperPublicInputs) -> Self {
        Self { bytes, public_header }
    }

    /// Read-only access to the serialised proof body.
    pub fn body_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Read-only access to the public-input header.
    pub fn public_header(&self) -> &WrapperPublicInputs {
        &self.public_header
    }
}

/// Parameters for the outer FRI/STIR proof: blowup, query count `r`,
/// folding schedule, hash family.  These are SEPARATE from the inner
/// proof's parameters — the wrapper has its own LDT instance.
///
/// Soundness target: must match the inner's NIST level.  Sanity-checked
/// in [`prove`] against `WrapperPublicInputs::nist_level`.
#[derive(Clone, Debug)]
pub struct WrapperParams {
    /// Outer LDT blowup factor.  Production: 32 (paper §10).
    pub blowup: usize,
    /// Outer query count `r`.  Production: 54/79/105 for L1/L3/L5
    /// (paper Table 2).
    pub num_queries: usize,
    /// Outer trace length `T` (rows).  Determined by the verifier-AIR
    /// trace builder — see `verifier_air::estimate_trace_length`.
    pub trace_length: usize,
    /// Whether to use STIR (`true`) or DEEP-FRI (`false`) as the outer
    /// LDT.  Production: STIR (paper §10.1, 2.2× faster prove + 4.4×
    /// smaller proof than FRI on Fibonacci L1).
    pub use_stir: bool,
}

impl WrapperParams {
    /// Default parameters for a given NIST level.  Paper §5 Table 2
    /// values.  Override via direct construction when calibrating.
    pub fn defaults_for_level(nist_level: u8) -> Self {
        let num_queries = match nist_level {
            1 => 54,
            3 => 79,
            5 => 105,
            _ => panic!("WrapperParams: unsupported NIST level {nist_level} (expected 1/3/5)"),
        };
        Self {
            blowup: 32,
            num_queries,
            // Placeholder trace length — real value set by
            // verifier_air::estimate_trace_length once the AIR layout
            // stabilises.  Used only for parameter-size sanity checks;
            // the prover sets the actual trace length from the inner
            // proof shape.
            trace_length: 1 << 20,
            use_stir: true,
        }
    }
}

/// Errors that can occur during wrapper proving.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WrapperError {
    /// Inner proof rejected by `verify_v2_real` — there is nothing
    /// valid to wrap.  The wrapper does NOT compress a false statement.
    InnerProofInvalid(String),
    /// `WrapperPublicInputs.nist_level` disagrees with the inner
    /// proof's level identifier or with `WrapperParams.num_queries`.
    LevelMismatch { public: u8, params_implied: u8 },
    /// Generic implementation-level failure during the wrapper-AIR
    /// trace synthesis or outer proof construction.  Implementation
    /// detail; consumers should treat as fatal.
    Internal(String),
    /// Wrapper STARK not yet implemented — returned by stubbed prove/
    /// verify until the verifier-AIR + outer prover land.
    NotImplemented(&'static str),
}

impl std::fmt::Display for WrapperError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InnerProofInvalid(msg) => write!(f, "inner proof invalid: {msg}"),
            Self::LevelMismatch { public, params_implied } => write!(
                f,
                "NIST level mismatch: public_inputs={public}, params imply level={params_implied}"
            ),
            Self::Internal(msg) => write!(f, "wrapper internal error: {msg}"),
            Self::NotImplemented(stage) => write!(f, "wrapper not yet implemented: {stage}"),
        }
    }
}

impl std::error::Error for WrapperError {}

// ─── Public functions: prove + verify ────────────────────────────────

/// Produce a wrapper STARK proof from a V2 inner proof.  Stub: returns
/// `WrapperError::NotImplemented` until the verifier-AIR + outer prover
/// land.
///
/// # Soundness contract
///
/// On success, the returned [`WrapperProof`] attests that there exists
/// a valid V2 inner proof whose `pi_hash` matches `public.pi_hash`.
/// The wrapper does NOT compress a false statement: if the inner proof
/// would fail `deep_ali::verify_v2_real`, this function returns
/// `WrapperError::InnerProofInvalid` immediately, without producing
/// a wrapper proof.
pub fn prove(
    inner_proof_bytes: &[u8],
    public: &WrapperPublicInputs,
    params: &WrapperParams,
) -> Result<WrapperProof, WrapperError> {
    let _ = (inner_proof_bytes, public, params);
    Err(WrapperError::NotImplemented(
        "wrapper prover (verifier_air + sha3_absorb_air + outer FRI/STIR not yet built)",
    ))
}

/// Verify a wrapper STARK proof against the given public inputs and
/// parameters.  Stub: returns `false` until the verifier impl lands.
///
/// # Soundness contract
///
/// Returns `true` iff the wrapper proof is well-formed AND its outer
/// FRI/STIR verify accepts AND the embedded public header matches
/// `public`.  Composed soundness is `min(inner, outer)` at the level
/// specified by `public.nist_level`.
pub fn verify(
    proof: &WrapperProof,
    public: &WrapperPublicInputs,
    params: &WrapperParams,
) -> bool {
    let _ = (proof, public, params);
    // Stub: returns false until verifier impl lands.  Tests should
    // call `verify` only via `assert!(!verify(...))` until the impl
    // exists, to catch accidental "works because stubbed" passes.
    false
}

// ─── Internal modules (skeletons) ────────────────────────────────────

pub mod verifier_air;
pub mod sha3_absorb_air;
pub mod bit_constraint;
pub mod keccak_round_air;
pub mod sponge_air;
pub mod composition;
pub mod fri_bridge;
pub mod sha3_stark;

/// Outer prover: runs the inner verifier inside the wrapper AIR and
/// produces the wrapper STARK proof.  Internal Merkle trees use
/// Poseidon (when `poseidon-accel` is enabled); final commitments and
/// the Fiat-Shamir transcript use SHA-3.
pub mod prover {
    // Module skeleton — implementation lands in subsequent commits.
}

/// Outer verifier: checks only the wrapper STARK proof.  No inner-proof
/// access required.  Verifier-path is pure SHA-3 for FIPS-202 alignment.
pub mod verifier {
    // Module skeleton — implementation lands in subsequent commits.
}

/// Smoke marker — ensures the crate compiles and is linked into the
/// workspace.  Removed once the real public API stabilizes.
pub const WRAPPER_STARK_SCAFFOLD_VERSION: &str = "0.0.2-api-contract";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scaffold_builds() {
        assert_eq!(WRAPPER_STARK_SCAFFOLD_VERSION, "0.0.2-api-contract");
    }

    #[test]
    fn wrapper_params_defaults() {
        let p1 = WrapperParams::defaults_for_level(1);
        assert_eq!(p1.num_queries, 54);
        assert_eq!(p1.blowup, 32);
        assert!(p1.use_stir);

        let p3 = WrapperParams::defaults_for_level(3);
        assert_eq!(p3.num_queries, 79);

        let p5 = WrapperParams::defaults_for_level(5);
        assert_eq!(p5.num_queries, 105);
    }

    #[test]
    #[should_panic(expected = "unsupported NIST level")]
    fn wrapper_params_rejects_invalid_level() {
        let _ = WrapperParams::defaults_for_level(2);
    }

    #[test]
    fn wrapper_public_inputs_roundtrip() {
        let pi = WrapperPublicInputs {
            pi_hash: vec![0xCA; 32],
            c_tilde_prime: vec![0x77; 48],
            nist_level: 3,
        };
        let cloned = pi.clone();
        assert_eq!(pi, cloned);
    }

    #[test]
    fn wrapper_proof_size_accounting() {
        let public_header = WrapperPublicInputs {
            pi_hash: vec![0; 32],
            c_tilde_prime: vec![0; 48],
            nist_level: 3,
        };
        let proof = WrapperProof::from_parts(vec![0xAB; 200_000], public_header);
        // 200K body + 32 pi_hash + 48 c_tilde_prime + 1 level byte
        assert_eq!(proof.size_bytes(), 200_000 + 32 + 48 + 1);
    }

    #[test]
    fn verifier_air_trace_length_is_power_of_two() {
        for level in [1u8, 3, 5] {
            let n = verifier_air::estimate_trace_length(level);
            assert!(n.is_power_of_two(), "level {level} rows={n}");
            // Sanity: trace fits in a reasonable memory budget.
            // Each row is `width` u64s; layout for L3 has width ~870.
            // L3 rows ≈ 2^18..2^20, so cells ≈ 256M, ~2 GiB at 8B each.
            // The budget will tighten significantly once the real
            // constraint set replaces conservative upper bounds.
            assert!(n <= 1 << 22, "level {level} trace too large: {n}");
        }
    }

    // ─── Stub-behaviour tests (must keep failing until impl lands) ──

    #[test]
    fn prove_stub_returns_not_implemented() {
        let public = WrapperPublicInputs {
            pi_hash: vec![0; 32],
            c_tilde_prime: vec![0; 48],
            nist_level: 3,
        };
        let params = WrapperParams::defaults_for_level(3);
        let result = prove(&[], &public, &params);
        assert!(matches!(result, Err(WrapperError::NotImplemented(_))));
    }

    #[test]
    fn verify_stub_returns_false() {
        let public = WrapperPublicInputs {
            pi_hash: vec![0; 32],
            c_tilde_prime: vec![0; 48],
            nist_level: 3,
        };
        let params = WrapperParams::defaults_for_level(3);
        let proof = WrapperProof::from_parts(vec![], public.clone());
        assert!(!verify(&proof, &public, &params));
    }
}
