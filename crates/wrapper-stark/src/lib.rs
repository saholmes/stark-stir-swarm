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
//!
//! # Scope
//!
//! 1. [`verifier_air`]: verifier-as-AIR for the `deep_ali_merge` inner
//!    verification predicate, including FRI/STIR query checks and
//!    `binding_cells_commit` OOD evaluations.
//! 2. [`sha3_absorb_air`]: SHA-3 absorb sequence as an AIR (unavoidable
//!    cost — inner proof's Merkle paths are SHA-3-committed).
//! 3. [`prover`]: outer prover that runs the inner verifier inside the
//!    AIR and produces the wrapper STARK proof.
//! 4. [`verifier`]: outer verifier — checks only the wrapper proof.
//!
//! See `docs/wrapper-stark-design.md` (to be written) for the detailed AIR
//! layout, dual-hash wiring, and soundness audit checklist.

#![allow(dead_code)]
#![allow(clippy::module_inception)]

// Note: the crate has no default features so it compiles to an empty
// stub under `cargo check --workspace` (avoids Cargo feature-unification
// pulling in conflicting mldsa-* features on `deep_ali`).  Real
// implementation modules below MUST be `#[cfg(feature = "sha3-*")]`-gated
// once they reference deep_ali types that require those features.

/// Verifier-as-AIR for the `deep_ali_merge` inner verification predicate.
///
/// Encodes:
/// - Constraint composition evaluation at FRI/STIR query points
/// - Merkle authentication path verification (delegates SHA-3 to
///   [`sha3_absorb_air`])
/// - `binding_cells_commit` OOD Schwartz-Zippel checks
/// - Permutation-argument consistency
/// - Fiat-Shamir transcript replay
pub mod verifier_air {
    // Module skeleton — implementation lands in subsequent commits.
}

/// SHA-3-as-AIR — minimal absorb-sequence AIR for verifying inner-proof
/// Merkle paths inside the wrapper.  This is the only place SHA-3-in-AIR
/// is unavoidable; dual-hash limits it to this subcircuit only.
pub mod sha3_absorb_air {
    // Module skeleton — implementation lands in subsequent commits.
}

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
pub const WRAPPER_STARK_SCAFFOLD_VERSION: &str = "0.0.1-scaffold";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scaffold_builds() {
        assert_eq!(WRAPPER_STARK_SCAFFOLD_VERSION, "0.0.1-scaffold");
    }
}
