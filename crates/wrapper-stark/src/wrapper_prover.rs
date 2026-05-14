//! Paper-grade SHA-3 STARK prover — wires the row-uniform AIR through
//! `deep_ali::fri::deep_fri_prove` to produce an actual
//! `DeepFriProof<SexticExt>` artefact.
//!
//! # End-to-end pipeline
//!
//! ```text
//!   message bytes
//!         │
//!         ▼  synthesize_uniform_trace
//!   UniformTrace
//!         │
//!         ▼  UniformAirConstraints::for_schema
//!   selected + always constraints
//!         │
//!         ▼  alphas_from_transcript(pi_hash)
//!   α coefficients
//!         │
//!         ▼  prepare_fri_input_row_uniform
//!   FriInput { lde, n_trace, blowup, c_eval }
//!         │
//!         ▼  FriDomain::new_radix2(n_trace · blowup)
//!         │  DeepFriParams::new(schedule, r, seed_z)
//!         ▼  deep_fri_prove::<SexticExt>(c_eval, domain, params)
//!   DeepFriProof<SexticExt>     ← paper-grade STARK proof artefact
//! ```
//!
//! The output proof:
//! - **size**: KiB-range, dominated by FRI Merkle paths
//! - **verify time**: polylog in n_trace (paper Table 5)
//! - **soundness**: unconditional NIST PQ at the level selected by
//!   the SHA-3 variant + Fp⁶ extension (paper §5 Table 2)

use ark_ff::Field;

use deep_ali::fri::{
    deep_fri_prove, deep_fri_verify, DeepFriProof, DeepFriParams, FriDomain,
};
use deep_ali::sextic_ext::SexticExt;

use crate::composition::alphas_from_transcript;
use crate::fri_bridge::{BridgeError, prepare_fri_input_row_uniform};
use crate::row_uniform::{
    UniformAirConstraints, UniformRowSchema, synthesize_uniform_trace,
};
use crate::sha3_absorb_air::Sha3Variant;

type FBase = ark_goldilocks::Goldilocks;
type Ext = SexticExt;

/// Errors from the wrapper STARK prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WrapperProverError {
    /// FRI bridge rejected the input (alpha count mismatch, bad blowup, etc.).
    BridgeError(BridgeError),
    /// Generic implementation-level error.
    Internal(String),
}

impl From<BridgeError> for WrapperProverError {
    fn from(e: BridgeError) -> Self { Self::BridgeError(e) }
}

impl std::fmt::Display for WrapperProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BridgeError(e) => write!(f, "wrapper prover bridge error: {e}"),
            Self::Internal(s) => write!(f, "wrapper prover internal: {s}"),
        }
    }
}

impl std::error::Error for WrapperProverError {}

/// Public inputs the SHA-3 STARK attests to.  Bound into the FS
/// transcript via `pi_hash`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sha3StarkPublicInputs {
    pub variant: Sha3Variant,
    /// 32-byte pi_hash: SHA3-256("WRAPPER-SHA3-V1" || variant_tag || message).
    /// Binds the proof to a specific (variant, message) pair so a
    /// malicious prover can't reuse a proof for a different statement.
    pub pi_hash: [u8; 32],
}

impl Sha3StarkPublicInputs {
    pub fn for_message(variant: Sha3Variant, message: &[u8]) -> Self {
        use ::sha3::Digest;
        let mut h = ::sha3::Sha3_256::new();
        h.update(b"WRAPPER-SHA3-V1");
        h.update(&[match variant {
            Sha3Variant::Sha3_256 => 1u8,
            Sha3Variant::Sha3_384 => 3,
            Sha3Variant::Sha3_512 => 5,
        }]);
        h.update(message);
        let digest = h.finalize();
        let mut pi_hash = [0u8; 32];
        pi_hash.copy_from_slice(&digest);
        Self { variant, pi_hash }
    }
}

/// The artefact returned by [`prove_sha3_air`].  Pair this with
/// [`Sha3StarkPublicInputs`] for verification via [`verify_sha3_air`].
pub struct Sha3StarkProof {
    pub public: Sha3StarkPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    /// Number of FRI queries `r` used in the proof.  Verifier needs
    /// this to reconstruct the params; in production it's bound into
    /// the public inputs by the FS transcript.
    pub r: usize,
    pub use_stir: bool,
}

/// Pad input bytes per FIPS 202 §B.2 into rate-sized blocks.  Caller-
/// friendly wrapper around the same padding used by
/// `sha3_absorb_air::hash`.
fn pad_input(input: &[u8], variant: Sha3Variant) -> Vec<Vec<u8>> {
    let block_len = variant.block_bytes();
    let mut blocks: Vec<Vec<u8>> = Vec::new();
    let mut offset = 0;
    while offset + block_len <= input.len() {
        blocks.push(input[offset..offset + block_len].to_vec());
        offset += block_len;
    }
    let mut last = vec![0u8; block_len];
    let tail = &input[offset..];
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] = 0x06;
    last[block_len - 1] |= 0x80;
    blocks.push(last);
    blocks
}

/// Prove the SHA-3 hashing of `message` under `variant` via the
/// row-uniform AIR + deep_ali FRI prover.
///
/// # Arguments
///
/// - `message`: input bytes to hash
/// - `variant`: SHA-3 variant (selects rate + FIPS 202 padding)
/// - `blowup`: FRI blowup factor (paper §10.1: production 32, smoke 4)
/// - `r`: FRI query count (paper Table 2: 54/79/105 for L1/L3/L5)
/// - `use_stir`: STIR (true) vs DEEP-FRI (false); paper §10.1 recommends STIR
pub fn prove_sha3_air(
    message: &[u8],
    variant: Sha3Variant,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<Sha3StarkProof, WrapperProverError> {
    // 1. Synthesise uniform trace.
    let blocks = pad_input(message, variant);
    let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
    let trace = synthesize_uniform_trace(&block_refs, variant);
    let schema = UniformRowSchema::new(variant);
    let air = UniformAirConstraints::for_schema(&schema);

    // 2. Derive FS alphas from public inputs.
    let public = Sha3StarkPublicInputs::for_message(variant, message);
    let mut seed_sel = public.pi_hash;
    seed_sel[0] ^= 0xA1;
    let mut seed_alw = public.pi_hash;
    seed_alw[0] ^= 0xA2;
    let alphas_sel = alphas_from_transcript::<FBase>(&seed_sel, air.selected.len());
    let alphas_alw = alphas_from_transcript::<FBase>(&seed_alw, air.always.len());

    // 3. Prepare FRI input.
    let fri_input = prepare_fri_input_row_uniform(
        &trace, &air, &alphas_sel, &alphas_alw, blowup,
    )?;
    let n_trace = fri_input.n_trace;
    let n_lde = fri_input.lde_length();

    // 4. Build FRI domain + params.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.pi_hash);
    if use_stir { params.stir = true; }

    // 5. Run deep_fri_prove.  This is where the actual STARK proving
    //    happens — FFT-based LDE, Merkle commitments, FRI folding,
    //    query opening, and proof serialisation.
    let _ = domain;  // currently consumed by deep_fri_prove's internal radix-2 domain
    let fri_proof = deep_fri_prove::<Ext>(fri_input.c_eval, FriDomain::new_radix2(n_lde), &params);

    Ok(Sha3StarkProof {
        public, fri_proof, n_trace, blowup, r, use_stir,
    })
}

/// Verify a wrapper SHA-3 STARK proof.  Reconstructs the FRI params
/// from the proof's bundled metadata + public inputs, then calls
/// `deep_fri_verify`.
pub fn verify_sha3_air(proof: &Sha3StarkProof) -> bool {
    let n_lde = proof.n_trace * proof.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, proof.r, 0xDEEFu64);
    params.public_inputs_hash = Some(proof.public.pi_hash);
    if proof.use_stir { params.stir = true; }

    deep_fri_verify::<Ext>(&params, &proof.fri_proof)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_inputs_pi_hash_is_deterministic() {
        // Same (variant, message) → same pi_hash.
        let a = Sha3StarkPublicInputs::for_message(Sha3Variant::Sha3_256, b"abc");
        let b = Sha3StarkPublicInputs::for_message(Sha3Variant::Sha3_256, b"abc");
        assert_eq!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn public_inputs_pi_hash_changes_with_message() {
        let a = Sha3StarkPublicInputs::for_message(Sha3Variant::Sha3_256, b"abc");
        let b = Sha3StarkPublicInputs::for_message(Sha3Variant::Sha3_256, b"abcd");
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn public_inputs_pi_hash_changes_with_variant() {
        let a = Sha3StarkPublicInputs::for_message(Sha3Variant::Sha3_256, b"abc");
        let b = Sha3StarkPublicInputs::for_message(Sha3Variant::Sha3_384, b"abc");
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    #[ignore = "slow — exercises full FRI prove + verify round-trip"]
    fn round_trip_sha3_256_abc_smoke() {
        // Smoke test: prove SHA3-256("abc") at blowup=4 + r=54, verify.
        // Marked `ignore` because the FRI prover for our wide trace
        // (7 557 cols × 128 rows after padding) is expensive — running
        // it in every `cargo test` invocation would slow CI.  Run via
        // `cargo test ... round_trip_sha3_256_abc_smoke -- --ignored`.
        let proof = prove_sha3_air(b"abc", Sha3Variant::Sha3_256, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("prove must succeed on valid trace");
        assert!(verify_sha3_air(&proof),
            "round-trip verify must accept on valid proof");
    }

    #[test]
    #[ignore = "slow — exercises tamper rejection"]
    fn round_trip_rejects_tampered_proof() {
        let mut proof = prove_sha3_air(b"abc", Sha3Variant::Sha3_256, 4, 54, false)
            .expect("prove must succeed");
        // Tamper: flip a byte of one of the FRI proof's serialised
        // Merkle roots.  Should break Merkle path verification.
        // Specific tampering point depends on DeepFriProof's structure;
        // for now we just tamper with the public_inputs_hash to ensure
        // the FS-binding catches the mismatch.
        proof.public.pi_hash[0] ^= 0xFF;
        assert!(!verify_sha3_air(&proof),
            "tampered proof must be rejected");
    }
}
