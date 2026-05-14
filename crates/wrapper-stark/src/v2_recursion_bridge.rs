//! Bridge: extract real F2b OOD evaluations from a `V2ProofReal` into
//! Ext-typed OOD equality claims suitable for the recursive STARK
//! gadget's OOD sub-circuit.
//!
//! # Scope of this module
//!
//! Wires sub-circuit 2 (binding-cells OOD) of `recursive_prover` to
//! the real F2b OOD outputs of a v2 ML-DSA proof.  Replaces the
//! synthetic `OodEqualityClaim<Goldilocks>` test values with real
//! Ext-typed OOD claims extracted from a real `V2ProofReal`.
//!
//! In the current v2 proof shape (post 2026-05-10), F2b has seven
//! OOD-bound binding legs:
//!
//! | Leg  | f side                               | g side                                       |
//! |------|--------------------------------------|----------------------------------------------|
//! | L2a  | Decompose col_r1 BCC                 | UseHint COL_R1 BCC                           |
//! | L3   | UseHint COL_ADJUSTED_R1 BCC          | W1Encode col_r1 BCC                          |
//! | L2c  | UseHint COL_H BCC                    | canonical public.h trace col (verifier IFFT) |
//! | L5   | V17 EQ-region col l (×L+3) BCC       | canonical public.a/c/t1d/w_approx_ntt poly   |
//! | L1   | Decompose col_r BCC                  | canonical INTT(public.w_approx_ntt) poly     |
//! | L4   | W1Encode col_bit(b) BCC (×bits)      | canonical bit-b col extracted from w1bytes   |
//! | L2b  | UseHint COL_R0_SIGN BCC              | canonical translated r0_sign                 |
//!
//! L2a and L3 are **BCC-vs-BCC** — both sides have FRI commits and
//! their OOD values are directly comparable.  The other legs are
//! **BCC-vs-public**: one side is FRI-committed, the other is
//! evaluated canonically by the verifier from public inputs at the
//! same FS-derived z.
//!
//! This module currently extracts the two BCC-vs-BCC pairs (L2a, L3).
//! The public-input legs (L1/L2b/L2c/L4/L5) require IFFT'ing the
//! public values to polynomials and evaluating those at z, which is
//! a larger piece of work — left as a follow-up.
//!
//! # Ext-vs-base types
//!
//! Recursive_prover's existing `OodEqualityClaim<F: Field>` is
//! parameterised over `ark_ff::Field`; the v2 F2b OOD values live in
//! `SexticExt`, which implements deep_ali's `TowerField` trait (not
//! `ark_ff::Field`).  We mirror the equality-claim shape here with
//! Ext-typed types — same arithmetic surface (residue + check_native),
//! same `binding_tag` discriminator.  A future lift of the recursive
//! prover's OOD AIR to operate over `Ext` will plug these in directly.
//!
//! # Soundness story
//!
//! The two BCC-vs-BCC OOD checks are the **same** Schwartz-Zippel
//! binding the recursive STARK gadget's sub-circuit 2 attests in-AIR:
//!
//! ```text
//!     f(z) − g(z) == 0  ⇒  f ≡ g as polynomials of degree < d
//! ```
//!
//! with error ≤ d / |Ext|.  At Fp⁶ (L1/L3) and d ≈ 2¹⁴, the SZ error
//! is ≤ 2⁻³⁷⁰.  The recursive prover's OOD accumulator AIR composes
//! N such checks under FS-derived α and attests their joint
//! satisfaction with one outer FRI proof.

use ark_goldilocks::Goldilocks;

use deep_ali::binding_cells_commit::{BindingCellsCommit, extract_ood_value};
use deep_ali::ml_dsa_verify_air_v2_orchestration::V2ProofReal;
use deep_ali::sextic_ext::SexticExt;
use deep_ali::tower_field::TowerField;

use crate::composition::alphas_from_transcript;
use crate::deep_ali_verifier_air::binding_cells_ood_verifier::{
    OodClaimBundle, OodEqualityClaim,
};
use crate::recursive_prover::{
    OodAccumulatorClaim, OodAccumulatorProof, RecursiveProverError,
    prove_ood_accumulator,
};

type Ext = SexticExt;

/// Degree of SexticExt over Goldilocks.  Each Ext element decomposes
/// into this many base-field coordinates via `TowerField::to_fp_components`.
pub const EXT_DEGREE: usize = 6;

// Per-coordinate static binding-tag tables (one per Ext leg we extract).
// Used by `flatten_ext_to_base` to give each base-field sub-claim a
// distinct &'static str discriminator.
const COORD_TAGS_L2A: [&str; EXT_DEGREE] = [
    "L2a.c0", "L2a.c1", "L2a.c2", "L2a.c3", "L2a.c4", "L2a.c5",
];
const COORD_TAGS_L3: [&str; EXT_DEGREE] = [
    "L3.c0", "L3.c1", "L3.c2", "L3.c3", "L3.c4", "L3.c5",
];

/// Ext-typed OOD equality claim: an assertion that two polynomials
/// agree at the FS-derived OOD challenge point z.
///
/// In the v2 F2b OOD context, `f_at_z` and `g_at_z` are both
/// `fri_proof.fz_per_layer[0]` values extracted from each side's
/// `BindingCellsCommit` — bound to the same z_0 because both BCCs
/// share `pi_hash`, `seed_z`, and packed LDE size.
#[derive(Clone, Debug)]
pub struct ExtOodEqualityClaim {
    pub f_at_z: Ext,
    pub g_at_z: Ext,
    pub binding_tag: &'static str,
}

impl ExtOodEqualityClaim {
    /// Schwartz-Zippel residue at the FS-derived z.
    pub fn residue(&self) -> Ext { self.f_at_z - self.g_at_z }

    /// Native check — true iff the two FRI-committed polynomials
    /// agree at z (residue is zero).
    pub fn check_native(&self) -> bool {
        use ark_ff::Zero;
        self.residue().is_zero()
    }
}

/// Bundle of Ext-typed OOD equality claims extracted from one v2
/// proof.  Mirror of `OodClaimBundle<F>` from recursive_prover, but
/// over `SexticExt`.
#[derive(Clone, Debug)]
pub struct ExtOodClaimBundle {
    pub claims: Vec<ExtOodEqualityClaim>,
}

impl ExtOodClaimBundle {
    pub fn check_all_native(&self) -> bool {
        self.claims.iter().all(|c| c.check_native())
    }

    pub fn first_failing(&self) -> Option<usize> {
        self.claims.iter().position(|c| !c.check_native())
    }
}

/// Errors during F2b OOD extraction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum V2BridgeError {
    /// Failed to deserialize a BCC blob from the v2 proof.
    BccDeserialize(String),
    /// FRI proof inside a BCC didn't carry an OOD value at layer 0.
    OodExtractFailed(String),
}

impl std::fmt::Display for V2BridgeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BccDeserialize(s)  => write!(f, "v2 BCC deserialize: {s}"),
            Self::OodExtractFailed(s) => write!(f, "v2 OOD extract: {s}"),
        }
    }
}
impl std::error::Error for V2BridgeError {}

/// Pull a `BindingCellsCommit` out of a length-prefixed bytes blob.
fn deserialize_bcc(blob: &[u8], leg: &str) -> Result<BindingCellsCommit, V2BridgeError> {
    BindingCellsCommit::from_bytes(blob)
        .map_err(|e| V2BridgeError::BccDeserialize(format!("{leg}: {e}")))
}

/// Build one OOD-equality claim from a BCC-vs-BCC pair (L2a or L3).
///
/// Both BCCs in a pair are committed with the same `pi_hash`, `seed_z`,
/// and packed LDE size, so their FRI-internal z_0 challenges align
/// (paper-required precondition for the SZ binding via
/// `verify_ood_consistency`).  We don't re-derive z_0 here; the OOD
/// residue check is `f(z) == g(z)`, which is invariant under any
/// common z value bound to both commits.
fn extract_pair_claim(
    f_bcc_blob: &[u8],
    g_bcc_blob: &[u8],
    binding_tag: &'static str,
) -> Result<ExtOodEqualityClaim, V2BridgeError> {
    let f_bcc = deserialize_bcc(f_bcc_blob, binding_tag)?;
    let g_bcc = deserialize_bcc(g_bcc_blob, binding_tag)?;
    let f_at_z = extract_ood_value(&f_bcc)
        .map_err(|e| V2BridgeError::OodExtractFailed(format!("{binding_tag}.f: {e}")))?;
    let g_at_z = extract_ood_value(&g_bcc)
        .map_err(|e| V2BridgeError::OodExtractFailed(format!("{binding_tag}.g: {e}")))?;
    Ok(ExtOodEqualityClaim { f_at_z, g_at_z, binding_tag })
}

/// Extract the BCC-vs-BCC F2b OOD bundle from a `V2ProofReal`.
///
/// Returns an `ExtOodClaimBundle` with two claims:
///   - L2a:  Decompose col_r1  ↔  UseHint COL_R1
///   - L3:   UseHint COL_ADJUSTED_R1  ↔  W1Encode col_r1
///
/// Both claims hold on an honestly-proven v2 (i.e.
/// `bundle.check_all_native() == true`).  If a malicious prover
/// produced inconsistent BCCs, `first_failing()` will flag the leg.
pub fn extract_v2_bcc_pair_ood_bundle(
    proof: &V2ProofReal,
) -> Result<ExtOodClaimBundle, V2BridgeError> {
    let l2a = extract_pair_claim(
        &proof.l2a_decompose_bcc, &proof.l2a_use_hint_bcc, "L2a",
    )?;
    let l3 = extract_pair_claim(
        &proof.l3_use_hint_bcc, &proof.l3_w1_encode_bcc, "L3",
    )?;
    Ok(ExtOodClaimBundle { claims: vec![l2a, l3] })
}

/// Expand an `ExtOodClaimBundle` into an `OodClaimBundle<Goldilocks>`
/// by projecting each Ext claim into EXT_DEGREE per-coordinate
/// Goldilocks sub-claims via `TowerField::to_fp_components`.
///
/// Soundness:  for each Ext equality `f_ext(z) − g_ext(z) == 0`, the
/// equality holds in `Fp⁶` iff every Goldilocks coordinate is zero:
///
/// ```text
///     f_ext − g_ext ∈ Fp⁶          iff    (f_ext − g_ext).c[k] = 0  ∀ k ∈ 0..6
/// ```
///
/// Decomposing yields EXT_DEGREE base-field equality claims per Ext
/// claim.  The base-field bundle is then consumable by the existing
/// `prove_ood_accumulator` AIR (which operates over Goldilocks) and
/// the FRI-side SZ at Fp⁶ is preserved by the BCC commits themselves
/// — flattening doesn't weaken the SZ bound, it just spreads it
/// across EXT_DEGREE rows of the OOD accumulator.
///
/// Currently supports the two BCC-vs-BCC legs L2a and L3 produced by
/// `extract_v2_bcc_pair_ood_bundle`.  Other binding tags trigger a
/// panic (we don't synthesise unknown static tags); add a new
/// `COORD_TAGS_*` table when extending to more F2b legs.
pub fn flatten_ext_to_base(ext: &ExtOodClaimBundle) -> OodClaimBundle<Goldilocks> {
    let mut claims = Vec::with_capacity(ext.claims.len() * EXT_DEGREE);
    for claim in &ext.claims {
        let f_coords = claim.f_at_z.to_fp_components();
        let g_coords = claim.g_at_z.to_fp_components();
        assert_eq!(f_coords.len(), EXT_DEGREE,
            "TowerField::to_fp_components returned wrong length for SexticExt");
        assert_eq!(g_coords.len(), EXT_DEGREE);
        let tags: &[&'static str; EXT_DEGREE] = match claim.binding_tag {
            "L2a" => &COORD_TAGS_L2A,
            "L3"  => &COORD_TAGS_L3,
            other => panic!(
                "flatten_ext_to_base: unknown binding_tag '{other}'; \
                 add a COORD_TAGS_* table for the new leg"
            ),
        };
        for i in 0..EXT_DEGREE {
            claims.push(OodEqualityClaim {
                z: Goldilocks::from(0u64),
                f_at_z: f_coords[i],
                g_at_z: g_coords[i],
                binding_tag: tags[i],
            });
        }
    }
    OodClaimBundle { claims }
}

/// End-to-end: extract real F2b OOD evaluations from a v2 ML-DSA
/// proof and produce a recursive STARK proof attesting the bundle.
///
/// Pipeline:
///
/// ```text
///   V2ProofReal
///       │
///       ▼  extract_v2_bcc_pair_ood_bundle
///   ExtOodClaimBundle  (2 Ext claims: L2a, L3)
///       │
///       ▼  flatten_ext_to_base
///   OodClaimBundle<Goldilocks>  (12 base claims: L2a.c{0..5}, L3.c{0..5})
///       │
///       ▼  FS-derive alphas from v2.pi_hash with seed-XOR 0xF5
///   OodAccumulatorClaim  (bundle + 12 alphas)
///       │
///       ▼  prove_ood_accumulator
///   OodAccumulatorProof  (DeepFriProof<SexticExt> attesting Σ α·(f−g) = 0)
/// ```
///
/// This is the first end-to-end wiring between an inner v2 proof's
/// F2b OOD outputs and the recursive STARK gadget's sub-circuit 2.
/// The returned proof attests:
///
///     ∃ witnesses such that every Goldilocks coordinate of every
///     F2b OOD residue at z_0 is zero — equivalently, that both
///     L2a's and L3's BCC-vs-BCC equalities hold at z_0 ∈ Fp⁶.
///
/// FS alphas are derived from `proof.pi_hash` with seed-XOR `0xF5`,
/// chosen distinct from the recursive_prover's own namespace
/// (`0xC1..C3`, `0xD0..D3`, `0xE0..E4`, `0xF0..F2`).
pub fn prove_v2_ood_recursive(
    proof: &V2ProofReal,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<OodAccumulatorProof, V2OodRecursiveError> {
    let ext_bundle = extract_v2_bcc_pair_ood_bundle(proof)
        .map_err(V2OodRecursiveError::Bridge)?;
    let base_bundle = flatten_ext_to_base(&ext_bundle);

    // FS-derive one alpha per flattened claim.
    let mut seed = proof.pi_hash;
    seed[0] ^= 0xF5;
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, base_bundle.claims.len());

    let claim = OodAccumulatorClaim { bundle: base_bundle, alphas };
    prove_ood_accumulator(&claim, blowup, r, use_stir)
        .map_err(V2OodRecursiveError::RecursiveProver)
}

/// Errors from the end-to-end `prove_v2_ood_recursive` pipeline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum V2OodRecursiveError {
    Bridge(V2BridgeError),
    RecursiveProver(RecursiveProverError),
}

impl std::fmt::Display for V2OodRecursiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bridge(e) => write!(f, "v2 bridge: {e}"),
            Self::RecursiveProver(e) => write!(f, "recursive prover: {e}"),
        }
    }
}
impl std::error::Error for V2OodRecursiveError {}

#[cfg(test)]
mod tests {
    use super::*;
    use deep_ali::ml_dsa::params::C_TILDE_BYTES;
    use deep_ali::ml_dsa_transcript;
    use deep_ali::ml_dsa_verify_air_v2_orchestration::{
        prove_v2_real, synthesize_demo_witness, verify_v2_real,
    };

    #[test]
    #[ignore = "slow — runs prove_v2_real to produce a real v2 proof"]
    fn extracts_honest_v2_bundle_check_passes() {
        let w = synthesize_demo_witness(7);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, /*blowup=*/4);

        // Sanity-check the proof verifies natively first.
        verify_v2_real(&w, &c_tilde, &proof, 4)
            .expect("honest v2 proof must verify");

        let bundle = extract_v2_bcc_pair_ood_bundle(&proof)
            .expect("OOD bundle extraction must succeed on a well-formed v2 proof");

        assert_eq!(bundle.claims.len(), 2, "L2a + L3 = 2 claims expected");
        assert!(bundle.check_all_native(),
            "honest v2 must satisfy F2b OOD checks: first_failing = {:?}",
            bundle.first_failing());

        use ark_ff::Zero;
        for c in &bundle.claims {
            assert!(c.residue().is_zero(),
                "{}: residue must be 0; got {:?}", c.binding_tag, c.residue());
        }
    }

    #[test]
    #[ignore = "slow — flatten Ext bundle into Goldilocks bundle"]
    fn flatten_ext_to_base_produces_12_base_claims() {
        let w = synthesize_demo_witness(13);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let ext_bundle = extract_v2_bcc_pair_ood_bundle(&proof).unwrap();
        assert_eq!(ext_bundle.claims.len(), 2);

        let base_bundle = flatten_ext_to_base(&ext_bundle);
        assert_eq!(base_bundle.claims.len(), 2 * EXT_DEGREE,
            "2 Ext claims × {EXT_DEGREE} coords = 12 base claims");

        // Every coordinate must be zero on an honest proof.
        assert!(base_bundle.check_all_native(),
            "honest v2: all 12 base-coord OOD residues must be zero");

        // Tag layout: claims 0..6 are L2a.c0..c5, 6..12 are L3.c0..c5.
        for i in 0..EXT_DEGREE {
            assert_eq!(base_bundle.claims[i].binding_tag, COORD_TAGS_L2A[i]);
            assert_eq!(base_bundle.claims[EXT_DEGREE + i].binding_tag, COORD_TAGS_L3[i]);
        }
    }

    #[test]
    #[ignore = "slow — full recursive STARK round-trip on real v2 OOD bundle"]
    fn prove_v2_ood_recursive_round_trip() {
        use crate::recursive_prover::verify_ood_accumulator;

        let w = synthesize_demo_witness(17);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        // Run the end-to-end pipeline: extract → flatten → FS alphas
        // → prove_ood_accumulator.
        let rec_proof = prove_v2_ood_recursive(&proof, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("v2 OOD recursive prove must succeed on honest input");

        // Local verify of the recursive STARK proof.
        assert!(verify_ood_accumulator(&rec_proof),
            "recursive OOD STARK must verify locally");

        // Reproducibility: re-running on the same v2 proof produces the
        // same public_inputs (pi_hash inside OodAccumulatorPublicInputs)
        // and a verifying proof.
        let rec_proof_2 = prove_v2_ood_recursive(&proof, 4, 54, false)
            .expect("second run must also succeed");
        assert_eq!(rec_proof.public.pi_hash, rec_proof_2.public.pi_hash,
            "v2 → recursive pi_hash must be deterministic in v2 proof");
        assert!(verify_ood_accumulator(&rec_proof_2));
    }

    #[test]
    #[ignore = "slow — direct tamper rejection on extracted claim"]
    fn tampered_ood_value_breaks_bundle_check() {
        // Test the bundle's native check_all_native: if one claim's
        // f_at_z is perturbed so f_at_z ≠ g_at_z, the bundle must
        // reject and first_failing must point to the perturbed leg.
        //
        // We don't tamper the on-the-wire BCC blob here because ark-
        // serialize blobs are robust to arbitrary byte flips: a flip
        // outside the fz_per_layer[0] encoding leaves the extracted
        // OOD value unchanged, and a flip inside the FRI Merkle path
        // typically corrupts deserialization rather than the OOD value
        // alone.  Soundness of the SZ binding lives in the FRI commit
        // itself (verified separately via deep_fri_verify); the
        // bundle's check is the cross-pair *equality* check, and
        // that's what we exercise here.
        let w = synthesize_demo_witness(11);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let mut bundle = extract_v2_bcc_pair_ood_bundle(&proof)
            .expect("honest bundle extraction must succeed");
        assert!(bundle.check_all_native(), "honest pre-tamper sanity");

        // Perturb the L2a claim's f_at_z so residue is non-zero.
        let one: Ext = <Ext as ark_ff::One>::one();
        bundle.claims[0].f_at_z = bundle.claims[0].f_at_z + one;

        assert!(!bundle.check_all_native(),
            "perturbed L2a must NOT pass OOD bundle check");
        assert_eq!(bundle.first_failing(), Some(0),
            "first failure should be the L2a (index 0) entry");

        // L3 untouched: should still self-check fine.
        assert!(bundle.claims[1].check_native(),
            "L3 (untouched) must still pass natively");
    }
}
