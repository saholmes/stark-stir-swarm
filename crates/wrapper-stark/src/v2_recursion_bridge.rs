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

use ark_ff::Zero as ArkZero;
use ark_goldilocks::Goldilocks;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_serialize::{CanonicalDeserialize, Compress, Validate};

use deep_ali::binding_cells_commit::{BindingCellsCommit, extract_ood_value};
use deep_ali::fri::{DeepFriProof, derive_z_ext_for_proof};
use deep_ali::ml_dsa::params::{K, L, N, W1_BITS_PER_COEF};
use deep_ali::ml_dsa_decompose;
use deep_ali::ml_dsa_decompose_air;
use deep_ali::ml_dsa_ntt_chained_air;
use deep_ali::ml_dsa_shake_absorb_multi_air;
use deep_ali::ml_dsa_transcript;
use deep_ali::ml_dsa_use_hint_air;
use deep_ali::ml_dsa_verify_air_v17::{
    N_EQ_ROWS, NUM_CONSTRAINTS as V17_NUM_CONSTRAINTS,
    VERIFY_AIR_V17_ACTIVE_ROWS, WIDTH as V17_WIDTH,
};
use deep_ali::ml_dsa_verify_air_v2_layout::{coeff_chain, intt as intt_layout, transcript as transcript_layout};
use deep_ali::ml_dsa_w1_encode_air;
use deep_ali::sub_air_with_trace::{
    augment_pi_hash, comb_coeffs_aug, deserialize_proof,
    extract_query_position_and_c_eval, extract_query_positions,
    lde_omega_pow, z_h_at,
};
use deep_ali::ml_dsa_verify_air_v2_orchestration::{
    V2ProofReal, V2Witness, derive_w_approx_witness, v2_fri_params,
};
use deep_ali::sextic_ext::SexticExt;
use deep_ali::tower_field::TowerField;

use crate::bit_constraint::{BitOp, CellRef};
use crate::composition::alphas_from_transcript;
use crate::deep_ali_verifier_air::binding_cells_ood_verifier::{
    OodClaimBundle, OodEqualityClaim,
};
use crate::deep_ali_verifier_air::constraint_composition_verifier::CompositionClaim;
use crate::deep_ali_verifier_air::permutation_argument_verifier::PermArgClaim;
use crate::recursive_prover::{
    OodAccumulatorClaim, OodAccumulatorProof, RecursiveProverError,
    RecursiveStarkProof, prove_ood_accumulator, prove_recursive_stark,
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

// Coordinate tags for the BCC-vs-public legs.  Each entry expands into
// EXT_DEGREE = 6 base-field sub-claims when flattened.
const COORD_TAGS_L2C: [&str; EXT_DEGREE] = [
    "L2c.c0", "L2c.c1", "L2c.c2", "L2c.c3", "L2c.c4", "L2c.c5",
];
const COORD_TAGS_L1: [&str; EXT_DEGREE] = [
    "L1.c0", "L1.c1", "L1.c2", "L1.c3", "L1.c4", "L1.c5",
];
const COORD_TAGS_L2B: [&str; EXT_DEGREE] = [
    "L2b.c0", "L2b.c1", "L2b.c2", "L2b.c3", "L2b.c4", "L2b.c5",
];

// L4 bit-column tags, max W1_BITS_PER_COEF = 6 (L1).  Slice to active
// length at runtime.
const COORD_TAGS_L4: [[&str; EXT_DEGREE]; 6] = [
    ["L4.b0.c0", "L4.b0.c1", "L4.b0.c2", "L4.b0.c3", "L4.b0.c4", "L4.b0.c5"],
    ["L4.b1.c0", "L4.b1.c1", "L4.b1.c2", "L4.b1.c3", "L4.b1.c4", "L4.b1.c5"],
    ["L4.b2.c0", "L4.b2.c1", "L4.b2.c2", "L4.b2.c3", "L4.b2.c4", "L4.b2.c5"],
    ["L4.b3.c0", "L4.b3.c1", "L4.b3.c2", "L4.b3.c3", "L4.b3.c4", "L4.b3.c5"],
    ["L4.b4.c0", "L4.b4.c1", "L4.b4.c2", "L4.b4.c3", "L4.b4.c4", "L4.b4.c5"],
    ["L4.b5.c0", "L4.b5.c1", "L4.b5.c2", "L4.b5.c3", "L4.b5.c4", "L4.b5.c5"],
];

// L5 V17 EQ-region tags, max L = 7 (mldsa-87) a_ntt slots + 3 = 10 total.
// Slice to active length at runtime.
const COORD_TAGS_L5: [[&str; EXT_DEGREE]; 10] = [
    ["L5.a0.c0", "L5.a0.c1", "L5.a0.c2", "L5.a0.c3", "L5.a0.c4", "L5.a0.c5"],
    ["L5.a1.c0", "L5.a1.c1", "L5.a1.c2", "L5.a1.c3", "L5.a1.c4", "L5.a1.c5"],
    ["L5.a2.c0", "L5.a2.c1", "L5.a2.c2", "L5.a2.c3", "L5.a2.c4", "L5.a2.c5"],
    ["L5.a3.c0", "L5.a3.c1", "L5.a3.c2", "L5.a3.c3", "L5.a3.c4", "L5.a3.c5"],
    ["L5.a4.c0", "L5.a4.c1", "L5.a4.c2", "L5.a4.c3", "L5.a4.c4", "L5.a4.c5"],
    ["L5.a5.c0", "L5.a5.c1", "L5.a5.c2", "L5.a5.c3", "L5.a5.c4", "L5.a5.c5"],
    ["L5.a6.c0", "L5.a6.c1", "L5.a6.c2", "L5.a6.c3", "L5.a6.c4", "L5.a6.c5"],
    ["L5.c_ntt.c0",  "L5.c_ntt.c1",  "L5.c_ntt.c2",  "L5.c_ntt.c3",  "L5.c_ntt.c4",  "L5.c_ntt.c5"],
    ["L5.t1d_ntt.c0","L5.t1d_ntt.c1","L5.t1d_ntt.c2","L5.t1d_ntt.c3","L5.t1d_ntt.c4","L5.t1d_ntt.c5"],
    ["L5.w_ntt.c0",  "L5.w_ntt.c1",  "L5.w_ntt.c2",  "L5.w_ntt.c3",  "L5.w_ntt.c4",  "L5.w_ntt.c5"],
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

// ─── BCC-vs-public leg extraction (L1, L2b, L2c, L4, L5) ─────────────

/// Compute g(z_ext) for a public-input leg, where g is the IFFT of the
/// canonical public trace column and z_ext is FS-derived from the
/// BCC's own FRI proof (must match `derive_z_ext_for_proof` on the
/// reconstructed v2_fri_params).
fn evaluate_public_col_at_z_ext(
    bcc: &BindingCellsCommit,
    public_trace_col: &[Goldilocks],
    pi_hash: [u8; 32],
    leg_tag: &'static str,
) -> Result<(Ext, Ext), V2BridgeError> {
    let n_trace = bcc.n_trace as usize;
    if public_trace_col.len() != n_trace {
        return Err(V2BridgeError::OodExtractFailed(format!(
            "{leg_tag}: public col len {} ≠ bcc.n_trace {}",
            public_trace_col.len(), n_trace
        )));
    }
    let packed_n_lde = n_trace * (bcc.blowup as usize) * (bcc.num_cols as usize);
    let params = v2_fri_params(packed_n_lde, pi_hash);
    let fri_proof = <DeepFriProof<Ext> as CanonicalDeserialize>::deserialize_with_mode(
        bcc.fri_proof_bytes.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|e| V2BridgeError::OodExtractFailed(
        format!("{leg_tag}: FRI deserialize: {e:?}")
    ))?;
    if fri_proof.fz_per_layer.is_empty() {
        return Err(V2BridgeError::OodExtractFailed(format!(
            "{leg_tag}: fz_per_layer empty"
        )));
    }
    let z_ext = derive_z_ext_for_proof::<Ext>(&fri_proof, &params);
    let f_at_z = fri_proof.fz_per_layer[0];

    // Public side: IFFT(public_trace_col) + Horner at z_ext.
    let dom = GeneralEvaluationDomain::<Goldilocks>::new(n_trace)
        .ok_or_else(|| V2BridgeError::OodExtractFailed(format!(
            "{leg_tag}: n_trace {n_trace} not radix-2"
        )))?;
    let coeffs = dom.ifft(public_trace_col);
    let mut g_at_z = Ext::zero();
    for k in (0..coeffs.len()).rev() {
        g_at_z = g_at_z * z_ext + <Ext as TowerField>::from_fp(coeffs[k]);
    }
    Ok((f_at_z, g_at_z))
}

/// Build one public-leg Ext OOD claim from a BCC blob + canonical
/// public trace column.
fn extract_public_leg_claim(
    bcc_blob: &[u8],
    public_trace_col: &[Goldilocks],
    pi_hash: [u8; 32],
    binding_tag: &'static str,
) -> Result<ExtOodEqualityClaim, V2BridgeError> {
    let bcc = deserialize_bcc(bcc_blob, binding_tag)?;
    let (f_at_z, g_at_z) =
        evaluate_public_col_at_z_ext(&bcc, public_trace_col, pi_hash, binding_tag)?;
    Ok(ExtOodEqualityClaim { f_at_z, g_at_z, binding_tag })
}

// ─── Canonical public-trace-column builders ──────────────────────────

fn build_public_h_col(public: &V2Witness) -> Vec<Goldilocks> {
    let n = (K * N).next_power_of_two();
    let mut col = vec![Goldilocks::zero(); n];
    for k in 0..K {
        for i in 0..N {
            col[k * N + i] = Goldilocks::from(public.h[k][i] as u64);
        }
    }
    col
}

fn build_canonical_w_approx_flat_col(public: &V2Witness) -> Vec<Goldilocks> {
    let n = (K * N).next_power_of_two();
    let canonical = derive_w_approx_witness(&public.w_approx_ntt);
    let mut col = vec![Goldilocks::zero(); n];
    for k in 0..K {
        for i in 0..N {
            col[k * N + i] = Goldilocks::from(canonical[k][i] as u64);
        }
    }
    col
}

fn build_translated_r0_sign_col(public: &V2Witness) -> Vec<Goldilocks> {
    use deep_ali::ml_dsa::params::Q;
    let n = (K * N).next_power_of_two();
    let canonical = derive_w_approx_witness(&public.w_approx_ntt);
    let mut col = vec![Goldilocks::zero(); n];
    for k in 0..K {
        for i in 0..N {
            let r = canonical[k][i];
            let (_r1, r0_lifted) = ml_dsa_decompose::decompose(r);
            let uh: u32 = if r0_lifted != 0 && r0_lifted <= Q / 2 { 1 } else { 0 };
            col[k * N + i] = Goldilocks::from(uh as u64);
        }
    }
    col
}

fn build_l4_bit_col(public: &V2Witness, bit: usize) -> Vec<Goldilocks> {
    let n = (K * N).next_power_of_two();
    let mut col = vec![Goldilocks::zero(); n];
    for r in 0..(K * N) {
        let off = r * W1_BITS_PER_COEF + bit;
        let bit_val = (public.w1bytes[off / 8] >> (off % 8)) & 1;
        col[r] = Goldilocks::from(bit_val as u64);
    }
    col
}

fn build_l5_a_ntt_col(public: &V2Witness, l: usize) -> Vec<Goldilocks> {
    let n_pad = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    let mut col = vec![Goldilocks::zero(); n_pad];
    for r in 0..N_EQ_ROWS {
        let k = r / N;
        let i = r % N;
        col[r] = Goldilocks::from(public.a_ntt[k][l][i] as u64);
    }
    col
}

fn build_l5_c_ntt_col(public: &V2Witness) -> Vec<Goldilocks> {
    let n_pad = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    let mut col = vec![Goldilocks::zero(); n_pad];
    for r in 0..N_EQ_ROWS {
        let i = r % N;
        col[r] = Goldilocks::from(public.c_ntt[i] as u64);
    }
    col
}

fn build_l5_t1d_ntt_col(public: &V2Witness) -> Vec<Goldilocks> {
    let n_pad = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    let mut col = vec![Goldilocks::zero(); n_pad];
    for r in 0..N_EQ_ROWS {
        let k = r / N;
        let i = r % N;
        col[r] = Goldilocks::from(public.t1d_ntt[k][i] as u64);
    }
    col
}

fn build_l5_w_approx_ntt_col(public: &V2Witness) -> Vec<Goldilocks> {
    let n_pad = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    let mut col = vec![Goldilocks::zero(); n_pad];
    for r in 0..N_EQ_ROWS {
        let k = r / N;
        let i = r % N;
        col[r] = Goldilocks::from(public.w_approx_ntt[k][i] as u64);
    }
    col
}

/// Extract the full BCC-vs-public F2b OOD bundle from a `V2ProofReal`
/// plus its public witness fields.  Includes L1 + L2b + L2c + L4 (one
/// per bit) + L5 (L + 3 columns).
///
/// On `mldsa-44` (L=4, W1_BITS_PER_COEF=6) the bundle has
/// 1 + 1 + 1 + 6 + (4 + 3) = 16 Ext claims.
///
/// On `mldsa-65` (L=5, W1_BITS_PER_COEF=4): 1+1+1+4+(5+3) = 15 claims.
/// On `mldsa-87` (L=7, W1_BITS_PER_COEF=4): 1+1+1+4+(7+3) = 17 claims.
pub fn extract_v2_public_leg_ood_bundle(
    proof: &V2ProofReal,
    public: &V2Witness,
) -> Result<ExtOodClaimBundle, V2BridgeError> {
    let pi_hash = proof.pi_hash;
    let mut claims = Vec::new();

    // L2c: public.h ↔ UseHint COL_H
    let l2c_col = build_public_h_col(public);
    claims.push(extract_public_leg_claim(
        &proof.l2c_use_hint_bcc, &l2c_col, pi_hash, "L2c",
    )?);

    // L1: canonical w_approx ↔ Decompose col_r
    let l1_col = build_canonical_w_approx_flat_col(public);
    claims.push(extract_public_leg_claim(
        &proof.l1_decompose_bcc, &l1_col, pi_hash, "L1",
    )?);

    // L2b: canonical translated r0_sign ↔ UseHint COL_R0_SIGN
    let l2b_col = build_translated_r0_sign_col(public);
    claims.push(extract_public_leg_claim(
        &proof.l2b_use_hint_bcc, &l2b_col, pi_hash, "L2b",
    )?);

    // L4: W1Encode bit columns ↔ canonical bit-b columns from w1bytes
    if proof.l4_w1_encode_bccs.len() != W1_BITS_PER_COEF {
        return Err(V2BridgeError::BccDeserialize(format!(
            "L4: expected {W1_BITS_PER_COEF} BCCs, got {}",
            proof.l4_w1_encode_bccs.len()
        )));
    }
    let l4_bit_tags: [&'static str; 6] = ["L4.b0","L4.b1","L4.b2","L4.b3","L4.b4","L4.b5"];
    for b in 0..W1_BITS_PER_COEF {
        let col = build_l4_bit_col(public, b);
        claims.push(extract_public_leg_claim(
            &proof.l4_w1_encode_bccs[b], &col, pi_hash, l4_bit_tags[b],
        )?);
    }

    // L5: V17 EQ-region columns ↔ public a_ntt[l] (l ∈ 0..L), c_ntt, t1d_ntt, w_approx_ntt
    let expected_l5_count = L + 3;
    if proof.l5_v17_eq_bccs.len() != expected_l5_count {
        return Err(V2BridgeError::BccDeserialize(format!(
            "L5: expected {expected_l5_count} BCCs, got {}",
            proof.l5_v17_eq_bccs.len()
        )));
    }
    let l5_a_tags: [&'static str; 7] = ["L5.a0","L5.a1","L5.a2","L5.a3","L5.a4","L5.a5","L5.a6"];
    let mut idx = 0;
    for l in 0..L {
        let col = build_l5_a_ntt_col(public, l);
        claims.push(extract_public_leg_claim(
            &proof.l5_v17_eq_bccs[idx], &col, pi_hash, l5_a_tags[l],
        )?);
        idx += 1;
    }
    {
        let col = build_l5_c_ntt_col(public);
        claims.push(extract_public_leg_claim(
            &proof.l5_v17_eq_bccs[idx], &col, pi_hash, "L5.c_ntt",
        )?);
        idx += 1;
    }
    {
        let col = build_l5_t1d_ntt_col(public);
        claims.push(extract_public_leg_claim(
            &proof.l5_v17_eq_bccs[idx], &col, pi_hash, "L5.t1d_ntt",
        )?);
        idx += 1;
    }
    {
        let col = build_l5_w_approx_ntt_col(public);
        claims.push(extract_public_leg_claim(
            &proof.l5_v17_eq_bccs[idx], &col, pi_hash, "L5.w_ntt",
        )?);
    }

    Ok(ExtOodClaimBundle { claims })
}

/// Extract the **full** v2 F2b OOD bundle — both the BCC-vs-BCC legs
/// (L2a, L3) and all BCC-vs-public legs (L1, L2b, L2c, L4, L5).  This
/// is the complete F2b cross-binding shape attested by a v2 proof.
pub fn extract_v2_full_ood_bundle(
    proof: &V2ProofReal,
    public: &V2Witness,
) -> Result<ExtOodClaimBundle, V2BridgeError> {
    let mut bundle = extract_v2_bcc_pair_ood_bundle(proof)?;
    let public_bundle = extract_v2_public_leg_ood_bundle(proof, public)?;
    bundle.claims.extend(public_bundle.claims);
    Ok(bundle)
}

/// End-to-end: extract the full F2b OOD bundle (BCC-vs-BCC +
/// BCC-vs-public) and prove its joint satisfaction with the recursive
/// OOD accumulator STARK.  Equivalent to `prove_v2_ood_recursive` but
/// covers all seven F2b legs (vs only L2a + L3).
pub fn prove_v2_full_ood_recursive(
    proof: &V2ProofReal,
    public: &V2Witness,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<OodAccumulatorProof, V2OodRecursiveError> {
    let ext_bundle = extract_v2_full_ood_bundle(proof, public)
        .map_err(V2OodRecursiveError::Bridge)?;
    let base_bundle = flatten_ext_to_base(&ext_bundle);

    let mut seed = proof.pi_hash;
    seed[0] ^= 0xF6;  // distinct from prove_v2_ood_recursive's 0xF5
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, base_bundle.claims.len());

    let claim = OodAccumulatorClaim { bundle: base_bundle, alphas };
    prove_ood_accumulator(&claim, blowup, r, use_stir)
        .map_err(V2OodRecursiveError::RecursiveProver)
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
            "L2a"             => &COORD_TAGS_L2A,
            "L3"              => &COORD_TAGS_L3,
            "L2c"             => &COORD_TAGS_L2C,
            "L1"              => &COORD_TAGS_L1,
            "L2b"             => &COORD_TAGS_L2B,
            // L4 bit-position tags ("L4.b0".."L4.b5")
            "L4.b0"           => &COORD_TAGS_L4[0],
            "L4.b1"           => &COORD_TAGS_L4[1],
            "L4.b2"           => &COORD_TAGS_L4[2],
            "L4.b3"           => &COORD_TAGS_L4[3],
            "L4.b4"           => &COORD_TAGS_L4[4],
            "L4.b5"           => &COORD_TAGS_L4[5],
            // L5 column tags ("L5.a0".."L5.a6", "L5.c_ntt", "L5.t1d_ntt", "L5.w_ntt")
            "L5.a0"           => &COORD_TAGS_L5[0],
            "L5.a1"           => &COORD_TAGS_L5[1],
            "L5.a2"           => &COORD_TAGS_L5[2],
            "L5.a3"           => &COORD_TAGS_L5[3],
            "L5.a4"           => &COORD_TAGS_L5[4],
            "L5.a5"           => &COORD_TAGS_L5[5],
            "L5.a6"           => &COORD_TAGS_L5[6],
            "L5.c_ntt"        => &COORD_TAGS_L5[7],
            "L5.t1d_ntt"      => &COORD_TAGS_L5[8],
            "L5.w_ntt"        => &COORD_TAGS_L5[9],
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

// ─── Sub-circuit 1 (REAL): v2 V17 sub-AIR per-query residue extractor ─
//
// Computes the v2 V17 sub-AIR's per-query constraint residue
//
//   r_k = c_eval(x_k) · Z_H(x_k) − Σ α_j · Φ_j(trace[x_k], x_k)
//
// for each of the V17 FRI proof's queries k.  On an honest v2 inner
// proof every r_k is zero in Fp⁶.  The recursive STARK's sub-circuit 1
// (constraint composition) attests Σ β_k · r_k = 0 over FS-derived β,
// flattening each Ext-typed residue into EXT_DEGREE base-field coords
// via `TowerField::to_fp_components` (same projection sub-circuit 2
// uses for OOD claims).
//
// Soundness gain vs the pi_hash anchor: each r_k is the SAME residue
// the inner verifier checks per query.  If the inner V17 proof's
// quotient relation doesn't hold at any queried position, the
// corresponding r_k is non-zero and the sub-circuit 1 accumulator
// catches it.  This is REAL cryptographic content tied to V17's
// constraint set, not just bit-booleanity over the pi_hash.

/// Compute per-query residues for one v2 sub-AIR FRI proof.
///
/// Replicates the per-query `c_eval(x) · Z_H(x) − Σ α_j Φ_j(trace[x])`
/// check from `deep_ali::sub_air_with_trace::verify_one_sub_air_with_trace`
/// but returns the Ext-typed residues (one per query) instead of
/// asserting zero.  On honest inputs all residues are zero.
fn extract_sub_air_residues(
    proof_bytes: &[u8],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    domain_sep: &[u8],
    width: usize,
    num_constraints: usize,
    eval_per_row_fn: impl Fn(&[Goldilocks], &[Goldilocks], usize) -> Vec<Goldilocks>,
) -> Result<Vec<Ext>, V2BridgeError> {
    let proof = deserialize_proof(proof_bytes)
        .map_err(|e| V2BridgeError::BccDeserialize(format!("sub-air proof: {e}")))?;
    let aug_pi_hash = augment_pi_hash(&pi_hash, &proof.trace_root, domain_sep);

    let fri_proof = <DeepFriProof<Ext> as CanonicalDeserialize>::deserialize_with_mode(
        proof.fri_proof_bytes.as_slice(), Compress::Yes, Validate::Yes,
    ).map_err(|e| V2BridgeError::OodExtractFailed(
        format!("sub-air FRI deserialize: {e:?}")
    ))?;
    let n0 = n_trace * blowup;
    let params = v2_fri_params(n0, aug_pi_hash);
    let m0 = params.schedule.first().copied().unwrap_or(2);

    let positions = extract_query_positions(&fri_proof)
        .map_err(|e| V2BridgeError::OodExtractFailed(format!("query positions: {e}")))?;
    let n_queries = positions.len();
    let comb_coeffs = comb_coeffs_aug(num_constraints, &aug_pi_hash, domain_sep);

    if proof.openings_cur.len() != n_queries || proof.openings_nxt.len() != n_queries {
        return Err(V2BridgeError::OodExtractFailed(format!(
            "openings count mismatch: cur={} nxt={} expected={n_queries}",
            proof.openings_cur.len(), proof.openings_nxt.len()
        )));
    }

    let mut residues = Vec::with_capacity(n_queries);
    for k in 0..n_queries {
        let (pos, c_eval_at_pos) = extract_query_position_and_c_eval(
            &fri_proof, k, n0, m0,
        ).map_err(|e| V2BridgeError::OodExtractFailed(format!("query {k}: {e}")))?;

        let cur_op = &proof.openings_cur[k];
        let nxt_op = &proof.openings_nxt[k];
        if cur_op.cells.len() != width || nxt_op.cells.len() != width {
            return Err(V2BridgeError::OodExtractFailed(format!(
                "query {k}: cells len mismatch (cur={}, nxt={}, expected={width})",
                cur_op.cells.len(), nxt_op.cells.len()
            )));
        }

        let trace_row = pos / blowup;
        // Match verify_one_sub_air's last-row gate: residue is 0 by
        // convention on the wrap-around row.
        if trace_row >= n_trace - 1 {
            residues.push(Ext::zero());
            continue;
        }

        let cvals = eval_per_row_fn(&cur_op.cells, &nxt_op.cells, trace_row);
        if cvals.len() != num_constraints {
            return Err(V2BridgeError::OodExtractFailed(format!(
                "query {k}: eval_per_row returned {} ≠ {num_constraints}",
                cvals.len()
            )));
        }
        let phi_at_pos: Goldilocks = (0..num_constraints)
            .map(|j| comb_coeffs[j] * cvals[j])
            .sum();
        let pos_f = lde_omega_pow(pos, n0);
        let z_h = z_h_at(pos_f, n_trace);
        // residue = c_eval(x) · Z_H(x) − Σ α_j · Φ_j(trace[x], x)
        let lhs = c_eval_at_pos * <Ext as TowerField>::from_fp(z_h);
        let rhs = <Ext as TowerField>::from_fp(phi_at_pos);
        residues.push(lhs - rhs);
    }

    Ok(residues)
}

/// Per-sub-AIR Ext-typed residues extracted from a v2 inner proof.
///
/// One vector per sub-AIR; `intt[k]` for k ∈ 0..K, plus V17, Decompose,
/// UseHint, W1Encode, TRANSCRIPT = K + 5 entries total.  On an honest
/// inner proof every residue in every vector is zero.
#[derive(Clone, Debug)]
pub struct V2SubAirResidues {
    pub v17:           Vec<Ext>,
    pub intt:          Vec<Vec<Ext>>,   // K = 4/6/8 instances at L1/L3/L5
    pub decompose:     Vec<Ext>,
    pub use_hint:      Vec<Ext>,
    pub w1_encode:     Vec<Ext>,
    pub transcript:    Vec<Ext>,
}

impl V2SubAirResidues {
    /// Total number of Ext residues across all sub-AIRs.
    pub fn total(&self) -> usize {
        self.v17.len()
            + self.intt.iter().map(|v| v.len()).sum::<usize>()
            + self.decompose.len()
            + self.use_hint.len()
            + self.w1_encode.len()
            + self.transcript.len()
    }

    /// True iff every residue in every sub-AIR is zero.
    pub fn all_zero(&self) -> bool {
        use ark_ff::Zero as _;
        self.v17.iter().all(|r| r.is_zero())
            && self.intt.iter().all(|v| v.iter().all(|r| r.is_zero()))
            && self.decompose.iter().all(|r| r.is_zero())
            && self.use_hint.iter().all(|r| r.is_zero())
            && self.w1_encode.iter().all(|r| r.is_zero())
            && self.transcript.iter().all(|r| r.is_zero())
    }
}

/// Extract per-query residues for ALL 10 v2 sub-AIRs (V17 + K×INTT +
/// Decompose + UseHint + W1Encode + TRANSCRIPT).
///
/// On an honest v2 inner proof every residue across every sub-AIR is
/// zero — `result.all_zero()` returns true.  Tampering any sub-AIR's
/// quotient at any queried position causes its residue vector to
/// contain at least one non-zero Ext value.
///
/// `public` is needed to reconstruct the TRANSCRIPT layout (mu_bytes
/// + w1bytes).  All other sub-AIRs derive their parameters from
/// constants in `ml_dsa_verify_air_v2_layout` + `proof.pi_hash`.
pub fn extract_v2_all_subair_residues(
    proof: &V2ProofReal,
    public: &V2Witness,
) -> Result<V2SubAirResidues, V2BridgeError> {
    let blowup = 4;  // v2 sub-AIRs all use this blowup
    let pi_hash = proof.pi_hash;

    // V17.
    let v17 = extract_sub_air_residues(
        &proof.fri_v17, VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two(), blowup,
        pi_hash, b"v17", V17_WIDTH, V17_NUM_CONSTRAINTS,
        |cur, nxt, row| deep_ali::ml_dsa_verify_air_v17::eval_per_row(cur, nxt, row),
    )?;

    // INTT × K.  Each instance has its own domain_sep tag b"intt:<k>".
    if proof.fri_intt.len() != K {
        return Err(V2BridgeError::OodExtractFailed(format!(
            "INTT: expected {K} sub-proofs, got {}", proof.fri_intt.len()
        )));
    }
    // Per-instance INTT trace size — matches the prover's
    // `(BUTTERFLIES_PER_NTT + 16).next_power_of_two()` (= 2048 at L1).
    // The layout's `intt::N_ROWS_POW2` is the combined multi-instance
    // size, NOT the per-instance one used by prove_one_sub_air_with_trace.
    let intt_n_trace = (ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT + 16).next_power_of_two();
    let mut intt = Vec::with_capacity(K);
    for k in 0..K {
        let mut tag = b"intt:".to_vec();
        tag.push(k as u8);
        let residues = extract_sub_air_residues(
            &proof.fri_intt[k], intt_n_trace, blowup,
            pi_hash, &tag,
            ml_dsa_ntt_chained_air::WIDTH, ml_dsa_ntt_chained_air::NUM_CONSTRAINTS,
            |cur, nxt, row| ml_dsa_ntt_chained_air::eval_per_row(cur, nxt, row),
        )?;
        intt.push(residues);
    }

    // Decompose, UseHint, W1Encode — all share coeff_chain::N_ROWS_POW2.
    let coeff_n_trace = coeff_chain::N_ROWS_POW2;
    let decompose = extract_sub_air_residues(
        &proof.fri_decompose, coeff_n_trace, blowup,
        pi_hash, b"decompose",
        ml_dsa_decompose_air::WIDTH, ml_dsa_decompose_air::NUM_CONSTRAINTS,
        |cur, nxt, row| ml_dsa_decompose_air::eval_per_row(cur, nxt, row),
    )?;
    let use_hint = extract_sub_air_residues(
        &proof.fri_use_hint, coeff_n_trace, blowup,
        pi_hash, b"use_hint",
        ml_dsa_use_hint_air::WIDTH, ml_dsa_use_hint_air::NUM_CONSTRAINTS,
        |cur, nxt, row| ml_dsa_use_hint_air::eval_per_row(cur, nxt, row),
    )?;
    let w1_encode = extract_sub_air_residues(
        &proof.fri_w1_encode, coeff_n_trace, blowup,
        pi_hash, b"w1_encode",
        ml_dsa_w1_encode_air::WIDTH, ml_dsa_w1_encode_air::NUM_CONSTRAINTS,
        |cur, nxt, row| ml_dsa_w1_encode_air::eval_per_row(cur, nxt, row),
    )?;

    // TRANSCRIPT — eval_per_row takes a MultiAbsorbLayout extra arg.
    let layout = ml_dsa_transcript::build_layout(&public.mu_bytes, &public.w1bytes);
    let transcript_n_trace = transcript_layout::N_ROWS_POW2;
    let transcript_num_cons = ml_dsa_shake_absorb_multi_air::num_constraints(&layout);
    let transcript = extract_sub_air_residues(
        &proof.fri_transcript, transcript_n_trace, blowup,
        pi_hash, b"transcript",
        ml_dsa_shake_absorb_multi_air::WIDTH, transcript_num_cons,
        |cur, nxt, row| ml_dsa_shake_absorb_multi_air::eval_per_row(cur, nxt, row, &layout),
    )?;

    Ok(V2SubAirResidues {
        v17, intt, decompose, use_hint, w1_encode, transcript,
    })
}

/// Build a sub-circuit 1 CompositionClaim from **all 10** v2 sub-AIRs'
/// per-query residues (V17 + K×INTT + Decompose + UseHint + W1Encode
/// + TRANSCRIPT).
///
/// Each Ext residue is flattened into EXT_DEGREE Goldilocks coords
/// and registered as a `BitOp::IsZero` constraint.  Total claim count
/// at L1: 10 sub-AIRs × ~54 queries × 6 coords ≈ 3240 (varies because
/// last-row gating sets some residues to Ext::zero()).
pub fn build_v2_all_subairs_composition(
    proof: &V2ProofReal,
    public: &V2Witness,
) -> Result<CompositionClaim<Goldilocks>, V2BridgeError> {
    let residues = extract_v2_all_subair_residues(proof, public)?;
    let total_ext = residues.total();
    let total_base = total_ext * EXT_DEGREE;

    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::with_capacity(total_base);
    let mut constraints: Vec<BitOp> = Vec::with_capacity(total_base);
    let mut next_col = 0usize;

    let push_residue_block = |residues: &[Ext], column_values: &mut Vec<(CellRef, Goldilocks)>,
                                    constraints: &mut Vec<BitOp>, next_col: &mut usize| {
        for r in residues {
            let coords = r.to_fp_components();
            for c in 0..EXT_DEGREE {
                let cell = CellRef::new(0, *next_col);
                column_values.push((cell, coords[c]));
                constraints.push(BitOp::IsZero { cell });
                *next_col += 1;
            }
        }
    };

    push_residue_block(&residues.v17, &mut column_values, &mut constraints, &mut next_col);
    for k in 0..residues.intt.len() {
        push_residue_block(&residues.intt[k], &mut column_values, &mut constraints, &mut next_col);
    }
    push_residue_block(&residues.decompose, &mut column_values, &mut constraints, &mut next_col);
    push_residue_block(&residues.use_hint,  &mut column_values, &mut constraints, &mut next_col);
    push_residue_block(&residues.w1_encode, &mut column_values, &mut constraints, &mut next_col);
    push_residue_block(&residues.transcript, &mut column_values, &mut constraints, &mut next_col);

    // FS alphas from pi_hash ⊕ 0xC6 (distinct from anchor 0xC4 + V17-only 0xC5).
    let mut seed = proof.pi_hash;
    seed[0] ^= 0xC6;
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, constraints.len());

    Ok(CompositionClaim {
        column_values, constraints, alphas,
        expected: Goldilocks::zero(),
    })
}

/// Build a sub-circuit 1 CompositionClaim from real v2 V17 per-query
/// residues.
///
/// For each of V17's `n_queries` queries, computes the residue
/// `c_eval(x) · Z_H(x) − Σ α_j Φ_j(trace[x])` (Ext-typed), flattens it
/// into EXT_DEGREE = 6 Goldilocks coordinates, and registers each
/// coordinate as a `BitOp::IsZero` constraint over a CompositionClaim
/// row-0 cell.
///
/// On an honest v2 inner proof every residue is zero (the inner
/// verifier checks this per-query), so every flattened coord is zero
/// and every IsZero constraint vanishes.  Composed sum =
/// Σ β_j · 0 = 0 = expected.
///
/// On a tampered inner V17 proof, at least one residue is non-zero
/// at one coord and (with FS-derived β) the composed sum is non-zero
/// with probability ≥ 1 − n/|Goldilocks|, catching the tamper.
pub fn build_v2_v17_subair_composition(
    proof: &V2ProofReal,
) -> Result<CompositionClaim<Goldilocks>, V2BridgeError> {
    let v17_n_trace = VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    let residues = extract_sub_air_residues(
        &proof.fri_v17, v17_n_trace, /*blowup=*/4,
        proof.pi_hash, b"v17",
        V17_WIDTH, V17_NUM_CONSTRAINTS,
        |cur, nxt, row| deep_ali::ml_dsa_verify_air_v17::eval_per_row(cur, nxt, row),
    )?;

    // Each Ext residue → 6 Goldilocks coords → 6 IsZero constraints.
    let total = residues.len() * EXT_DEGREE;
    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::with_capacity(total);
    let mut constraints: Vec<BitOp> = Vec::with_capacity(total);
    for (k, r) in residues.iter().enumerate() {
        let coords = r.to_fp_components();
        for c in 0..EXT_DEGREE {
            let col = k * EXT_DEGREE + c;
            let cell = CellRef::new(0, col);
            column_values.push((cell, coords[c]));
            constraints.push(BitOp::IsZero { cell });
        }
    }

    // FS alphas derived from v2 pi_hash with a new seed-XOR.
    let mut seed = proof.pi_hash;
    seed[0] ^= 0xC5;  // distinct from anchor's 0xC4
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, constraints.len());

    Ok(CompositionClaim {
        column_values, constraints, alphas,
        expected: Goldilocks::zero(),
    })
}

// ─── Sub-circuit 1 wiring (constraint composition over v2 pi_hash) ──
//
// The wrapper-stark recursive_prover's sub-circuit 1 expects a
// `CompositionClaim<Goldilocks>`: a vector of `BitOp` constraints over
// trace cells with column values supplied at an FS-derived point z.
//
// For v2, the natural sub-circuit-1 statement would be "for each of
// the 10 v2 sub-AIRs, Σ α_j · Φ_j(trace_at_z) = 0".  But v2's
// sub-AIRs are field-valued AIRs with `eval_per_row` functions and
// quotient-polynomial FRI commits — not BitOp-shaped.  Encoding them
// into BitOp claims would require lifting each `eval_per_row` to a
// bit-level constraint network (substantial work — the wrapper-stark
// gadget's eventual verifier-AIR target).
//
// Pragmatic intermediate: we attach a v2-bound *anchor* composition
// that binds the 256 bits of the v2 `pi_hash` into the recursive
// STARK's composition leg via 256 `BitOp::Boolean` constraints.  Each
// bit is in {0, 1} (it came from a u8 byte), so every Boolean
// constraint evaluates to zero on an honest input.  This:
//
//   1. Makes sub-circuit 1 NON-VACUOUS — there's a real constraint
//      check (`b·(b−1) = 0`) per pi_hash bit.
//   2. Binds the v2 pi_hash into the composed RecursiveStarkProof's
//      outer_pi_hash via the BitOp constraints' alpha-weighted sum.
//   3. Doesn't claim to re-prove the inner v2 verifier (that's what
//      the full verifier-AIR will do, eventually).
//
// The anchor's soundness is "the prover knows the bits of the v2
// pi_hash", which the FS-binding into outer_pi_hash already gives;
// it's the architectural shape that matters here, not new
// soundness.

/// Build a `CompositionClaim<Goldilocks>` that binds the v2 pi_hash
/// bytes' bits via 256 `BitOp::Boolean` constraints.
///
/// Layout:
///   - row 0 has 256 cells, one per pi_hash bit (column = bit index)
///   - cell value = 0 or 1
///   - constraint per cell = `BitOp::Boolean { b: cell }`
///   - alphas FS-derived from `pi_hash` ⊕ `0xC4` (distinct from
///     recursive_prover's `0xC1/0xC2/0xC3` namespace)
///   - expected = 0 (every Boolean constraint vanishes on input ∈ {0,1})
pub fn build_v2_pi_hash_anchor_composition(
    pi_hash: [u8; 32],
) -> CompositionClaim<Goldilocks> {
    use crate::bit_constraint::CellRef;

    let mut column_values: Vec<(CellRef, Goldilocks)> = Vec::with_capacity(256);
    let mut constraints: Vec<BitOp> = Vec::with_capacity(256);
    for byte_idx in 0..32 {
        let byte = pi_hash[byte_idx];
        for bit in 0..8 {
            let col = byte_idx * 8 + bit;
            let bit_val = ((byte >> bit) & 1) as u64;
            let cell = CellRef::new(0, col);
            column_values.push((cell, Goldilocks::from(bit_val)));
            constraints.push(BitOp::Boolean { b: cell });
        }
    }

    let mut seed = pi_hash;
    seed[0] ^= 0xC4;
    let alphas = alphas_from_transcript::<Goldilocks>(&seed, constraints.len());

    CompositionClaim {
        column_values,
        constraints,
        alphas,
        expected: Goldilocks::zero(),
    }
}

/// Build a vestige `PermArgClaim<Goldilocks>` whose multisets are
/// equal by construction — left == right, both derived from the v2
/// pi_hash bytes packed into Goldilocks field elements.
///
/// T_MEM was removed from v2 on 2026-05-10 (superseded by F2b L0-L4),
/// so there is no real perm-arg leg in the inner proof.  This vestige
/// keeps the recursive_prover's sub-circuit 3 satisfied; the multiset
/// equality is trivially true, providing no additional soundness
/// but completing the 3-sub-circuit composition shape.
pub fn build_v2_pi_hash_vestige_perm_arg(
    pi_hash: [u8; 32],
) -> PermArgClaim<Goldilocks> {
    // Pack pi_hash into 4 little-endian u64s.
    let mut elems = Vec::with_capacity(4);
    for chunk_idx in 0..4 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&pi_hash[8 * chunk_idx..8 * (chunk_idx + 1)]);
        elems.push(Goldilocks::from(u64::from_le_bytes(bytes)));
    }

    // Use a FS-derived γ from pi_hash so the perm-arg's z is bound.
    let mut seed = pi_hash;
    seed[0] ^= 0xE5;
    let gamma = alphas_from_transcript::<Goldilocks>(&seed, 1)[0];

    PermArgClaim {
        left: elems.clone(),
        right: elems,
        gamma,
        perm_tag: "v2-pi-hash-vestige",
    }
}

/// End-to-end: take a v2 ML-DSA proof and produce ONE outer
/// `RecursiveStarkProof` that composes all three sub-circuits:
///
///   sub-circuit 1 (constraint composition):
///     256 `BitOp::Boolean` checks over the v2 pi_hash bits.
///   sub-circuit 2 (binding-cells OOD):
///     Full F2b OOD bundle (BCC-vs-BCC + BCC-vs-public), flattened
///     to Goldilocks via per-coordinate expansion.
///   sub-circuit 3 (perm-arg multiset equality):
///     Vestige (left = right = packed v2 pi_hash u64s) — T_MEM was
///     removed from v2 on 2026-05-10, so this leg is trivially true.
///
/// Returns ONE outer `DeepFriProof<SexticExt>` attesting all three
/// sub-circuit statements simultaneously, with an `outer_pi_hash`
/// binding the three sub-pi_hashes + n_trace_max into the FS
/// transcript via SHA3-256.
pub fn prove_v2_composed_recursive(
    proof: &V2ProofReal,
    public: &V2Witness,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, V2OodRecursiveError> {
    // Sub-circuit 1: pi_hash anchor composition.
    let comp_claim = build_v2_pi_hash_anchor_composition(proof.pi_hash);

    // Sub-circuit 2: real full F2b OOD bundle, flattened.
    let ext_bundle = extract_v2_full_ood_bundle(proof, public)
        .map_err(V2OodRecursiveError::Bridge)?;
    let base_bundle = flatten_ext_to_base(&ext_bundle);
    let mut ood_seed = proof.pi_hash;
    ood_seed[0] ^= 0xF6;
    let ood_alphas = alphas_from_transcript::<Goldilocks>(
        &ood_seed, base_bundle.claims.len(),
    );
    let ood_claim = OodAccumulatorClaim {
        bundle: base_bundle, alphas: ood_alphas,
    };

    // Sub-circuit 3: vestige perm-arg.
    let perm_claim = build_v2_pi_hash_vestige_perm_arg(proof.pi_hash);

    prove_recursive_stark(&comp_claim, &ood_claim, &perm_claim, blowup, r, use_stir)
        .map_err(V2OodRecursiveError::RecursiveProver)
}

/// End-to-end with **REAL** sub-circuit 1: replaces the pi_hash anchor
/// with v2 V17 sub-AIR per-query residues.  The composed
/// RecursiveStarkProof now attests:
///
///   1. Sub-circuit 1: every coord of every V17 per-query residue
///      `c_eval(x) · Z_H(x) − Σ α_j Φ_j(trace[x])` is zero.  This
///      is the SAME residue the inner v2 verifier checks per query —
///      tampering V17's quotient breaks this leg.
///   2. Sub-circuit 2: full F2b OOD (BCC-vs-BCC + BCC-vs-public)
///      with all coordinates zero (Schwartz-Zippel at z_0 ∈ Fp⁶).
///   3. Sub-circuit 3: vestige perm-arg (T_MEM removed from v2).
///
/// Sub-circuit 1 here covers V17 only — the largest and most
/// architecturally significant v2 sub-AIR.  Extending to the other
/// 9 sub-AIRs (4×INTT, Decompose, UseHint, W1Encode, TRANSCRIPT) is
/// the same pattern: pass each sub-AIR's `eval_per_row` and
/// constraint count to `extract_sub_air_residues`.
/// End-to-end with **ALL 10 v2 sub-AIRs** real in sub-circuit 1.
/// The composed RecursiveStarkProof attests:
///
///   1. Sub-circuit 1: every coord of every per-query residue across
///      V17 + K×INTT + Decompose + UseHint + W1Encode + TRANSCRIPT
///      is zero.  Tampering ANY sub-AIR's quotient relation at ANY
///      queried position breaks this leg.
///   2. Sub-circuit 2: full F2b OOD (BCC-vs-BCC + BCC-vs-public).
///   3. Sub-circuit 3: vestige perm-arg.
///
/// This is the FULL inner-verifier per-query constraint check across
/// every v2 sub-AIR, expressed as one outer recursive STARK proof.
pub fn prove_v2_all_subairs_composed_recursive(
    proof: &V2ProofReal,
    public: &V2Witness,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, V2OodRecursiveError> {
    // Sub-circuit 1: REAL all-10-sub-AIRs per-query residue composition.
    let comp_claim = build_v2_all_subairs_composition(proof, public)
        .map_err(V2OodRecursiveError::Bridge)?;

    // Sub-circuit 2: full F2b OOD bundle, flattened.
    let ext_bundle = extract_v2_full_ood_bundle(proof, public)
        .map_err(V2OodRecursiveError::Bridge)?;
    let base_bundle = flatten_ext_to_base(&ext_bundle);
    let mut ood_seed = proof.pi_hash;
    ood_seed[0] ^= 0xF6;
    let ood_alphas = alphas_from_transcript::<Goldilocks>(
        &ood_seed, base_bundle.claims.len(),
    );
    let ood_claim = OodAccumulatorClaim {
        bundle: base_bundle, alphas: ood_alphas,
    };

    // Sub-circuit 3: vestige perm-arg.
    let perm_claim = build_v2_pi_hash_vestige_perm_arg(proof.pi_hash);

    prove_recursive_stark(&comp_claim, &ood_claim, &perm_claim, blowup, r, use_stir)
        .map_err(V2OodRecursiveError::RecursiveProver)
}

pub fn prove_v2_v17_composed_recursive(
    proof: &V2ProofReal,
    public: &V2Witness,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, V2OodRecursiveError> {
    // Sub-circuit 1: REAL V17 per-query residue composition.
    let comp_claim = build_v2_v17_subair_composition(proof)
        .map_err(V2OodRecursiveError::Bridge)?;

    // Sub-circuit 2: full F2b OOD bundle, flattened.
    let ext_bundle = extract_v2_full_ood_bundle(proof, public)
        .map_err(V2OodRecursiveError::Bridge)?;
    let base_bundle = flatten_ext_to_base(&ext_bundle);
    let mut ood_seed = proof.pi_hash;
    ood_seed[0] ^= 0xF6;
    let ood_alphas = alphas_from_transcript::<Goldilocks>(
        &ood_seed, base_bundle.claims.len(),
    );
    let ood_claim = OodAccumulatorClaim {
        bundle: base_bundle, alphas: ood_alphas,
    };

    // Sub-circuit 3: vestige perm-arg.
    let perm_claim = build_v2_pi_hash_vestige_perm_arg(proof.pi_hash);

    prove_recursive_stark(&comp_claim, &ood_claim, &perm_claim, blowup, r, use_stir)
        .map_err(V2OodRecursiveError::RecursiveProver)
}

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
    #[ignore = "slow — full F2b OOD bundle (BCC-vs-BCC + BCC-vs-public)"]
    fn extract_v2_full_ood_bundle_honest() {
        let w = synthesize_demo_witness(19);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        // Public legs only.
        let public_bundle = extract_v2_public_leg_ood_bundle(&proof, &w)
            .expect("public-leg OOD bundle extraction must succeed");
        // mldsa-44 (L1): L=4, W1_BITS_PER_COEF=6 → 1+1+1+6+(4+3) = 16 claims
        let expected_public_count = 1 + 1 + 1 + W1_BITS_PER_COEF + (L + 3);
        assert_eq!(public_bundle.claims.len(), expected_public_count);
        assert!(public_bundle.check_all_native(),
            "honest v2 must satisfy all BCC-vs-public OOD legs; \
             first_failing = {:?}", public_bundle.first_failing());

        // Full bundle: BCC-vs-BCC (2) + BCC-vs-public (16) = 18 at mldsa-44.
        let full_bundle = extract_v2_full_ood_bundle(&proof, &w)
            .expect("full F2b OOD bundle extraction must succeed");
        assert_eq!(full_bundle.claims.len(), 2 + expected_public_count);
        assert!(full_bundle.check_all_native(),
            "honest v2 must satisfy ALL F2b OOD legs");
    }

    #[test]
    #[ignore = "slow — full F2b OOD bundle → recursive STARK round-trip"]
    fn prove_v2_full_ood_recursive_round_trip() {
        use crate::recursive_prover::verify_ood_accumulator;

        let w = synthesize_demo_witness(23);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let rec_proof = prove_v2_full_ood_recursive(&proof, &w, 4, 54, false)
            .expect("full v2 OOD recursive prove must succeed");
        assert!(verify_ood_accumulator(&rec_proof),
            "full v2 → recursive STARK must verify locally");
    }

    #[test]
    #[ignore = "slow — tampered public input breaks the full F2b bundle"]
    fn tampered_public_breaks_full_bundle() {
        let mut w = synthesize_demo_witness(29);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        // Honest bundle must accept.
        let honest = extract_v2_full_ood_bundle(&proof, &w).unwrap();
        assert!(honest.check_all_native());

        // Tamper a public h value — L2c's canonical column changes,
        // so g(z_ext) ≠ f(z_ext) at the L2c leg.
        w.h[0][0] ^= 1;
        let tampered = extract_v2_full_ood_bundle(&proof, &w).unwrap();
        assert!(!tampered.check_all_native(),
            "public.h tamper must break the F2b bundle");

        // L2c is at index 2 in the full bundle (after L2a, L3).
        assert_eq!(tampered.first_failing(), Some(2),
            "first failing should be L2c (index 2) after public.h tamper");
    }

    #[test]
    fn v2_pi_hash_anchor_composition_shape() {
        // Fast unit test: anchor has 256 cells + 256 Boolean constraints
        // + 256 alphas + expected = 0.  Doesn't require running v2.
        let pi_hash = [0xA5u8; 32];
        let claim = build_v2_pi_hash_anchor_composition(pi_hash);
        assert_eq!(claim.column_values.len(), 256);
        assert_eq!(claim.constraints.len(), 256);
        assert_eq!(claim.alphas.len(), 256);
        assert_eq!(claim.expected, Goldilocks::zero());

        // Each cell value is 0 or 1.
        for (_cref, v) in &claim.column_values {
            assert!(*v == Goldilocks::zero() || *v == Goldilocks::from(1u64),
                "cell value {v:?} not in {{0, 1}}");
        }
    }

    #[test]
    fn v2_pi_hash_vestige_perm_arg_is_trivially_equal() {
        let pi_hash = [0x5Au8; 32];
        let claim = build_v2_pi_hash_vestige_perm_arg(pi_hash);
        assert_eq!(claim.left.len(), 4);
        assert_eq!(claim.right.len(), 4);
        assert_eq!(claim.left, claim.right);
        assert_eq!(claim.perm_tag, "v2-pi-hash-vestige");
    }

    #[test]
    #[ignore = "slow — extract real V17 sub-AIR per-query residues"]
    fn build_v2_v17_subair_composition_honest() {
        let w = synthesize_demo_witness(37);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let claim = build_v2_v17_subair_composition(&proof)
            .expect("V17 residue extraction must succeed on honest proof");

        // V17 ships V2_NUM_QUERIES queries (L1 = 54) × EXT_DEGREE = 6 coords.
        assert_eq!(claim.constraints.len() % EXT_DEGREE, 0,
            "constraint count must be multiple of EXT_DEGREE");
        assert_eq!(claim.column_values.len(), claim.constraints.len());

        // Every cell value (= Goldilocks coord of an Ext residue) must
        // be zero on an honest proof.  Each BitOp::IsZero constraint
        // then evaluates to 0.
        for (_cref, v) in &claim.column_values {
            assert!(v.is_zero(),
                "honest V17 residue must be zero at every coord; got {v:?}");
        }
    }

    #[test]
    #[ignore = "slow — extract residues from ALL 10 v2 sub-AIRs"]
    fn extract_all_subair_residues_honest() {
        let w = synthesize_demo_witness(43);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let residues = extract_v2_all_subair_residues(&proof, &w)
            .expect("all-sub-AIR residue extraction must succeed");

        // Counts: V17 + K INTT + 3 COEFF + 1 TRANSCRIPT.
        assert!(!residues.v17.is_empty(), "V17 residues must be non-empty");
        assert_eq!(residues.intt.len(), K, "must have K INTT instances");
        for k in 0..K {
            assert!(!residues.intt[k].is_empty(),
                "INTT[{k}] residues must be non-empty");
        }
        assert!(!residues.decompose.is_empty());
        assert!(!residues.use_hint.is_empty());
        assert!(!residues.w1_encode.is_empty());
        assert!(!residues.transcript.is_empty());

        // Diagnostic: which sub-AIR has non-zero residues?
        use ark_ff::Zero as _;
        let v17_zero = residues.v17.iter().all(|r| r.is_zero());
        let intt_zero: Vec<bool> = residues.intt.iter().map(|v| v.iter().all(|r| r.is_zero())).collect();
        let dec_zero = residues.decompose.iter().all(|r| r.is_zero());
        let uh_zero = residues.use_hint.iter().all(|r| r.is_zero());
        let w1_zero = residues.w1_encode.iter().all(|r| r.is_zero());
        let tr_zero = residues.transcript.iter().all(|r| r.is_zero());
        eprintln!("per-sub-AIR zero-residue check: V17={v17_zero}, INTT={intt_zero:?}, Decompose={dec_zero}, UseHint={uh_zero}, W1Encode={w1_zero}, TRANSCRIPT={tr_zero}");

        assert!(residues.all_zero(),
            "honest v2: every residue across all 10 sub-AIRs must be zero");

        let total = residues.total();
        eprintln!("v2 sub-AIR residue totals @ L1: V17={}, INTT_per_k={}, Decompose={}, UseHint={}, W1Encode={}, TRANSCRIPT={}, total Ext={total}",
            residues.v17.len(), residues.intt[0].len(),
            residues.decompose.len(), residues.use_hint.len(),
            residues.w1_encode.len(), residues.transcript.len());
    }

    #[test]
    #[ignore = "slow — build CompositionClaim from all 10 sub-AIRs"]
    fn build_v2_all_subairs_composition_honest() {
        let w = synthesize_demo_witness(47);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let claim = build_v2_all_subairs_composition(&proof, &w)
            .expect("all-sub-AIRs composition must build on honest proof");

        // Multiple of EXT_DEGREE = 6.
        assert_eq!(claim.constraints.len() % EXT_DEGREE, 0);
        assert_eq!(claim.column_values.len(), claim.constraints.len());

        // All cell values zero on honest input.
        for (_cref, v) in &claim.column_values {
            assert!(v.is_zero(),
                "all-sub-AIRs honest composition: every coord must be zero; got {v:?}");
        }
    }

    #[test]
    #[ignore = "slow — full 10-sub-AIR composed RecursiveStarkProof"]
    fn prove_v2_all_subairs_composed_recursive_round_trip() {
        use crate::recursive_prover::verify_recursive_stark;

        let w = synthesize_demo_witness(53);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let rec = prove_v2_all_subairs_composed_recursive(&proof, &w, 4, 54, false)
            .expect("all-10-sub-AIR composed prove must succeed");

        assert!(verify_recursive_stark(&rec),
            "10-sub-AIR composed RecursiveStarkProof must verify locally");
    }

    #[test]
    #[ignore = "slow — V17-real composed RecursiveStarkProof end-to-end"]
    fn prove_v2_v17_composed_recursive_round_trip() {
        use crate::recursive_prover::verify_recursive_stark;

        let w = synthesize_demo_witness(41);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let rec = prove_v2_v17_composed_recursive(&proof, &w, 4, 54, false)
            .expect("V17-real composed recursive prove must succeed");

        assert!(verify_recursive_stark(&rec),
            "V17-real composed RecursiveStarkProof must verify locally");
    }

    #[test]
    #[ignore = "slow — full composed RecursiveStarkProof from real v2 proof"]
    fn prove_v2_composed_recursive_round_trip() {
        use crate::recursive_prover::verify_recursive_stark;

        let w = synthesize_demo_witness(31);
        let c_tilde: [u8; C_TILDE_BYTES] =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let proof = prove_v2_real(&w, &c_tilde, 4);

        let rec = prove_v2_composed_recursive(&proof, &w, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("composed recursive prove must succeed");

        assert!(verify_recursive_stark(&rec),
            "composed RecursiveStarkProof must verify locally");
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
