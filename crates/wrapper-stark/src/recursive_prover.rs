//! Recursive STARK prover — STEP 4 plumbing: takes a sub-circuit's
//! accumulator AIR (synthesised trace + column-major form from steps
//! 1-3) and produces a `DeepFriProof<SexticExt>` over the FRI/STIR LDT.
//!
//! # Currently implemented
//!
//! - `prove_composition_accumulator` / `verify_composition_accumulator`
//!   — wraps the constraint-composition accumulator AIR (sub-circuit
//!   1 of the recursive STARK) end-to-end through `deep_fri_prove`.
//!
//! Sub-circuits 2 (OOD residue) and 3 (perm-arg Π running product)
//! land in subsequent commits following the same template.
//!
//! # Pipeline (one sub-circuit)
//!
//! ```text
//!   CompositionClaim                                            (public + witness)
//!         │
//!         ▼  AccumulatorTrace::synthesise
//!   AccumulatorTrace                                            (n_rows × 3)
//!         │
//!         ▼  accumulator_trace_to_columns
//!   columns: Vec<Vec<F>>                                        (padded to next pow2)
//!         │
//!         ▼  lde_trace_columns
//!   LDE: Vec<Vec<F>>                                            (× blowup)
//!         │
//!         ▼  c_eval composition (Initial + Step + FinalBoundary,
//!         │  α_j FS-derived from pi_hash)
//!   c_eval: Vec<F>                                              (length n_lde)
//!         │
//!         ▼  deep_fri_prove::<SexticExt>(c_eval, domain, params)
//!   DeepFriProof<SexticExt>                                     (the artefact)
//! ```
//!
//! # Soundness story
//!
//! Three constraint families are alpha-weighted into `c_eval`:
//!
//! - **Initial** (gated by `indicator_0`):
//!   `α_init · indicator_0[r] · (sum[r] − alpha[r] · phi[r])`
//! - **Step** (masked off at row 0):
//!   `α_step · (1 − indicator_0[r]) · (sum[r] − sum_prev[r] − alpha[r] · phi[r])`
//! - **FinalBoundary** (gated by `indicator_last`):
//!   `α_final · indicator_last[r] · (sum[r] − expected)`
//!
//! where `sum_prev[r] = lde[sum_col][(r − blowup) mod n_lde]`.  Each α
//! is FS-derived from `pi_hash` with a distinct seed XOR.  On padding
//! rows the constraints stay satisfied because the trace synthesiser
//! sets `alpha = phi = 0` and `sum_pad = final_sum`, propagating the
//! invariant through the LDE.

use ark_ff::Zero;

use deep_ali::fri::{
    deep_fri_prove, deep_fri_verify, DeepFriProof, DeepFriParams, FriDomain,
};
use deep_ali::sextic_ext::SexticExt;
use deep_ali::trace_import::lde_trace_columns;

use crate::composition::alphas_from_transcript;
use crate::deep_ali_verifier_air::constraint_composition_verifier::{
    AccumulatorTrace, CompositionClaim, accumulator_trace_to_columns,
    verify_accumulator_columns,
};
use crate::deep_ali_verifier_air::binding_cells_ood_verifier::{
    OodAccumulatorTrace, OodClaimBundle, ood_accumulator_trace_to_columns,
    verify_ood_accumulator_columns,
};
use crate::deep_ali_verifier_air::permutation_argument_verifier::{
    PermArgAccumulatorTrace, PermArgClaim, perm_arg_accumulator_trace_to_columns,
    verify_perm_arg_accumulator_columns,
};
use crate::fri_bridge::compute_single_row_indicator_lde;

type FBase = ark_goldilocks::Goldilocks;
type Ext = SexticExt;

/// Errors from the recursive STARK prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursiveProverError {
    /// Claim shape is malformed (e.g. alphas count != constraints count).
    InvalidClaim(String),
    /// Synthesised trace failed its column-major self-check; bug in
    /// the AIR encoding rather than the prover wiring.
    TraceSelfCheckFailed,
    /// Configuration error (bad blowup, etc.).
    Internal(String),
}

impl std::fmt::Display for RecursiveProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidClaim(s) => write!(f, "invalid claim: {s}"),
            Self::TraceSelfCheckFailed => write!(f, "trace failed self-check"),
            Self::Internal(s) => write!(f, "recursive prover internal: {s}"),
        }
    }
}

impl std::error::Error for RecursiveProverError {}

/// Public inputs for the constraint-composition sub-circuit STARK.
/// Binds the claim's `expected` value, the alphas the prover used to
/// composer Φ, and a canonical hash of the claim's witness columns
/// into a 32-byte `pi_hash`.  The verifier needs only `pi_hash` +
/// `expected` + `n_constraints` to re-derive the same α_init/α_step/
/// α_final used by the prover.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositionAccumulatorPublicInputs {
    /// The expected composed value (= 0 on honest constraint set).
    pub expected: FBase,
    /// Number of constraints composed (= n_rows of the accumulator AIR).
    pub n_constraints: usize,
    /// 32-byte FS commitment binding (expected, n_constraints, alphas,
    /// claim-witness digest).  Re-derived by the verifier in the same
    /// way; if the prover lied about any input, the alphas it FS-derived
    /// won't match what the verifier will FS-derive.
    pub pi_hash: [u8; 32],
}

impl CompositionAccumulatorPublicInputs {
    /// Derive public inputs (incl. pi_hash) from a claim.  pi_hash binds:
    ///   "WRAPPER-COMP-ACC-V1"  ‖ expected_LE_bytes ‖ n_constraints_LE
    ///   ‖ for each j: alpha_j_LE ‖ phi_j_LE  ‖ final_sum_LE
    pub fn for_claim(claim: &CompositionClaim<FBase>) -> Self {
        use ::sha3::Digest;
        let n = claim.constraints.len();
        let trace = AccumulatorTrace::synthesise(claim);
        let final_sum = if n == 0 { FBase::zero() } else { trace.partial_sum[n - 1] };
        let mut h = ::sha3::Sha3_256::new();
        h.update(b"WRAPPER-COMP-ACC-V1");
        h.update(field_to_le_bytes(&claim.expected));
        h.update((n as u64).to_le_bytes());
        for j in 0..n {
            h.update(field_to_le_bytes(&trace.alpha[j]));
            h.update(field_to_le_bytes(&trace.phi[j]));
        }
        h.update(field_to_le_bytes(&final_sum));
        let digest = h.finalize();
        let mut pi_hash = [0u8; 32];
        pi_hash.copy_from_slice(&digest);
        Self { expected: claim.expected, n_constraints: n, pi_hash }
    }
}

/// Encode a Goldilocks field element as 8 little-endian bytes (it's a
/// 64-bit prime field, so this is canonical).
fn field_to_le_bytes(x: &FBase) -> [u8; 8] {
    use ark_ff::{BigInteger, PrimeField};
    let big = x.into_bigint();
    let mut buf = [0u8; 8];
    let limbs = big.to_bytes_le();
    let take = limbs.len().min(8);
    buf[..take].copy_from_slice(&limbs[..take]);
    buf
}

/// Recursive STARK proof for the constraint-composition sub-circuit.
pub struct CompositionAccumulatorProof {
    pub public: CompositionAccumulatorPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove the constraint-composition accumulator sub-circuit through
/// deep_fri_prove.
///
/// # Arguments
///
/// - `claim`: CompositionClaim (column-value table, constraints,
///   alphas, expected composed value)
/// - `blowup`: LDE blowup factor (production 32; smoke 4)
/// - `r`: FRI query count (paper Table 2: 54/79/105 for L1/L3/L5)
/// - `use_stir`: STIR (true) vs DEEP-FRI (false)
pub fn prove_composition_accumulator(
    claim: &CompositionClaim<FBase>,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<CompositionAccumulatorProof, RecursiveProverError> {
    // 0. Shape check.
    claim.check_shape().map_err(|e| RecursiveProverError::InvalidClaim(format!("{e:?}")))?;
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(RecursiveProverError::Internal(format!(
            "blowup must be power-of-2 >= 2; got {blowup}"
        )));
    }
    if claim.constraints.is_empty() {
        return Err(RecursiveProverError::InvalidClaim(
            "constraints must be non-empty".into()
        ));
    }

    // 1. Synthesise accumulator trace + derive public inputs.
    let trace = AccumulatorTrace::synthesise(claim);
    let public = CompositionAccumulatorPublicInputs::for_claim(claim);

    // 2. Column-major + padding.  3 columns: alpha, phi, partial_sum.
    let columns = accumulator_trace_to_columns(&trace);
    if !verify_accumulator_columns(&columns, claim.expected) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }
    let n_trace = columns[0].len();
    let n_lde = n_trace * blowup;

    // 3. LDE each column.
    let lde: Vec<Vec<FBase>> = lde_trace_columns(&columns, n_trace, blowup)
        .map_err(|e| RecursiveProverError::Internal(format!("LDE: {e}")))?;

    // 4. FS-derive α_init, α_step, α_final from pi_hash with distinct seeds.
    let mut seed_init  = public.pi_hash;  seed_init[0]  ^= 0xC1;
    let mut seed_step  = public.pi_hash;  seed_step[0]  ^= 0xC2;
    let mut seed_final = public.pi_hash;  seed_final[0] ^= 0xC3;
    let alpha_init  = alphas_from_transcript::<FBase>(&seed_init, 1)[0];
    let alpha_step  = alphas_from_transcript::<FBase>(&seed_step, 1)[0];
    let alpha_final = alphas_from_transcript::<FBase>(&seed_final, 1)[0];

    // 5. Build row indicators for boundary constraints.
    let ind_0    = compute_single_row_indicator_lde(0, n_trace, blowup);
    let ind_last = compute_single_row_indicator_lde(n_trace - 1, n_trace, blowup);

    // 6. Compose c_eval per LDE row.
    //
    //    α_init  · ind_0[r]      · (sum[r] − alpha[r] · phi[r])
    //  + α_step  · (1 − ind_0[r]) · (sum[r] − sum_prev[r] − alpha[r] · phi[r])
    //  + α_final · ind_last[r]   · (sum[r] − expected)
    //
    //  sum_prev[r] = lde[sum_col][(r − blowup) mod n_lde]
    let (alpha_lde, phi_lde, sum_lde) = (&lde[0], &lde[1], &lde[2]);
    let mut c_eval = vec![FBase::zero(); n_lde];
    let shift = blowup;
    for idx in 0..n_lde {
        let r_prev = (idx + n_lde - shift) % n_lde;
        let curr_sum = sum_lde[idx];
        let prev_sum = sum_lde[r_prev];
        let alpha_v  = alpha_lde[idx];
        let phi_v    = phi_lde[idx];

        let init_term  = curr_sum - alpha_v * phi_v;
        let step_term  = curr_sum - prev_sum - alpha_v * phi_v;
        let final_term = curr_sum - claim.expected;

        let i0 = ind_0[idx];
        let il = ind_last[idx];
        let not_i0 = FBase::from(1u64) - i0;

        c_eval[idx]  = alpha_init  * i0     * init_term;
        c_eval[idx] += alpha_step  * not_i0 * step_term;
        c_eval[idx] += alpha_final * il     * final_term;
    }

    // 7. Build FRI domain + params + run deep_fri_prove.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.pi_hash);
    if use_stir { params.stir = true; }

    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    Ok(CompositionAccumulatorProof {
        public, fri_proof, n_trace, blowup, r, use_stir,
    })
}

/// Verify a composition-accumulator STARK proof.  Reconstructs the FRI
/// params from the proof's bookkeeping + public inputs and invokes
/// `deep_fri_verify`.
pub fn verify_composition_accumulator(proof: &CompositionAccumulatorProof) -> bool {
    let n_lde = proof.n_trace * proof.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, proof.r, 0xDEEFu64);
    params.public_inputs_hash = Some(proof.public.pi_hash);
    if proof.use_stir { params.stir = true; }
    deep_fri_verify::<Ext>(&params, &proof.fri_proof)
}

// ─── Sub-circuit 2: OOD residue accumulator ───────────────────────────

/// Standalone claim for the OOD residue accumulator prover.  Bundles
/// the (f, g) equality claims together with their FS-derived alphas
/// — equivalent to (bundle, alphas) but ergonomic for one-shot proving.
#[derive(Clone, Debug)]
pub struct OodAccumulatorClaim {
    pub bundle: OodClaimBundle<FBase>,
    pub alphas: Vec<FBase>,
}

impl OodAccumulatorClaim {
    /// Shape check: alphas count must match bundle size.
    pub fn check_shape(&self) -> Result<(), String> {
        if self.alphas.len() != self.bundle.claims.len() {
            return Err(format!(
                "alphas count {} != claims count {}",
                self.alphas.len(), self.bundle.claims.len()
            ));
        }
        Ok(())
    }
}

/// Public inputs for the OOD-accumulator sub-circuit STARK.  Binds the
/// claim's claim-count, the alphas, and the (f, g) witness columns
/// into a 32-byte `pi_hash`.  Boundary is fixed at 0 (sum = 0 at the
/// final row), so it's not part of the public inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OodAccumulatorPublicInputs {
    pub n_claims: usize,
    pub pi_hash: [u8; 32],
}

impl OodAccumulatorPublicInputs {
    pub fn for_claim(claim: &OodAccumulatorClaim) -> Self {
        use ::sha3::Digest;
        let n = claim.bundle.claims.len();
        let mut h = ::sha3::Sha3_256::new();
        h.update(b"WRAPPER-OOD-ACC-V1");
        h.update((n as u64).to_le_bytes());
        for j in 0..n {
            h.update(field_to_le_bytes(&claim.bundle.claims[j].f_at_z));
            h.update(field_to_le_bytes(&claim.bundle.claims[j].g_at_z));
            h.update(field_to_le_bytes(&claim.alphas[j]));
        }
        let digest = h.finalize();
        let mut pi_hash = [0u8; 32];
        pi_hash.copy_from_slice(&digest);
        Self { n_claims: n, pi_hash }
    }
}

/// Recursive STARK proof for the OOD residue sub-circuit.
pub struct OodAccumulatorProof {
    pub public: OodAccumulatorPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove the OOD residue accumulator sub-circuit through deep_fri_prove.
///
/// Constraint families composed into c_eval:
///
///   α_res  · (residue − (f − g))                              — every row
///   α_init · ind_0     · (sum − α · residue)                  — row 0
///   α_step · (1 − ind_0) · (sum − sum_prev − α · residue)     — r > 0
///   α_fin  · ind_last  · sum                                  — last row
pub fn prove_ood_accumulator(
    claim: &OodAccumulatorClaim,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<OodAccumulatorProof, RecursiveProverError> {
    claim.check_shape().map_err(RecursiveProverError::InvalidClaim)?;
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(RecursiveProverError::Internal(format!(
            "blowup must be power-of-2 >= 2; got {blowup}"
        )));
    }
    if claim.bundle.claims.is_empty() {
        return Err(RecursiveProverError::InvalidClaim(
            "bundle must have at least one claim".into()
        ));
    }

    // 1. Synthesise OOD accumulator trace + derive public inputs.
    let trace = OodAccumulatorTrace::synthesise(&claim.bundle, &claim.alphas);
    let public = OodAccumulatorPublicInputs::for_claim(claim);

    // 2. Column-major + padding (5 cols: f, g, residue, alpha, partial_sum).
    let columns = ood_accumulator_trace_to_columns(&trace);
    if !verify_ood_accumulator_columns(&columns) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }
    let n_trace = columns[0].len();
    let n_lde = n_trace * blowup;

    // 3. LDE each column.
    let lde: Vec<Vec<FBase>> = lde_trace_columns(&columns, n_trace, blowup)
        .map_err(|e| RecursiveProverError::Internal(format!("LDE: {e}")))?;

    // 4. FS-derive α_res, α_init, α_step, α_fin from pi_hash.
    let mut s_res  = public.pi_hash;  s_res[0]  ^= 0xD0;
    let mut s_init = public.pi_hash;  s_init[0] ^= 0xD1;
    let mut s_step = public.pi_hash;  s_step[0] ^= 0xD2;
    let mut s_fin  = public.pi_hash;  s_fin[0]  ^= 0xD3;
    let a_res   = alphas_from_transcript::<FBase>(&s_res, 1)[0];
    let a_init  = alphas_from_transcript::<FBase>(&s_init, 1)[0];
    let a_step  = alphas_from_transcript::<FBase>(&s_step, 1)[0];
    let a_final = alphas_from_transcript::<FBase>(&s_fin, 1)[0];

    // 5. Row indicators.
    let ind_0    = compute_single_row_indicator_lde(0, n_trace, blowup);
    let ind_last = compute_single_row_indicator_lde(n_trace - 1, n_trace, blowup);

    // 6. Compose c_eval.
    let (f_lde, g_lde, res_lde, alpha_lde, sum_lde) =
        (&lde[0], &lde[1], &lde[2], &lde[3], &lde[4]);
    let mut c_eval = vec![FBase::zero(); n_lde];
    let shift = blowup;
    for idx in 0..n_lde {
        let r_prev = (idx + n_lde - shift) % n_lde;
        let f_v   = f_lde[idx];
        let g_v   = g_lde[idx];
        let res_v = res_lde[idx];
        let a_v   = alpha_lde[idx];
        let sum_v = sum_lde[idx];
        let sum_p = sum_lde[r_prev];

        let res_def    = res_v - (f_v - g_v);
        let init_term  = sum_v - a_v * res_v;
        let step_term  = sum_v - sum_p - a_v * res_v;
        let final_term = sum_v;

        let i0 = ind_0[idx];
        let il = ind_last[idx];
        let not_i0 = FBase::from(1u64) - i0;

        c_eval[idx]  = a_res   * res_def;
        c_eval[idx] += a_init  * i0     * init_term;
        c_eval[idx] += a_step  * not_i0 * step_term;
        c_eval[idx] += a_final * il     * final_term;
    }

    // 7. FRI prove.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.pi_hash);
    if use_stir { params.stir = true; }

    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    Ok(OodAccumulatorProof {
        public, fri_proof, n_trace, blowup, r, use_stir,
    })
}

/// Verify an OOD residue accumulator STARK proof.
pub fn verify_ood_accumulator(proof: &OodAccumulatorProof) -> bool {
    let n_lde = proof.n_trace * proof.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, proof.r, 0xDEEFu64);
    params.public_inputs_hash = Some(proof.public.pi_hash);
    if proof.use_stir { params.stir = true; }
    deep_fri_verify::<Ext>(&params, &proof.fri_proof)
}

// ─── Sub-circuit 3: Perm-arg Π running-product accumulator ────────────

/// Public inputs for the perm-arg sub-circuit STARK.  Binds the
/// challenge γ, the perm-tag (domain separator), and the (left, right)
/// witness multisets into a 32-byte `pi_hash`.  The verifier needs γ
/// to reconstruct the per-row (γ + l) and (γ + r) factors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermArgPublicInputs {
    pub gamma: FBase,
    pub n_elements: usize,
    pub pi_hash: [u8; 32],
}

impl PermArgPublicInputs {
    pub fn for_claim(claim: &PermArgClaim<FBase>) -> Self {
        use ::sha3::Digest;
        let n = claim.left.len();
        let mut h = ::sha3::Sha3_256::new();
        h.update(b"WRAPPER-PERMARG-V1");
        h.update(field_to_le_bytes(&claim.gamma));
        h.update(claim.perm_tag.as_bytes());
        h.update((claim.perm_tag.len() as u64).to_le_bytes());
        h.update((n as u64).to_le_bytes());
        for x in &claim.left  { h.update(field_to_le_bytes(x)); }
        h.update((claim.right.len() as u64).to_le_bytes());
        for x in &claim.right { h.update(field_to_le_bytes(x)); }
        let digest = h.finalize();
        let mut pi_hash = [0u8; 32];
        pi_hash.copy_from_slice(&digest);
        Self { gamma: claim.gamma, n_elements: n, pi_hash }
    }
}

/// Recursive STARK proof for the perm-arg sub-circuit.
pub struct PermArgProof {
    pub public: PermArgPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove the perm-arg Π running-product accumulator sub-circuit through
/// deep_fri_prove.  Five constraint families:
///
///   α_il · ind_0    · (rl − (γ + l))                       — row 0
///   α_ir · ind_0    · (rr − (γ + r))                       — row 0
///   α_sl · (1−ind_0)·(rl − rl_prev · (γ + l))              — r > 0
///   α_sr · (1−ind_0)·(rr − rr_prev · (γ + r))              — r > 0
///   α_fn · ind_last · (rl − rr)                            — last row
pub fn prove_perm_arg_accumulator(
    claim: &PermArgClaim<FBase>,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<PermArgProof, RecursiveProverError> {
    claim.check_shape().map_err(RecursiveProverError::InvalidClaim)?;
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(RecursiveProverError::Internal(format!(
            "blowup must be power-of-2 >= 2; got {blowup}"
        )));
    }
    if claim.left.is_empty() {
        return Err(RecursiveProverError::InvalidClaim(
            "left multiset must be non-empty".into()
        ));
    }

    // 1. Synthesise perm-arg accumulator trace + derive public inputs.
    let trace = PermArgAccumulatorTrace::synthesise(claim);
    let public = PermArgPublicInputs::for_claim(claim);

    // 2. Column-major + padding (4 cols: l, r, running_left, running_right).
    let columns = perm_arg_accumulator_trace_to_columns(&trace);
    if !verify_perm_arg_accumulator_columns(&columns, claim.gamma) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }
    let n_trace = columns[0].len();
    let n_lde = n_trace * blowup;

    // 3. LDE each column.
    let lde: Vec<Vec<FBase>> = lde_trace_columns(&columns, n_trace, blowup)
        .map_err(|e| RecursiveProverError::Internal(format!("LDE: {e}")))?;

    // 4. FS-derive five α's from pi_hash with distinct seeds.
    let mut s_il = public.pi_hash;  s_il[0] ^= 0xE0;
    let mut s_ir = public.pi_hash;  s_ir[0] ^= 0xE1;
    let mut s_sl = public.pi_hash;  s_sl[0] ^= 0xE2;
    let mut s_sr = public.pi_hash;  s_sr[0] ^= 0xE3;
    let mut s_fn = public.pi_hash;  s_fn[0] ^= 0xE4;
    let a_il = alphas_from_transcript::<FBase>(&s_il, 1)[0];
    let a_ir = alphas_from_transcript::<FBase>(&s_ir, 1)[0];
    let a_sl = alphas_from_transcript::<FBase>(&s_sl, 1)[0];
    let a_sr = alphas_from_transcript::<FBase>(&s_sr, 1)[0];
    let a_fn = alphas_from_transcript::<FBase>(&s_fn, 1)[0];

    // 5. Row indicators.
    let ind_0    = compute_single_row_indicator_lde(0, n_trace, blowup);
    let ind_last = compute_single_row_indicator_lde(n_trace - 1, n_trace, blowup);

    // 6. Compose c_eval.
    let (l_lde, r_lde, rl_lde, rr_lde) = (&lde[0], &lde[1], &lde[2], &lde[3]);
    let gamma = claim.gamma;
    let mut c_eval = vec![FBase::zero(); n_lde];
    let shift = blowup;
    for idx in 0..n_lde {
        let r_prev = (idx + n_lde - shift) % n_lde;
        let l_v   = l_lde[idx];
        let rt_v  = r_lde[idx];
        let rl_v  = rl_lde[idx];
        let rr_v  = rr_lde[idx];
        let rl_p  = rl_lde[r_prev];
        let rr_p  = rr_lde[r_prev];

        let init_l = rl_v - (gamma + l_v);
        let init_r = rr_v - (gamma + rt_v);
        let step_l = rl_v - rl_p * (gamma + l_v);
        let step_r = rr_v - rr_p * (gamma + rt_v);
        let final_t = rl_v - rr_v;

        let i0 = ind_0[idx];
        let il = ind_last[idx];
        let not_i0 = FBase::from(1u64) - i0;

        c_eval[idx]  = a_il * i0     * init_l;
        c_eval[idx] += a_ir * i0     * init_r;
        c_eval[idx] += a_sl * not_i0 * step_l;
        c_eval[idx] += a_sr * not_i0 * step_r;
        c_eval[idx] += a_fn * il     * final_t;
    }

    // 7. FRI prove.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.pi_hash);
    if use_stir { params.stir = true; }

    let fri_proof = deep_fri_prove::<Ext>(c_eval, domain, &params);

    Ok(PermArgProof {
        public, fri_proof, n_trace, blowup, r, use_stir,
    })
}

/// Verify a perm-arg accumulator STARK proof.
pub fn verify_perm_arg_accumulator(proof: &PermArgProof) -> bool {
    let n_lde = proof.n_trace * proof.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, proof.r, 0xDEEFu64);
    params.public_inputs_hash = Some(proof.public.pi_hash);
    if proof.use_stir { params.stir = true; }
    deep_fri_verify::<Ext>(&params, &proof.fri_proof)
}

// ─── STEP 6: outer composition — one FRI proof for all three ──────────
//
// Collapses the three independent per-sub-circuit FRI proofs into ONE
// outer DeepFriProof attesting the entire recursive STARK statement:
//
//   ∃ witnesses such that:
//     1. Σ α_j · Φ_j = expected   (constraint composition)
//   ∧ 2. Σ α_j · (f_j − g_j) = 0  (binding-cells OOD)
//   ∧ 3. ∏(γ + l_i) = ∏(γ + r_i)  (perm-arg multiset equality)
//
// All three sub-circuits' columns are LDE'd on a single shared domain
// of size `n_trace_max × blowup`, where `n_trace_max` is the next
// power-of-2 strictly large enough to host each sub-circuit's column-
// major trace.  Per-sub-circuit c_eval contributions are summed with
// outer α's FS-derived from `outer_pi_hash`.

/// Pad a column to a target length using a closure that produces the
/// next value given the current padding row (0-indexed from start of
/// padding) and the previous row's value at this column.
fn pad_column<F: Clone>(col: &mut Vec<F>, target: usize, mut next: impl FnMut(usize, &F) -> F) {
    let mut k = 0usize;
    while col.len() < target {
        let prev = col.last().unwrap().clone();
        col.push(next(k, &prev));
        k += 1;
    }
}

/// Public inputs for the composed recursive STARK proof.  Binds all
/// three sub-circuit pi_hashes + `n_trace_max` into one outer pi_hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveStarkPublicInputs {
    pub composition: CompositionAccumulatorPublicInputs,
    pub ood: OodAccumulatorPublicInputs,
    pub perm_arg: PermArgPublicInputs,
    pub n_trace_max: usize,
    pub outer_pi_hash: [u8; 32],
}

impl RecursiveStarkPublicInputs {
    pub fn for_claims(
        comp_claim: &CompositionClaim<FBase>,
        ood_claim: &OodAccumulatorClaim,
        perm_claim: &PermArgClaim<FBase>,
        n_trace_max: usize,
    ) -> Self {
        use ::sha3::Digest;
        let composition = CompositionAccumulatorPublicInputs::for_claim(comp_claim);
        let ood = OodAccumulatorPublicInputs::for_claim(ood_claim);
        let perm_arg = PermArgPublicInputs::for_claim(perm_claim);
        let mut h = ::sha3::Sha3_256::new();
        h.update(b"WRAPPER-RECURSIVE-V1");
        h.update(composition.pi_hash);
        h.update(ood.pi_hash);
        h.update(perm_arg.pi_hash);
        h.update((n_trace_max as u64).to_le_bytes());
        let digest = h.finalize();
        let mut outer_pi_hash = [0u8; 32];
        outer_pi_hash.copy_from_slice(&digest);
        Self { composition, ood, perm_arg, n_trace_max, outer_pi_hash }
    }
}

/// Composed recursive STARK proof.  Single DeepFriProof attesting all
/// three sub-circuits simultaneously.
pub struct RecursiveStarkProof {
    pub public: RecursiveStarkPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove the recursive STARK statement — all three sub-circuits
/// composed into ONE outer FRI proof.
pub fn prove_recursive_stark(
    comp_claim: &CompositionClaim<FBase>,
    ood_claim: &OodAccumulatorClaim,
    perm_claim: &PermArgClaim<FBase>,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, RecursiveProverError> {
    // 0. Shape checks.
    comp_claim.check_shape().map_err(|e| RecursiveProverError::InvalidClaim(format!("{e:?}")))?;
    ood_claim.check_shape().map_err(RecursiveProverError::InvalidClaim)?;
    perm_claim.check_shape().map_err(RecursiveProverError::InvalidClaim)?;
    if !blowup.is_power_of_two() || blowup < 2 {
        return Err(RecursiveProverError::Internal(format!(
            "blowup must be power-of-2 >= 2; got {blowup}"
        )));
    }
    if comp_claim.constraints.is_empty() {
        return Err(RecursiveProverError::InvalidClaim(
            "composition constraints must be non-empty".into()
        ));
    }
    if ood_claim.bundle.claims.is_empty() {
        return Err(RecursiveProverError::InvalidClaim(
            "OOD bundle must be non-empty".into()
        ));
    }
    if perm_claim.left.is_empty() {
        return Err(RecursiveProverError::InvalidClaim(
            "perm-arg multiset must be non-empty".into()
        ));
    }

    // 1. Synthesise all three sub-circuits + their initial column-major.
    let comp_trace = AccumulatorTrace::synthesise(comp_claim);
    let mut comp_cols = accumulator_trace_to_columns(&comp_trace);
    if !verify_accumulator_columns(&comp_cols, comp_claim.expected) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }

    let ood_trace = OodAccumulatorTrace::synthesise(&ood_claim.bundle, &ood_claim.alphas);
    let mut ood_cols = ood_accumulator_trace_to_columns(&ood_trace);
    if !verify_ood_accumulator_columns(&ood_cols) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }

    let perm_trace = PermArgAccumulatorTrace::synthesise(perm_claim);
    let mut perm_cols = perm_arg_accumulator_trace_to_columns(&perm_trace);
    if !verify_perm_arg_accumulator_columns(&perm_cols, perm_claim.gamma) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }

    // 2. Compute n_trace_max = max of (already pow2) padded lengths.
    let n_trace_max = comp_cols[0].len()
        .max(ood_cols[0].len())
        .max(perm_cols[0].len());
    debug_assert!(n_trace_max.is_power_of_two());
    let n_lde = n_trace_max * blowup;

    // 3. Pad each sub-circuit's columns to n_trace_max using its rule.
    //
    //    Composition padding rule: alpha=phi=0, sum carries (=final).
    //    OOD padding rule:         f=g=residue=alpha=0, sum carries (=0).
    //    Perm-arg padding rule:    l=r=0, rl & rr multiply by γ.
    //
    //    Each sub-circuit's step-3 trace_to_columns already pads to its
    //    own next pow2; here we extend further (if needed) to the shared
    //    n_trace_max while preserving each sub-circuit's invariants.
    pad_column(&mut comp_cols[0], n_trace_max, |_, _| FBase::zero());        // alpha
    pad_column(&mut comp_cols[1], n_trace_max, |_, _| FBase::zero());        // phi
    pad_column(&mut comp_cols[2], n_trace_max, |_, prev| *prev);             // sum

    pad_column(&mut ood_cols[0], n_trace_max, |_, _| FBase::zero());         // f
    pad_column(&mut ood_cols[1], n_trace_max, |_, _| FBase::zero());         // g
    pad_column(&mut ood_cols[2], n_trace_max, |_, _| FBase::zero());         // residue
    pad_column(&mut ood_cols[3], n_trace_max, |_, _| FBase::zero());         // alpha
    pad_column(&mut ood_cols[4], n_trace_max, |_, prev| *prev);              // sum

    let gamma = perm_claim.gamma;
    pad_column(&mut perm_cols[0], n_trace_max, |_, _| FBase::zero());        // l
    pad_column(&mut perm_cols[1], n_trace_max, |_, _| FBase::zero());        // r
    pad_column(&mut perm_cols[2], n_trace_max, |_, prev| *prev * gamma);     // rl
    pad_column(&mut perm_cols[3], n_trace_max, |_, prev| *prev * gamma);     // rr

    // Re-verify each sub-circuit's column form at the new shared length.
    if !verify_accumulator_columns(&comp_cols, comp_claim.expected) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }
    if !verify_ood_accumulator_columns(&ood_cols) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }
    if !verify_perm_arg_accumulator_columns(&perm_cols, gamma) {
        return Err(RecursiveProverError::TraceSelfCheckFailed);
    }

    // 4. LDE every column on the shared domain.
    let comp_lde = lde_trace_columns(&comp_cols, n_trace_max, blowup)
        .map_err(|e| RecursiveProverError::Internal(format!("comp LDE: {e}")))?;
    let ood_lde = lde_trace_columns(&ood_cols, n_trace_max, blowup)
        .map_err(|e| RecursiveProverError::Internal(format!("ood LDE: {e}")))?;
    let perm_lde = lde_trace_columns(&perm_cols, n_trace_max, blowup)
        .map_err(|e| RecursiveProverError::Internal(format!("perm LDE: {e}")))?;

    // 5. Derive outer pi_hash + outer alphas.
    let public = RecursiveStarkPublicInputs::for_claims(
        comp_claim, ood_claim, perm_claim, n_trace_max,
    );
    let mut s_o_c = public.outer_pi_hash;  s_o_c[0] ^= 0xF0;
    let mut s_o_o = public.outer_pi_hash;  s_o_o[0] ^= 0xF1;
    let mut s_o_p = public.outer_pi_hash;  s_o_p[0] ^= 0xF2;
    let outer_a_comp = alphas_from_transcript::<FBase>(&s_o_c, 1)[0];
    let outer_a_ood  = alphas_from_transcript::<FBase>(&s_o_o, 1)[0];
    let outer_a_perm = alphas_from_transcript::<FBase>(&s_o_p, 1)[0];

    // 6. Build shared row indicators at n_trace_max.
    let ind_0    = compute_single_row_indicator_lde(0, n_trace_max, blowup);
    let ind_last = compute_single_row_indicator_lde(n_trace_max - 1, n_trace_max, blowup);

    // 7. Compute per-sub-circuit inner α's from each sub-circuit's pi_hash.
    let comp_pi = public.composition.pi_hash;
    let ood_pi  = public.ood.pi_hash;
    let perm_pi = public.perm_arg.pi_hash;
    let mut s; // reused scratch
    s = comp_pi;  s[0] ^= 0xC1;  let c_a_init = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = comp_pi;  s[0] ^= 0xC2;  let c_a_step = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = comp_pi;  s[0] ^= 0xC3;  let c_a_fin  = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = ood_pi;   s[0] ^= 0xD0;  let o_a_res  = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = ood_pi;   s[0] ^= 0xD1;  let o_a_init = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = ood_pi;   s[0] ^= 0xD2;  let o_a_step = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = ood_pi;   s[0] ^= 0xD3;  let o_a_fin  = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = perm_pi;  s[0] ^= 0xE0;  let p_a_il   = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = perm_pi;  s[0] ^= 0xE1;  let p_a_ir   = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = perm_pi;  s[0] ^= 0xE2;  let p_a_sl   = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = perm_pi;  s[0] ^= 0xE3;  let p_a_sr   = alphas_from_transcript::<FBase>(&s, 1)[0];
    s = perm_pi;  s[0] ^= 0xE4;  let p_a_fn   = alphas_from_transcript::<FBase>(&s, 1)[0];

    // 8. Compose outer_c_eval per LDE row across all three sub-circuits.
    let (c_alpha, c_phi, c_sum) = (&comp_lde[0], &comp_lde[1], &comp_lde[2]);
    let (o_f, o_g, o_res, o_alpha, o_sum) =
        (&ood_lde[0], &ood_lde[1], &ood_lde[2], &ood_lde[3], &ood_lde[4]);
    let (p_l, p_r, p_rl, p_rr) =
        (&perm_lde[0], &perm_lde[1], &perm_lde[2], &perm_lde[3]);

    let shift = blowup;
    let mut outer_c_eval = vec![FBase::zero(); n_lde];
    for idx in 0..n_lde {
        let r_prev = (idx + n_lde - shift) % n_lde;
        let i0 = ind_0[idx];
        let il = ind_last[idx];
        let not_i0 = FBase::from(1u64) - i0;

        // Sub-circuit 1: constraint composition.
        let comp_init  = c_sum[idx] - c_alpha[idx] * c_phi[idx];
        let comp_step  = c_sum[idx] - c_sum[r_prev] - c_alpha[idx] * c_phi[idx];
        let comp_final = c_sum[idx] - comp_claim.expected;
        let comp_term  =
              c_a_init * i0     * comp_init
            + c_a_step * not_i0 * comp_step
            + c_a_fin  * il     * comp_final;

        // Sub-circuit 2: OOD residue accumulator.
        let ood_res_def    = o_res[idx] - (o_f[idx] - o_g[idx]);
        let ood_init       = o_sum[idx] - o_alpha[idx] * o_res[idx];
        let ood_step       = o_sum[idx] - o_sum[r_prev] - o_alpha[idx] * o_res[idx];
        let ood_final      = o_sum[idx];
        let ood_term  =
              o_a_res  * ood_res_def
            + o_a_init * i0     * ood_init
            + o_a_step * not_i0 * ood_step
            + o_a_fin  * il     * ood_final;

        // Sub-circuit 3: perm-arg Π running-product.
        let perm_init_l  = p_rl[idx] - (gamma + p_l[idx]);
        let perm_init_r  = p_rr[idx] - (gamma + p_r[idx]);
        let perm_step_l  = p_rl[idx] - p_rl[r_prev] * (gamma + p_l[idx]);
        let perm_step_r  = p_rr[idx] - p_rr[r_prev] * (gamma + p_r[idx]);
        let perm_final   = p_rl[idx] - p_rr[idx];
        let perm_term  =
              p_a_il * i0     * perm_init_l
            + p_a_ir * i0     * perm_init_r
            + p_a_sl * not_i0 * perm_step_l
            + p_a_sr * not_i0 * perm_step_r
            + p_a_fn * il     * perm_final;

        // Outer α-weighted sum.
        outer_c_eval[idx] = outer_a_comp * comp_term
                          + outer_a_ood  * ood_term
                          + outer_a_perm * perm_term;
    }

    // 9. Run deep_fri_prove on the outer composed c_eval.
    let domain = FriDomain::new_radix2(n_lde);
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, r, 0xDEEFu64);
    params.public_inputs_hash = Some(public.outer_pi_hash);
    if use_stir { params.stir = true; }

    let fri_proof = deep_fri_prove::<Ext>(outer_c_eval, domain, &params);

    Ok(RecursiveStarkProof {
        public, fri_proof, n_trace: n_trace_max, blowup, r, use_stir,
    })
}

/// Verify the composed recursive STARK proof.  Reconstructs the FRI
/// params from the outer pi_hash + proof bookkeeping and invokes
/// `deep_fri_verify`.
pub fn verify_recursive_stark(proof: &RecursiveStarkProof) -> bool {
    let n_lde = proof.n_trace * proof.blowup;
    let log2_n_lde = n_lde.trailing_zeros() as usize;
    let schedule: Vec<usize> = (0..log2_n_lde).map(|_| 2).collect();
    let mut params = DeepFriParams::new(schedule, proof.r, 0xDEEFu64);
    params.public_inputs_hash = Some(proof.public.outer_pi_hash);
    if proof.use_stir { params.stir = true; }
    deep_fri_verify::<Ext>(&params, &proof.fri_proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bit_constraint::{BitOp, CellRef};

    fn gf(x: u64) -> FBase { FBase::from(x) }

    fn xor_chain_claim() -> CompositionClaim<FBase> {
        // Eight cells, six XOR constraints chained.  All satisfied.
        let mut cells = Vec::new();
        for i in 0..8 {
            cells.push((CellRef::new(0, i), gf((i as u64) & 1)));
        }
        let mut constraints = Vec::new();
        for i in 0..6 {
            constraints.push(BitOp::Xor {
                c: CellRef::new(0, i + 2),
                a: CellRef::new(0, i),
                b: CellRef::new(0, i + 1),
            });
        }
        // Re-derive cell c-values so the XORs are honest:
        // c[i+2] = a[i] XOR b[i+1].  Build by overwriting.
        let mut vals: Vec<u8> = vec![0u8; 8];
        vals[0] = 1; vals[1] = 0;  // arbitrary seed bits
        for i in 0..6 {
            vals[i + 2] = vals[i] ^ vals[i + 1];
        }
        let column_values: Vec<(CellRef, FBase)> = (0..8)
            .map(|i| (CellRef::new(0, i), gf(vals[i] as u64))).collect();
        let alphas: Vec<FBase> = (1..=6u64).map(gf).collect();
        CompositionClaim { column_values, constraints, alphas, expected: gf(0) }
    }

    #[test]
    fn public_inputs_pi_hash_is_deterministic() {
        let claim = xor_chain_claim();
        let a = CompositionAccumulatorPublicInputs::for_claim(&claim);
        let b = CompositionAccumulatorPublicInputs::for_claim(&claim);
        assert_eq!(a.pi_hash, b.pi_hash);
        assert_eq!(a.expected, b.expected);
        assert_eq!(a.n_constraints, b.n_constraints);
    }

    #[test]
    fn public_inputs_pi_hash_changes_with_expected() {
        let mut claim = xor_chain_claim();
        let a = CompositionAccumulatorPublicInputs::for_claim(&claim);
        claim.expected = gf(42);
        // Note: changing expected without changing the trace makes the
        // trace inconsistent — but pi_hash derivation is purely
        // structural, so it should still produce a distinct hash.
        let b = CompositionAccumulatorPublicInputs::for_claim(&claim);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn prove_rejects_empty_constraints() {
        let claim = CompositionClaim::<FBase> {
            column_values: vec![],
            constraints: vec![],
            alphas: vec![],
            expected: gf(0),
        };
        let result = prove_composition_accumulator(&claim, 4, 54, false);
        assert!(matches!(result,
            Err(RecursiveProverError::InvalidClaim(_))));
    }

    #[test]
    fn prove_rejects_bad_blowup() {
        let claim = xor_chain_claim();
        let result = prove_composition_accumulator(&claim, 3, 54, false);
        assert!(matches!(result, Err(RecursiveProverError::Internal(_))));
    }

    #[test]
    #[ignore = "slow — exercises full FRI prove + verify round-trip"]
    fn round_trip_composition_accumulator_smoke() {
        let claim = xor_chain_claim();
        let proof = prove_composition_accumulator(&claim, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("prove must succeed on valid claim");
        assert!(verify_composition_accumulator(&proof),
            "round-trip verify must accept on honest proof");
    }

    #[test]
    #[ignore = "slow — exercises tamper rejection"]
    fn round_trip_rejects_tampered_pi_hash() {
        let claim = xor_chain_claim();
        let mut proof = prove_composition_accumulator(&claim, 4, 54, false)
            .expect("prove must succeed");
        proof.public.pi_hash[0] ^= 0xFF;
        assert!(!verify_composition_accumulator(&proof),
            "tampered pi_hash must be rejected by FS-binding");
    }

    #[test]
    #[ignore = "slow — exercises STIR variant"]
    fn round_trip_composition_accumulator_stir() {
        let claim = xor_chain_claim();
        let proof = prove_composition_accumulator(&claim, 4, 54, true)
            .expect("STIR prove must succeed");
        assert!(verify_composition_accumulator(&proof),
            "STIR round-trip verify must accept");
    }

    // ─── Sub-circuit 2 (OOD residue accumulator) tests ─────────────

    use crate::deep_ali_verifier_air::binding_cells_ood_verifier::OodEqualityClaim;

    fn ood_honest_claim() -> OodAccumulatorClaim {
        let z = gf(0xC0FFEE_DEAD_BEEFu64);
        let v = gf(0x12345);
        let bundle = OodClaimBundle::<FBase> {
            claims: vec![
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2a" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2b" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2c" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L3" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L4" },
                OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L5" },
            ],
        };
        let alphas: Vec<FBase> = (1..=7u64).map(gf).collect();
        OodAccumulatorClaim { bundle, alphas }
    }

    #[test]
    fn ood_public_inputs_pi_hash_is_deterministic() {
        let claim = ood_honest_claim();
        let a = OodAccumulatorPublicInputs::for_claim(&claim);
        let b = OodAccumulatorPublicInputs::for_claim(&claim);
        assert_eq!(a.pi_hash, b.pi_hash);
        assert_eq!(a.n_claims, 7);
    }

    #[test]
    fn ood_public_inputs_pi_hash_changes_with_alpha() {
        let mut claim = ood_honest_claim();
        let a = OodAccumulatorPublicInputs::for_claim(&claim);
        claim.alphas[2] = gf(0xFEED);
        let b = OodAccumulatorPublicInputs::for_claim(&claim);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn ood_prove_rejects_alpha_count_mismatch() {
        let mut claim = ood_honest_claim();
        claim.alphas.pop();  // 6 alphas for 7 claims
        let result = prove_ood_accumulator(&claim, 4, 54, false);
        assert!(matches!(result, Err(RecursiveProverError::InvalidClaim(_))));
    }

    #[test]
    fn ood_prove_rejects_empty_bundle() {
        let claim = OodAccumulatorClaim {
            bundle: OodClaimBundle::<FBase> { claims: vec![] },
            alphas: vec![],
        };
        let result = prove_ood_accumulator(&claim, 4, 54, false);
        assert!(matches!(result, Err(RecursiveProverError::InvalidClaim(_))));
    }

    #[test]
    #[ignore = "slow — exercises OOD FRI prove + verify round-trip"]
    fn round_trip_ood_accumulator_smoke() {
        let claim = ood_honest_claim();
        let proof = prove_ood_accumulator(&claim, 4, 54, false)
            .expect("prove must succeed on honest OOD bundle");
        assert!(verify_ood_accumulator(&proof),
            "OOD round-trip verify must accept");
    }

    #[test]
    #[ignore = "slow — exercises STIR variant on OOD"]
    fn round_trip_ood_accumulator_stir() {
        let claim = ood_honest_claim();
        let proof = prove_ood_accumulator(&claim, 4, 54, true)
            .expect("STIR prove must succeed");
        assert!(verify_ood_accumulator(&proof),
            "OOD STIR round-trip verify must accept");
    }

    #[test]
    #[ignore = "slow — exercises tamper rejection on OOD"]
    fn round_trip_ood_rejects_tampered_pi_hash() {
        let claim = ood_honest_claim();
        let mut proof = prove_ood_accumulator(&claim, 4, 54, false)
            .expect("prove must succeed");
        proof.public.pi_hash[0] ^= 0xFF;
        assert!(!verify_ood_accumulator(&proof),
            "tampered OOD pi_hash must be rejected");
    }

    // ─── Sub-circuit 3 (perm-arg Π running-product) tests ──────────

    fn perm_arg_honest_claim() -> PermArgClaim<FBase> {
        // 5-element multisets, right is a permutation of left.
        PermArgClaim {
            left:  vec![gf(11), gf(22), gf(33), gf(44), gf(55)],
            right: vec![gf(33), gf(11), gf(55), gf(22), gf(44)],
            gamma: gf(0xDEAD_C0DE),
            perm_tag: "T_MEM",
        }
    }

    #[test]
    fn perm_arg_public_inputs_pi_hash_is_deterministic() {
        let claim = perm_arg_honest_claim();
        let a = PermArgPublicInputs::for_claim(&claim);
        let b = PermArgPublicInputs::for_claim(&claim);
        assert_eq!(a.pi_hash, b.pi_hash);
        assert_eq!(a.gamma, claim.gamma);
        assert_eq!(a.n_elements, 5);
    }

    #[test]
    fn perm_arg_public_inputs_pi_hash_changes_with_gamma() {
        let mut claim = perm_arg_honest_claim();
        let a = PermArgPublicInputs::for_claim(&claim);
        claim.gamma = gf(0x99);
        let b = PermArgPublicInputs::for_claim(&claim);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn perm_arg_public_inputs_pi_hash_changes_with_tag() {
        let mut claim = perm_arg_honest_claim();
        let a = PermArgPublicInputs::for_claim(&claim);
        claim.perm_tag = "T_OTHER";
        let b = PermArgPublicInputs::for_claim(&claim);
        assert_ne!(a.pi_hash, b.pi_hash);
    }

    #[test]
    fn perm_arg_prove_rejects_size_mismatch() {
        let claim = PermArgClaim {
            left:  vec![gf(1), gf(2), gf(3)],
            right: vec![gf(1), gf(2)],
            gamma: gf(1),
            perm_tag: "T_MEM",
        };
        let result = prove_perm_arg_accumulator(&claim, 4, 54, false);
        assert!(matches!(result, Err(RecursiveProverError::InvalidClaim(_))));
    }

    #[test]
    fn perm_arg_prove_rejects_unequal_multisets() {
        // Trace satisfies its constraints up to the FinalBoundary, which
        // catches that running_left != running_right.  Should fail the
        // column-level self-check → TraceSelfCheckFailed.
        let claim = PermArgClaim {
            left:  vec![gf(1), gf(2), gf(3)],
            right: vec![gf(1), gf(2), gf(5)],
            gamma: gf(7),
            perm_tag: "T_MEM",
        };
        let result = prove_perm_arg_accumulator(&claim, 4, 54, false);
        assert!(matches!(result,
            Err(RecursiveProverError::TraceSelfCheckFailed)));
    }

    #[test]
    fn perm_arg_prove_rejects_empty() {
        let claim = PermArgClaim::<FBase> {
            left: vec![], right: vec![],
            gamma: gf(1),
            perm_tag: "T_MEM",
        };
        let result = prove_perm_arg_accumulator(&claim, 4, 54, false);
        assert!(matches!(result, Err(RecursiveProverError::InvalidClaim(_))));
    }

    #[test]
    #[ignore = "slow — exercises perm-arg FRI prove + verify round-trip"]
    fn round_trip_perm_arg_accumulator_smoke() {
        let claim = perm_arg_honest_claim();
        let proof = prove_perm_arg_accumulator(&claim, 4, 54, false)
            .expect("prove must succeed on honest perm-arg");
        assert!(verify_perm_arg_accumulator(&proof),
            "perm-arg round-trip verify must accept");
    }

    #[test]
    #[ignore = "slow — exercises STIR variant on perm-arg"]
    fn round_trip_perm_arg_accumulator_stir() {
        let claim = perm_arg_honest_claim();
        let proof = prove_perm_arg_accumulator(&claim, 4, 54, true)
            .expect("STIR prove must succeed");
        assert!(verify_perm_arg_accumulator(&proof),
            "perm-arg STIR round-trip verify must accept");
    }

    #[test]
    #[ignore = "slow — exercises tamper rejection on perm-arg"]
    fn round_trip_perm_arg_rejects_tampered_pi_hash() {
        let claim = perm_arg_honest_claim();
        let mut proof = prove_perm_arg_accumulator(&claim, 4, 54, false)
            .expect("prove must succeed");
        proof.public.pi_hash[0] ^= 0xFF;
        assert!(!verify_perm_arg_accumulator(&proof),
            "tampered perm-arg pi_hash must be rejected");
    }

    // ─── STEP 6 (composed outer FRI proof) tests ───────────────────

    #[test]
    fn recursive_public_inputs_pi_hash_is_deterministic() {
        let c = xor_chain_claim();
        let o = ood_honest_claim();
        let p = perm_arg_honest_claim();
        let a = RecursiveStarkPublicInputs::for_claims(&c, &o, &p, 8);
        let b = RecursiveStarkPublicInputs::for_claims(&c, &o, &p, 8);
        assert_eq!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn recursive_public_inputs_pi_hash_changes_per_subclaim() {
        let c = xor_chain_claim();
        let o = ood_honest_claim();
        let p = perm_arg_honest_claim();
        let a = RecursiveStarkPublicInputs::for_claims(&c, &o, &p, 8);
        let mut p2 = perm_arg_honest_claim();
        p2.gamma = gf(0x99);
        let b = RecursiveStarkPublicInputs::for_claims(&c, &o, &p2, 8);
        assert_ne!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn recursive_prove_rejects_bad_blowup() {
        let c = xor_chain_claim();
        let o = ood_honest_claim();
        let p = perm_arg_honest_claim();
        let result = prove_recursive_stark(&c, &o, &p, 3, 54, false);
        assert!(matches!(result, Err(RecursiveProverError::Internal(_))));
    }

    #[test]
    #[ignore = "slow — exercises full composed recursive FRI prove + verify"]
    fn round_trip_recursive_stark_smoke() {
        let c = xor_chain_claim();
        let o = ood_honest_claim();
        let p = perm_arg_honest_claim();
        let proof = prove_recursive_stark(&c, &o, &p, /*blowup=*/4, /*r=*/54, /*stir=*/false)
            .expect("composed prove must succeed");
        assert!(verify_recursive_stark(&proof),
            "composed recursive STARK round-trip must accept");
    }

    #[test]
    #[ignore = "slow — exercises STIR variant on composed proof"]
    fn round_trip_recursive_stark_stir() {
        let c = xor_chain_claim();
        let o = ood_honest_claim();
        let p = perm_arg_honest_claim();
        let proof = prove_recursive_stark(&c, &o, &p, 4, 54, true)
            .expect("composed STIR prove must succeed");
        assert!(verify_recursive_stark(&proof),
            "composed recursive STIR round-trip must accept");
    }

    #[test]
    #[ignore = "slow — composed proof rejects tampered outer pi_hash"]
    fn round_trip_recursive_rejects_tampered_outer_pi_hash() {
        let c = xor_chain_claim();
        let o = ood_honest_claim();
        let p = perm_arg_honest_claim();
        let mut proof = prove_recursive_stark(&c, &o, &p, 4, 54, false)
            .expect("composed prove must succeed");
        proof.public.outer_pi_hash[0] ^= 0xFF;
        assert!(!verify_recursive_stark(&proof),
            "tampered outer pi_hash must be rejected");
    }
}
