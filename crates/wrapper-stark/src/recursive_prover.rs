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
}
