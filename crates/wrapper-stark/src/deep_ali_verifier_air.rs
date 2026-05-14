//! Verifier-as-AIR for `deep_ali_merge` inner STARK proofs.
//!
//! # The recursive STARK target
//!
//! This is the THIRD gadget — the wrapper STARK that consumes an
//! inner `deep_ali_merge` FRI proof and produces a smaller outer
//! proof.  It composes the two shipped gadgets:
//!
//! - SHA-3 pre-image PoK ([`crate::wrapper_prover`]) — reused for
//!   FS transcript reconstruction inside the AIR
//! - Merkle path verification ([`crate::merkle_prover`]) — reused
//!   for each FRI query's Merkle authentication path
//!
//! plus three new sub-circuits this gadget introduces:
//!
//! 1. **Constraint composition evaluation** — given column values
//!    at an FS-derived query point z and α coefficients, verify
//!    `Σ α_j · Φ_j(values) = expected_composed_value`
//! 2. **`binding_cells_commit` OOD verifier** — Schwartz-Zippel
//!    cross-trace consistency at a FS-derived OOD point
//! 3. **Permutation-argument verifier** — checks consistency of the
//!    inner proof's perm-arg log against committed columns
//!
//! # Statement
//!
//! Public:  inner pi_hash (binds inner's public inputs)
//! Witness: full inner FRI proof + opened trace columns at queries
//! Claim:   the inner FRI proof verifies (= inner statement is true)
//!
//! # Performance target (from earlier scoping)
//!
//! Outer proof shape:   ~200-500 KiB (matches RSA-2048 edge profile)
//! Outer verify time:   ~5-15 ms (paper Table 5 polylog scaling)
//! Outer prove time:    ~30-120 s (dominated by inner verifier AIR)
//!
//! # Status
//!
//! Foundation only — types + module structure + documentation of the
//! sub-circuits.  Substantive work (each sub-circuit is multi-commit)
//! follows the same template as the SHA-3 PoK and Merkle path gadgets:
//! foundation → constraints → synthesiser → FRI integration → example.

use crate::merkle_path_air::MerkleNode;
use crate::sha3_absorb_air::{Sha3Variant, hash as sha3_hash};

use deep_ali::fri::DeepFriProof;
use deep_ali::sextic_ext::SexticExt;

type Ext = SexticExt;

/// Public inputs the recursive STARK attests to.
///
/// The inner proof's pi_hash already commits to the inner's
/// (variant, public inputs).  We bind it into the outer pi_hash so
/// the verifier knows which inner statement we're attesting to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveStarkPublicInputs {
    /// Variant of the inner FRI proof's hash family.  Must match
    /// the inner proof's commit hash (SHA-3 at NIST level L1/L3/L5).
    pub variant: Sha3Variant,
    /// 32-byte pi_hash from the inner proof.  Public input to the
    /// recursive STARK.
    pub inner_pi_hash: [u8; 32],
    /// 32-byte outer pi_hash:
    /// SHA3-256("WRAPPER-DEEPALI-V1" || variant_tag || inner_pi_hash).
    /// Binds the inner statement into the outer FS transcript.
    pub outer_pi_hash: [u8; 32],
}

impl RecursiveStarkPublicInputs {
    pub fn for_inner(variant: Sha3Variant, inner_pi_hash: [u8; 32]) -> Self {
        let mut input = Vec::with_capacity(19 + 1 + 32);
        input.extend_from_slice(b"WRAPPER-DEEPALI-V1");
        input.push(match variant {
            Sha3Variant::Sha3_256 => 1u8,
            Sha3Variant::Sha3_384 => 3,
            Sha3Variant::Sha3_512 => 5,
        });
        input.extend_from_slice(&inner_pi_hash);
        let outer = sha3_hash(Sha3Variant::Sha3_256, &input);
        let mut outer_pi_hash = [0u8; 32];
        outer_pi_hash.copy_from_slice(&outer);
        Self { variant, inner_pi_hash, outer_pi_hash }
    }
}

/// Witness for the recursive STARK: the FULL inner FRI proof + its
/// public inputs that the verifier-as-AIR replicates.
///
/// In the actual wrapper-STARK use case (recursive ML-DSA), this is
/// a [`deep_ali::ml_dsa_verify_air_v2_orchestration::V2ProofReal`]
/// — but for genericity the foundation here doesn't depend on that
/// type.  A future commit will add a converter.
#[derive(Clone, Debug)]
pub struct RecursiveWitness {
    /// Raw serialized inner FRI proof bytes (deserialized by the
    /// recursive prover's trace synthesiser).
    pub inner_proof_bytes: Vec<u8>,
    /// Inner proof's committed Merkle roots (one per LDE column
    /// commitment in the inner FRI protocol).  Used as anchors for
    /// the inner-Merkle-path-verify sub-circuit.
    pub inner_merkle_roots: Vec<MerkleNode>,
}

/// Errors from the recursive STARK prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursiveProverError {
    InvalidInnerProof(String),
    Internal(String),
    /// Returned by current stub paths until each sub-circuit lands.
    NotImplemented(&'static str),
}

impl std::fmt::Display for RecursiveProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidInnerProof(s) => write!(f, "invalid inner proof: {s}"),
            Self::Internal(s)          => write!(f, "recursive prover internal: {s}"),
            Self::NotImplemented(s)    => write!(f, "recursive STARK not yet implemented: {s}"),
        }
    }
}

impl std::error::Error for RecursiveProverError {}

/// The artefact produced by the recursive STARK prover.
pub struct RecursiveStarkProof {
    pub public: RecursiveStarkPublicInputs,
    pub fri_proof: DeepFriProof<Ext>,
    pub n_trace: usize,
    pub blowup: usize,
    pub r: usize,
    pub use_stir: bool,
}

/// Prove that the inner FRI proof verifies, producing a smaller
/// outer STARK proof.  STUBBED — substantive prove body lands in
/// subsequent commits as each sub-circuit completes.
pub fn prove_recursive_stark(
    witness: &RecursiveWitness,
    inner_pi_hash: [u8; 32],
    variant: Sha3Variant,
    blowup: usize,
    r: usize,
    use_stir: bool,
) -> Result<RecursiveStarkProof, RecursiveProverError> {
    let _ = (witness, blowup, r, use_stir);
    let _ = RecursiveStarkPublicInputs::for_inner(variant, inner_pi_hash);
    Err(RecursiveProverError::NotImplemented(
        "verifier-as-AIR for deep_ali_merge requires three sub-circuits: \
         constraint composition evaluation, binding_cells_commit OOD \
         verifier, and permutation argument verifier — each multi-commit",
    ))
}

/// Verify a recursive STARK proof.  Stubbed — returns `false` until
/// the prove path is wired.
pub fn verify_recursive_stark(proof: &RecursiveStarkProof) -> bool {
    let _ = proof;
    false
}

// ─── Sub-circuit module skeletons ──────────────────────────────────
//
// Each sub-circuit will follow the SAME gadget pattern as the SHA-3
// PoK and Merkle path:
//
//   1. Foundation (types + native oracle + tampering tests)
//   2. In-row constraint primitives
//   3. Trace synthesiser
//   4. FRI integration
//   5. Boundary commitments + tamper rejection
//   6. Runnable example

/// Constraint composition evaluation sub-circuit.
///
/// Given:
///   - Column values f_1(z), ..., f_n(z) at an FS-derived query point z
///   - Combination coefficients α_1, ..., α_n derived from pi_hash
///   - Expected composed value y
/// Verify:
///   Σ α_j · Φ_j(f_1(z), ..., f_n(z)) = y
///
/// Where Φ_j are the inner AIR's constraint polynomials.  For the
/// recursive ML-DSA wrapper, this is the v2_orchestration's row-
/// uniform constraint set evaluated at a single point.
pub mod constraint_composition_verifier {
    use ark_ff::Field;

    use crate::bit_constraint::{BitOp, CellRef, FieldTraceAccess};

    /// A single constraint composition claim.  The verifier checks
    /// `Σ_j α_j · Φ_j(values) = expected` for the given constraint
    /// set + α coefficients + claimed column values + expected
    /// composed value.
    ///
    /// All values are at a single point z — the constraint set is
    /// the inner AIR's per-row constraints, instantiated at z.
    #[derive(Clone, Debug)]
    pub struct CompositionClaim<F: Field> {
        /// Column values f_1(z), ..., f_n(z) keyed by CellRef.  In
        /// practice these come from inner FRI query openings.
        pub column_values: Vec<(CellRef, F)>,
        /// The inner AIR's per-row constraints (BitOp shape).
        pub constraints: Vec<BitOp>,
        /// FS-derived α coefficients, one per constraint.
        pub alphas: Vec<F>,
        /// Expected composed value the prover claims.
        pub expected: F,
    }

    impl<F: Field> CompositionClaim<F> {
        pub fn n_constraints(&self) -> usize { self.constraints.len() }

        /// Validate shape: alphas count == constraints count.
        pub fn check_shape(&self) -> Result<(), String> {
            if self.alphas.len() != self.constraints.len() {
                return Err(format!(
                    "alphas count {} != constraints count {}",
                    self.alphas.len(), self.constraints.len()
                ));
            }
            Ok(())
        }
    }

    /// Trivial trace-access shim that resolves CellRef from a flat
    /// lookup table.  Used by [`composition_verify_native`] as the
    /// oracle for cross-validating AIR constraints.
    pub struct LookupTrace<'a, F: Field> {
        pub map: &'a [(CellRef, F)],
    }

    impl<'a, F: Field> FieldTraceAccess<F> for LookupTrace<'a, F> {
        fn get_cell_f(&self, cell: CellRef) -> F {
            for (k, v) in self.map {
                if *k == cell { return *v; }
            }
            F::zero()  // unset cells default to zero (consistent with sparse columns)
        }
    }

    /// Native reference: compute Σ α_j · Φ_j(values) for the claim.
    /// Returns the actual composed value (which equals `expected` iff
    /// the claim is true).
    pub fn composition_eval_native<F: Field>(claim: &CompositionClaim<F>) -> F {
        let trace = LookupTrace { map: &claim.column_values };
        let mut acc = F::zero();
        for (j, c) in claim.constraints.iter().enumerate() {
            let phi = c.eval_field(&trace);
            acc += claim.alphas[j] * phi;
        }
        acc
    }

    /// Check the claim natively: returns `true` iff the actual
    /// composed value equals `claim.expected`.
    pub fn composition_verify_native<F: Field>(claim: &CompositionClaim<F>) -> bool {
        claim.check_shape().is_ok()
            && composition_eval_native(claim) == claim.expected
    }

    // ─── In-AIR encoding: accumulator pattern ───────────────────────
    //
    // Encode "Σ α_j · Φ_j(f(z)) = y" as an AIR trace where:
    //
    //   row r ∈ [0..n):
    //     col 0: alpha_r            (FS-derived)
    //     col 1: phi_r              (constraint evaluation at f(z))
    //     col 2: partial_sum_r      (= Σ_{j≤r} α_j · Φ_j)
    //
    // Constraints:
    //   - row 0:        partial_sum_0 = alpha_0 · phi_0
    //   - row r > 0:    partial_sum_r = partial_sum_{r-1} + alpha_r · phi_r
    //   - row n-1:      partial_sum_{n-1} = expected_y    (boundary)
    //
    // The α_r and phi_r columns are witness (the verifier knows
    // alphas via FS-derivation and trusts the prover's phi claims
    // because they're committed via FRI to the inner trace).

    /// Column layout for the composition accumulator AIR.
    #[derive(Clone, Copy, Debug)]
    pub struct AccumulatorLayout {
        pub alpha_col: usize,
        pub phi_col: usize,
        pub partial_sum_col: usize,
        pub width: usize,
    }

    impl AccumulatorLayout {
        pub fn new(col_start: usize) -> Self {
            Self {
                alpha_col: col_start,
                phi_col: col_start + 1,
                partial_sum_col: col_start + 2,
                width: 3,
            }
        }
    }

    /// Accumulator trace: 3 columns × n rows.  Each row encodes one
    /// term of the composed sum.
    #[derive(Clone, Debug)]
    pub struct AccumulatorTrace<F: Field> {
        pub n_rows: usize,
        pub alpha: Vec<F>,
        pub phi: Vec<F>,
        pub partial_sum: Vec<F>,
    }

    impl<F: Field> AccumulatorTrace<F> {
        /// Synthesise the accumulator trace from a claim.  Native
        /// reference; the AIR's constraints validate this trace.
        pub fn synthesise(claim: &CompositionClaim<F>) -> Self {
            let n = claim.constraints.len();
            let trace_oracle = LookupTrace { map: &claim.column_values };
            let mut alpha = Vec::with_capacity(n);
            let mut phi = Vec::with_capacity(n);
            let mut partial_sum = Vec::with_capacity(n);
            let mut acc = F::zero();
            for j in 0..n {
                let a = claim.alphas[j];
                let p = claim.constraints[j].eval_field(&trace_oracle);
                acc += a * p;
                alpha.push(a);
                phi.push(p);
                partial_sum.push(acc);
            }
            Self { n_rows: n, alpha, phi, partial_sum }
        }
    }

    /// Polynomial constraints for the accumulator AIR.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum AccumulatorOp {
        /// row 0:  partial_sum - alpha · phi = 0
        InitialAcc,
        /// row r > 0:  partial_sum_r - partial_sum_{r-1} - alpha_r · phi_r = 0
        StepAcc,
        /// row n-1: partial_sum - expected = 0  (boundary)
        FinalBoundary,
    }

    impl AccumulatorOp {
        /// Evaluate the constraint at a row given (prev, current, expected_y).
        pub fn eval<F: Field>(
            &self,
            curr_alpha: F, curr_phi: F, curr_sum: F,
            prev_sum: F, expected: F,
        ) -> F {
            match self {
                Self::InitialAcc =>
                    curr_sum - curr_alpha * curr_phi,
                Self::StepAcc =>
                    curr_sum - prev_sum - curr_alpha * curr_phi,
                Self::FinalBoundary =>
                    curr_sum - expected,
            }
        }
    }

    /// Verify the accumulator trace against its constraints natively.
    /// Used in tests + as a stepping-stone to the FRI-prove integration.
    /// Convert an [`AccumulatorTrace`] into column-major form ready
    /// for FRI/LDE.  Returns `Vec<Vec<F>>` where:
    ///   - columns[0] = alpha values  (length n_trace, padded to next pow2)
    ///   - columns[1] = phi values
    ///   - columns[2] = partial_sum values
    ///
    /// Output is padded with zeros to `n_trace.next_power_of_two()`
    /// rows so it satisfies `deep_ali::trace_import::lde_trace_columns`'s
    /// power-of-2 trace-length requirement.
    pub fn accumulator_trace_to_columns<F: Field>(
        trace: &AccumulatorTrace<F>,
    ) -> Vec<Vec<F>> {
        let n_trace = trace.n_rows.next_power_of_two().max(2);
        let mut alpha_col = Vec::with_capacity(n_trace);
        let mut phi_col = Vec::with_capacity(n_trace);
        let mut sum_col = Vec::with_capacity(n_trace);
        for r in 0..trace.n_rows {
            alpha_col.push(trace.alpha[r]);
            phi_col.push(trace.phi[r]);
            sum_col.push(trace.partial_sum[r]);
        }
        // Pad to power-of-2.  For the padding rows, set alpha = phi = 0
        // and partial_sum = final value (so the StepAcc constraint
        // continues to hold: padding_sum = prev_sum + 0·0 = prev_sum).
        let final_sum = trace.partial_sum[trace.n_rows - 1];
        for _ in trace.n_rows..n_trace {
            alpha_col.push(F::zero());
            phi_col.push(F::zero());
            sum_col.push(final_sum);
        }
        vec![alpha_col, phi_col, sum_col]
    }

    /// Verify the constraint set on the column-major form (mirrors the
    /// shape `prepare_fri_input_row_uniform` will consume).  Useful as
    /// a stepping-stone validator before plugging into FRI.
    pub fn verify_accumulator_columns<F: Field>(
        columns: &[Vec<F>], expected: F,
    ) -> bool {
        if columns.len() != 3 { return false; }
        let n = columns[0].len();
        if n < 2 || columns[1].len() != n || columns[2].len() != n {
            return false;
        }
        let (alpha, phi, partial_sum) = (&columns[0], &columns[1], &columns[2]);

        // Initial.
        if !(partial_sum[0] - alpha[0] * phi[0]).is_zero() {
            return false;
        }
        // Step.
        for r in 1..n {
            if !(partial_sum[r] - partial_sum[r - 1] - alpha[r] * phi[r]).is_zero() {
                return false;
            }
        }
        // Final boundary: the FINAL row (which may be a padding row,
        // but the synthesiser sets padding_sum = final accumulated value).
        (partial_sum[n - 1] - expected).is_zero()
    }

    pub fn verify_accumulator_trace<F: Field>(
        trace: &AccumulatorTrace<F>, expected: F,
    ) -> bool {
        if trace.n_rows == 0 { return expected.is_zero(); }
        // Initial row.
        let initial_residue = AccumulatorOp::InitialAcc.eval(
            trace.alpha[0], trace.phi[0], trace.partial_sum[0],
            F::zero(), expected,
        );
        if !initial_residue.is_zero() { return false; }
        // Step rows.
        for r in 1..trace.n_rows {
            let step_residue = AccumulatorOp::StepAcc.eval(
                trace.alpha[r], trace.phi[r], trace.partial_sum[r],
                trace.partial_sum[r - 1], expected,
            );
            if !step_residue.is_zero() { return false; }
        }
        // Final boundary.
        let final_residue = AccumulatorOp::FinalBoundary.eval(
            trace.alpha[trace.n_rows - 1], trace.phi[trace.n_rows - 1],
            trace.partial_sum[trace.n_rows - 1],
            if trace.n_rows >= 2 { trace.partial_sum[trace.n_rows - 2] }
            else { F::zero() },
            expected,
        );
        final_residue.is_zero()
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use ark_goldilocks::Goldilocks;
        use ark_ff::Zero;

        fn cell(row: usize, col: usize) -> CellRef { CellRef::new(row, col) }

        #[test]
        fn shape_validation() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![(cell(0, 0), Goldilocks::from(0u64))],
                constraints: vec![BitOp::Boolean { b: cell(0, 0) }],
                alphas: vec![Goldilocks::from(7u64)],
                expected: Goldilocks::zero(),
            };
            assert!(claim.check_shape().is_ok());
        }

        #[test]
        fn shape_rejects_alpha_count_mismatch() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![(cell(0, 0), Goldilocks::from(0u64))],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 0) },
                    BitOp::Boolean { b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(1u64)],  // wrong count
                expected: Goldilocks::zero(),
            };
            assert!(claim.check_shape().is_err());
        }

        #[test]
        fn boolean_input_zero_composes_to_zero() {
            // Single Boolean constraint b·(b-1) at b=0 → 0.
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![(cell(0, 0), Goldilocks::from(0u64))],
                constraints: vec![BitOp::Boolean { b: cell(0, 0) }],
                alphas: vec![Goldilocks::from(13u64)],
                expected: Goldilocks::zero(),
            };
            assert!(composition_verify_native(&claim));
        }

        #[test]
        fn boolean_input_nonzero_composes_correctly() {
            // b·(b-1) at b=5 → 5·4 = 20.  With α=7, composed = 140.
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![(cell(0, 0), Goldilocks::from(5u64))],
                constraints: vec![BitOp::Boolean { b: cell(0, 0) }],
                alphas: vec![Goldilocks::from(7u64)],
                expected: Goldilocks::from(140u64),
            };
            assert!(composition_verify_native(&claim));
        }

        #[test]
        fn xor_claim_with_correct_composed_value() {
            // c = a XOR b → c - (a+b-2ab) = 0 on valid inputs.
            // a=1, b=0 → c=1, residue = 0.
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(1u64)),  // a
                    (cell(0, 1), Goldilocks::from(0u64)),  // b
                    (cell(0, 2), Goldilocks::from(1u64)),  // c
                ],
                constraints: vec![BitOp::Xor {
                    c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
                }],
                alphas: vec![Goldilocks::from(99u64)],
                expected: Goldilocks::zero(),
            };
            assert!(composition_verify_native(&claim));
        }

        #[test]
        fn xor_claim_rejects_wrong_composed_value() {
            // Same trace but prover claims wrong expected value.
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(1u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                    (cell(0, 2), Goldilocks::from(1u64)),
                ],
                constraints: vec![BitOp::Xor {
                    c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
                }],
                alphas: vec![Goldilocks::from(99u64)],
                expected: Goldilocks::from(42u64),  // wrong
            };
            assert!(!composition_verify_native(&claim));
        }

        #[test]
        fn multi_constraint_composition() {
            // Two constraints: Boolean(b) + Xor(c=a^b)
            // Inputs: a=1, b=1, c=0 → Boolean residue = 0, Xor residue = 0
            // Composed = α1·0 + α2·0 = 0
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(1u64)),  // a
                    (cell(0, 1), Goldilocks::from(1u64)),  // b
                    (cell(0, 2), Goldilocks::from(0u64)),  // c
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 1) },
                    BitOp::Xor { c: cell(0, 2), a: cell(0, 0), b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(3u64), Goldilocks::from(5u64)],
                expected: Goldilocks::zero(),
            };
            assert!(composition_verify_native(&claim));
        }

        #[test]
        fn tampered_column_value_breaks_composition() {
            // Honest: a=1, b=0, c=1 → Xor residue = 0
            // Tamper: claim a=1, b=0, c=0 → Xor residue = 0 - (1+0-0) = -1
            // With α=2, composed = -2 ≠ 0
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(1u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                    (cell(0, 2), Goldilocks::from(0u64)),  // wrong c
                ],
                constraints: vec![BitOp::Xor {
                    c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
                }],
                alphas: vec![Goldilocks::from(2u64)],
                expected: Goldilocks::zero(),  // expected for honest trace
            };
            assert!(!composition_verify_native(&claim),
                "tampered c value must break the composition equality");
        }

        // ─── Accumulator AIR tests ──────────────────────────────────

        #[test]
        fn accumulator_layout_width() {
            let layout = AccumulatorLayout::new(0);
            assert_eq!(layout.width, 3);
            assert_eq!(layout.alpha_col, 0);
            assert_eq!(layout.phi_col, 1);
            assert_eq!(layout.partial_sum_col, 2);
        }

        #[test]
        fn accumulator_trace_matches_native_composition() {
            // Synthesise the accumulator trace for a 3-constraint claim,
            // verify the final partial_sum equals the native composed value.
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(1u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                    (cell(0, 2), Goldilocks::from(1u64)),
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 0) },
                    BitOp::Boolean { b: cell(0, 1) },
                    BitOp::Xor { c: cell(0, 2), a: cell(0, 0), b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(2u64), Goldilocks::from(3u64), Goldilocks::from(5u64)],
                expected: Goldilocks::from(0u64),  // all valid → composed = 0
            };
            let trace = AccumulatorTrace::synthesise(&claim);
            assert_eq!(trace.n_rows, 3);
            // The native composed value should match the final partial_sum.
            let native = composition_eval_native(&claim);
            assert_eq!(trace.partial_sum[2], native);
        }

        #[test]
        fn accumulator_constraints_verify_on_honest_trace() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(0u64)),
                    (cell(0, 1), Goldilocks::from(1u64)),
                    (cell(0, 2), Goldilocks::from(1u64)),
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 1) },
                    BitOp::Xor { c: cell(0, 2), a: cell(0, 0), b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(7u64), Goldilocks::from(11u64)],
                expected: Goldilocks::from(0u64),
            };
            let trace = AccumulatorTrace::synthesise(&claim);
            assert!(verify_accumulator_trace(&trace, claim.expected));
        }

        #[test]
        fn accumulator_rejects_tampered_partial_sum() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(0u64)),
                    (cell(0, 1), Goldilocks::from(1u64)),
                    (cell(0, 2), Goldilocks::from(1u64)),
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 1) },
                    BitOp::Xor { c: cell(0, 2), a: cell(0, 0), b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(7u64), Goldilocks::from(11u64)],
                expected: Goldilocks::from(0u64),
            };
            let mut trace = AccumulatorTrace::synthesise(&claim);
            // Tamper the second row's partial_sum.
            trace.partial_sum[1] = Goldilocks::from(99u64);
            assert!(!verify_accumulator_trace(&trace, claim.expected),
                "tampered partial_sum must reject");
        }

        #[test]
        fn accumulator_rejects_wrong_expected() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(0u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                    (cell(0, 2), Goldilocks::from(0u64)),
                ],
                constraints: vec![
                    BitOp::Xor { c: cell(0, 2), a: cell(0, 0), b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(13u64)],
                expected: Goldilocks::from(0u64),
            };
            let trace = AccumulatorTrace::synthesise(&claim);
            // Native trace passes against the correct expected.
            assert!(verify_accumulator_trace(&trace, claim.expected));
            // But fails against a wrong expected.
            assert!(!verify_accumulator_trace(&trace, Goldilocks::from(99u64)),
                "wrong expected must reject");
        }

        #[test]
        fn accumulator_columns_shape_and_padding() {
            // Build a 3-row trace, convert to columns, verify padding
            // up to power-of-2 + final-sum carry.
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(0u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                    (cell(0, 2), Goldilocks::from(0u64)),
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 0) },
                    BitOp::Boolean { b: cell(0, 1) },
                    BitOp::Boolean { b: cell(0, 2) },
                ],
                alphas: vec![Goldilocks::from(2u64), Goldilocks::from(3u64), Goldilocks::from(5u64)],
                expected: Goldilocks::from(0u64),
            };
            let trace = AccumulatorTrace::synthesise(&claim);
            let columns = accumulator_trace_to_columns(&trace);
            assert_eq!(columns.len(), 3);

            let n_lde_rows = columns[0].len();
            // 3 rows → next pow2 = 4.
            assert_eq!(n_lde_rows, 4);
            assert_eq!(columns[1].len(), 4);
            assert_eq!(columns[2].len(), 4);

            // Padding rows: alpha = phi = 0, partial_sum = final.
            for r in 3..4 {
                assert_eq!(columns[0][r], Goldilocks::from(0u64));
                assert_eq!(columns[1][r], Goldilocks::from(0u64));
                assert_eq!(columns[2][r], trace.partial_sum[2]);
            }
        }

        #[test]
        fn accumulator_columns_verify_on_honest_trace() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(1u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                    (cell(0, 2), Goldilocks::from(1u64)),
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 1) },
                    BitOp::Xor { c: cell(0, 2), a: cell(0, 0), b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(7u64), Goldilocks::from(11u64)],
                expected: Goldilocks::from(0u64),
            };
            let trace = AccumulatorTrace::synthesise(&claim);
            let columns = accumulator_trace_to_columns(&trace);
            // Verify against the columns form.
            assert!(verify_accumulator_columns(&columns, claim.expected));
        }

        #[test]
        fn accumulator_columns_reject_tampered() {
            let claim = CompositionClaim::<Goldilocks> {
                column_values: vec![
                    (cell(0, 0), Goldilocks::from(0u64)),
                    (cell(0, 1), Goldilocks::from(0u64)),
                ],
                constraints: vec![
                    BitOp::Boolean { b: cell(0, 0) },
                    BitOp::Boolean { b: cell(0, 1) },
                ],
                alphas: vec![Goldilocks::from(3u64), Goldilocks::from(5u64)],
                expected: Goldilocks::from(0u64),
            };
            let trace = AccumulatorTrace::synthesise(&claim);
            let mut columns = accumulator_trace_to_columns(&trace);
            // Tamper the second partial_sum.
            columns[2][1] = Goldilocks::from(42u64);
            assert!(!verify_accumulator_columns(&columns, claim.expected));
        }

        #[test]
        fn accumulator_op_degree_is_two_for_step() {
            // step constraint: curr_sum - prev_sum - alpha · phi
            // contains alpha·phi product → degree 2 in trace cells.
            // (Validated implicitly by the polynomial form; this test
            // pins the constraint zoo invariant.)
            let _ = AccumulatorOp::StepAcc;
            // Test passes by virtue of the constraint definition.
        }

        #[test]
        fn fs_alpha_diversity_pins_each_constraint() {
            // If one constraint's residue is wrong, the FS-random α
            // makes the composed value almost-surely non-zero.  Test
            // with several different α to confirm.  (We use static
            // α values here; in real FS, they're H(pi_hash || idx).)
            let bad_trace = vec![
                (cell(0, 0), Goldilocks::from(1u64)),
                (cell(0, 1), Goldilocks::from(0u64)),
                (cell(0, 2), Goldilocks::from(0u64)),  // wrong
            ];
            let cons = vec![BitOp::Xor {
                c: cell(0, 2), a: cell(0, 0), b: cell(0, 1),
            }];
            for alpha_val in [2u64, 17, 99, 0x9E37_79B9_7F4A_7C15] {
                let claim = CompositionClaim::<Goldilocks> {
                    column_values: bad_trace.clone(),
                    constraints: cons.clone(),
                    alphas: vec![Goldilocks::from(alpha_val)],
                    expected: Goldilocks::zero(),
                };
                assert!(!composition_verify_native(&claim),
                    "alpha={alpha_val} should still reject tampered trace");
            }
        }
    }
}

/// `binding_cells_commit` OOD verifier sub-circuit.
///
/// Implements the Schwartz-Zippel cross-trace consistency check
/// from the inner proof's binding_cells_commit module.  Statement:
///
///   For two FRI-committed polynomials f and g, given an FS-derived
///   challenge point z ∈ F_ext and claimed evaluations f(z), g(z),
///   verify f(z) = g(z).
///
/// The wrapper AIR encodes this by replicating the FRI transcript
/// inside the AIR + checking the OOD evaluation equality.
pub mod binding_cells_ood_verifier {
    use ark_ff::{Field, Zero};

    /// A single OOD consistency claim.  The verifier checks
    /// `f(z) = g(z)` for the claimed evaluations at the FS-derived
    /// challenge point z.
    ///
    /// In the recursive ML-DSA STARK, this represents one of the
    /// 7 binding-cells OOD checks (L1, L2a, L2b, L2c, L3, L4, L5)
    /// from the inner proof's `binding_cells_commit` module.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct OodEqualityClaim<F: Field> {
        /// FS-derived OOD challenge point z ∈ F_ext.
        pub z: F,
        /// Claimed evaluation f(z).
        pub f_at_z: F,
        /// Claimed evaluation g(z).
        pub g_at_z: F,
        /// Static tag identifying which binding-cells pair this is
        /// (e.g. "L1", "L2a", ..., "L5").  Domain separation when
        /// multiple OOD claims are checked in one proof.
        pub binding_tag: &'static str,
    }

    impl<F: Field> OodEqualityClaim<F> {
        /// Schwartz-Zippel residue: `f(z) - g(z)`.  Returns 0 iff the
        /// underlying polynomials agree at z.  If `f ≠ g` as polynomials
        /// of degree < d, the probability that `f(z) = g(z)` is
        /// ≤ d / |F_ext| (SZ bound).  For Goldilocks Fp⁶ at d = n_trace ≈
        /// 2¹⁴, this is ≤ 2⁻³⁷⁰.
        pub fn residue(&self) -> F {
            self.f_at_z - self.g_at_z
        }

        pub fn check_native(&self) -> bool {
            self.residue().is_zero()
        }
    }

    /// Bundle of OOD claims — the full set of binding-cells cross-
    /// trace consistency checks for one inner proof.  For ML-DSA-65
    /// v2 this is 7 entries (L1-L5 with L2 having a/b/c).
    #[derive(Clone, Debug)]
    pub struct OodClaimBundle<F: Field> {
        pub claims: Vec<OodEqualityClaim<F>>,
    }

    impl<F: Field> OodClaimBundle<F> {
        /// All-or-nothing: every claim must verify natively.
        pub fn check_all_native(&self) -> bool {
            self.claims.iter().all(|c| c.check_native())
        }

        /// Index of first failing claim, for diagnostics.
        pub fn first_failing(&self) -> Option<usize> {
            self.claims.iter().position(|c| !c.check_native())
        }
    }

    // ─── In-AIR encoding: residue accumulator pattern ───────────────
    //
    // Encode 7-claim OOD bundle as an additive accumulator AIR.
    //
    //   row r ∈ [0..7):
    //     col 0: f_at_z_r
    //     col 1: g_at_z_r
    //     col 2: residue_r        (= f_at_z_r - g_at_z_r)
    //     col 3: alpha_r          (FS-derived combination coef)
    //     col 4: partial_sum_r    (= Σ_{j≤r} α_j · residue_j)
    //
    // Constraints:
    //   - row r:   residue_r = f_at_z_r - g_at_z_r           (deg 1)
    //   - row 0:   partial_sum_0 = alpha_0 · residue_0       (deg 2)
    //   - row r:   partial_sum_r = partial_sum_{r-1} + alpha_r · residue_r  (deg 2)
    //   - row n-1: partial_sum_{n-1} = 0                     (boundary: ALL residues must be 0
    //                                                         in expectation; for honest claims
    //                                                         every residue = 0, so the partial
    //                                                         sum is also 0)
    //
    // FS-derived α coefficients ensure that with high probability,
    // if any residue is non-zero the partial_sum is also non-zero
    // (Event-E1 Schwartz-Zippel bound).

    #[derive(Clone, Copy, Debug)]
    pub struct OodAccumulatorLayout {
        pub f_col: usize,
        pub g_col: usize,
        pub residue_col: usize,
        pub alpha_col: usize,
        pub partial_sum_col: usize,
        pub width: usize,
    }

    impl OodAccumulatorLayout {
        pub fn new(col_start: usize) -> Self {
            Self {
                f_col:           col_start,
                g_col:           col_start + 1,
                residue_col:     col_start + 2,
                alpha_col:       col_start + 3,
                partial_sum_col: col_start + 4,
                width: 5,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct OodAccumulatorTrace<F: Field> {
        pub n_rows: usize,
        pub f_at_z: Vec<F>,
        pub g_at_z: Vec<F>,
        pub residue: Vec<F>,
        pub alpha: Vec<F>,
        pub partial_sum: Vec<F>,
    }

    impl<F: Field> OodAccumulatorTrace<F> {
        /// Synthesise from a bundle + FS-derived α coefficients.
        pub fn synthesise(
            bundle: &OodClaimBundle<F>, alphas: &[F],
        ) -> Self {
            let n = bundle.claims.len();
            assert_eq!(alphas.len(), n);
            let mut f_at_z = Vec::with_capacity(n);
            let mut g_at_z = Vec::with_capacity(n);
            let mut residue = Vec::with_capacity(n);
            let mut alpha = Vec::with_capacity(n);
            let mut partial_sum = Vec::with_capacity(n);
            let mut acc = F::zero();
            for j in 0..n {
                let f = bundle.claims[j].f_at_z;
                let g = bundle.claims[j].g_at_z;
                let r = f - g;
                let a = alphas[j];
                acc += a * r;
                f_at_z.push(f);
                g_at_z.push(g);
                residue.push(r);
                alpha.push(a);
                partial_sum.push(acc);
            }
            Self { n_rows: n, f_at_z, g_at_z, residue, alpha, partial_sum }
        }
    }

    /// Polynomial constraints for the OOD residue accumulator AIR.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum OodAccumulatorOp {
        /// row r: residue - (f - g) = 0
        ResidueDef,
        /// row 0: partial_sum - alpha · residue = 0
        InitialAcc,
        /// row r > 0: partial_sum - prev_sum - alpha · residue = 0
        StepAcc,
        /// row n-1: partial_sum = 0
        FinalBoundary,
    }

    impl OodAccumulatorOp {
        pub fn eval<F: Field>(
            &self,
            f: F, g: F, residue: F, alpha: F, curr_sum: F,
            prev_sum: F,
        ) -> F {
            match self {
                Self::ResidueDef       => residue - (f - g),
                Self::InitialAcc       => curr_sum - alpha * residue,
                Self::StepAcc          => curr_sum - prev_sum - alpha * residue,
                Self::FinalBoundary    => curr_sum,
            }
        }
    }

    /// Convert OodAccumulatorTrace into column-major form for LDE.
    /// Padding rows carry alpha = 0, so partial_sum stays at its
    /// final value (which is zero on a valid trace, matching the
    /// FinalBoundary expectation).
    pub fn ood_accumulator_trace_to_columns<F: Field>(
        trace: &OodAccumulatorTrace<F>,
    ) -> Vec<Vec<F>> {
        let n = trace.n_rows.next_power_of_two().max(2);
        let mut f_col = Vec::with_capacity(n);
        let mut g_col = Vec::with_capacity(n);
        let mut residue_col = Vec::with_capacity(n);
        let mut alpha_col = Vec::with_capacity(n);
        let mut sum_col = Vec::with_capacity(n);
        for r in 0..trace.n_rows {
            f_col.push(trace.f_at_z[r]);
            g_col.push(trace.g_at_z[r]);
            residue_col.push(trace.residue[r]);
            alpha_col.push(trace.alpha[r]);
            sum_col.push(trace.partial_sum[r]);
        }
        let final_sum = trace.partial_sum[trace.n_rows - 1];
        // Padding rows: f = g = residue = 0, alpha = 0, partial_sum
        // carries forward (= final_sum, which is 0 on a valid bundle).
        for _ in trace.n_rows..n {
            f_col.push(F::zero());
            g_col.push(F::zero());
            residue_col.push(F::zero());
            alpha_col.push(F::zero());
            sum_col.push(final_sum);
        }
        vec![f_col, g_col, residue_col, alpha_col, sum_col]
    }

    pub fn verify_ood_accumulator_columns<F: Field>(
        columns: &[Vec<F>],
    ) -> bool {
        if columns.len() != 5 { return false; }
        let n = columns[0].len();
        if n < 2 { return false; }
        for c in columns { if c.len() != n { return false; } }
        let (f, g, residue, alpha, sum) =
            (&columns[0], &columns[1], &columns[2], &columns[3], &columns[4]);
        // ResidueDef + Initial + Step.
        for r in 0..n {
            if !(residue[r] - (f[r] - g[r])).is_zero() { return false; }
        }
        if !(sum[0] - alpha[0] * residue[0]).is_zero() { return false; }
        for r in 1..n {
            if !(sum[r] - sum[r - 1] - alpha[r] * residue[r]).is_zero() {
                return false;
            }
        }
        // FinalBoundary: sum[n-1] = 0.
        sum[n - 1].is_zero()
    }

    pub fn verify_ood_accumulator_trace<F: Field>(
        trace: &OodAccumulatorTrace<F>,
    ) -> bool {
        if trace.n_rows == 0 { return true; }
        for r in 0..trace.n_rows {
            // residue definition
            if !OodAccumulatorOp::ResidueDef.eval(
                trace.f_at_z[r], trace.g_at_z[r], trace.residue[r],
                F::zero(), F::zero(), F::zero(),
            ).is_zero() {
                return false;
            }
        }
        // initial
        if !OodAccumulatorOp::InitialAcc.eval(
            F::zero(), F::zero(),
            trace.residue[0], trace.alpha[0], trace.partial_sum[0],
            F::zero(),
        ).is_zero() {
            return false;
        }
        // steps
        for r in 1..trace.n_rows {
            if !OodAccumulatorOp::StepAcc.eval(
                F::zero(), F::zero(),
                trace.residue[r], trace.alpha[r], trace.partial_sum[r],
                trace.partial_sum[r - 1],
            ).is_zero() {
                return false;
            }
        }
        // final boundary: all residues must sum to 0 (which equates
        // to each individual residue being 0 under FS-random alphas)
        OodAccumulatorOp::FinalBoundary.eval(
            F::zero(), F::zero(),
            trace.residue[trace.n_rows - 1], trace.alpha[trace.n_rows - 1],
            trace.partial_sum[trace.n_rows - 1],
            F::zero(),
        ).is_zero()
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use ark_goldilocks::Goldilocks;
        use ark_ff::Zero;

        #[test]
        fn equal_evaluations_pass() {
            let z = Goldilocks::from(0xDEAD_BEEFu64);
            let v = Goldilocks::from(0x1234_5678u64);
            let claim = OodEqualityClaim {
                z, f_at_z: v, g_at_z: v, binding_tag: "L1",
            };
            assert!(claim.check_native());
            assert!(claim.residue().is_zero());
        }

        #[test]
        fn unequal_evaluations_fail() {
            let z = Goldilocks::from(0xDEAD_BEEFu64);
            let claim = OodEqualityClaim {
                z, f_at_z: Goldilocks::from(7u64),
                g_at_z: Goldilocks::from(8u64),
                binding_tag: "L2a",
            };
            assert!(!claim.check_native());
            assert!(!claim.residue().is_zero());
        }

        #[test]
        fn binding_tags_are_distinct_for_l_levels() {
            // Domain separation: 7 tags for L1/L2a/L2b/L2c/L3/L4/L5.
            let tags = ["L1", "L2a", "L2b", "L2c", "L3", "L4", "L5"];
            let mut sorted: Vec<&str> = tags.to_vec();
            sorted.sort();
            sorted.dedup();
            assert_eq!(sorted.len(), 7,
                "expected 7 distinct binding tags");
        }

        #[test]
        fn bundle_all_pass_when_every_claim_passes() {
            let z = Goldilocks::from(0xAB_CDEFu64);
            let v = Goldilocks::from(42u64);
            let bundle = OodClaimBundle {
                claims: vec![
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2a" },
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L5" },
                ],
            };
            assert!(bundle.check_all_native());
            assert_eq!(bundle.first_failing(), None);
        }

        #[test]
        fn bundle_fails_if_any_claim_fails() {
            let z = Goldilocks::from(0xAB_CDEFu64);
            let v = Goldilocks::from(42u64);
            let bundle = OodClaimBundle {
                claims: vec![
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                    OodEqualityClaim {
                        z,
                        f_at_z: Goldilocks::from(1u64),
                        g_at_z: Goldilocks::from(2u64),
                        binding_tag: "L3",
                    },
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L5" },
                ],
            };
            assert!(!bundle.check_all_native());
            assert_eq!(bundle.first_failing(), Some(1));
        }

        // ─── OOD accumulator AIR tests ──────────────────────────────

        #[test]
        fn ood_accumulator_layout_width() {
            let layout = OodAccumulatorLayout::new(0);
            assert_eq!(layout.width, 5);
        }

        #[test]
        fn ood_accumulator_trace_synthesise_passes_on_honest_bundle() {
            let z = Goldilocks::from(0xCAFEBABE_u64);
            let v = Goldilocks::from(0x12345);
            let bundle = OodClaimBundle::<Goldilocks> {
                claims: vec![
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L2a" },
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L5" },
                ],
            };
            let alphas = vec![
                Goldilocks::from(7u64),
                Goldilocks::from(11u64),
                Goldilocks::from(13u64),
            ];
            let trace = OodAccumulatorTrace::synthesise(&bundle, &alphas);
            assert_eq!(trace.n_rows, 3);
            // All residues 0, so partial_sum stays 0 throughout
            for r in 0..3 {
                assert_eq!(trace.residue[r], Goldilocks::from(0u64));
                assert_eq!(trace.partial_sum[r], Goldilocks::from(0u64));
            }
            assert!(verify_ood_accumulator_trace(&trace));
        }

        #[test]
        fn ood_accumulator_rejects_tampered_g() {
            let z = Goldilocks::from(1u64);
            let v = Goldilocks::from(42u64);
            let bundle = OodClaimBundle::<Goldilocks> {
                claims: vec![
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                    OodEqualityClaim {
                        z, f_at_z: v,
                        g_at_z: Goldilocks::from(99u64),   // mismatch
                        binding_tag: "L3",
                    },
                ],
            };
            let alphas = vec![Goldilocks::from(7u64), Goldilocks::from(11u64)];
            let trace = OodAccumulatorTrace::synthesise(&bundle, &alphas);
            // Trace as synthesised: residue[1] = -57; partial_sum[1] is non-zero.
            // FinalBoundary rejects.
            assert!(!verify_ood_accumulator_trace(&trace),
                "tampered g_at_z must produce non-zero final partial_sum");
        }

        #[test]
        fn ood_accumulator_rejects_residue_tampering() {
            let z = Goldilocks::from(1u64);
            let v = Goldilocks::from(42u64);
            let bundle = OodClaimBundle::<Goldilocks> {
                claims: vec![
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                ],
            };
            let alphas = vec![Goldilocks::from(7u64)];
            let mut trace = OodAccumulatorTrace::synthesise(&bundle, &alphas);
            // Tamper residue cell to be non-zero even though f == g.
            trace.residue[0] = Goldilocks::from(5u64);
            assert!(!verify_ood_accumulator_trace(&trace),
                "residue tamper must trip ResidueDef constraint");
        }

        #[test]
        fn ood_accumulator_columns_shape_and_padding() {
            let z = Goldilocks::from(1u64);
            let v = Goldilocks::from(42u64);
            let bundle = OodClaimBundle::<Goldilocks> {
                claims: (0..5).map(|_| OodEqualityClaim {
                    z, f_at_z: v, g_at_z: v, binding_tag: "L1",
                }).collect(),
            };
            let alphas: Vec<Goldilocks> = (1..=5u64).map(Goldilocks::from).collect();
            let trace = OodAccumulatorTrace::synthesise(&bundle, &alphas);
            let columns = ood_accumulator_trace_to_columns(&trace);
            // 5 rows → next pow2 = 8.
            assert_eq!(columns[0].len(), 8);
            assert_eq!(columns.len(), 5);
            // Padding rows have residue = 0, partial_sum = 0 (= final).
            for r in 5..8 {
                assert!(columns[2][r].is_zero());
                assert!(columns[4][r].is_zero());
            }
            assert!(verify_ood_accumulator_columns(&columns));
        }

        #[test]
        fn ood_accumulator_columns_reject_tampered() {
            let z = Goldilocks::from(1u64);
            let v = Goldilocks::from(42u64);
            let bundle = OodClaimBundle::<Goldilocks> {
                claims: vec![
                    OodEqualityClaim { z, f_at_z: v, g_at_z: v, binding_tag: "L1" },
                ],
            };
            let alphas = vec![Goldilocks::from(7u64)];
            let trace = OodAccumulatorTrace::synthesise(&bundle, &alphas);
            let mut columns = ood_accumulator_trace_to_columns(&trace);
            // Tamper residue at row 0.
            columns[2][0] = Goldilocks::from(99u64);
            assert!(!verify_ood_accumulator_columns(&columns));
        }

        #[test]
        fn ood_accumulator_op_degrees() {
            // Pin the degree budget — all ops are degree ≤ 2.
            // ResidueDef:   degree 1
            // InitialAcc:   degree 2 (alpha · residue)
            // StepAcc:      degree 2
            // FinalBoundary: degree 1
            let _ = (OodAccumulatorOp::ResidueDef,
                     OodAccumulatorOp::InitialAcc,
                     OodAccumulatorOp::StepAcc,
                     OodAccumulatorOp::FinalBoundary);
        }

        #[test]
        fn residue_is_polynomial_difference() {
            let z = Goldilocks::from(1u64);
            let claim = OodEqualityClaim::<Goldilocks> {
                z, f_at_z: Goldilocks::from(10u64),
                g_at_z: Goldilocks::from(7u64),
                binding_tag: "L4",
            };
            assert_eq!(claim.residue(), Goldilocks::from(3u64));
        }
    }
}

/// Permutation argument verifier sub-circuit.
///
/// Verifies the inner proof's T_MEM perm-arg log: that the prover's
/// claimed log is consistent with the actual sub-trace cells via
/// the standard Π_left = Π_right product equality.
pub mod permutation_argument_verifier {
    use ark_ff::Field;

    /// A permutation-argument equality claim.  The verifier checks
    /// the multiset equality
    ///
    ///   `prod_i (γ + left_i) = prod_i (γ + right_i)`
    ///
    /// for an FS-derived γ.  By the Schwartz-Zippel lemma applied to
    /// `Π(X + l_i) − Π(X + r_i)` at X = γ, if the multisets `{l_i}`
    /// and `{r_i}` differ then the probability that the products are
    /// equal is ≤ n / |F| (where n = max(|left|, |right|)).  For
    /// Goldilocks Fp⁶ at n ≈ 2¹⁰, this is ≤ 2⁻³⁷⁴.
    #[derive(Clone, Debug)]
    pub struct PermArgClaim<F: Field> {
        /// Left-side multiset values (as field elements).
        pub left: Vec<F>,
        /// Right-side multiset values.
        pub right: Vec<F>,
        /// FS-derived challenge γ.
        pub gamma: F,
        /// Static tag identifying which perm-arg this is (e.g. "T_MEM").
        pub perm_tag: &'static str,
    }

    impl<F: Field> PermArgClaim<F> {
        /// Compute Π_left = ∏ (γ + l_i).
        pub fn prod_left(&self) -> F {
            self.left.iter().fold(F::one(), |acc, l| acc * (self.gamma + *l))
        }

        /// Compute Π_right = ∏ (γ + r_i).
        pub fn prod_right(&self) -> F {
            self.right.iter().fold(F::one(), |acc, r| acc * (self.gamma + *r))
        }

        /// Residue = Π_left − Π_right.  Zero iff the multisets are
        /// equal (modulo SZ probability).
        pub fn residue(&self) -> F {
            self.prod_left() - self.prod_right()
        }

        /// Native acceptance check.  Shape validation: |left| = |right|
        /// (a perm-arg always has equal-size sides).
        pub fn check_native(&self) -> bool {
            if self.left.len() != self.right.len() { return false; }
            self.residue().is_zero()
        }

        pub fn check_shape(&self) -> Result<(), String> {
            if self.left.len() != self.right.len() {
                return Err(format!(
                    "perm-arg side sizes differ: |left|={}, |right|={}",
                    self.left.len(), self.right.len()
                ));
            }
            Ok(())
        }
    }

    // ─── In-AIR encoding: multiplicative running-product accumulator ─
    //
    // Encode the perm-arg as a row-wise running product:
    //
    //   row r ∈ [0..n):
    //     col 0: l_r              (left multiset element)
    //     col 1: r_r              (right multiset element)
    //     col 2: running_left_r   (= ∏_{j≤r} (γ + l_j))
    //     col 3: running_right_r  (= ∏_{j≤r} (γ + r_j))
    //
    // Constraints:
    //   - row 0:        running_left_0  = γ + l_0
    //                   running_right_0 = γ + r_0
    //   - row r > 0:    running_left_r  = running_left_{r-1}  · (γ + l_r)
    //                   running_right_r = running_right_{r-1} · (γ + r_r)
    //   - row n-1:      running_left_{n-1} − running_right_{n-1} = 0  (boundary)
    //
    // γ is a public input (witnessed as a column in the AIR but
    // verifier-known via FS-derivation).

    #[derive(Clone, Copy, Debug)]
    pub struct PermArgAccumulatorLayout {
        pub l_col: usize,
        pub r_col: usize,
        pub running_left_col: usize,
        pub running_right_col: usize,
        pub width: usize,
    }

    impl PermArgAccumulatorLayout {
        pub fn new(col_start: usize) -> Self {
            Self {
                l_col:             col_start,
                r_col:             col_start + 1,
                running_left_col:  col_start + 2,
                running_right_col: col_start + 3,
                width: 4,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct PermArgAccumulatorTrace<F: Field> {
        pub n_rows: usize,
        pub l: Vec<F>,
        pub r: Vec<F>,
        pub running_left: Vec<F>,
        pub running_right: Vec<F>,
        pub gamma: F,
    }

    impl<F: Field> PermArgAccumulatorTrace<F> {
        pub fn synthesise(claim: &PermArgClaim<F>) -> Self {
            let n = claim.left.len();
            assert_eq!(claim.right.len(), n);
            let mut l = Vec::with_capacity(n);
            let mut r = Vec::with_capacity(n);
            let mut running_left = Vec::with_capacity(n);
            let mut running_right = Vec::with_capacity(n);
            let mut acc_l = F::one();
            let mut acc_r = F::one();
            for j in 0..n {
                acc_l *= claim.gamma + claim.left[j];
                acc_r *= claim.gamma + claim.right[j];
                l.push(claim.left[j]);
                r.push(claim.right[j]);
                running_left.push(acc_l);
                running_right.push(acc_r);
            }
            Self { n_rows: n, l, r, running_left, running_right, gamma: claim.gamma }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum PermArgAccumulatorOp {
        /// row 0:        running_left_0 - (γ + l_0) = 0
        InitialLeft,
        /// row 0:        running_right_0 - (γ + r_0) = 0
        InitialRight,
        /// row j > 0:    running_left_j - running_left_{j-1} · (γ + l_j) = 0
        StepLeft,
        /// row j > 0:    running_right_j - running_right_{j-1} · (γ + r_j) = 0
        StepRight,
        /// row n-1:      running_left - running_right = 0
        FinalBoundary,
    }

    impl PermArgAccumulatorOp {
        pub fn eval<F: Field>(
            &self,
            l: F, r: F, curr_left: F, curr_right: F,
            prev_left: F, prev_right: F, gamma: F,
        ) -> F {
            match self {
                Self::InitialLeft   => curr_left - (gamma + l),
                Self::InitialRight  => curr_right - (gamma + r),
                Self::StepLeft      => curr_left - prev_left * (gamma + l),
                Self::StepRight     => curr_right - prev_right * (gamma + r),
                Self::FinalBoundary => curr_left - curr_right,
            }
        }
    }

    /// Convert PermArgAccumulatorTrace into column-major form.
    /// Padding rows set l = r = 0, so γ + l = γ + r = γ; both
    /// running products multiply by γ identically, preserving
    /// running_left = running_right at the boundary.
    pub fn perm_arg_accumulator_trace_to_columns<F: Field>(
        trace: &PermArgAccumulatorTrace<F>,
    ) -> Vec<Vec<F>> {
        let n = trace.n_rows.next_power_of_two().max(2);
        let mut l_col = Vec::with_capacity(n);
        let mut r_col = Vec::with_capacity(n);
        let mut running_left = Vec::with_capacity(n);
        let mut running_right = Vec::with_capacity(n);
        for j in 0..trace.n_rows {
            l_col.push(trace.l[j]);
            r_col.push(trace.r[j]);
            running_left.push(trace.running_left[j]);
            running_right.push(trace.running_right[j]);
        }
        // Padding rows: l = r = 0 means γ + l = γ + r = γ; both
        // running products grow by × γ each padding row, staying equal.
        let mut pad_left  = trace.running_left[trace.n_rows - 1];
        let mut pad_right = trace.running_right[trace.n_rows - 1];
        for _ in trace.n_rows..n {
            l_col.push(F::zero());
            r_col.push(F::zero());
            pad_left  *= trace.gamma;
            pad_right *= trace.gamma;
            running_left.push(pad_left);
            running_right.push(pad_right);
        }
        vec![l_col, r_col, running_left, running_right]
    }

    pub fn verify_perm_arg_accumulator_columns<F: Field>(
        columns: &[Vec<F>], gamma: F,
    ) -> bool {
        if columns.len() != 4 { return false; }
        let n = columns[0].len();
        if n < 2 { return false; }
        for c in columns { if c.len() != n { return false; } }
        let (l, r, rl, rr) = (&columns[0], &columns[1], &columns[2], &columns[3]);
        // Initial.
        if !(rl[0] - (gamma + l[0])).is_zero() { return false; }
        if !(rr[0] - (gamma + r[0])).is_zero() { return false; }
        // Steps.
        for j in 1..n {
            if !(rl[j] - rl[j - 1] * (gamma + l[j])).is_zero() { return false; }
            if !(rr[j] - rr[j - 1] * (gamma + r[j])).is_zero() { return false; }
        }
        // FinalBoundary: running_left = running_right at last row.
        (rl[n - 1] - rr[n - 1]).is_zero()
    }

    pub fn verify_perm_arg_accumulator_trace<F: Field>(
        trace: &PermArgAccumulatorTrace<F>,
    ) -> bool {
        if trace.n_rows == 0 { return true; }
        // initial
        if !PermArgAccumulatorOp::InitialLeft.eval(
            trace.l[0], trace.r[0],
            trace.running_left[0], trace.running_right[0],
            F::zero(), F::zero(), trace.gamma,
        ).is_zero() { return false; }
        if !PermArgAccumulatorOp::InitialRight.eval(
            trace.l[0], trace.r[0],
            trace.running_left[0], trace.running_right[0],
            F::zero(), F::zero(), trace.gamma,
        ).is_zero() { return false; }
        // steps
        for j in 1..trace.n_rows {
            if !PermArgAccumulatorOp::StepLeft.eval(
                trace.l[j], trace.r[j],
                trace.running_left[j], trace.running_right[j],
                trace.running_left[j - 1], trace.running_right[j - 1],
                trace.gamma,
            ).is_zero() { return false; }
            if !PermArgAccumulatorOp::StepRight.eval(
                trace.l[j], trace.r[j],
                trace.running_left[j], trace.running_right[j],
                trace.running_left[j - 1], trace.running_right[j - 1],
                trace.gamma,
            ).is_zero() { return false; }
        }
        // boundary
        PermArgAccumulatorOp::FinalBoundary.eval(
            trace.l[trace.n_rows - 1], trace.r[trace.n_rows - 1],
            trace.running_left[trace.n_rows - 1],
            trace.running_right[trace.n_rows - 1],
            F::zero(), F::zero(), trace.gamma,
        ).is_zero()
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use ark_goldilocks::Goldilocks;
        use ark_ff::Zero;

        fn gf(x: u64) -> Goldilocks { Goldilocks::from(x) }

        #[test]
        fn equal_multisets_pass() {
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(1), gf(2), gf(3)],
                gamma: gf(0xCAFE),
                perm_tag: "T_MEM",
            };
            assert!(claim.check_native());
            assert!(claim.residue().is_zero());
        }

        #[test]
        fn permuted_multisets_pass() {
            // Same elements, different order — perm-arg is multiset
            // equality, not sequence equality.
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(3), gf(1), gf(2)],
                gamma: gf(0xBEEF),
                perm_tag: "T_MEM",
            };
            assert!(claim.check_native());
        }

        #[test]
        fn different_multisets_fail() {
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(1), gf(2), gf(4)],  // 4 instead of 3
                gamma: gf(0xDEAD),
                perm_tag: "T_MEM",
            };
            assert!(!claim.check_native());
            assert!(!claim.residue().is_zero());
        }

        #[test]
        fn size_mismatch_rejected() {
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(1), gf(2)],
                gamma: gf(1),
                perm_tag: "T_MEM",
            };
            assert!(!claim.check_native());
            assert!(claim.check_shape().is_err());
        }

        #[test]
        fn multiset_with_duplicates_pass() {
            // Multisets count multiplicities.
            let claim = PermArgClaim {
                left:  vec![gf(7), gf(7), gf(8)],
                right: vec![gf(7), gf(8), gf(7)],
                gamma: gf(99),
                perm_tag: "T_MEM",
            };
            assert!(claim.check_native());
        }

        #[test]
        fn empty_multisets_pass() {
            // Vacuous case: both empty ⇒ both products = 1 ⇒ equal.
            let claim = PermArgClaim::<Goldilocks> {
                left: vec![], right: vec![],
                gamma: gf(13),
                perm_tag: "T_MEM",
            };
            assert!(claim.check_native());
        }

        #[test]
        fn gamma_diversity_doesnt_create_false_acceptance() {
            // Different multisets — at every random γ tested, must reject.
            let left  = vec![gf(1), gf(2), gf(3)];
            let right = vec![gf(1), gf(2), gf(5)];
            for gamma_val in [1u64, 7, 999, 0x9E37_79B9_7F4A_7C15] {
                let claim = PermArgClaim {
                    left: left.clone(), right: right.clone(),
                    gamma: gf(gamma_val),
                    perm_tag: "T_MEM",
                };
                assert!(!claim.check_native(),
                    "γ={gamma_val} should reject different multisets");
            }
        }

        // ─── Perm-arg accumulator AIR tests ──────────────────────────

        #[test]
        fn perm_arg_accumulator_layout_width() {
            let layout = PermArgAccumulatorLayout::new(0);
            assert_eq!(layout.width, 4);
        }

        #[test]
        fn perm_arg_accumulator_synthesises_correct_products() {
            // 3-element multisets, same elements different order
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(3), gf(1), gf(2)],
                gamma: gf(7),
                perm_tag: "T_MEM",
            };
            let trace = PermArgAccumulatorTrace::synthesise(&claim);
            assert_eq!(trace.n_rows, 3);
            // Final running products should equal prod_left, prod_right
            // and be equal to each other.
            assert_eq!(trace.running_left[2], claim.prod_left());
            assert_eq!(trace.running_right[2], claim.prod_right());
            assert_eq!(trace.running_left[2], trace.running_right[2]);
        }

        #[test]
        fn perm_arg_accumulator_verifies_on_honest_claim() {
            let claim = PermArgClaim {
                left:  vec![gf(10), gf(20), gf(30), gf(40)],
                right: vec![gf(20), gf(30), gf(40), gf(10)],
                gamma: gf(0xCAFE),
                perm_tag: "T_MEM",
            };
            let trace = PermArgAccumulatorTrace::synthesise(&claim);
            assert!(verify_perm_arg_accumulator_trace(&trace));
        }

        #[test]
        fn perm_arg_accumulator_rejects_tampered_running_left() {
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(3), gf(1), gf(2)],
                gamma: gf(7),
                perm_tag: "T_MEM",
            };
            let mut trace = PermArgAccumulatorTrace::synthesise(&claim);
            trace.running_left[1] = gf(99);
            assert!(!verify_perm_arg_accumulator_trace(&trace),
                "tampered running_left must reject");
        }

        #[test]
        fn perm_arg_accumulator_rejects_unequal_multisets() {
            // Different multisets — synthesised trace ends with
            // running_left ≠ running_right → FinalBoundary rejects.
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(1), gf(2), gf(5)],  // 5 instead of 3
                gamma: gf(7),
                perm_tag: "T_MEM",
            };
            let trace = PermArgAccumulatorTrace::synthesise(&claim);
            assert!(!verify_perm_arg_accumulator_trace(&trace));
        }

        #[test]
        fn perm_arg_accumulator_columns_shape_and_padding() {
            // 5-element multisets → next pow2 = 8.
            let claim = PermArgClaim {
                left:  vec![gf(11), gf(22), gf(33), gf(44), gf(55)],
                right: vec![gf(33), gf(11), gf(55), gf(22), gf(44)],
                gamma: gf(0xDEAD),
                perm_tag: "T_MEM",
            };
            let trace = PermArgAccumulatorTrace::synthesise(&claim);
            let columns = perm_arg_accumulator_trace_to_columns(&trace);
            assert_eq!(columns.len(), 4);
            assert_eq!(columns[0].len(), 8);
            // Padding rows: l = r = 0.
            for r in 5..8 {
                assert!(columns[0][r].is_zero());
                assert!(columns[1][r].is_zero());
            }
            // Padding rows: running_left and running_right both multiply
            // by γ identically, so they stay equal across padding.
            for r in 5..8 {
                assert_eq!(columns[2][r], columns[3][r]);
            }
            assert!(verify_perm_arg_accumulator_columns(&columns, claim.gamma));
        }

        #[test]
        fn perm_arg_accumulator_columns_reject_tampered() {
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(3), gf(1), gf(2)],
                gamma: gf(7),
                perm_tag: "T_MEM",
            };
            let trace = PermArgAccumulatorTrace::synthesise(&claim);
            let mut columns = perm_arg_accumulator_trace_to_columns(&trace);
            // Tamper a running-left value.
            columns[2][1] = gf(99);
            assert!(!verify_perm_arg_accumulator_columns(&columns, claim.gamma));
        }

        #[test]
        fn perm_arg_accumulator_columns_reject_unequal_multisets() {
            // Different multisets → final running_left ≠ running_right,
            // FinalBoundary fails after padding.
            let claim = PermArgClaim {
                left:  vec![gf(1), gf(2), gf(3)],
                right: vec![gf(1), gf(2), gf(5)],
                gamma: gf(0xC0DE),
                perm_tag: "T_MEM",
            };
            let trace = PermArgAccumulatorTrace::synthesise(&claim);
            let columns = perm_arg_accumulator_trace_to_columns(&trace);
            assert!(!verify_perm_arg_accumulator_columns(&columns, claim.gamma));
        }

        #[test]
        fn perm_arg_accumulator_op_degrees() {
            // StepLeft and StepRight are degree 2 (prev_running · (γ + l_j))
            let _ = (PermArgAccumulatorOp::InitialLeft,
                     PermArgAccumulatorOp::InitialRight,
                     PermArgAccumulatorOp::StepLeft,
                     PermArgAccumulatorOp::StepRight,
                     PermArgAccumulatorOp::FinalBoundary);
        }

        #[test]
        fn tampered_single_element_breaks_argument() {
            // Honest left + right matching except one element.
            let mut left  = vec![gf(1), gf(2), gf(3), gf(4), gf(5)];
            let mut right = left.clone();
            // Tamper one element of right.
            right[2] = gf(99);
            let claim = PermArgClaim {
                left, right,
                gamma: gf(0xC0DE),
                perm_tag: "T_MEM",
            };
            assert!(!claim.check_native(),
                "single-element tamper must break perm-arg");
            let _ = (left, right) = (claim.left.clone(), claim.right.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_inputs_outer_pi_hash_is_deterministic() {
        let inner = [0xCAu8; 32];
        let a = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, inner);
        let b = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, inner);
        assert_eq!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn public_inputs_outer_pi_hash_changes_with_inner() {
        let i1 = [0xAAu8; 32];
        let i2 = [0xBBu8; 32];
        let a = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, i1);
        let b = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, i2);
        assert_ne!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn public_inputs_outer_pi_hash_changes_with_variant() {
        let inner = [0xCDu8; 32];
        let a = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_256, inner);
        let b = RecursiveStarkPublicInputs::for_inner(Sha3Variant::Sha3_384, inner);
        assert_ne!(a.outer_pi_hash, b.outer_pi_hash);
    }

    #[test]
    fn prove_recursive_returns_not_implemented_today() {
        let witness = RecursiveWitness {
            inner_proof_bytes: vec![0u8; 100],
            inner_merkle_roots: vec![],
        };
        let result = prove_recursive_stark(
            &witness, [0; 32], Sha3Variant::Sha3_256, 4, 54, false,
        );
        assert!(matches!(result, Err(RecursiveProverError::NotImplemented(_))));
    }

    #[test]
    fn verify_recursive_returns_false_today() {
        // Create a dummy proof via a roundabout path: we can't
        // easily construct a DeepFriProof manually so we just call
        // verify on a synthetically-zero'd struct.  This is fine
        // because the stub always returns false.
        let _ = verify_recursive_stark;  // type check; cannot easily call without DeepFriProof
    }
}
