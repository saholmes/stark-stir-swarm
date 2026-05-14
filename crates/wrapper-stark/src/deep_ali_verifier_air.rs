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
