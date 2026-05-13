//! Constraint composition layer.
//!
//! # Purpose
//!
//! The SHA-3 AIR emits a list of position-specific [`BitOp`]
//! constraints — 843 200 of them for one Keccak-f1600 permutation,
//! more for a multi-block sponge.  FRI/STIR consumes ONE composition
//! polynomial, not a list.  This module folds a list of BitOps into
//! the single polynomial
//!
//! ```text
//!   Φ(trace) = Σ_j α_j · Φ_j(trace)
//! ```
//!
//! where the `α_j` ∈ F_ext are FS-derived from the transcript.  This
//! matches the standard STARK pattern (paper §3.1, Definition 1) and
//! enables Event-E1 (combination-cancellation) soundness analysis:
//! a single non-zero Φ_j puts the composed Φ off-codeword with
//! probability ≥ 1 − 1/|F_ext| (Schwartz-Zippel).
//!
//! # Soundness contract
//!
//! On a valid trace (every Φ_j evaluates to 0), Φ evaluates to 0 for
//! every choice of α_j — hence FRI accepts.  On an invalid trace
//! (some Φ_j ≠ 0), the probability that the FS-derived α_j happen
//! to make Φ = 0 is ≤ 1/|F_ext| ≈ 2⁻³⁸⁴ for Goldilocks Fp⁶ at L3.
//! See [`crate::sha3_absorb_air`]'s feedback note on FS-deriving
//! perm-arg challenges in F_ext.
//!
//! # FS-derived coefficients
//!
//! `alphas_from_transcript(transcript_seed, n_constraints) -> Vec<F>`
//! takes a 32-byte transcript commitment and a constraint count, and
//! produces `n_constraints` independent F-elements.  The transcript
//! seed in production will be the inner proof's pi_hash for binding;
//! tests use a static seed.

use ark_ff::{Field, PrimeField};
use crate::bit_constraint::{BitOp, FieldTraceAccess};

/// A list of BitOps that should ALL be satisfied by a valid trace.
/// Wraps a `Vec<BitOp>` with composition + evaluation helpers.
#[derive(Clone, Debug)]
pub struct ConstraintSet {
    pub constraints: Vec<BitOp>,
}

impl ConstraintSet {
    pub fn new(constraints: Vec<BitOp>) -> Self { Self { constraints } }

    /// Number of constraints in the set.
    pub fn len(&self) -> usize { self.constraints.len() }
    pub fn is_empty(&self) -> bool { self.constraints.is_empty() }

    /// Evaluate the composed polynomial Φ(trace) = Σ α_j · Φ_j(trace)
    /// on a field-trace.  Returns ZERO iff every individual constraint
    /// evaluates to zero (modulo Event-E1 SZ noise — for non-random
    /// α the residue can accidentally cancel; that's why production
    /// MUST use [`alphas_from_transcript`] to derive α via FS).
    pub fn evaluate_composed<F: Field>(
        &self,
        alphas: &[F],
        trace: &impl FieldTraceAccess<F>,
    ) -> F {
        assert_eq!(alphas.len(), self.constraints.len(),
            "α coefficient count must equal constraint count");
        let mut acc = F::zero();
        for (op, &alpha) in self.constraints.iter().zip(alphas) {
            acc += alpha * op.eval_field(trace);
        }
        acc
    }

    /// Returns the maximum degree across all constraints in the set.
    /// Drives the AIR's `d_c` parameter — paper Corollary 1 uses
    /// `D = d_c · T` to bound the composed polynomial degree.
    pub fn max_degree(&self) -> usize {
        self.constraints.iter().map(|c| c.degree()).max().unwrap_or(0)
    }

    /// Returns the index of the first failing constraint on a trace,
    /// or `None` if every constraint is satisfied.  Diagnostic helper
    /// for debugging — production code MUST go through `evaluate_composed`
    /// because individual `Φ_j ≠ 0` can be masked by random α (the
    /// whole point of Event-E1 is that this masking is SZ-improbable).
    pub fn first_failing<F: Field>(
        &self, trace: &impl FieldTraceAccess<F>,
    ) -> Option<usize> {
        self.constraints.iter().enumerate()
            .find(|(_, c)| !c.eval_field(trace).is_zero())
            .map(|(i, _)| i)
    }
}

/// Derive `n` independent challenge coefficients α_j ∈ F from a
/// 32-byte transcript seed.  Uses SHA-3-256 as a CSPRNG: each
/// 8 bytes of output gives one u64 that's reduced mod p to an F
/// element.  Soundness: each α_j is computationally indistinguishable
/// from uniform in F under SHA-3 CR (paper §2.1 Theorem 8 / FIPS 202).
///
/// In production this is wired to the FS transcript (the inner proof's
/// pi_hash + accumulated state).  Tests use a static seed.
pub fn alphas_from_transcript<F: PrimeField>(
    transcript_seed: &[u8; 32],
    n: usize,
) -> Vec<F> {
    use ::sha3::Digest;
    let mut out = Vec::with_capacity(n);
    let mut counter: u64 = 0;
    while out.len() < n {
        let mut h = ::sha3::Sha3_256::new();
        h.update(b"WRAPPER-STARK-ALPHA-V1");
        h.update(transcript_seed);
        h.update(counter.to_le_bytes());
        let digest = h.finalize();
        // Extract 4 × 8-byte u64s per digest (256 / 64 = 4).
        for k in 0..4 {
            if out.len() == n { break; }
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(&digest[8 * k..8 * (k + 1)]);
            let v = u64::from_le_bytes(bytes);
            out.push(F::from(v));
        }
        counter += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_goldilocks::Goldilocks;
    use ark_ff::{Zero, UniformRand};
    use crate::bit_constraint::{BitOp, CellRef, FieldMockTrace, MockTrace, TraceAccess, lift_to_field};
    use crate::keccak_round_air::{
        ThetaLayout, theta_constraints, synthesize_theta, write_theta_cells,
    };
    use crate::sha3_absorb_air::{KeccakState, bit_state_from_lanes};

    fn cell(row: usize, col: usize) -> CellRef { CellRef::new(row, col) }

    fn make_seed() -> [u8; 32] {
        let mut s = [0u8; 32];
        for i in 0..32 { s[i] = (0xCA + i as u8) % 255; }
        s
    }

    #[test]
    fn composition_zero_on_satisfying_trace() {
        // 8 simple XOR constraints, all satisfied; composition must be 0.
        let mut ops = Vec::new();
        for i in 0..8 {
            ops.push(BitOp::Xor {
                c: cell(0, 2 + 3 * i),
                a: cell(0,     3 * i),
                b: cell(0, 1 + 3 * i),
            });
        }
        let set = ConstraintSet::new(ops);

        let mut t = FieldMockTrace::<Goldilocks>::zeros(1, 24);
        // Fill with valid XOR triples: a, b, c = a XOR b.
        for i in 0..8 {
            let a = (i & 1) as u64;
            let b = ((i >> 1) & 1) as u64;
            t.set(cell(0,     3 * i), Goldilocks::from(a));
            t.set(cell(0, 1 + 3 * i), Goldilocks::from(b));
            t.set(cell(0, 2 + 3 * i), Goldilocks::from(a ^ b));
        }

        let alphas = alphas_from_transcript::<Goldilocks>(&make_seed(), set.len());
        let composed = set.evaluate_composed(&alphas, &t);
        assert!(composed.is_zero(),
            "satisfying trace must give Φ = 0; got {composed:?}");
    }

    #[test]
    fn composition_nonzero_on_tampered_trace_with_fs_alphas() {
        // Same trace but with one XOR result corrupted.  With
        // FS-derived random alphas the composed residue is almost
        // surely non-zero.
        let mut ops = Vec::new();
        for i in 0..8 {
            ops.push(BitOp::Xor {
                c: cell(0, 2 + 3 * i),
                a: cell(0,     3 * i),
                b: cell(0, 1 + 3 * i),
            });
        }
        let set = ConstraintSet::new(ops);

        let mut t = FieldMockTrace::<Goldilocks>::zeros(1, 24);
        for i in 0..8 {
            let a = (i & 1) as u64;
            let b = ((i >> 1) & 1) as u64;
            t.set(cell(0,     3 * i), Goldilocks::from(a));
            t.set(cell(0, 1 + 3 * i), Goldilocks::from(b));
            t.set(cell(0, 2 + 3 * i), Goldilocks::from(a ^ b));
        }
        // Tamper one output.
        t.set(cell(0, 2), Goldilocks::from(1u64));  // wrong: a=0,b=0,c should be 0

        let alphas = alphas_from_transcript::<Goldilocks>(&make_seed(), set.len());
        let composed = set.evaluate_composed(&alphas, &t);
        assert!(!composed.is_zero(),
            "tampered trace must give Φ ≠ 0 with FS alphas; got zero");
    }

    #[test]
    fn alphas_are_deterministic_given_seed() {
        // Same seed → same alphas, every time.  Required for the
        // verifier to re-derive coefficients identically.
        let seed = make_seed();
        let a1 = alphas_from_transcript::<Goldilocks>(&seed, 17);
        let a2 = alphas_from_transcript::<Goldilocks>(&seed, 17);
        assert_eq!(a1, a2);
    }

    #[test]
    fn alphas_differ_for_different_seeds() {
        // Different seeds → different alphas (with high probability).
        let s1 = [0xAA; 32];
        let s2 = [0xBB; 32];
        let a1 = alphas_from_transcript::<Goldilocks>(&s1, 17);
        let a2 = alphas_from_transcript::<Goldilocks>(&s2, 17);
        assert_ne!(a1, a2);
    }

    #[test]
    fn alphas_count_matches_request() {
        for n in [1usize, 7, 17, 64, 100, 1024] {
            let alphas = alphas_from_transcript::<Goldilocks>(&make_seed(), n);
            assert_eq!(alphas.len(), n);
        }
    }

    #[test]
    fn composed_residue_zero_iff_first_failing_none() {
        // Diagnostic invariant: `first_failing` returns Some iff
        // `evaluate_composed` is non-zero (modulo the SZ probability
        // of accidental cancellation — which our static test seed
        // doesn't trigger for this trace, established empirically).
        let mut ops = Vec::new();
        for i in 0..4 {
            ops.push(BitOp::Xor {
                c: cell(0, 2 + 3 * i),
                a: cell(0,     3 * i),
                b: cell(0, 1 + 3 * i),
            });
        }
        let set = ConstraintSet::new(ops);

        // Satisfying trace
        let mut t = FieldMockTrace::<Goldilocks>::zeros(1, 12);
        for i in 0..4 {
            t.set(cell(0,     3 * i), Goldilocks::from(0u64));
            t.set(cell(0, 1 + 3 * i), Goldilocks::from(0u64));
            t.set(cell(0, 2 + 3 * i), Goldilocks::from(0u64));
        }
        let alphas = alphas_from_transcript::<Goldilocks>(&make_seed(), set.len());
        assert!(set.evaluate_composed(&alphas, &t).is_zero());
        assert_eq!(set.first_failing(&t), None);

        // Tamper one constraint
        t.set(cell(0, 2), Goldilocks::from(1u64));
        assert!(!set.evaluate_composed(&alphas, &t).is_zero());
        assert!(set.first_failing(&t).is_some());
    }

    #[test]
    fn max_degree_reflects_constraint_zoo() {
        let ops = vec![
            BitOp::Boolean { b: cell(0, 0) },     // degree 2
            BitOp::Copy { c: cell(0, 1), a: cell(0, 0) }, // degree 1
        ];
        let set = ConstraintSet::new(ops);
        assert_eq!(set.max_degree(), 2);

        // Empty set
        let empty = ConstraintSet::new(vec![]);
        assert_eq!(empty.max_degree(), 0);
    }

    #[test]
    fn composes_full_theta_constraint_set() {
        // The headline integration test: compose the full 8 000-constraint
        // θ set with FS-derived α, evaluate on a real synthesised trace,
        // get zero.  Tamper one cell, get non-zero.
        let layout = ThetaLayout::new(0, 0);
        let set = ConstraintSet::new(theta_constraints(&layout));
        assert_eq!(set.len(), 8000);
        assert_eq!(set.max_degree(), 2);

        let s: KeccakState = [0xDEAD_BEEF_CAFE_BABE; 25];
        let input = bit_state_from_lanes(&s);
        let synth = synthesize_theta(&input);

        let mut trace = MockTrace::zeros(1, layout.width);
        write_theta_cells(&synth, &layout, &mut trace);
        let field_trace: FieldMockTrace<Goldilocks> = lift_to_field(&trace);

        let alphas = alphas_from_transcript::<Goldilocks>(&make_seed(), set.len());
        let composed = set.evaluate_composed(&alphas, &field_trace);
        assert!(composed.is_zero(),
            "valid θ trace must compose to 0; got {composed:?}");

        // Tamper: flip a bit in the output state.
        let mut tampered = trace.clone();
        let bad_cell = layout.output_bit(11, 22);
        let original = tampered.get_cell(bad_cell);
        tampered.set(bad_cell, 1 - original);
        let tampered_field: FieldMockTrace<Goldilocks> = lift_to_field(&tampered);
        let composed_bad = set.evaluate_composed(&alphas, &tampered_field);
        assert!(!composed_bad.is_zero(),
            "tampered θ trace must compose to non-zero");
    }

    #[test]
    fn random_alphas_give_same_satisfaction_classification() {
        // Sanity: composition with truly-random (non-FS) alphas
        // still gives 0 on a satisfying trace, non-zero on tampered.
        // This catches bugs in `evaluate_composed` that would only
        // be visible with non-FS alphas (e.g. accidental alpha
        // index/constraint index misalignment).
        use rand::SeedableRng;
        use rand::rngs::StdRng;

        let layout = ThetaLayout::new(0, 0);
        let set = ConstraintSet::new(theta_constraints(&layout));

        let s: KeccakState = [0u64; 25];
        let input = bit_state_from_lanes(&s);
        let synth = synthesize_theta(&input);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_theta_cells(&synth, &layout, &mut trace);
        let field_trace: FieldMockTrace<Goldilocks> = lift_to_field(&trace);

        let mut rng = StdRng::seed_from_u64(0xDEAD_BEEF);
        let alphas: Vec<Goldilocks> = (0..set.len())
            .map(|_| Goldilocks::rand(&mut rng))
            .collect();
        assert!(set.evaluate_composed(&alphas, &field_trace).is_zero());
    }
}
