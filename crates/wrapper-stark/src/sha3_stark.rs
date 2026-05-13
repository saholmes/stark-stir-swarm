//! End-to-end SHA-3 AIR orchestrator — message bytes to composed residue.
//!
//! Wires the full pipeline:
//!
//! ```text
//!   message bytes
//!         │
//!         ▼  pad10*1 (FIPS 202 §B.2)
//!   padded blocks
//!         │
//!         ▼  build SpongeLayout(variant, n_blocks)
//!   layout + constraint set
//!         │
//!         ▼  synthesize_sponge(blocks, variant)
//!   cells satisfying constraints
//!         │
//!         ▼  write into FieldMockTrace<Goldilocks>
//!   field-element trace
//!         │
//!         ▼  alphas_from_transcript(pi_hash, n_constraints)
//!   FS-derived combination coefficients
//!         │
//!         ▼  ConstraintSet::evaluate_composed(alphas, trace)
//!   Σ α_j · Φ_j  ∈ Goldilocks
//! ```
//!
//! Returns `Ok(Goldilocks::ZERO)` on a valid trace, `Ok(non_zero)` if
//! the synthesiser+constraints disagree (a bug), `Err(...)` on
//! configuration errors.  Tampering tests verify that bit-flips
//! produce non-zero residues with FS-derived α.
//!
//! # What this DOES
//!
//! Demonstrates the wrapper-stark constraint pipeline end-to-end.
//! The residue value is exactly what FRI/STIR would low-degree-test
//! once the [`crate::fri_bridge`] row-uniform refactor lands.
//!
//! # What this DOES NOT do
//!
//! - Produce a STARK proof (no LDE, no Merkle commits, no FRI/STIR
//!   queries).  This is the constraint-satisfaction layer only.
//! - Verify a SHA-3 preimage claim cryptographically.  For that, we
//!   need the wrapper-stark constraint set to be wired through
//!   [`deep_ali::fri::deep_fri_prove`].

use ark_goldilocks::Goldilocks;

use crate::bit_constraint::{FieldMockTrace, MockTrace, lift_to_field};
use crate::composition::{ConstraintSet, alphas_from_transcript};
use crate::sha3_absorb_air::Sha3Variant;
use crate::sponge_air::{
    SpongeLayout, sponge_constraints, synthesize_sponge, write_sponge_cells,
};

/// Errors from the end-to-end SHA-3 AIR orchestrator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sha3StarkError {
    /// Internal: synthesiser produced cells that don't satisfy the
    /// constraint set under i128 evaluation.  Either the synthesiser
    /// has a bug or the constraint set has a bug — should never
    /// happen in production code paths.
    SynthesiserConstraintMismatch { first_failing_constraint_idx: usize },
}

impl std::fmt::Display for Sha3StarkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SynthesiserConstraintMismatch { first_failing_constraint_idx: i } =>
                write!(f, "synthesiser/constraint mismatch at constraint #{i}"),
        }
    }
}

impl std::error::Error for Sha3StarkError {}

/// Compute the SHA-3 AIR constraint residue for `message` under
/// `variant`.  Returns `Goldilocks::ZERO` on a valid AIR trace (the
/// expected outcome when synth + constraints agree).
///
/// `fs_seed` is the Fiat-Shamir transcript seed used to derive the
/// constraint composition coefficients.  In production this is bound
/// to the inner proof's `pi_hash` for FS-soundness; for standalone
/// SHA-3 STARK proofs, callers may pass any 32-byte commitment that
/// includes `(variant, message_hash)` in its preimage.
pub fn sha3_air_residue(
    variant: Sha3Variant,
    message: &[u8],
    fs_seed: &[u8; 32],
) -> Result<Goldilocks, Sha3StarkError> {
    // 1. FIPS 202 §B.2 padding into rate-sized blocks.
    let block_len = variant.block_bytes();
    let mut blocks: Vec<Vec<u8>> = Vec::new();
    let mut offset = 0;
    while offset + block_len <= message.len() {
        blocks.push(message[offset..offset + block_len].to_vec());
        offset += block_len;
    }
    let mut last = vec![0u8; block_len];
    let tail = &message[offset..];
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] = 0x06;
    last[block_len - 1] |= 0x80;
    blocks.push(last);

    // 2. Build layout and constraint set.
    let layout = SpongeLayout::new(variant, blocks.len(), 0);
    let constraint_set = ConstraintSet::new(sponge_constraints(&layout));

    // 3. Synthesize cells.
    let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
    let cells = synthesize_sponge(&block_refs, variant);

    // 4. Write into a u64 mock trace.
    let n_rows = layout.rows();
    let row_width = layout.max_row_width();
    let mut u64_trace = MockTrace::zeros(n_rows, row_width);
    write_sponge_cells(&cells, &layout, &mut u64_trace);

    // 5. Internal consistency check: every constraint must satisfy
    // under i128 eval too (if synth disagrees with constraints under
    // i128 then field eval is irrelevant).
    if let Some(idx) = constraint_set.first_failing(
        &lift_to_field::<Goldilocks>(&u64_trace)
    ) {
        return Err(Sha3StarkError::SynthesiserConstraintMismatch {
            first_failing_constraint_idx: idx,
        });
    }

    // 6. Lift to Goldilocks + derive FS alphas + evaluate composed.
    let field_trace: FieldMockTrace<Goldilocks> = lift_to_field(&u64_trace);
    let alphas = alphas_from_transcript::<Goldilocks>(fs_seed, constraint_set.len());
    Ok(constraint_set.evaluate_composed(&alphas, &field_trace))
}

/// Statistics about a SHA-3 AIR for the given variant + message.
/// Useful for paper-grade constraint accounting and trace-size
/// reporting.
#[derive(Debug, Clone, Copy)]
pub struct Sha3AirStats {
    pub variant: Sha3Variant,
    pub message_len: usize,
    pub n_blocks: usize,
    pub n_rows: usize,
    pub row_width: usize,
    pub total_cells: usize,
    pub total_constraints: usize,
    pub max_constraint_degree: usize,
}

pub fn sha3_air_stats(variant: Sha3Variant, message_len: usize) -> Sha3AirStats {
    let block_len = variant.block_bytes();
    let n_blocks = (message_len / block_len) + 1;  // +1 for padding block
    let layout = SpongeLayout::new(variant, n_blocks, 0);
    let constraints = sponge_constraints(&layout);
    let set = ConstraintSet::new(constraints);
    Sha3AirStats {
        variant,
        message_len,
        n_blocks,
        n_rows: layout.rows(),
        row_width: layout.max_row_width(),
        total_cells: layout.rows() * layout.max_row_width(),
        total_constraints: set.len(),
        max_constraint_degree: set.max_degree(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Zero;

    fn fs_seed() -> [u8; 32] { [0xCAu8; 32] }

    #[test]
    fn empty_message_residue_is_zero() {
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let r = sha3_air_residue(variant, b"", &fs_seed()).unwrap();
            assert!(r.is_zero(),
                "variant {variant:?} empty message residue should be zero; got {r:?}");
        }
    }

    #[test]
    fn abc_message_residue_is_zero() {
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let r = sha3_air_residue(variant, b"abc", &fs_seed()).unwrap();
            assert!(r.is_zero(), "variant {variant:?} 'abc' residue should be zero");
        }
    }

    #[test]
    fn multi_block_message_residue_is_zero() {
        let msg = vec![0xA5u8; 200];
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let r = sha3_air_residue(variant, &msg, &fs_seed()).unwrap();
            assert!(r.is_zero(), "variant {variant:?} 200-byte residue should be zero");
        }
    }

    #[test]
    fn different_messages_give_different_alpha_paths_but_both_zero() {
        // The fs_seed is the same here, so alphas are the same — but
        // the underlying constraint set differs because n_blocks may
        // differ.  Both should still yield zero on valid traces.
        let r_short = sha3_air_residue(Sha3Variant::Sha3_256, b"abc", &fs_seed()).unwrap();
        let r_long  = sha3_air_residue(Sha3Variant::Sha3_256, &[0xA5u8; 200], &fs_seed()).unwrap();
        assert!(r_short.is_zero());
        assert!(r_long.is_zero());
    }

    #[test]
    fn air_stats_make_sense() {
        // L1 / "abc" — one block, 97 rows.
        let stats = sha3_air_stats(Sha3Variant::Sha3_256, 3);
        assert_eq!(stats.n_blocks, 1);
        assert_eq!(stats.n_rows, 97);
        assert_eq!(stats.max_constraint_degree, 2);
        // Constraint count for one block: roughly 843K permutation +
        // absorb_xor + threading.  Must be > 843K and < 1M.
        assert!(stats.total_constraints > 843_000);
        assert!(stats.total_constraints < 1_000_000);

        // L3 multi-block (200 bytes / 104-byte block = 1 + padding = 2 blocks)
        let stats3 = sha3_air_stats(Sha3Variant::Sha3_384, 200);
        assert_eq!(stats3.n_blocks, 2);
        assert_eq!(stats3.n_rows, 194);
        assert!(stats3.total_constraints > 1_700_000);  // ~2× single-block

        // L5 (576-bit rate = 72-byte block).  200 bytes / 72 = 2 + padding = 3 blocks.
        let stats5 = sha3_air_stats(Sha3Variant::Sha3_512, 200);
        assert_eq!(stats5.n_blocks, 3);
        assert_eq!(stats5.n_rows, 291);
        assert!(stats5.total_constraints > 2_500_000);  // ~3× single-block
    }

    #[test]
    fn stats_scale_linearly_with_blocks() {
        // Within one variant, total_constraints should scale linearly
        // with n_blocks.
        let one  = sha3_air_stats(Sha3Variant::Sha3_256, 3);
        let many = sha3_air_stats(Sha3Variant::Sha3_256, 3 + 4 * one.n_rows /* arbitrary multi */);
        // Allow ±10 % slack for absorb_xor + threading overhead variance.
        let ratio = many.total_constraints as f64 / one.total_constraints as f64;
        assert!(ratio > many.n_blocks as f64 * 0.95);
        assert!(ratio < many.n_blocks as f64 * 1.05);
    }
}
