//! Row-uniform AIR encoding for SHA-3.
//!
//! # Why row-uniform
//!
//! Every production STARK encodes Keccak with **row-uniform** constraints:
//! a small set of polynomial identities that fire at every trace row,
//! gated by selector polynomials that pick the sub-step.  This is what
//! `deep_ali::fri::deep_fri_prove` consumes.
//!
//! Our prior [`crate::keccak_round_air`] module uses **cell-list**
//! constraints — each [`BitOp`] references absolute `CellRef { row, col }`.
//! That's good for testing constraint logic but doesn't fit deep_ali's
//! AIR model.  This module is the paper-grade replacement that the
//! FRI bridge actually consumes.
//!
//! # Row schema (uniform across the entire trace)
//!
//! Each row has the SAME column layout:
//!
//! ```text
//!   columns        meaning
//!   ──────────     ─────────────────────────────────────────
//!   [0..1600)      state_in_bits   (input state, 25 × 64)
//!   [1600..3200)   state_out_bits  (output state, 25 × 64)
//!   [3200..6400)   helper_bits     (sub-step-specific, zero when unused)
//!   [6400..6464)   rc_bits         (round constant for ι, public)
//!   [6464..7552)   block_bits      (absorb input, up to 1088 bits for SHA3-256)
//!   [7552..7557)   selectors       (5 cells: s_θ, s_ρπ, s_χ, s_ι, s_absorb)
//!   ──────────     ─────────────────────────────────────────
//!   width = 7557 cells per row
//! ```
//!
//! Helper-cell budget per sub-step (zero-padded into the 3200-cell
//! [`UniformRowSchema::helpers`] range):
//!
//! - θ:    960 chain + 320 C + 320 D = 1600 cells (uses first 1600)
//! - ρπ:   0
//! - χ:    1600 not_b1 + 1600 and_part = 3200 cells (uses all 3200)
//! - ι:    0
//!
//! Selector columns hold {0, 1}; exactly one selector is 1 per row.
//!
//! # Block structure (per absorb block: 97 rows)
//!
//! Row 0 within a block: absorb-XOR (s_absorb = 1)
//! Rows 1..97:           24 rounds × 4 sub-steps in order θ, ρπ, χ, ι
//!
//! # Constraints
//!
//! All constraints have the form `Φ(state_in[r], state_out[r], helpers[r],
//! rc[r], block[r], selectors[r], state_in[r+1], …) = 0`, fired
//! everywhere but gated by selectors.
//!
//! Examples:
//! - `s_θ(r) · (helpers_chain_0(r) - state_in(r) ⊕ state_in(r))` enforces
//!   the first XOR in the θ column-parity chain
//! - `s_ρπ(r) · (state_out[dst](r) - state_in[src]((r) at rotated bit))` enforces
//!   the bit-permutation
//! - "thread" constraint:  `state_in[bit](r+1) - state_out[bit](r) = 0`
//!   (no selector — applies between consecutive rows ALWAYS, since
//!   every sub-step row hands off its output to the next row's input)
//!
//! This commit lands the **schema + selector machinery** only.  The
//! row-uniform constraint generators (analogues of theta_constraints,
//! etc.) come in subsequent commits.

use core::ops::Range;
use crate::sha3_absorb_air::Sha3Variant;

/// Uniform column layout for SHA-3 row-uniform AIR.
#[derive(Clone, Debug)]
pub struct UniformRowSchema {
    pub variant: Sha3Variant,
    pub width: usize,
    /// Input state bit cells: 25 lanes × 64 bits = 1600 cells.
    pub state_in: Range<usize>,
    /// Output state bit cells: 1600 cells.
    pub state_out: Range<usize>,
    /// Sub-step helpers (zero-padded union of θ + χ helpers): 3200 cells.
    pub helpers: Range<usize>,
    /// Round-constant bits for ι: 64 cells.  Public-input column —
    /// the verifier knows these values from `ROUND_CONSTANTS[round_at_row(r)]`.
    pub rc_bits: Range<usize>,
    /// Absorb block bits.  Width = variant.rate_bits() (e.g. 1088 for SHA3-256).
    pub block_bits: Range<usize>,
    /// Selectors (one cell per sub-step + absorb): 5 cells.
    pub selectors: Range<usize>,
}

impl UniformRowSchema {
    pub fn new(variant: Sha3Variant) -> Self {
        let state_in     = 0..1600;
        let state_out    = 1600..3200;
        let helpers      = 3200..6400;
        let rc_bits      = 6400..6464;
        let block_bits   = 6464..6464 + variant.rate_bits();
        let selectors    = block_bits.end..block_bits.end + 5;
        let width        = selectors.end;
        Self { variant, width, state_in, state_out, helpers, rc_bits, block_bits, selectors }
    }

    pub fn state_in_bit(&self, lane: usize, bit: usize) -> usize {
        debug_assert!(lane < 25 && bit < 64);
        self.state_in.start + 64 * lane + bit
    }

    pub fn state_out_bit(&self, lane: usize, bit: usize) -> usize {
        debug_assert!(lane < 25 && bit < 64);
        self.state_out.start + 64 * lane + bit
    }

    pub fn helper_bit(&self, helper_offset: usize) -> usize {
        debug_assert!(helper_offset < self.helpers.len());
        self.helpers.start + helper_offset
    }

    pub fn rc_bit(&self, bit: usize) -> usize {
        debug_assert!(bit < 64);
        self.rc_bits.start + bit
    }

    pub fn block_bit(&self, bit: usize) -> usize {
        debug_assert!(bit < self.block_bits.len());
        self.block_bits.start + bit
    }

    pub fn selector(&self, sel: SelectorIndex) -> usize {
        self.selectors.start + sel as usize
    }
}

/// The five selector columns in the row-uniform schema.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(usize)]
pub enum SelectorIndex {
    Theta  = 0,
    RhoPi  = 1,
    Chi    = 2,
    Iota   = 3,
    Absorb = 4,
}

impl SelectorIndex {
    pub const ALL: [Self; 5] = [
        Self::Theta, Self::RhoPi, Self::Chi, Self::Iota, Self::Absorb,
    ];
}

/// One row's sub-step type, derived from the row index modulo 97.
/// Row 0 of every block is absorb-XOR; rows 1..97 are 24 rounds in
/// order θ, ρπ, χ, ι.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowType {
    Absorb,
    SubStep { round_idx: u8, sub_step: SelectorIndex },
}

impl RowType {
    /// Classify a row at position `r` within a block (r ∈ [0..97)).
    pub fn at_block_row(r: usize) -> Self {
        if r == 0 {
            Self::Absorb
        } else {
            let r = r - 1; // 0-indexed position within the permutation
            let round_idx = (r / 4) as u8;
            let sub_step = match r % 4 {
                0 => SelectorIndex::Theta,
                1 => SelectorIndex::RhoPi,
                2 => SelectorIndex::Chi,
                3 => SelectorIndex::Iota,
                _ => unreachable!(),
            };
            Self::SubStep { round_idx, sub_step }
        }
    }

    /// Which selector should be 1 for this row.
    pub fn active_selector(&self) -> SelectorIndex {
        match self {
            Self::Absorb => SelectorIndex::Absorb,
            Self::SubStep { sub_step, .. } => *sub_step,
        }
    }

    /// The round index for ι rows (otherwise None).  Drives which
    /// round-constant value the AIR pins into `rc_bits` at this row.
    pub fn iota_round(&self) -> Option<u8> {
        match self {
            Self::SubStep { round_idx, sub_step: SelectorIndex::Iota } => Some(*round_idx),
            _ => None,
        }
    }
}

/// Number of rows per absorb block (1 absorb + 24 rounds × 4 sub-steps).
pub const ROWS_PER_BLOCK: usize = 97;

/// Number of rows for an N-block sponge run.
pub fn rows_for_blocks(n_blocks: usize) -> usize {
    ROWS_PER_BLOCK * n_blocks
}

/// Selector column values for the entire trace.  Returns a vector of
/// length `n_rows` where `selectors[r]` = the active SelectorIndex
/// at row `r`.  Verifier publicly computes this from row index — no
/// witness needed.
pub fn selector_pattern(n_blocks: usize) -> Vec<SelectorIndex> {
    let mut out = Vec::with_capacity(rows_for_blocks(n_blocks));
    for _block in 0..n_blocks {
        for r in 0..ROWS_PER_BLOCK {
            out.push(RowType::at_block_row(r).active_selector());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_widths_per_variant() {
        let s256 = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let s384 = UniformRowSchema::new(Sha3Variant::Sha3_384);
        let s512 = UniformRowSchema::new(Sha3Variant::Sha3_512);

        // state_in + state_out + helpers + rc_bits + block_bits + selectors
        assert_eq!(s256.width, 1600 + 1600 + 3200 + 64 + 1088 + 5);  // 7557
        assert_eq!(s384.width, 1600 + 1600 + 3200 + 64 +  832 + 5);  // 7301
        assert_eq!(s512.width, 1600 + 1600 + 3200 + 64 +  576 + 5);  // 7045

        // Ranges should be contiguous and non-overlapping.
        for s in [&s256, &s384, &s512] {
            assert_eq!(s.state_in.start, 0);
            assert_eq!(s.state_in.end, s.state_out.start);
            assert_eq!(s.state_out.end, s.helpers.start);
            assert_eq!(s.helpers.end, s.rc_bits.start);
            assert_eq!(s.rc_bits.end, s.block_bits.start);
            assert_eq!(s.block_bits.end, s.selectors.start);
            assert_eq!(s.selectors.end, s.width);
            assert_eq!(s.state_in.len(), 1600);
            assert_eq!(s.state_out.len(), 1600);
            assert_eq!(s.helpers.len(), 3200);
            assert_eq!(s.rc_bits.len(), 64);
            assert_eq!(s.selectors.len(), 5);
        }
    }

    #[test]
    fn cell_accessors_inside_ranges() {
        let s = UniformRowSchema::new(Sha3Variant::Sha3_256);
        assert!(s.state_in.contains(&s.state_in_bit(0, 0)));
        assert!(s.state_in.contains(&s.state_in_bit(24, 63)));
        assert!(s.state_out.contains(&s.state_out_bit(0, 0)));
        assert!(s.helpers.contains(&s.helper_bit(0)));
        assert!(s.helpers.contains(&s.helper_bit(3199)));
        assert!(s.rc_bits.contains(&s.rc_bit(0)));
        assert!(s.rc_bits.contains(&s.rc_bit(63)));
        assert!(s.block_bits.contains(&s.block_bit(0)));
        assert!(s.block_bits.contains(&s.block_bit(s.block_bits.len() - 1)));
        for sel in SelectorIndex::ALL {
            assert!(s.selectors.contains(&s.selector(sel)));
        }
    }

    #[test]
    fn row_classification_within_block() {
        assert_eq!(RowType::at_block_row(0), RowType::Absorb);

        // Round 0: rows 1..5 are θ, ρπ, χ, ι
        for (r, expected_sub) in [(1, SelectorIndex::Theta), (2, SelectorIndex::RhoPi),
                                  (3, SelectorIndex::Chi), (4, SelectorIndex::Iota)] {
            let rt = RowType::at_block_row(r);
            assert_eq!(rt.active_selector(), expected_sub);
            if expected_sub == SelectorIndex::Iota {
                assert_eq!(rt.iota_round(), Some(0));
            }
        }

        // Round 5: rows 21..25
        for (r, expected_sub) in [(21, SelectorIndex::Theta), (22, SelectorIndex::RhoPi),
                                  (23, SelectorIndex::Chi), (24, SelectorIndex::Iota)] {
            assert_eq!(RowType::at_block_row(r).active_selector(), expected_sub);
        }

        // Round 23 (last): rows 93..97
        for (r, expected_sub) in [(93, SelectorIndex::Theta), (94, SelectorIndex::RhoPi),
                                  (95, SelectorIndex::Chi), (96, SelectorIndex::Iota)] {
            let rt = RowType::at_block_row(r);
            assert_eq!(rt.active_selector(), expected_sub);
            if expected_sub == SelectorIndex::Iota {
                assert_eq!(rt.iota_round(), Some(23));
            }
        }
    }

    #[test]
    fn selector_pattern_for_n_blocks() {
        let p = selector_pattern(2);
        assert_eq!(p.len(), 2 * ROWS_PER_BLOCK);
        // Row 0 = absorb, row 97 = absorb (start of block 1).
        assert_eq!(p[0],  SelectorIndex::Absorb);
        assert_eq!(p[97], SelectorIndex::Absorb);
        // First θ row in each block at offset 1.
        assert_eq!(p[1],  SelectorIndex::Theta);
        assert_eq!(p[98], SelectorIndex::Theta);
        // No two consecutive rows in a block have the same sub-step.
        // (Except inter-block: rows 96 = ι of block 0, row 97 = absorb
        // of block 1 — those differ.)
        for r in 0..p.len() - 1 {
            if r % ROWS_PER_BLOCK == 0 { continue; }  // skip the inter-block boundary
            assert_ne!(p[r], p[r + 1], "consecutive same-step at row {r}");
        }
    }

    #[test]
    fn selector_count_per_block() {
        // Each block has 1 absorb + 24 of each {θ, ρπ, χ, ι}.
        let p = selector_pattern(1);
        assert_eq!(p.iter().filter(|&&s| s == SelectorIndex::Absorb).count(), 1);
        for sub in [SelectorIndex::Theta, SelectorIndex::RhoPi,
                    SelectorIndex::Chi, SelectorIndex::Iota] {
            assert_eq!(p.iter().filter(|&&s| s == sub).count(), 24,
                "expected 24 of {sub:?} per block");
        }
    }

    #[test]
    fn rows_for_blocks_is_linear() {
        assert_eq!(rows_for_blocks(0), 0);
        assert_eq!(rows_for_blocks(1), 97);
        assert_eq!(rows_for_blocks(2), 194);
        assert_eq!(rows_for_blocks(10), 970);
    }

    #[test]
    fn iota_round_only_on_iota_rows() {
        // θ/ρπ/χ rows don't carry a round index even though they're
        // part of a round.  Only ι exposes its round_idx (because that's
        // what selects the round constant for the rc_bits column).
        let r2 = RowType::at_block_row(2);  // ρπ of round 0
        assert_eq!(r2.iota_round(), None);

        let r4 = RowType::at_block_row(4);  // ι of round 0
        assert_eq!(r4.iota_round(), Some(0));
    }
}
