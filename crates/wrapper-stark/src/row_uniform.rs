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

// ─── Row-uniform constraint generators ──────────────────────────────
//
// Constraints reference COLUMNS only (no absolute row).  They're
// applied at every row of the trace; the selector multiplier gates
// them to the appropriate sub-step.  Composition polynomial:
//
//   Φ(trace, r) = Σ_j α_j · selector_at(r, j) · Φ_j(cells_at_row(r))
//
// On rows where the selector is 0 the contribution is 0 — the
// constraint vanishes vacuously, no booleanity required of the
// underlying Φ_j.

/// Number of rows for an N-block sponge run.
pub fn rows_for_blocks(n_blocks: usize) -> usize {
    ROWS_PER_BLOCK * n_blocks
}

/// Reference to one column of the uniform-schema trace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ColRef(pub usize);

/// A row-uniform polynomial constraint.  References COLUMNS only —
/// the row is implicit (the row at which the constraint fires).
/// All ops also implicitly carry a selector that gates them; the
/// selector wrapper is [`RowUniformConstraint`] below.
///
/// Cross-row reference (`NextRow*`) variants reference cells at the
/// row after the current one, used for state-threading between
/// consecutive sub-step rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowUniformOp {
    /// `c = a XOR b` at the current row, both inputs boolean.
    Xor { c: ColRef, a: ColRef, b: ColRef },
    /// `c = a AND b`, boolean inputs.
    And { c: ColRef, a: ColRef, b: ColRef },
    /// `c = NOT a`.
    Not { c: ColRef, a: ColRef },
    /// `c = a` — used for ρπ bit-permutation between state_in cells
    /// and state_out cells.
    Copy { c: ColRef, a: ColRef },
    /// `c = a XOR k` where `k ∈ {0, 1}` is a public/static bit (ι).
    XorConst { c: ColRef, a: ColRef, k: u8 },
    /// `b ∈ {0, 1}` — booleanity constraint.
    Boolean { b: ColRef },
    /// `dst(next_row) = src(this_row)` — cross-row threading copy.
    /// Used between consecutive sub-step rows to propagate state_out
    /// of row r into state_in of row r+1.
    NextRowCopy { dst: ColRef, src: ColRef },
}

impl RowUniformOp {
    /// Algebraic degree of the constraint polynomial (before selector
    /// multiplication).  After selector multiplication degree += 1.
    pub fn degree(&self) -> usize {
        match self {
            Self::Xor { .. }            => 2,  // 2ab term
            Self::And { .. }            => 2,  // a·b term
            Self::Not { .. }            => 1,
            Self::Copy { .. }           => 1,
            Self::XorConst { .. }       => 1,
            Self::Boolean { .. }        => 2,
            Self::NextRowCopy { .. }    => 1,
        }
    }
}

/// One row-uniform constraint = a selector + the polynomial it gates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RowUniformConstraint {
    /// Selector that gates this constraint.  At a row r:
    /// - if `selectors[r] == this.selector`, the constraint must hold
    /// - otherwise, the constraint is multiplied by 0 (vacuous)
    pub selector: SelectorIndex,
    pub op: RowUniformOp,
}

impl RowUniformConstraint {
    /// Total degree after selector multiplication.  Selector cells
    /// are degree-1 (linear).
    pub fn total_degree(&self) -> usize {
        1 + self.op.degree()
    }
}

// ─── Helper-cell column allocation for θ ─────────────────────────────
//
// θ uses the first 1600 cells of the [`helpers`] range:
//   helpers[0..960]      parity-chain intermediates: 3 per (x, bit)
//                        layout: [3*(64*x + bit) + i for i ∈ 0..3]
//   helpers[960..1280]   column parities C[x][bit]:
//                        layout: [960 + 64*x + bit]
//   helpers[1280..1600]  diffuse vector D[x][bit]:
//                        layout: [1280 + 64*x + bit]

fn theta_chain_col(schema: &UniformRowSchema, x: usize, bit: usize, i: usize) -> ColRef {
    debug_assert!(x < 5 && bit < 64 && i < 3);
    ColRef(schema.helper_bit(3 * (64 * x + bit) + i))
}
fn theta_parity_c_col(schema: &UniformRowSchema, x: usize, bit: usize) -> ColRef {
    debug_assert!(x < 5 && bit < 64);
    ColRef(schema.helper_bit(960 + 64 * x + bit))
}
fn theta_diffuse_d_col(schema: &UniformRowSchema, x: usize, bit: usize) -> ColRef {
    debug_assert!(x < 5 && bit < 64);
    ColRef(schema.helper_bit(1280 + 64 * x + bit))
}

/// Emit row-uniform constraints for the θ sub-step.  All gated by
/// `SelectorIndex::Theta`.  Total: 1 600 booleanity + 3 200 XOR
/// = 4 800 constraints (matches the cell-list count).
pub fn theta_row_uniform_constraints(
    schema: &UniformRowSchema,
) -> Vec<RowUniformConstraint> {
    let mut out: Vec<RowUniformConstraint> = Vec::with_capacity(4800);

    // Booleanity on all θ-helper cells.
    for x in 0..5 {
        for bit in 0..64 {
            for i in 0..3 {
                out.push(RowUniformConstraint {
                    selector: SelectorIndex::Theta,
                    op: RowUniformOp::Boolean { b: theta_chain_col(schema, x, bit, i) },
                });
            }
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Boolean { b: theta_parity_c_col(schema, x, bit) },
            });
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Boolean { b: theta_diffuse_d_col(schema, x, bit) },
            });
        }
    }

    // XOR-chain: C[x][bit] = ⊕_{y∈[0..5)} state_in[5y+x][bit]
    for x in 0..5 {
        for bit in 0..64 {
            // chain0 = state_in[x][bit] ⊕ state_in[5+x][bit]
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Xor {
                    c: theta_chain_col(schema, x, bit, 0),
                    a: ColRef(schema.state_in_bit(x, bit)),
                    b: ColRef(schema.state_in_bit(5 + x, bit)),
                },
            });
            // chain1 = chain0 ⊕ state_in[10+x][bit]
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Xor {
                    c: theta_chain_col(schema, x, bit, 1),
                    a: theta_chain_col(schema, x, bit, 0),
                    b: ColRef(schema.state_in_bit(10 + x, bit)),
                },
            });
            // chain2 = chain1 ⊕ state_in[15+x][bit]
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Xor {
                    c: theta_chain_col(schema, x, bit, 2),
                    a: theta_chain_col(schema, x, bit, 1),
                    b: ColRef(schema.state_in_bit(15 + x, bit)),
                },
            });
            // C[x][bit] = chain2 ⊕ state_in[20+x][bit]
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Xor {
                    c: theta_parity_c_col(schema, x, bit),
                    a: theta_chain_col(schema, x, bit, 2),
                    b: ColRef(schema.state_in_bit(20 + x, bit)),
                },
            });
        }
    }

    // D[x][bit] = C[(x-1) mod 5][bit] ⊕ C[(x+1) mod 5][(bit-1) mod 64]
    for x in 0..5 {
        for bit in 0..64 {
            let prev_x = (x + 4) % 5;
            let next_x = (x + 1) % 5;
            let rot_src_bit = (bit + 63) % 64;
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Theta,
                op: RowUniformOp::Xor {
                    c: theta_diffuse_d_col(schema, x, bit),
                    a: theta_parity_c_col(schema, prev_x, bit),
                    b: theta_parity_c_col(schema, next_x, rot_src_bit),
                },
            });
        }
    }

    // state_out[5y+x][bit] = state_in[5y+x][bit] ⊕ D[x][bit]
    for y in 0..5 {
        for x in 0..5 {
            for bit in 0..64 {
                out.push(RowUniformConstraint {
                    selector: SelectorIndex::Theta,
                    op: RowUniformOp::Xor {
                        c: ColRef(schema.state_out_bit(5 * y + x, bit)),
                        a: ColRef(schema.state_in_bit(5 * y + x, bit)),
                        b: theta_diffuse_d_col(schema, x, bit),
                    },
                });
            }
        }
    }

    out
}

// ─── Row-uniform ρπ constraints ─────────────────────────────────────
//
// ρ rotates each lane; π permutes lane positions.  Fused into a single
// bit-position re-indexing: no helpers, no arithmetic — only Copy
// constraints from state_in (at rotated bit) to state_out (at permuted
// lane).  All gated by `SelectorIndex::RhoPi`.

/// Emit row-uniform constraints for the ρπ sub-step.  Total: 1 600
/// Copy constraints, one per (lane, bit) of the output state.  No
/// helper-cell booleanity needed (ρπ has no helpers); state_in/
/// state_out booleanity is enforced globally on every row.
pub fn rho_pi_row_uniform_constraints(
    schema: &UniformRowSchema,
) -> Vec<RowUniformConstraint> {
    use crate::sha3_absorb_air::RHO_OFFSETS;

    let mut out = Vec::with_capacity(1600);

    // output[5·((2x+3y) mod 5) + y][bit] = input[5y + x][(bit - off) mod 64]
    for x in 0..5 {
        for y in 0..5 {
            let src_lane = 5 * y + x;
            let dst_lane = 5 * ((2 * x + 3 * y) % 5) + y;
            let off = RHO_OFFSETS[src_lane] as usize;
            for bit in 0..64 {
                let src_bit = (bit + 64 - off) % 64;
                out.push(RowUniformConstraint {
                    selector: SelectorIndex::RhoPi,
                    op: RowUniformOp::Copy {
                        c: ColRef(schema.state_out_bit(dst_lane, bit)),
                        a: ColRef(schema.state_in_bit(src_lane, src_bit)),
                    },
                });
            }
        }
    }

    out
}

// ─── Row-uniform χ constraints ──────────────────────────────────────
//
// χ uses the SECOND half of the helpers range to avoid collision with
// θ's helper allocation:
//   helpers[1600..3200]   χ helpers
//   layout:  [1600 + 0..1600] = not_b1 helpers (one per output bit)
//            wait — we need 1600 not_b1 + 1600 and_part = 3200 cells,
//            but only 1600 free helper columns remain.
//
// CHANGE: χ helpers OVERLAP with θ helpers.  Both sub-steps share the
// 3200-cell helpers range — θ writes to it on θ rows, χ writes on χ
// rows, and the selector ensures only one sub-step's constraints fire
// at any given row.  This is the row-uniform space-optimization: the
// total helper budget is `max(per_sub_step)` = 3 200 (driven by χ),
// not `sum(per_sub_step)`.

fn chi_not_b1_col(schema: &UniformRowSchema, lane: usize, bit: usize) -> ColRef {
    debug_assert!(lane < 25 && bit < 64);
    ColRef(schema.helper_bit(64 * lane + bit))   // helpers[0..1600]
}
fn chi_and_part_col(schema: &UniformRowSchema, lane: usize, bit: usize) -> ColRef {
    debug_assert!(lane < 25 && bit < 64);
    ColRef(schema.helper_bit(1600 + 64 * lane + bit))   // helpers[1600..3200]
}

/// Emit row-uniform constraints for the χ sub-step.  Per (lane, bit):
/// - Not: `not_b1 = NOT state_in[lane_+1][bit]`
/// - And: `and_part = not_b1 AND state_in[lane_+2][bit]`
/// - Xor: `state_out[lane][bit] = state_in[lane][bit] XOR and_part`
/// Plus booleanity on the two helper cells per (lane, bit).
/// Total: 3 200 booleanity + 1 600 Not + 1 600 And + 1 600 Xor = 8 000.
pub fn chi_row_uniform_constraints(
    schema: &UniformRowSchema,
) -> Vec<RowUniformConstraint> {
    let mut out: Vec<RowUniformConstraint> = Vec::with_capacity(8000);

    // Booleanity on χ helpers.
    for lane in 0..25 {
        for bit in 0..64 {
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Chi,
                op: RowUniformOp::Boolean { b: chi_not_b1_col(schema, lane, bit) },
            });
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Chi,
                op: RowUniformOp::Boolean { b: chi_and_part_col(schema, lane, bit) },
            });
        }
    }

    // Operations per (lane, bit).
    for y in 0..5 {
        for x in 0..5 {
            let i0 = 5 * y + x;
            let i1 = 5 * y + (x + 1) % 5;
            let i2 = 5 * y + (x + 2) % 5;
            for bit in 0..64 {
                out.push(RowUniformConstraint {
                    selector: SelectorIndex::Chi,
                    op: RowUniformOp::Not {
                        c: chi_not_b1_col(schema, i0, bit),
                        a: ColRef(schema.state_in_bit(i1, bit)),
                    },
                });
                out.push(RowUniformConstraint {
                    selector: SelectorIndex::Chi,
                    op: RowUniformOp::And {
                        c: chi_and_part_col(schema, i0, bit),
                        a: chi_not_b1_col(schema, i0, bit),
                        b: ColRef(schema.state_in_bit(i2, bit)),
                    },
                });
                out.push(RowUniformConstraint {
                    selector: SelectorIndex::Chi,
                    op: RowUniformOp::Xor {
                        c: ColRef(schema.state_out_bit(i0, bit)),
                        a: ColRef(schema.state_in_bit(i0, bit)),
                        b: chi_and_part_col(schema, i0, bit),
                    },
                });
            }
        }
    }

    out
}

// ─── Row-uniform ι constraints ──────────────────────────────────────
//
// ι: XOR round constant into lane (0,0), pass through lanes 1..25.
// The round constant is provided publicly via the `rc_bits` columns
// (the verifier knows ROUND_CONSTANTS[round_at_row(r)][bit] for each
// ι row, so rc_bits column values are computed verifier-side and
// pinned by boundary constraints — not part of this constraint set).
//
// We use Xor (not XorConst) here because the constant is in a column,
// not baked into the polynomial.

/// Emit row-uniform constraints for the ι sub-step.  Per bit ∈ [0..64):
/// - Xor: `state_out[0][bit] = state_in[0][bit] XOR rc_bits[bit]`
/// Per (lane, bit) for lane ∈ [1..25):
/// - Copy: `state_out[lane][bit] = state_in[lane][bit]`
/// Total: 64 Xor + 24·64 Copy = 1 600 constraints.  No helper booleanity
/// (ι has no helpers); rc_bits booleanity handled by the global booleanity
/// generator since rc cells are publicly bound elsewhere.
pub fn iota_row_uniform_constraints(
    schema: &UniformRowSchema,
) -> Vec<RowUniformConstraint> {
    let mut out = Vec::with_capacity(1600);

    // Lane (0, 0): XOR with round-constant bit
    for bit in 0..64 {
        out.push(RowUniformConstraint {
            selector: SelectorIndex::Iota,
            op: RowUniformOp::Xor {
                c: ColRef(schema.state_out_bit(0, bit)),
                a: ColRef(schema.state_in_bit(0, bit)),
                b: ColRef(schema.rc_bit(bit)),
            },
        });
    }
    // Lanes 1..25: pass-through (Copy)
    for lane in 1..25 {
        for bit in 0..64 {
            out.push(RowUniformConstraint {
                selector: SelectorIndex::Iota,
                op: RowUniformOp::Copy {
                    c: ColRef(schema.state_out_bit(lane, bit)),
                    a: ColRef(schema.state_in_bit(lane, bit)),
                },
            });
        }
    }

    out
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

    // ─── Row-uniform constraint generator tests ─────────────────────

    #[test]
    fn row_uniform_op_degrees() {
        let c = ColRef(0);
        assert_eq!(RowUniformOp::Xor { c, a: c, b: c }.degree(), 2);
        assert_eq!(RowUniformOp::And { c, a: c, b: c }.degree(), 2);
        assert_eq!(RowUniformOp::Not { c, a: c }.degree(), 1);
        assert_eq!(RowUniformOp::Copy { c, a: c }.degree(), 1);
        assert_eq!(RowUniformOp::XorConst { c, a: c, k: 0 }.degree(), 1);
        assert_eq!(RowUniformOp::Boolean { b: c }.degree(), 2);
        assert_eq!(RowUniformOp::NextRowCopy { dst: c, src: c }.degree(), 1);
    }

    #[test]
    fn row_uniform_constraint_total_degree() {
        // After selector multiplication, degree += 1.
        let c = ColRef(0);
        let xor = RowUniformConstraint {
            selector: SelectorIndex::Theta,
            op: RowUniformOp::Xor { c, a: c, b: c },
        };
        assert_eq!(xor.total_degree(), 3);  // selector × XOR = 1 + 2

        let bool_op = RowUniformConstraint {
            selector: SelectorIndex::Theta,
            op: RowUniformOp::Boolean { b: c },
        };
        assert_eq!(bool_op.total_degree(), 3);  // selector × Boolean = 1 + 2
    }

    #[test]
    fn theta_row_uniform_constraint_count() {
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = theta_row_uniform_constraints(&schema);
        // Same shape as cell-list θ: 4 800 booleanity + 3 200 XOR.
        // But here all wear the Theta selector.
        let n_bool = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Boolean { .. })).count();
        let n_xor  = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Xor { .. })).count();
        // Helper-only booleanity (state_in/state_out booleanity is
        // shared across all sub-steps and lives in a separate
        // generator).
        assert_eq!(n_bool, 5 * 64 * 5);  // 5 helper bits per (x, bit) × 5×64 (x,bit) pairs
                                          //         = (3 chain + 1 C + 1 D) × 5 × 64 = 1 600
        assert_eq!(n_bool, 1600);
        assert_eq!(n_xor, 3200);   // 4 chain + 1 D + 25×64/5 = 320×4 + 320 + 1600 = 3 200
        assert_eq!(cs.len(), 4800);

        // All gated by Theta.
        for c in &cs {
            assert_eq!(c.selector, SelectorIndex::Theta);
        }
    }

    #[test]
    fn theta_row_uniform_helper_cols_within_helper_range() {
        // All theta helper col references must land inside the
        // helpers range (paper-grade column allocation).
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = theta_row_uniform_constraints(&schema);

        for c in &cs {
            match c.op {
                RowUniformOp::Boolean { b: ColRef(c) } => {
                    if schema.state_in.contains(&c) { continue; } // state cells boolean elsewhere
                    if schema.state_out.contains(&c) { continue; }
                    assert!(schema.helpers.contains(&c),
                        "θ booleanity col {c} outside helpers range");
                }
                RowUniformOp::Xor { c, a, b } => {
                    for col in [c.0, a.0, b.0] {
                        assert!(
                            schema.state_in.contains(&col)
                                || schema.state_out.contains(&col)
                                || schema.helpers.contains(&col),
                            "θ XOR col {col} outside state/helpers ranges"
                        );
                    }
                }
                _ => {}
            }
        }
    }

    #[test]
    fn theta_row_uniform_writes_state_out_only_at_end() {
        // The last 1 600 XOR constraints are the state_out = state_in ⊕ D updates.
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = theta_row_uniform_constraints(&schema);

        let state_update_count = cs.iter().filter(|c| match c.op {
            RowUniformOp::Xor { c, .. } => schema.state_out.contains(&c.0),
            _ => false,
        }).count();
        assert_eq!(state_update_count, 25 * 64,
            "θ should produce exactly 25×64 state_out updates");

        let chain_xor_count = cs.iter().filter(|c| match c.op {
            RowUniformOp::Xor { c, .. } => schema.helpers.contains(&c.0),
            _ => false,
        }).count();
        // 4 chain steps × 5×64 (x,bit) pairs + 1 D update per (x, bit)
        // = 4 × 320 + 320 = 1600
        assert_eq!(chain_xor_count, 1600);
    }

    #[test]
    fn theta_row_uniform_no_arithmetic_outside_xor_or_boolean() {
        // θ uses only Boolean + XOR — no AND, NOT, Copy, XorConst,
        // NextRowCopy.  Pin this constraint-zoo invariant.
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        for c in theta_row_uniform_constraints(&schema) {
            match c.op {
                RowUniformOp::Xor { .. } | RowUniformOp::Boolean { .. } => {},
                other => panic!("θ should not emit {other:?}"),
            }
        }
    }

    // ─── ρπ row-uniform tests ───────────────────────────────────────

    #[test]
    fn rho_pi_row_uniform_count_and_kind() {
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = rho_pi_row_uniform_constraints(&schema);
        // 1600 Copy constraints, no helpers, no booleanity here
        // (global booleanity covers state cells).
        assert_eq!(cs.len(), 1600);
        for c in &cs {
            assert_eq!(c.selector, SelectorIndex::RhoPi);
            assert!(matches!(c.op, RowUniformOp::Copy { .. }),
                "ρπ should emit only Copy; got {:?}", c.op);
        }
    }

    #[test]
    fn rho_pi_row_uniform_writes_all_state_out_bits() {
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = rho_pi_row_uniform_constraints(&schema);

        // The set of destination columns should be EXACTLY the
        // state_out bit columns.
        let mut dst_cols: Vec<usize> = cs.iter().filter_map(|c| match c.op {
            RowUniformOp::Copy { c, .. } => Some(c.0),
            _ => None,
        }).collect();
        dst_cols.sort();
        dst_cols.dedup();
        assert_eq!(dst_cols.len(), 1600);
        for col in &dst_cols {
            assert!(schema.state_out.contains(col));
        }
    }

    // ─── χ row-uniform tests ────────────────────────────────────────

    #[test]
    fn chi_row_uniform_count_and_kinds() {
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = chi_row_uniform_constraints(&schema);

        let n_bool = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Boolean { .. })).count();
        let n_not  = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Not     { .. })).count();
        let n_and  = cs.iter().filter(|c| matches!(c.op, RowUniformOp::And     { .. })).count();
        let n_xor  = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Xor     { .. })).count();

        assert_eq!(n_bool, 3200);  // 2 helper cells per (lane, bit) × 25×64
        assert_eq!(n_not,  1600);
        assert_eq!(n_and,  1600);
        assert_eq!(n_xor,  1600);
        assert_eq!(cs.len(), 8000);

        for c in &cs {
            assert_eq!(c.selector, SelectorIndex::Chi);
        }
    }

    #[test]
    fn chi_helpers_dont_conflict_with_theta() {
        // θ uses helpers[0..1600]; χ uses helpers[0..3200].  At any
        // given row, the active selector ensures only one sub-step's
        // constraints fire, so the overlap is safe.  This test pins
        // the documented overlap.
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let theta_cols: std::collections::HashSet<usize> = theta_row_uniform_constraints(&schema)
            .iter().filter_map(|c| match c.op {
                RowUniformOp::Boolean { b: ColRef(c) } if schema.helpers.contains(&c) => Some(c),
                _ => None,
            }).collect();
        let chi_cols: std::collections::HashSet<usize> = chi_row_uniform_constraints(&schema)
            .iter().filter_map(|c| match c.op {
                RowUniformOp::Boolean { b: ColRef(c) } if schema.helpers.contains(&c) => Some(c),
                _ => None,
            }).collect();
        // The helper columns overlap; this is intentional space-sharing.
        assert!(!theta_cols.is_disjoint(&chi_cols),
            "θ and χ helper col sets should overlap (space-sharing)");
        // But the active-selector gating ensures only the right
        // constraint set fires at any given row.
    }

    // ─── ι row-uniform tests ────────────────────────────────────────

    #[test]
    fn iota_row_uniform_count_and_kinds() {
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = iota_row_uniform_constraints(&schema);

        let n_xor  = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Xor  { .. })).count();
        let n_copy = cs.iter().filter(|c| matches!(c.op, RowUniformOp::Copy { .. })).count();

        assert_eq!(n_xor, 64);          // lane (0,0) gets the round constant
        assert_eq!(n_copy, 24 * 64);    // pass-through for lanes 1..25
        assert_eq!(cs.len(), 1600);

        for c in &cs {
            assert_eq!(c.selector, SelectorIndex::Iota);
        }
    }

    #[test]
    fn iota_lane_zero_uses_rc_bits() {
        // Verify ι's lane-(0,0) XORs source the second operand from
        // the rc_bits column range.
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let cs = iota_row_uniform_constraints(&schema);
        let rc_xors: Vec<_> = cs.iter().filter_map(|c| match c.op {
            RowUniformOp::Xor { b: ColRef(col), .. } if schema.rc_bits.contains(&col) => Some(col),
            _ => None,
        }).collect();
        assert_eq!(rc_xors.len(), 64,
            "exactly 64 ι XORs should reference rc_bits cells");
    }

    // ─── Combined: 4-sub-step row-uniform constraint count ──────────

    #[test]
    fn total_row_uniform_constraints_for_one_round() {
        // Total per-round row-uniform constraints (excluding cross-row
        // threading and global booleanity which are separate generators):
        // θ:  4 800
        // ρπ: 1 600
        // χ:  8 000
        // ι:  1 600
        //     ------
        //     16 000 total
        let schema = UniformRowSchema::new(Sha3Variant::Sha3_256);
        let n_theta  = theta_row_uniform_constraints(&schema).len();
        let n_rho_pi = rho_pi_row_uniform_constraints(&schema).len();
        let n_chi    = chi_row_uniform_constraints(&schema).len();
        let n_iota   = iota_row_uniform_constraints(&schema).len();
        assert_eq!(n_theta + n_rho_pi + n_chi + n_iota, 16_000);
    }
}
