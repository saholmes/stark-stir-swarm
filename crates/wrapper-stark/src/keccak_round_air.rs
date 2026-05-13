//! Keccak round AIR — per-sub-step constraint sets and trace synthesisers.
//!
//! This module bridges the bit-level Keccak reference (the oracle in
//! [`crate::sha3_absorb_air`]) to the polynomial constraint primitives
//! ([`crate::bit_constraint::BitOp`]) by defining, for each Keccak
//! sub-step, the column layout + constraint set + trace synthesiser.
//!
//! Pattern (one per sub-step):
//!
//! 1. `<step>Layout` — names every cell position used by the step
//! 2. `<step>_constraints(layout) -> Vec<BitOp>` — emits all constraints
//! 3. `synthesize_<step>(input, layout) -> trace cells` — produces a
//!    cell assignment that satisfies the constraints
//! 4. Test that the bit-level reference's output equals the synthesized
//!    cells AND that all constraints evaluate to zero on the synthesized
//!    trace.
//!
//! # Current scope
//!
//! Only the **θ (theta) step** is implemented in this commit.  Follow-up
//! commits add ρ+π, χ, ι, then compose into a full round and a full
//! 24-round permutation as the AIR builds out.
//!
//! # θ structure (FIPS 202 §3.2.1)
//!
//! For each column x ∈ [0..5):
//!   `C[x][bit] = ⊕_{y∈[0..5)} A[5y + x][bit]`
//!
//! For each x ∈ [0..5):
//!   `D[x][bit] = C[(x-1) mod 5][bit] ⊕ C[(x+1) mod 5][(bit-1) mod 64]`
//!
//! For each (x, y, bit):
//!   `A_out[5y + x][bit] = A_in[5y + x][bit] ⊕ D[x][bit]`
//!
//! AIR encoding choices:
//! - 5-input XOR-chains for `C[x][bit]` ⇒ 4 binary XORs + 3 intermediate
//!   boolean cells per (x, bit), 3 × 5 × 64 = 960 helper cells total
//! - `D[x][bit]` is one binary XOR per (x, bit): 5 × 64 = 320 cells
//! - `A_out` is one binary XOR per (x, y, bit): 25 × 64 = 1 600 cells

use crate::bit_constraint::{BitOp, CellRef, TraceAccess};
use crate::sha3_absorb_air::{BitState, LaneBits};

/// Column layout for the θ sub-step in a single row of the AIR.
///
/// All cell counts assume the entire θ step packs into ONE wrapper-AIR
/// row.  The trace synthesiser fills cells in this row; the constraint
/// set references only cells within this row (no cross-row constraints
/// in θ — those are reserved for the trace's outer LDE folding, not
/// for sub-step transitions).
///
/// Cell groups by column range:
/// - input state: 25 lanes × 64 bits = 1 600 bit cells
/// - column-parity helpers (XOR-chain intermediates): 5 × 64 × 3 = 960
/// - column parities `C[x][bit]`: 5 × 64 = 320
/// - diffuse vector `D[x][bit]`: 5 × 64 = 320
/// - output state: 1 600
///
/// Total θ row width: 1 600 + 960 + 320 + 320 + 1 600 = 4 800 cells.
#[derive(Clone, Debug)]
pub struct ThetaLayout {
    pub row: usize,
    pub input_state_start:        usize,
    pub parity_chain_start:       usize,  // 960 cells = 5 cols × 64 bits × 3 intermediates
    pub parity_c_start:           usize,  // 320 cells = 5 × 64
    pub diffuse_d_start:          usize,  // 320 cells = 5 × 64
    pub output_state_start:       usize,
    /// Total width covered by this layout (suffix of the row).
    pub width: usize,
}

impl ThetaLayout {
    /// Build a θ layout starting at `col_start` of `row`.
    pub fn new(row: usize, col_start: usize) -> Self {
        let input_state_start  = col_start;
        let parity_chain_start = input_state_start  + 1600;
        let parity_c_start     = parity_chain_start + 960;
        let diffuse_d_start    = parity_c_start     + 320;
        let output_state_start = diffuse_d_start    + 320;
        let end                = output_state_start + 1600;
        Self {
            row,
            input_state_start, parity_chain_start, parity_c_start,
            diffuse_d_start, output_state_start,
            width: end - col_start,
        }
    }

    /// Input state bit cell for lane (5y+x), bit `b`.
    pub fn input_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.input_state_start + 64 * lane_idx + bit)
    }

    /// XOR-chain intermediate `i ∈ [0..3)` for column `x`, bit `b`.
    /// Chain is: `tmp0 = a0⊕a1`, `tmp1 = tmp0⊕a2`, `tmp2 = tmp1⊕a3`,
    /// final `C[x][b] = tmp2⊕a4`.
    pub fn parity_chain_bit(&self, x: usize, bit: usize, i: usize) -> CellRef {
        debug_assert!(x < 5 && bit < 64 && i < 3);
        CellRef::new(self.row, self.parity_chain_start + 3 * (64 * x + bit) + i)
    }

    /// Column parity `C[x][bit]`.
    pub fn parity_c(&self, x: usize, bit: usize) -> CellRef {
        debug_assert!(x < 5 && bit < 64);
        CellRef::new(self.row, self.parity_c_start + 64 * x + bit)
    }

    /// Diffuse vector `D[x][bit]`.
    pub fn diffuse_d(&self, x: usize, bit: usize) -> CellRef {
        debug_assert!(x < 5 && bit < 64);
        CellRef::new(self.row, self.diffuse_d_start + 64 * x + bit)
    }

    /// Output state bit cell for lane (5y+x), bit `b`.
    pub fn output_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.output_state_start + 64 * lane_idx + bit)
    }
}

/// Emit the full set of polynomial constraints for one θ step.  Per-row
/// constraint count is exactly:
/// - Booleanity on input bits:                       1 600
/// - Booleanity on parity-chain intermediates:         960
/// - Booleanity on C[x][bit] cells:                    320
/// - Booleanity on D[x][bit] cells:                    320
/// - Booleanity on output bits:                      1 600
/// - XOR for parity-chain step 0 (a0 ⊕ a1):           320
/// - XOR for parity-chain step 1 (chain0 ⊕ a2):        320
/// - XOR for parity-chain step 2 (chain1 ⊕ a3):        320
/// - XOR for C[x][bit] = chain2 ⊕ a4:                  320
/// - XOR for D[x][bit] = C[x-1] ⊕ rot1(C[x+1]):        320
/// - XOR for output = input ⊕ D:                    1 600
/// Total: 4 800 booleanity + 3 200 XOR = 8 000 constraints.
pub fn theta_constraints(layout: &ThetaLayout) -> Vec<BitOp> {
    let mut out: Vec<BitOp> = Vec::with_capacity(8000);

    // Booleanity on every cell that participates.
    for lane in 0..25 {
        for bit in 0..64 {
            out.push(BitOp::Boolean { b: layout.input_bit(lane, bit) });
            out.push(BitOp::Boolean { b: layout.output_bit(lane, bit) });
        }
    }
    for x in 0..5 {
        for bit in 0..64 {
            for i in 0..3 {
                out.push(BitOp::Boolean { b: layout.parity_chain_bit(x, bit, i) });
            }
            out.push(BitOp::Boolean { b: layout.parity_c(x, bit) });
            out.push(BitOp::Boolean { b: layout.diffuse_d(x, bit) });
        }
    }

    // XOR-chain: C[x][bit] = ⊕_{y∈[0..5)} input[5y+x][bit]
    for x in 0..5 {
        for bit in 0..64 {
            // chain0 = input[x][bit] ⊕ input[5+x][bit]
            out.push(BitOp::Xor {
                c: layout.parity_chain_bit(x, bit, 0),
                a: layout.input_bit(x, bit),
                b: layout.input_bit(5 + x, bit),
            });
            // chain1 = chain0 ⊕ input[10+x][bit]
            out.push(BitOp::Xor {
                c: layout.parity_chain_bit(x, bit, 1),
                a: layout.parity_chain_bit(x, bit, 0),
                b: layout.input_bit(10 + x, bit),
            });
            // chain2 = chain1 ⊕ input[15+x][bit]
            out.push(BitOp::Xor {
                c: layout.parity_chain_bit(x, bit, 2),
                a: layout.parity_chain_bit(x, bit, 1),
                b: layout.input_bit(15 + x, bit),
            });
            // C[x][bit] = chain2 ⊕ input[20+x][bit]
            out.push(BitOp::Xor {
                c: layout.parity_c(x, bit),
                a: layout.parity_chain_bit(x, bit, 2),
                b: layout.input_bit(20 + x, bit),
            });
        }
    }

    // D[x][bit] = C[(x-1) mod 5][bit] ⊕ C[(x+1) mod 5][(bit-1) mod 64]
    for x in 0..5 {
        for bit in 0..64 {
            let prev_x = (x + 4) % 5;
            let next_x = (x + 1) % 5;
            let rot_src_bit = (bit + 63) % 64;
            out.push(BitOp::Xor {
                c: layout.diffuse_d(x, bit),
                a: layout.parity_c(prev_x, bit),
                b: layout.parity_c(next_x, rot_src_bit),
            });
        }
    }

    // output[5y+x][bit] = input[5y+x][bit] ⊕ D[x][bit]
    for y in 0..5 {
        for x in 0..5 {
            for bit in 0..64 {
                out.push(BitOp::Xor {
                    c: layout.output_bit(5 * y + x, bit),
                    a: layout.input_bit(5 * y + x, bit),
                    b: layout.diffuse_d(x, bit),
                });
            }
        }
    }

    out
}

/// Trace-fill record for one θ step: the actual cell values that
/// satisfy [`theta_constraints`].  Used by the trace synthesiser to
/// emit a complete row.
#[derive(Clone, Debug)]
pub struct ThetaCells {
    pub input_state: BitState,
    pub parity_chain: [[[u8; 3]; 64]; 5],
    pub parity_c:    [LaneBits; 5],
    pub diffuse_d:   [LaneBits; 5],
    pub output_state: BitState,
}

/// Synthesize the cell values for one θ step from a bit-level input
/// state.  The produced [`ThetaCells`] is guaranteed to satisfy
/// [`theta_constraints`] (proven by the round-trip test below).
pub fn synthesize_theta(input: &BitState) -> ThetaCells {
    let mut parity_chain = [[[0u8; 3]; 64]; 5];
    let mut parity_c     = [[0u8; 64]; 5];
    for x in 0..5 {
        for bit in 0..64 {
            let a0 = input[x][bit];
            let a1 = input[5 + x][bit];
            let a2 = input[10 + x][bit];
            let a3 = input[15 + x][bit];
            let a4 = input[20 + x][bit];
            let c0 = a0 ^ a1;
            let c1 = c0 ^ a2;
            let c2 = c1 ^ a3;
            let cf = c2 ^ a4;
            parity_chain[x][bit] = [c0, c1, c2];
            parity_c[x][bit] = cf;
        }
    }

    let mut diffuse_d = [[0u8; 64]; 5];
    for x in 0..5 {
        for bit in 0..64 {
            let prev_x = (x + 4) % 5;
            let next_x = (x + 1) % 5;
            let src_bit = (bit + 63) % 64;
            diffuse_d[x][bit] = parity_c[prev_x][bit] ^ parity_c[next_x][src_bit];
        }
    }

    let mut output_state: BitState = *input;
    for y in 0..5 {
        for x in 0..5 {
            for bit in 0..64 {
                output_state[5 * y + x][bit] ^= diffuse_d[x][bit];
            }
        }
    }

    ThetaCells {
        input_state: *input, parity_chain, parity_c,
        diffuse_d, output_state,
    }
}

/// Write θ cells into a mock trace at the given layout.  Used by tests
/// to validate that the synthesised cells satisfy [`theta_constraints`].
pub fn write_theta_cells(
    cells: &ThetaCells,
    layout: &ThetaLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    for lane in 0..25 {
        for bit in 0..64 {
            trace.set(layout.input_bit(lane, bit),  cells.input_state[lane][bit] as u64);
            trace.set(layout.output_bit(lane, bit), cells.output_state[lane][bit] as u64);
        }
    }
    for x in 0..5 {
        for bit in 0..64 {
            for i in 0..3 {
                trace.set(
                    layout.parity_chain_bit(x, bit, i),
                    cells.parity_chain[x][bit][i] as u64,
                );
            }
            trace.set(layout.parity_c(x, bit), cells.parity_c[x][bit] as u64);
            trace.set(layout.diffuse_d(x, bit), cells.diffuse_d[x][bit] as u64);
        }
    }
}

// ─── ρ + π fused sub-step ───────────────────────────────────────────
//
// ρ rotates each lane by [`RHO_OFFSETS`] and π permutes lane positions
// (x, y) → (y, 2x + 3y mod 5).  Both are bit-position re-indexings
// with no arithmetic — encoded as Copy constraints.

use crate::sha3_absorb_air::{PI_LANE_INDICES as _, RHO_OFFSETS};

/// Column layout for the ρπ sub-step.  Much cheaper than θ: no
/// intermediate helpers needed because ρπ is just bit-position
/// re-indexing.
///
/// Cell groups:
/// - input state (= θ output if composed): 1 600 bit cells
/// - output state (after ρπ):              1 600 bit cells
///
/// Total row width: 3 200 cells.
#[derive(Clone, Debug)]
pub struct RhoPiLayout {
    pub row: usize,
    pub input_state_start: usize,
    pub output_state_start: usize,
    pub width: usize,
}

impl RhoPiLayout {
    pub fn new(row: usize, col_start: usize) -> Self {
        let input_state_start  = col_start;
        let output_state_start = input_state_start + 1600;
        let end                = output_state_start + 1600;
        Self {
            row,
            input_state_start, output_state_start,
            width: end - col_start,
        }
    }

    pub fn input_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.input_state_start + 64 * lane_idx + bit)
    }

    pub fn output_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.output_state_start + 64 * lane_idx + bit)
    }
}

/// Emit constraints for one ρπ sub-step.  Total: 1 600 input booleanity
/// + 1 600 output booleanity + 1 600 Copy = 4 800 constraints.
///
/// Each Copy constraint is the polynomial identity
/// `output[dst][bit] − input[src][src_bit] = 0`, where:
/// - `src = 5y + x`
/// - `dst = 5 · ((2x + 3y) mod 5) + y`     (π permutation)
/// - `src_bit = (bit + 64 − RHO_OFFSETS[src]) mod 64`  (ρ rotation)
pub fn rho_pi_constraints(layout: &RhoPiLayout) -> Vec<BitOp> {
    let mut out: Vec<BitOp> = Vec::with_capacity(4800);

    for lane in 0..25 {
        for bit in 0..64 {
            out.push(BitOp::Boolean { b: layout.input_bit(lane, bit) });
            out.push(BitOp::Boolean { b: layout.output_bit(lane, bit) });
        }
    }

    for x in 0..5 {
        for y in 0..5 {
            let src = 5 * y + x;
            let dst = 5 * ((2 * x + 3 * y) % 5) + y;
            let off = RHO_OFFSETS[src] as usize;
            for bit in 0..64 {
                let src_bit = (bit + 64 - off) % 64;
                out.push(BitOp::Copy {
                    c: layout.output_bit(dst, bit),
                    a: layout.input_bit(src, src_bit),
                });
            }
        }
    }

    out
}

/// Synthesised cell values for one ρπ step.
#[derive(Clone, Debug)]
pub struct RhoPiCells {
    pub input_state: BitState,
    pub output_state: BitState,
}

/// Synthesize ρπ cells from a bit-level input state.  Output matches
/// the bit-level reference's ρπ behaviour exactly.
pub fn synthesize_rho_pi(input: &BitState) -> RhoPiCells {
    let mut output_state: BitState = [[0u8; 64]; 25];
    for x in 0..5 {
        for y in 0..5 {
            let src = 5 * y + x;
            let dst = 5 * ((2 * x + 3 * y) % 5) + y;
            let off = RHO_OFFSETS[src] as usize;
            for bit in 0..64 {
                let src_bit = (bit + 64 - off) % 64;
                output_state[dst][bit] = input[src][src_bit];
            }
        }
    }
    RhoPiCells { input_state: *input, output_state }
}

/// Write ρπ cells into a mock trace at the given layout.
pub fn write_rho_pi_cells(
    cells: &RhoPiCells,
    layout: &RhoPiLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    for lane in 0..25 {
        for bit in 0..64 {
            trace.set(layout.input_bit(lane, bit),  cells.input_state[lane][bit] as u64);
            trace.set(layout.output_bit(lane, bit), cells.output_state[lane][bit] as u64);
        }
    }
}

// ─── χ (chi) sub-step ────────────────────────────────────────────────
//
// The only non-linear step.  For each (x, y, bit):
//   A_out[5y+x][bit] = B[5y+x][bit] ⊕ ((¬B[5y+(x+1)%5][bit]) & B[5y+(x+2)%5][bit])
//
// Encoded as 3 BitOps per bit: NOT, AND, XOR — plus two intermediate
// cells (not_b1, and_part).

/// Column layout for the χ sub-step.
///
/// Cell groups:
/// - input state (= ρπ output if composed): 1 600 bit cells
/// - `not_b1` helpers (one per bit):        1 600 cells
/// - `and_part` helpers (one per bit):      1 600 cells
/// - output state:                          1 600 cells
///
/// Total row width: 6 400 cells.
#[derive(Clone, Debug)]
pub struct ChiLayout {
    pub row: usize,
    pub input_state_start:  usize,
    pub not_b1_start:       usize,
    pub and_part_start:     usize,
    pub output_state_start: usize,
    pub width: usize,
}

impl ChiLayout {
    pub fn new(row: usize, col_start: usize) -> Self {
        let input_state_start  = col_start;
        let not_b1_start       = input_state_start  + 1600;
        let and_part_start     = not_b1_start       + 1600;
        let output_state_start = and_part_start     + 1600;
        let end                = output_state_start + 1600;
        Self {
            row,
            input_state_start, not_b1_start,
            and_part_start, output_state_start,
            width: end - col_start,
        }
    }

    pub fn input_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.input_state_start + 64 * lane_idx + bit)
    }
    pub fn not_b1(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.not_b1_start + 64 * lane_idx + bit)
    }
    pub fn and_part(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.and_part_start + 64 * lane_idx + bit)
    }
    pub fn output_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.output_state_start + 64 * lane_idx + bit)
    }
}

/// Emit constraints for one χ sub-step.  Per bit: 1 NOT + 1 AND + 1 XOR
/// + 4 booleanity (input, not_b1, and_part, output) = 7 constraints.
/// Across 1 600 bits: 11 200 constraints.
pub fn chi_constraints(layout: &ChiLayout) -> Vec<BitOp> {
    let mut out: Vec<BitOp> = Vec::with_capacity(11200);

    // Booleanity on all participating cells.
    for lane in 0..25 {
        for bit in 0..64 {
            out.push(BitOp::Boolean { b: layout.input_bit(lane, bit) });
            out.push(BitOp::Boolean { b: layout.not_b1(lane, bit) });
            out.push(BitOp::Boolean { b: layout.and_part(lane, bit) });
            out.push(BitOp::Boolean { b: layout.output_bit(lane, bit) });
        }
    }

    // Operations per bit.
    for y in 0..5 {
        for x in 0..5 {
            let i0 = 5 * y + x;
            let i1 = 5 * y + (x + 1) % 5;
            let i2 = 5 * y + (x + 2) % 5;
            for bit in 0..64 {
                // not_b1 = NOT input[i1][bit]
                out.push(BitOp::Not {
                    c: layout.not_b1(i0, bit),
                    a: layout.input_bit(i1, bit),
                });
                // and_part = not_b1 AND input[i2][bit]
                out.push(BitOp::And {
                    c: layout.and_part(i0, bit),
                    a: layout.not_b1(i0, bit),
                    b: layout.input_bit(i2, bit),
                });
                // output[i0][bit] = input[i0][bit] XOR and_part
                out.push(BitOp::Xor {
                    c: layout.output_bit(i0, bit),
                    a: layout.input_bit(i0, bit),
                    b: layout.and_part(i0, bit),
                });
            }
        }
    }

    out
}

/// Synthesised cell values for one χ step.
#[derive(Clone, Debug)]
pub struct ChiCells {
    pub input_state:  BitState,
    pub not_b1:       BitState,
    pub and_part:     BitState,
    pub output_state: BitState,
}

pub fn synthesize_chi(input: &BitState) -> ChiCells {
    let mut not_b1   = [[0u8; 64]; 25];
    let mut and_part = [[0u8; 64]; 25];
    let mut output_state = [[0u8; 64]; 25];

    for y in 0..5 {
        for x in 0..5 {
            let i0 = 5 * y + x;
            let i1 = 5 * y + (x + 1) % 5;
            let i2 = 5 * y + (x + 2) % 5;
            for bit in 0..64 {
                not_b1[i0][bit]       = 1 - input[i1][bit];
                and_part[i0][bit]     = not_b1[i0][bit] & input[i2][bit];
                output_state[i0][bit] = input[i0][bit] ^ and_part[i0][bit];
            }
        }
    }

    ChiCells { input_state: *input, not_b1, and_part, output_state }
}

pub fn write_chi_cells(
    cells: &ChiCells,
    layout: &ChiLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    for lane in 0..25 {
        for bit in 0..64 {
            trace.set(layout.input_bit(lane, bit),  cells.input_state[lane][bit] as u64);
            trace.set(layout.not_b1(lane, bit),     cells.not_b1[lane][bit] as u64);
            trace.set(layout.and_part(lane, bit),   cells.and_part[lane][bit] as u64);
            trace.set(layout.output_bit(lane, bit), cells.output_state[lane][bit] as u64);
        }
    }
}

// ─── ι (iota) sub-step ───────────────────────────────────────────────
//
// XOR the per-round constant into lane (0, 0).  Smallest sub-step:
// 64 XorConst constraints (with public bit values from ROUND_CONSTANTS),
// 128 booleanity (input + output for lane 0,0).  Lanes 1..25 are
// pass-through — encoded as Copy constraints if we want a complete
// state-update record, otherwise they can be elided.  We keep them
// for layout uniformity.

/// Column layout for the ι sub-step.  Identical shape to ρπ: input
/// state, output state, no helpers.
#[derive(Clone, Debug)]
pub struct IotaLayout {
    pub row: usize,
    pub input_state_start: usize,
    pub output_state_start: usize,
    pub width: usize,
}

impl IotaLayout {
    pub fn new(row: usize, col_start: usize) -> Self {
        let input_state_start  = col_start;
        let output_state_start = input_state_start + 1600;
        let end                = output_state_start + 1600;
        Self {
            row, input_state_start, output_state_start,
            width: end - col_start,
        }
    }

    pub fn input_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.input_state_start + 64 * lane_idx + bit)
    }

    pub fn output_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.output_state_start + 64 * lane_idx + bit)
    }
}

/// Emit constraints for one ι sub-step at the given round index.  The
/// round constant `ROUND_CONSTANTS[round_idx]` is decomposed into 64
/// public bits; lane (0, 0) receives XorConst(k=that_bit) per position,
/// lanes 1..25 receive Copy (pass-through).  Plus booleanity on every
/// input + output cell (3 200 total).
pub fn iota_constraints(layout: &IotaLayout, round_idx: usize) -> Vec<BitOp> {
    use crate::sha3_absorb_air::{lane_to_bits, ROUND_CONSTANTS};
    assert!(round_idx < 24);
    let rc_bits = lane_to_bits(ROUND_CONSTANTS[round_idx]);

    // 3 200 booleanity + 64 XorConst + 24×64 Copy = 4 800 constraints
    let mut out: Vec<BitOp> = Vec::with_capacity(4800);

    for lane in 0..25 {
        for bit in 0..64 {
            out.push(BitOp::Boolean { b: layout.input_bit(lane, bit) });
            out.push(BitOp::Boolean { b: layout.output_bit(lane, bit) });
        }
    }

    // Lane (0, 0) — XOR with round constant bits
    for bit in 0..64 {
        out.push(BitOp::XorConst {
            c: layout.output_bit(0, bit),
            a: layout.input_bit(0, bit),
            k: rc_bits[bit],
        });
    }
    // Lanes 1..25 — pass-through
    for lane in 1..25 {
        for bit in 0..64 {
            out.push(BitOp::Copy {
                c: layout.output_bit(lane, bit),
                a: layout.input_bit(lane, bit),
            });
        }
    }

    out
}

#[derive(Clone, Debug)]
pub struct IotaCells {
    pub input_state: BitState,
    pub output_state: BitState,
}

pub fn synthesize_iota(input: &BitState, round_idx: usize) -> IotaCells {
    use crate::sha3_absorb_air::{lane_to_bits, ROUND_CONSTANTS};
    assert!(round_idx < 24);
    let rc_bits = lane_to_bits(ROUND_CONSTANTS[round_idx]);

    let mut output_state = *input;
    for bit in 0..64 {
        output_state[0][bit] ^= rc_bits[bit];
    }
    IotaCells { input_state: *input, output_state }
}

pub fn write_iota_cells(
    cells: &IotaCells,
    layout: &IotaLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    for lane in 0..25 {
        for bit in 0..64 {
            trace.set(layout.input_bit(lane, bit),  cells.input_state[lane][bit] as u64);
            trace.set(layout.output_bit(lane, bit), cells.output_state[lane][bit] as u64);
        }
    }
}

// ─── Full Keccak round (4 sub-step rows + cross-row state threading) ─
//
// Layout: rows = [row_offset .. row_offset+4), one row per sub-step.
//   row_offset + 0  →  θ
//   row_offset + 1  →  ρπ
//   row_offset + 2  →  χ
//   row_offset + 3  →  ι
//
// Cross-row state threading is enforced by Copy constraints between
// the output_state of sub-step N (row r) and the input_state of
// sub-step N+1 (row r+1).  These are the constraints a malicious
// prover would have to break to cheat the state evolution — they're
// the soundness backbone of the multi-row encoding.

/// Layout for one complete Keccak round.
#[derive(Clone, Debug)]
pub struct RoundLayout {
    pub round_idx: usize,
    pub row_offset: usize,
    pub theta:  ThetaLayout,
    pub rho_pi: RhoPiLayout,
    pub chi:    ChiLayout,
    pub iota:   IotaLayout,
}

impl RoundLayout {
    /// Place the round starting at `row_offset`.  All sub-step
    /// layouts start at column 0 of their respective row (the trace
    /// LDE will see different prefixes per row — unification to a
    /// fixed row width happens in the outer round-sequence layout).
    pub fn new(round_idx: usize, row_offset: usize) -> Self {
        assert!(round_idx < 24);
        Self {
            round_idx,
            row_offset,
            theta:  ThetaLayout::new(row_offset,     0),
            rho_pi: RhoPiLayout::new(row_offset + 1, 0),
            chi:    ChiLayout::new(row_offset + 2,   0),
            iota:   IotaLayout::new(row_offset + 3,  0),
        }
    }

    /// Number of trace rows this round occupies.
    pub fn rows(&self) -> usize { 4 }

    /// Maximum row width across the 4 sub-steps.  When this layout
    /// is embedded in the outer trace, every row must have at least
    /// this width allocated.
    pub fn max_row_width(&self) -> usize {
        [self.theta.width, self.rho_pi.width, self.chi.width, self.iota.width]
            .iter().copied().max().unwrap()
    }
}

/// Emit all constraints for one full round: 4 sub-step constraint
/// sets + 3 × 1 600 cross-row Copy constraints for state threading
/// between consecutive sub-steps.  Total per round: 28 800 + 4 800
/// = 33 600 constraints.
pub fn round_constraints(layout: &RoundLayout) -> Vec<BitOp> {
    let mut out: Vec<BitOp> = Vec::with_capacity(33600);
    out.extend(theta_constraints(&layout.theta));
    out.extend(rho_pi_constraints(&layout.rho_pi));
    out.extend(chi_constraints(&layout.chi));
    out.extend(iota_constraints(&layout.iota, layout.round_idx));

    // Cross-row state threading:
    //   θ.output_bit(lane, bit)  ≡  ρπ.input_bit(lane, bit)
    //   ρπ.output_bit(lane, bit) ≡  χ.input_bit(lane, bit)
    //   χ.output_bit(lane, bit)  ≡  ι.input_bit(lane, bit)
    for lane in 0..25 {
        for bit in 0..64 {
            out.push(BitOp::Copy {
                c: layout.rho_pi.input_bit(lane, bit),
                a: layout.theta.output_bit(lane, bit),
            });
            out.push(BitOp::Copy {
                c: layout.chi.input_bit(lane, bit),
                a: layout.rho_pi.output_bit(lane, bit),
            });
            out.push(BitOp::Copy {
                c: layout.iota.input_bit(lane, bit),
                a: layout.chi.output_bit(lane, bit),
            });
        }
    }

    out
}

/// All cell values for one complete round.
#[derive(Clone, Debug)]
pub struct RoundCells {
    pub theta:  ThetaCells,
    pub rho_pi: RhoPiCells,
    pub chi:    ChiCells,
    pub iota:   IotaCells,
}

impl RoundCells {
    /// Final state after this round (= ι output).
    pub fn output_state(&self) -> BitState {
        self.iota.output_state
    }
}

/// Synthesize cell values for one full Keccak round.  Chains the 4
/// sub-step synthesisers and produces a consistent cell set that
/// satisfies every constraint emitted by [`round_constraints`].
pub fn synthesize_round(input: &BitState, round_idx: usize) -> RoundCells {
    let theta  = synthesize_theta(input);
    let rho_pi = synthesize_rho_pi(&theta.output_state);
    let chi    = synthesize_chi(&rho_pi.output_state);
    let iota   = synthesize_iota(&chi.output_state, round_idx);
    RoundCells { theta, rho_pi, chi, iota }
}

/// Write all 4 sub-step row's cells into a mock trace.
pub fn write_round_cells(
    cells: &RoundCells,
    layout: &RoundLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    write_theta_cells(&cells.theta,   &layout.theta,  trace);
    write_rho_pi_cells(&cells.rho_pi, &layout.rho_pi, trace);
    write_chi_cells(&cells.chi,       &layout.chi,    trace);
    write_iota_cells(&cells.iota,     &layout.iota,   trace);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bit_constraint::MockTrace;
    use crate::sha3_absorb_air::{
        bit_state_from_lanes, KeccakState, ROUND_CONSTANTS,
    };

    fn make_input_state() -> BitState {
        // Non-trivial state — every lane has a distinct pattern, so
        // every θ XOR-chain is exercised with a non-uniform input.
        let mut s: KeccakState = [0; 25];
        for i in 0..25 {
            s[i] = (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
                 ^ ROUND_CONSTANTS[i % 24];
        }
        bit_state_from_lanes(&s)
    }

    /// Native θ-only step on a bit-level state (extracted from
    /// keccak_round_bit_level): used as the ground-truth oracle.
    fn theta_native(bs: &mut BitState) {
        let mut c = [[0u8; 64]; 5];
        for x in 0..5 {
            for bit in 0..64 {
                c[x][bit] = bs[x][bit] ^ bs[5 + x][bit] ^ bs[10 + x][bit]
                          ^ bs[15 + x][bit] ^ bs[20 + x][bit];
            }
        }
        let mut d = [[0u8; 64]; 5];
        for x in 0..5 {
            for bit in 0..64 {
                let prev_x = (x + 4) % 5;
                let next_x = (x + 1) % 5;
                let src_bit = (bit + 63) % 64;
                d[x][bit] = c[prev_x][bit] ^ c[next_x][src_bit];
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                for bit in 0..64 {
                    bs[5 * y + x][bit] ^= d[x][bit];
                }
            }
        }
    }

    #[test]
    fn theta_layout_widths_correct() {
        let layout = ThetaLayout::new(0, 0);
        // 1 600 input + 960 chain + 320 C + 320 D + 1 600 output = 4 800
        assert_eq!(layout.width, 4800);
    }

    #[test]
    fn theta_constraint_count_matches_design() {
        let layout = ThetaLayout::new(0, 0);
        let constraints = theta_constraints(&layout);
        // Per module doc:
        //  4 800 booleanity + 3 200 XOR = 8 000 constraints
        let n_bool: usize = constraints.iter()
            .filter(|c| matches!(c, BitOp::Boolean { .. })).count();
        let n_xor: usize = constraints.iter()
            .filter(|c| matches!(c, BitOp::Xor { .. })).count();
        assert_eq!(n_bool, 4800, "booleanity count");
        assert_eq!(n_xor, 3200, "XOR count");
        assert_eq!(constraints.len(), 8000);
    }

    #[test]
    fn synthesized_theta_matches_native() {
        let input = make_input_state();
        let synth = synthesize_theta(&input);

        let mut native = input;
        theta_native(&mut native);

        assert_eq!(synth.output_state, native,
            "synthesize_theta output differs from native θ");
    }

    #[test]
    fn synthesized_theta_satisfies_all_constraints() {
        let layout = ThetaLayout::new(0, 0);
        let constraints = theta_constraints(&layout);

        let input = make_input_state();
        let synth = synthesize_theta(&input);

        // Allocate a mock trace just wide enough for the θ layout.
        let mut trace = MockTrace::zeros(1, layout.width);
        write_theta_cells(&synth, &layout, &mut trace);

        // EVERY constraint must evaluate to zero on the synthesised trace.
        for (i, c) in constraints.iter().enumerate() {
            assert!(c.satisfied_by(&trace),
                "constraint #{i} = {c:?} not satisfied; residue = {}",
                c.eval(&trace));
        }
    }

    #[test]
    fn tampering_with_output_breaks_at_least_one_constraint() {
        // Soundness check: if we corrupt a single output bit, at least
        // one constraint must reject.  This pins that the constraint
        // set is non-vacuous (otherwise a malicious prover could
        // produce any output cells and the AIR would accept).
        let layout = ThetaLayout::new(0, 0);
        let constraints = theta_constraints(&layout);

        let input = make_input_state();
        let synth = synthesize_theta(&input);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_theta_cells(&synth, &layout, &mut trace);

        // Flip one output bit.
        let bad_cell = layout.output_bit(7, 13);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        let n_failing = constraints.iter()
            .filter(|c| !c.satisfied_by(&trace))
            .count();
        assert!(n_failing >= 1,
            "tampering with output bit didn't trip any constraint");
    }

    #[test]
    fn tampering_with_intermediate_chain_breaks_constraint() {
        // Same idea but on a non-boundary cell (parity-chain intermediate).
        let layout = ThetaLayout::new(0, 0);
        let constraints = theta_constraints(&layout);

        let input = make_input_state();
        let synth = synthesize_theta(&input);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_theta_cells(&synth, &layout, &mut trace);

        let bad_cell = layout.parity_chain_bit(2, 17, 1);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        assert!(constraints.iter().any(|c| !c.satisfied_by(&trace)));
    }

    #[test]
    fn theta_layout_starts_at_arbitrary_col() {
        // Layout should compose cleanly when placed at non-zero col_start
        // (will matter when θ is one of 5 sub-step regions in a real row).
        let layout = ThetaLayout::new(3, 100);
        assert_eq!(layout.input_state_start, 100);
        assert_eq!(layout.input_bit(0, 0), CellRef::new(3, 100));
        assert_eq!(layout.output_bit(24, 63),
                   CellRef::new(3, 100 + layout.width - 1));
    }

    // ─── ρπ sub-step tests ──────────────────────────────────────────

    /// Native ρπ-only step on a bit-level state (extracted from
    /// keccak_round_bit_level): used as the ground-truth oracle.
    fn rho_pi_native(bs: &BitState) -> BitState {
        let mut out = [[0u8; 64]; 25];
        for x in 0..5 {
            for y in 0..5 {
                let src = 5 * y + x;
                let dst = 5 * ((2 * x + 3 * y) % 5) + y;
                let off = RHO_OFFSETS[src] as usize;
                for bit in 0..64 {
                    let src_bit = (bit + 64 - off) % 64;
                    out[dst][bit] = bs[src][src_bit];
                }
            }
        }
        out
    }

    #[test]
    fn rho_pi_layout_widths_correct() {
        let layout = RhoPiLayout::new(0, 0);
        // 1 600 input + 1 600 output = 3 200
        assert_eq!(layout.width, 3200);
    }

    #[test]
    fn rho_pi_constraint_count_matches_design() {
        let layout = RhoPiLayout::new(0, 0);
        let constraints = rho_pi_constraints(&layout);
        let n_bool: usize = constraints.iter()
            .filter(|c| matches!(c, BitOp::Boolean { .. })).count();
        let n_copy: usize = constraints.iter()
            .filter(|c| matches!(c, BitOp::Copy { .. })).count();
        assert_eq!(n_bool, 3200, "booleanity count (input + output)");
        assert_eq!(n_copy, 1600, "Copy count (one per output bit)");
        assert_eq!(constraints.len(), 4800);
    }

    #[test]
    fn synthesized_rho_pi_matches_native() {
        let input = make_input_state();
        let synth = synthesize_rho_pi(&input);
        let native = rho_pi_native(&input);
        assert_eq!(synth.output_state, native);
    }

    #[test]
    fn synthesized_rho_pi_satisfies_all_constraints() {
        let layout = RhoPiLayout::new(0, 0);
        let constraints = rho_pi_constraints(&layout);
        let input = make_input_state();
        let synth = synthesize_rho_pi(&input);

        let mut trace = MockTrace::zeros(1, layout.width);
        write_rho_pi_cells(&synth, &layout, &mut trace);

        for (i, c) in constraints.iter().enumerate() {
            assert!(c.satisfied_by(&trace),
                "constraint #{i} = {c:?} not satisfied; residue = {}",
                c.eval(&trace));
        }
    }

    #[test]
    fn rho_pi_tampering_breaks_constraint() {
        let layout = RhoPiLayout::new(0, 0);
        let constraints = rho_pi_constraints(&layout);
        let input = make_input_state();
        let synth = synthesize_rho_pi(&input);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_rho_pi_cells(&synth, &layout, &mut trace);

        // Flip one output bit.
        let bad_cell = layout.output_bit(11, 23);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        let n_failing = constraints.iter()
            .filter(|c| !c.satisfied_by(&trace))
            .count();
        assert!(n_failing >= 1,
            "tampering with output bit didn't trip any ρπ constraint");
    }

    #[test]
    fn rho_pi_layout_starts_at_arbitrary_col() {
        let layout = RhoPiLayout::new(2, 50);
        assert_eq!(layout.input_state_start, 50);
        assert_eq!(layout.input_bit(0, 0), CellRef::new(2, 50));
        assert_eq!(layout.output_bit(24, 63),
                   CellRef::new(2, 50 + layout.width - 1));
    }

    #[test]
    fn rho_pi_no_xor_or_and_constraints() {
        // ρπ is pure bit-shuffling; no arithmetic operations.  Pin
        // that the constraint set contains only Boolean and Copy.
        let layout = RhoPiLayout::new(0, 0);
        for c in rho_pi_constraints(&layout) {
            assert!(matches!(c, BitOp::Boolean { .. } | BitOp::Copy { .. }),
                "ρπ should emit only Boolean + Copy; found {c:?}");
        }
    }

    // ─── χ sub-step tests ───────────────────────────────────────────

    fn chi_native(bs: &BitState) -> BitState {
        let mut out = [[0u8; 64]; 25];
        for y in 0..5 {
            let row = [
                bs[5*y    ], bs[5*y + 1], bs[5*y + 2], bs[5*y + 3], bs[5*y + 4],
            ];
            for x in 0..5 {
                for bit in 0..64 {
                    let not_b1   = 1u8 - row[(x + 1) % 5][bit];
                    let and_part = not_b1 & row[(x + 2) % 5][bit];
                    out[5*y + x][bit] = row[x][bit] ^ and_part;
                }
            }
        }
        out
    }

    #[test]
    fn chi_layout_widths_correct() {
        let layout = ChiLayout::new(0, 0);
        // 1600 input + 1600 not_b1 + 1600 and_part + 1600 output = 6 400
        assert_eq!(layout.width, 6400);
    }

    #[test]
    fn chi_constraint_count_matches_design() {
        let layout = ChiLayout::new(0, 0);
        let constraints = chi_constraints(&layout);
        let n_bool = constraints.iter().filter(|c| matches!(c, BitOp::Boolean { .. })).count();
        let n_not  = constraints.iter().filter(|c| matches!(c, BitOp::Not     { .. })).count();
        let n_and  = constraints.iter().filter(|c| matches!(c, BitOp::And     { .. })).count();
        let n_xor  = constraints.iter().filter(|c| matches!(c, BitOp::Xor     { .. })).count();
        // 4 × 1600 booleanity + 1600 each NOT/AND/XOR = 6 400 + 4 800 = 11 200
        assert_eq!(n_bool, 6400);
        assert_eq!(n_not,  1600);
        assert_eq!(n_and,  1600);
        assert_eq!(n_xor,  1600);
        assert_eq!(constraints.len(), 11200);
    }

    #[test]
    fn synthesized_chi_matches_native() {
        let input = make_input_state();
        let synth = synthesize_chi(&input);
        let native = chi_native(&input);
        assert_eq!(synth.output_state, native);
    }

    #[test]
    fn synthesized_chi_satisfies_all_constraints() {
        let layout = ChiLayout::new(0, 0);
        let constraints = chi_constraints(&layout);
        let input = make_input_state();
        let synth = synthesize_chi(&input);

        let mut trace = MockTrace::zeros(1, layout.width);
        write_chi_cells(&synth, &layout, &mut trace);

        for (i, c) in constraints.iter().enumerate() {
            assert!(c.satisfied_by(&trace),
                "χ constraint #{i} = {c:?} residue = {}", c.eval(&trace));
        }
    }

    #[test]
    fn chi_tampering_breaks_constraint() {
        let layout = ChiLayout::new(0, 0);
        let constraints = chi_constraints(&layout);
        let input = make_input_state();
        let synth = synthesize_chi(&input);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_chi_cells(&synth, &layout, &mut trace);

        // Flip an intermediate `and_part` cell (most subtle attack
        // surface — it's an internal helper, not a boundary).
        let bad_cell = layout.and_part(8, 31);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        assert!(constraints.iter().any(|c| !c.satisfied_by(&trace)));
    }

    #[test]
    fn chi_uses_all_three_arithmetic_ops() {
        let layout = ChiLayout::new(0, 0);
        let cs = chi_constraints(&layout);
        assert!(cs.iter().any(|c| matches!(c, BitOp::Not { .. })));
        assert!(cs.iter().any(|c| matches!(c, BitOp::And { .. })));
        assert!(cs.iter().any(|c| matches!(c, BitOp::Xor { .. })));
        // No Copy or XorConst — that's ρπ and ι respectively.
        assert!(!cs.iter().any(|c| matches!(c, BitOp::Copy     { .. })));
        assert!(!cs.iter().any(|c| matches!(c, BitOp::XorConst { .. })));
    }

    // ─── ι sub-step tests ───────────────────────────────────────────

    fn iota_native(bs: &BitState, round_idx: usize) -> BitState {
        use crate::sha3_absorb_air::{lane_to_bits, ROUND_CONSTANTS};
        let rc = lane_to_bits(ROUND_CONSTANTS[round_idx]);
        let mut out = *bs;
        for bit in 0..64 {
            out[0][bit] ^= rc[bit];
        }
        out
    }

    #[test]
    fn iota_layout_widths_correct() {
        let layout = IotaLayout::new(0, 0);
        assert_eq!(layout.width, 3200);
    }

    #[test]
    fn iota_constraint_count_matches_design() {
        let layout = IotaLayout::new(0, 0);
        let constraints = iota_constraints(&layout, 0);
        let n_bool      = constraints.iter().filter(|c| matches!(c, BitOp::Boolean  { .. })).count();
        let n_xor_const = constraints.iter().filter(|c| matches!(c, BitOp::XorConst { .. })).count();
        let n_copy      = constraints.iter().filter(|c| matches!(c, BitOp::Copy     { .. })).count();
        // 3 200 booleanity + 64 XorConst + 24×64 Copy = 4 800
        assert_eq!(n_bool, 3200);
        assert_eq!(n_xor_const, 64);
        assert_eq!(n_copy, 24 * 64);
        assert_eq!(constraints.len(), 4800);
    }

    #[test]
    fn synthesized_iota_matches_native_round0() {
        let input = make_input_state();
        let synth = synthesize_iota(&input, 0);
        let native = iota_native(&input, 0);
        assert_eq!(synth.output_state, native);
    }

    #[test]
    fn synthesized_iota_matches_native_all_rounds() {
        // Round constants change per round; the synthesiser must use
        // ROUND_CONSTANTS[round_idx] correctly for every round.
        let input = make_input_state();
        for round in 0..24 {
            let synth = synthesize_iota(&input, round);
            let native = iota_native(&input, round);
            assert_eq!(synth.output_state, native, "round {round}");
        }
    }

    #[test]
    fn synthesized_iota_satisfies_all_constraints() {
        for round in [0usize, 1, 12, 23] {
            let layout = IotaLayout::new(0, 0);
            let constraints = iota_constraints(&layout, round);
            let input = make_input_state();
            let synth = synthesize_iota(&input, round);
            let mut trace = MockTrace::zeros(1, layout.width);
            write_iota_cells(&synth, &layout, &mut trace);

            for c in &constraints {
                assert!(c.satisfied_by(&trace),
                    "ι round {round} constraint {c:?} residue = {}",
                    c.eval(&trace));
            }
        }
    }

    #[test]
    fn iota_tampering_lane00_breaks_constraint() {
        // Tampering with lane (0,0) — the only lane ι actually
        // modifies — must trip a constraint.
        let layout = IotaLayout::new(0, 0);
        let constraints = iota_constraints(&layout, 7);
        let input = make_input_state();
        let synth = synthesize_iota(&input, 7);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_iota_cells(&synth, &layout, &mut trace);

        let bad_cell = layout.output_bit(0, 5);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        assert!(constraints.iter().any(|c| !c.satisfied_by(&trace)));
    }

    #[test]
    fn iota_tampering_passthrough_lane_breaks_copy() {
        // Tampering with a pass-through lane (1..25) must also trip
        // a constraint — verifies the Copy pass-through is enforced.
        let layout = IotaLayout::new(0, 0);
        let constraints = iota_constraints(&layout, 7);
        let input = make_input_state();
        let synth = synthesize_iota(&input, 7);
        let mut trace = MockTrace::zeros(1, layout.width);
        write_iota_cells(&synth, &layout, &mut trace);

        let bad_cell = layout.output_bit(13, 27);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        assert!(constraints.iter().any(|c| !c.satisfied_by(&trace)));
    }

    // ─── Composition: all 4 sub-steps land same output as native ────

    #[test]
    fn theta_then_rho_pi_then_chi_then_iota_matches_full_round() {
        // The strongest cross-check yet: chain all 4 sub-step
        // synthesisers and verify their output equals
        // `keccak_round_bit_level` for the same round.
        use crate::sha3_absorb_air::keccak_round_bit_level;

        for round in [0usize, 7, 23] {
            let input = make_input_state();

            let theta  = synthesize_theta(&input);
            let rho_pi = synthesize_rho_pi(&theta.output_state);
            let chi    = synthesize_chi(&rho_pi.output_state);
            let iota   = synthesize_iota(&chi.output_state, round);

            let mut native_state = input;
            keccak_round_bit_level(&mut native_state, round);

            assert_eq!(iota.output_state, native_state,
                "full-round composition diverges at round {round}");
        }
    }

    // ─── Full round (4-row + cross-row threading) tests ─────────────

    #[test]
    fn round_layout_has_4_rows() {
        let layout = RoundLayout::new(0, 0);
        assert_eq!(layout.rows(), 4);
        // Rows assigned correctly per sub-step
        assert_eq!(layout.theta.row,  0);
        assert_eq!(layout.rho_pi.row, 1);
        assert_eq!(layout.chi.row,    2);
        assert_eq!(layout.iota.row,   3);
    }

    #[test]
    fn round_layout_max_row_width_is_chi() {
        let layout = RoundLayout::new(0, 0);
        // χ is the widest sub-step (6 400); the outer trace must
        // allocate at least this width per row.
        assert_eq!(layout.max_row_width(), 6400);
    }

    #[test]
    fn round_constraint_count_matches_design() {
        let layout = RoundLayout::new(0, 0);
        let cs = round_constraints(&layout);
        // Per-sub-step: θ=8 000, ρπ=4 800, χ=11 200, ι=4 800 = 28 800
        // Cross-row threading: 3 × 1 600 = 4 800 Copy constraints
        // Total: 33 600
        assert_eq!(cs.len(), 33_600);

        // Cross-row Copy constraints exist (i.e. threading is wired)
        let cross_row_copies = cs.iter().filter(|c| match c {
            BitOp::Copy { c, a } => c.row != a.row,
            _ => false,
        }).count();
        assert_eq!(cross_row_copies, 3 * 1600,
            "must have 3 × 1 600 cross-row Copy constraints for state threading");
    }

    #[test]
    fn synthesized_round_matches_native_for_all_rounds() {
        // For every round 0..24, the round synthesiser must produce
        // an output state equal to `keccak_round_bit_level` for that
        // round on the same input.
        use crate::sha3_absorb_air::keccak_round_bit_level;
        let input = make_input_state();
        for round in 0..24 {
            let cells = synthesize_round(&input, round);
            let mut native = input;
            keccak_round_bit_level(&mut native, round);
            assert_eq!(cells.output_state(), native, "round {round}");
        }
    }

    #[test]
    fn synthesized_round_satisfies_all_constraints() {
        // Build a multi-row mock trace big enough for the 4-row layout,
        // synthesise + write cells, verify EVERY constraint passes.
        let layout = RoundLayout::new(5, 0);  // round 5, row 0
        let row_width = layout.max_row_width();
        let n_rows = layout.row_offset + layout.rows();
        let mut trace = MockTrace::zeros(n_rows, row_width);

        let input = make_input_state();
        let cells = synthesize_round(&input, 5);
        write_round_cells(&cells, &layout, &mut trace);

        let constraints = round_constraints(&layout);
        for (i, c) in constraints.iter().enumerate() {
            assert!(c.satisfied_by(&trace),
                "round constraint #{i} = {c:?} residue = {}",
                c.eval(&trace));
        }
    }

    #[test]
    fn round_threading_tampering_breaks_constraint() {
        // The critical test for cross-row state threading: if a
        // prover tries to "skip" a sub-step by writing different
        // values into the next-row input than what came out of the
        // previous-row output, the Copy threading constraints MUST
        // catch it.  Without this property the multi-row encoding
        // is unsound.
        let layout = RoundLayout::new(5, 0);
        let row_width = layout.max_row_width();
        let n_rows = layout.row_offset + layout.rows();
        let mut trace = MockTrace::zeros(n_rows, row_width);

        let input = make_input_state();
        let cells = synthesize_round(&input, 5);
        write_round_cells(&cells, &layout, &mut trace);

        // Tamper: write a different value into the χ input row that
        // does NOT match the ρπ output row.  This simulates a prover
        // trying to splice in a fake state between sub-steps.
        let bad_cell = layout.chi.input_bit(8, 21);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        let constraints = round_constraints(&layout);
        let n_failing = constraints.iter()
            .filter(|c| !c.satisfied_by(&trace))
            .count();
        // At least the threading Copy + at least one χ constraint
        // must catch this — the χ output now no longer matches the
        // χ input either.
        assert!(n_failing >= 2,
            "tampering with χ input should trip ≥ 2 constraints; got {n_failing}");
    }

    #[test]
    fn round_supports_non_zero_row_offset() {
        // Make sure rounds at non-zero row_offsets work — required
        // for chaining multiple rounds into a full permutation.
        let layout = RoundLayout::new(3, 12);  // round 3 at rows 12..16
        assert_eq!(layout.theta.row,  12);
        assert_eq!(layout.rho_pi.row, 13);
        assert_eq!(layout.chi.row,    14);
        assert_eq!(layout.iota.row,   15);

        let row_width = layout.max_row_width();
        let n_rows = layout.row_offset + layout.rows();
        let mut trace = MockTrace::zeros(n_rows, row_width);

        let input = make_input_state();
        let cells = synthesize_round(&input, 3);
        write_round_cells(&cells, &layout, &mut trace);

        let constraints = round_constraints(&layout);
        for c in &constraints {
            assert!(c.satisfied_by(&trace),
                "constraint {c:?} failed at row_offset=12");
        }
    }
}
