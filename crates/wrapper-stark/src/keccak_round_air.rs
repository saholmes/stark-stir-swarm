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
}
