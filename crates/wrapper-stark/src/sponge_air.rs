//! SHA-3 sponge construction as an AIR.
//!
//! # Architecture
//!
//! The sponge wraps the Keccak-f1600 permutation AIR (from
//! [`crate::keccak_round_air`]) with absorb rows that XOR each input
//! block into the state's rate region, then run a full permutation.
//!
//! ```text
//!  ┌─ row 0      absorb XOR (block 0)
//!  │  rows 1-96  Keccak-f1600 permutation (24 rounds × 4 sub-steps)
//!  ┝─ row 97     absorb XOR (block 1)
//!  │  rows 98-193 Keccak-f1600 permutation
//!  │   ...
//!  ┕─ row N·97-1  final permutation output (= digest source for squeeze)
//! ```
//!
//! 97 rows per absorb block.  For SHA3-256, all inputs ≤ 135 bytes
//! fit in 1 padded block (97 rows); the maximum µ-hash absorption
//! in ML-DSA-65 (mu = SHAKE256("...")) is 64 bytes — single block.
//!
//! # Out of scope for this commit
//!
//! - FIPS 202 padding constraints (caller provides padded blocks)
//! - Squeeze constraints (digest extraction from final state)
//! - Variable-output SHAKE
//!
//! These come in subsequent commits.

use crate::bit_constraint::{BitOp, CellRef};
use crate::keccak_round_air::{
    PermutationLayout, PermutationCells,
    permutation_constraints, synthesize_permutation, write_permutation_cells,
};
use crate::sha3_absorb_air::{BitState, LaneBits, Sha3Variant, lane_to_bits};

/// Column layout for one absorb-XOR row.  Combines:
/// - input_state (1 600 bit cells): incoming sponge state
/// - block_bits (rate_bits cells): the block being absorbed
/// - output_state (1 600 bit cells): state after XOR-into-rate
#[derive(Clone, Debug)]
pub struct AbsorbXorLayout {
    pub variant: Sha3Variant,
    pub row: usize,
    pub input_state_start:  usize,
    pub block_bits_start:   usize,
    pub output_state_start: usize,
    pub width: usize,
}

impl AbsorbXorLayout {
    pub fn new(variant: Sha3Variant, row: usize, col_start: usize) -> Self {
        let input_state_start  = col_start;
        let block_bits_start   = input_state_start  + 1600;
        let output_state_start = block_bits_start   + variant.rate_bits();
        let end                = output_state_start + 1600;
        Self {
            variant, row,
            input_state_start, block_bits_start, output_state_start,
            width: end - col_start,
        }
    }

    pub fn input_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.input_state_start + 64 * lane_idx + bit)
    }

    /// Block-bit cell.  `bit_idx` ∈ [0..rate_bits).
    pub fn block_bit(&self, bit_idx: usize) -> CellRef {
        debug_assert!(bit_idx < self.variant.rate_bits());
        CellRef::new(self.row, self.block_bits_start + bit_idx)
    }

    pub fn output_bit(&self, lane_idx: usize, bit: usize) -> CellRef {
        debug_assert!(lane_idx < 25 && bit < 64);
        CellRef::new(self.row, self.output_state_start + 64 * lane_idx + bit)
    }
}

/// Emit constraints for one absorb-XOR row.  Layout:
/// - rate region (lanes 0..rate_lanes): output = input XOR block (1 XOR per bit)
/// - capacity region (lanes rate_lanes..25): output = input (Copy per bit)
/// - booleanity on all participating cells
pub fn absorb_xor_constraints(layout: &AbsorbXorLayout) -> Vec<BitOp> {
    let rate_lanes = layout.variant.rate_bits() / 64;
    // Booleanity: 1 600 input + rate_bits block + 1 600 output
    // Rate region XORs: rate_bits
    // Capacity region Copies: (25 - rate_lanes) × 64
    let cap_lanes = 25 - rate_lanes;
    let cap_cells = cap_lanes * 64;
    let rate_bits = layout.variant.rate_bits();
    let total = (1600 + rate_bits + 1600) + rate_bits + cap_cells;
    let mut out = Vec::with_capacity(total);

    // Booleanity.
    for lane in 0..25 {
        for bit in 0..64 {
            out.push(BitOp::Boolean { b: layout.input_bit(lane, bit) });
            out.push(BitOp::Boolean { b: layout.output_bit(lane, bit) });
        }
    }
    for b in 0..rate_bits {
        out.push(BitOp::Boolean { b: layout.block_bit(b) });
    }

    // Rate region: output[lane][bit] = input[lane][bit] XOR block[lane*64 + bit]
    for lane in 0..rate_lanes {
        for bit in 0..64 {
            out.push(BitOp::Xor {
                c: layout.output_bit(lane, bit),
                a: layout.input_bit(lane, bit),
                b: layout.block_bit(64 * lane + bit),
            });
        }
    }
    // Capacity region: output = input (pass-through)
    for lane in rate_lanes..25 {
        for bit in 0..64 {
            out.push(BitOp::Copy {
                c: layout.output_bit(lane, bit),
                a: layout.input_bit(lane, bit),
            });
        }
    }

    out
}

/// Synthesised absorb-XOR cells.
#[derive(Clone, Debug)]
pub struct AbsorbXorCells {
    pub variant: Sha3Variant,
    pub input_state:  BitState,
    pub block_bits:   Vec<u8>,    // length = variant.rate_bits()
    pub output_state: BitState,
}

/// Synthesize cells for one absorb-XOR row.  `block` must be exactly
/// `variant.block_bytes()` long (caller-provided padding).
pub fn synthesize_absorb_xor(
    input_state: &BitState,
    block: &[u8],
    variant: Sha3Variant,
) -> AbsorbXorCells {
    assert_eq!(block.len(), variant.block_bytes(),
        "synthesize_absorb_xor: block size mismatch");
    let rate_lanes = variant.rate_bits() / 64;

    // Decompose block bytes into rate_bits boolean cells: bit b within
    // lane k is bit b of byte (k*8 + b/8) at position (b%8).  This
    // matches the lane-packing scheme used by `absorb_block` (LE bytes
    // packed into u64 lanes).
    let mut block_bits: Vec<u8> = Vec::with_capacity(variant.rate_bits());
    for lane in 0..rate_lanes {
        let mut lane_u64 = 0u64;
        for j in 0..8 {
            lane_u64 |= (block[8 * lane + j] as u64) << (8 * j);
        }
        let lb: LaneBits = lane_to_bits(lane_u64);
        block_bits.extend_from_slice(&lb);
    }

    // Compute output_state.
    let mut output_state = *input_state;
    for lane in 0..rate_lanes {
        for bit in 0..64 {
            output_state[lane][bit] ^= block_bits[64 * lane + bit];
        }
    }
    // capacity lanes are pass-through (already copied in *input_state)

    AbsorbXorCells {
        variant, input_state: *input_state, block_bits, output_state,
    }
}

pub fn write_absorb_xor_cells(
    cells: &AbsorbXorCells,
    layout: &AbsorbXorLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    for lane in 0..25 {
        for bit in 0..64 {
            trace.set(layout.input_bit(lane, bit),  cells.input_state[lane][bit] as u64);
            trace.set(layout.output_bit(lane, bit), cells.output_state[lane][bit] as u64);
        }
    }
    for b in 0..cells.variant.rate_bits() {
        trace.set(layout.block_bit(b), cells.block_bits[b] as u64);
    }
}

// ─── Multi-block sponge ─────────────────────────────────────────────

/// Layout for a multi-block SHA-3 absorb sequence.  Each block uses
/// 97 rows (1 absorb XOR + 96 permutation), starting at consecutive
/// `row_offset + k * 97` for k ∈ [0..n_blocks).
#[derive(Clone, Debug)]
pub struct SpongeLayout {
    pub variant: Sha3Variant,
    pub row_offset: usize,
    pub n_blocks: usize,
    pub absorbs: Vec<AbsorbXorLayout>,
    pub permutations: Vec<PermutationLayout>,
}

impl SpongeLayout {
    pub fn new(variant: Sha3Variant, n_blocks: usize, row_offset: usize) -> Self {
        let mut absorbs = Vec::with_capacity(n_blocks);
        let mut permutations = Vec::with_capacity(n_blocks);
        for k in 0..n_blocks {
            let absorb_row = row_offset + k * 97;
            absorbs.push(AbsorbXorLayout::new(variant, absorb_row, 0));
            // Permutation starts immediately after absorb row (1 row),
            // occupies 96 rows.
            permutations.push(PermutationLayout::new(absorb_row + 1));
        }
        Self { variant, row_offset, n_blocks, absorbs, permutations }
    }

    pub fn rows(&self) -> usize { 97 * self.n_blocks }

    pub fn max_row_width(&self) -> usize {
        // absorb-XOR row width = 1600 + rate_bits + 1600
        // permutation max row width = 6400
        let absorb_w = 1600 + self.variant.rate_bits() + 1600;
        std::cmp::max(absorb_w, 6400)
    }
}

/// Emit all constraints for a multi-block sponge.  Total per block:
/// - absorb_xor: 1 600 in-bool + 1 600 out-bool + rate_bits block-bool
///   + rate_bits XOR + (25-rate_lanes)·64 Copy
/// - permutation: 843 200
/// - intra-block threading: absorb_xor.output ≡ first_round.theta.input
///   (1 600 Copy)
/// - inter-block threading (k > 0): last_round[k-1].iota.output ≡
///   absorb_xor[k].input (1 600 Copy)
pub fn sponge_constraints(layout: &SpongeLayout) -> Vec<BitOp> {
    let mut out: Vec<BitOp> = Vec::new();

    for k in 0..layout.n_blocks {
        out.extend(absorb_xor_constraints(&layout.absorbs[k]));
        out.extend(permutation_constraints(&layout.permutations[k]));

        // Intra-block: absorb_xor.output_state ≡ first_round[k].θ.input
        let absorb = &layout.absorbs[k];
        let first_round_theta = &layout.permutations[k].first_round().theta;
        for lane in 0..25 {
            for bit in 0..64 {
                out.push(BitOp::Copy {
                    c: first_round_theta.input_bit(lane, bit),
                    a: absorb.output_bit(lane, bit),
                });
            }
        }

        // Inter-block: last_round[k-1].ι.output ≡ absorb_xor[k].input
        if k > 0 {
            let prev_iota = &layout.permutations[k - 1].last_round().iota;
            let cur_absorb = &layout.absorbs[k];
            for lane in 0..25 {
                for bit in 0..64 {
                    out.push(BitOp::Copy {
                        c: cur_absorb.input_bit(lane, bit),
                        a: prev_iota.output_bit(lane, bit),
                    });
                }
            }
        }
    }

    out
}

/// All cells for a multi-block sponge.
#[derive(Clone, Debug)]
pub struct SpongeCells {
    pub variant: Sha3Variant,
    pub absorbs:      Vec<AbsorbXorCells>,
    pub permutations: Vec<PermutationCells>,
}

impl SpongeCells {
    /// Final sponge state after all N absorbs.  Source for the squeeze.
    pub fn final_state(&self) -> BitState {
        self.permutations[self.permutations.len() - 1].output_state()
    }
}

/// Synthesize cells for a multi-block sponge.  `blocks` must contain
/// exactly `n_blocks` × `variant.block_bytes()` bytes of input (caller
/// pre-pads using FIPS 202 §B.2; see `crate::sha3_absorb_air::hash`
/// for the canonical padding scheme).
pub fn synthesize_sponge(
    blocks: &[&[u8]],
    variant: Sha3Variant,
) -> SpongeCells {
    let n_blocks = blocks.len();
    let mut absorbs = Vec::with_capacity(n_blocks);
    let mut permutations = Vec::with_capacity(n_blocks);
    let mut state: BitState = [[0u8; 64]; 25];

    for block in blocks {
        let absorb = synthesize_absorb_xor(&state, block, variant);
        state = absorb.output_state;
        absorbs.push(absorb);

        let perm = synthesize_permutation(&state);
        state = perm.output_state();
        permutations.push(perm);
    }

    SpongeCells { variant, absorbs, permutations }
}

pub fn write_sponge_cells(
    cells: &SpongeCells,
    layout: &SpongeLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) {
    for k in 0..layout.n_blocks {
        write_absorb_xor_cells(&cells.absorbs[k], &layout.absorbs[k], trace);
        write_permutation_cells(&cells.permutations[k], &layout.permutations[k], trace);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bit_constraint::{MockTrace, TraceAccess};
    use crate::sha3_absorb_air::{hash, lanes_from_bit_state};

    fn pad_input(input: &[u8], variant: Sha3Variant) -> Vec<Vec<u8>> {
        // Reproduce the padding scheme from `crate::sha3_absorb_air::hash`:
        // 0x06 domain separator + zero pad + 0x80 last bit, blocks of
        // exactly block_bytes.
        let block_len = variant.block_bytes();
        let mut blocks: Vec<Vec<u8>> = Vec::new();
        let mut offset = 0;
        while offset + block_len <= input.len() {
            blocks.push(input[offset..offset + block_len].to_vec());
            offset += block_len;
        }
        let mut last = vec![0u8; block_len];
        let tail = &input[offset..];
        last[..tail.len()].copy_from_slice(tail);
        last[tail.len()] = 0x06;
        last[block_len - 1] |= 0x80;
        blocks.push(last);
        blocks
    }

    fn extract_digest(state: &BitState, variant: Sha3Variant) -> Vec<u8> {
        let lanes = lanes_from_bit_state(state);
        let mut out = Vec::with_capacity(variant.output_bytes());
        let full = variant.output_bytes() / 8;
        for i in 0..full {
            out.extend_from_slice(&lanes[i].to_le_bytes());
        }
        let tail = variant.output_bytes() - 8 * full;
        if tail > 0 {
            let bs = lanes[full].to_le_bytes();
            out.extend_from_slice(&bs[..tail]);
        }
        out
    }

    #[test]
    fn absorb_xor_layout_width() {
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let l = AbsorbXorLayout::new(variant, 0, 0);
            assert_eq!(l.width, 1600 + variant.rate_bits() + 1600);
        }
    }

    #[test]
    fn absorb_xor_constraint_count() {
        let variant = Sha3Variant::Sha3_256;
        let l = AbsorbXorLayout::new(variant, 0, 0);
        let cs = absorb_xor_constraints(&l);

        let r = variant.rate_bits();          // 1088
        let rate_lanes = r / 64;              // 17
        let cap_lanes = 25 - rate_lanes;      // 8
        let cap_cells = cap_lanes * 64;       // 512

        let n_bool = cs.iter().filter(|c| matches!(c, BitOp::Boolean { .. })).count();
        let n_xor  = cs.iter().filter(|c| matches!(c, BitOp::Xor { .. })).count();
        let n_copy = cs.iter().filter(|c| matches!(c, BitOp::Copy { .. })).count();

        assert_eq!(n_bool, 1600 + 1600 + r);
        assert_eq!(n_xor, r);
        assert_eq!(n_copy, cap_cells);
    }

    #[test]
    fn synthesized_absorb_xor_satisfies_constraints() {
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let layout = AbsorbXorLayout::new(variant, 0, 0);
            let constraints = absorb_xor_constraints(&layout);

            // Non-trivial input state + non-trivial block bytes.
            let mut state: BitState = [[0u8; 64]; 25];
            for lane in 0..25 {
                for bit in 0..64 {
                    state[lane][bit] = ((lane + bit) % 2) as u8;
                }
            }
            let block: Vec<u8> = (0..variant.block_bytes())
                .map(|i| ((i * 17) % 256) as u8).collect();

            let cells = synthesize_absorb_xor(&state, &block, variant);
            let mut trace = MockTrace::zeros(1, layout.width);
            write_absorb_xor_cells(&cells, &layout, &mut trace);

            for c in &constraints {
                assert!(c.satisfied_by(&trace),
                    "variant={variant:?} constraint {c:?} residue = {}",
                    c.eval(&trace));
            }
        }
    }

    #[test]
    fn sponge_single_block_matches_hash() {
        // Single-block input: empty input is 0 bytes + padding fills
        // one block.  Sponge AIR output should match SHA-3 hash().
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let blocks = pad_input(b"", variant);
            assert_eq!(blocks.len(), 1);

            let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
            let cells = synthesize_sponge(&block_refs, variant);
            let digest = extract_digest(&cells.final_state(), variant);
            let expected = hash(variant, b"");
            assert_eq!(digest, expected, "variant {variant:?} empty input");
        }
    }

    #[test]
    fn sponge_abc_matches_hash() {
        // "abc" still fits in one block for all variants.
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let blocks = pad_input(b"abc", variant);
            let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
            let cells = synthesize_sponge(&block_refs, variant);
            let digest = extract_digest(&cells.final_state(), variant);
            assert_eq!(digest, hash(variant, b"abc"), "variant {variant:?} abc");
        }
    }

    #[test]
    fn sponge_multi_block_matches_hash() {
        // 200-byte input forces multi-block absorption for all variants.
        let input = vec![0xA5u8; 200];
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let blocks = pad_input(&input, variant);
            assert!(blocks.len() >= 2, "variant {variant:?} should need multiple blocks");
            let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
            let cells = synthesize_sponge(&block_refs, variant);
            let digest = extract_digest(&cells.final_state(), variant);
            assert_eq!(digest, hash(variant, &input), "variant {variant:?} multi-block");
        }
    }

    #[test]
    fn sponge_constraints_satisfied_on_synthesized_trace() {
        // Build a sponge AIR trace for SHA3-256("abc"), write all
        // cells, verify every constraint passes.  This is the
        // full end-to-end constraint validation for the sponge.
        let variant = Sha3Variant::Sha3_256;
        let blocks = pad_input(b"abc", variant);
        let n_blocks = blocks.len();
        assert_eq!(n_blocks, 1);

        let layout = SpongeLayout::new(variant, n_blocks, 0);
        let row_width = layout.max_row_width();
        let n_rows = layout.rows();
        let mut trace = MockTrace::zeros(n_rows, row_width);

        let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let cells = synthesize_sponge(&block_refs, variant);
        write_sponge_cells(&cells, &layout, &mut trace);

        let constraints = sponge_constraints(&layout);
        for (i, c) in constraints.iter().enumerate() {
            if !c.satisfied_by(&trace) {
                panic!("sponge constraint #{i} = {c:?} residue = {}",
                    c.eval(&trace));
            }
        }
    }

    #[test]
    fn sponge_tampering_with_block_bit_breaks_constraint() {
        // Soundness: if a prover tampers with a block bit, the
        // absorb-XOR constraint MUST reject.
        let variant = Sha3Variant::Sha3_256;
        let blocks = pad_input(b"abc", variant);
        let layout = SpongeLayout::new(variant, blocks.len(), 0);
        let row_width = layout.max_row_width();
        let n_rows = layout.rows();
        let mut trace = MockTrace::zeros(n_rows, row_width);

        let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let cells = synthesize_sponge(&block_refs, variant);
        write_sponge_cells(&cells, &layout, &mut trace);

        let bad_cell = layout.absorbs[0].block_bit(42);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        let constraints = sponge_constraints(&layout);
        assert!(constraints.iter().any(|c| !c.satisfied_by(&trace)));
    }

    #[test]
    fn sponge_inter_block_tampering_breaks_constraint() {
        // Soundness: if a prover tampers with absorb[k].input_state
        // (k > 0) to differ from permutation[k-1].output_state, the
        // inter-block threading Copy MUST reject.  This pins the
        // multi-block splicing-attack defense.
        let variant = Sha3Variant::Sha3_256;
        let input = vec![0xA5u8; 200];
        let blocks = pad_input(&input, variant);
        assert!(blocks.len() >= 2);

        let layout = SpongeLayout::new(variant, blocks.len(), 0);
        let row_width = layout.max_row_width();
        let n_rows = layout.rows();
        let mut trace = MockTrace::zeros(n_rows, row_width);

        let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let cells = synthesize_sponge(&block_refs, variant);
        write_sponge_cells(&cells, &layout, &mut trace);

        // Tamper with absorb[1].input_state.
        let bad_cell = layout.absorbs[1].input_bit(7, 19);
        let original = trace.get_cell(bad_cell);
        trace.set(bad_cell, 1 - original);

        let constraints = sponge_constraints(&layout);
        assert!(constraints.iter().any(|c| !c.satisfied_by(&trace)),
            "inter-block tampering should trip the threading Copy");
    }
}
