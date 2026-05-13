//! Verifier-as-AIR for the `deep_ali_merge` inner verification predicate.
//!
//! # Architecture
//!
//! The wrapper AIR uses **row-region gating**: distinct phases of the
//! inner verifier occupy non-overlapping row ranges in a single trace,
//! and selector polynomials ensure each region's constraints fire only
//! within its rows.  This mirrors the RSA-2048 monolithic AIR pattern
//! and avoids the cross-trace binding overhead that drives the modular
//! v2 ML-DSA proof from ~10 sub-FRI proofs to one outer FRI.
//!
//! # Trace regions (in row order)
//!
//! 1. **PiHashRecompute** — recompute the inner proof's `pi_hash` from
//!    `(pk, mu, sig, c_tilde_prime, pp_vector)` and bind to the public
//!    input.  Uses [`crate::sha3_absorb_air`] as a sub-circuit.
//!
//! 2. **SubProofQuery** × 10 sub-proofs (V17, INTT×K, Decompose,
//!    UseHint, W1Encode, Transcript) — for each, encode `r` FRI/STIR
//!    query verifications: open trace leaf, verify Merkle path, evaluate
//!    constraint composition, check fold consistency.
//!
//! 3. **CrossTraceBinding** × 8 binding levels (F2b L0–L5 plus the
//!    intt_l0/intt_l1 row openings) — encode the trace-row openings
//!    that pin sub-AIR outputs to public inputs and to each other.
//!
//! 4. **OodConsistency** — for each `binding_cells_commit` pair,
//!    verify the Schwartz-Zippel cross-trace eval at the FS-derived
//!    `z_ext` point.  Uses [`crate::fri::derive_z_ext_for_proof`]
//!    transcript replay to recompute `z_ext` inside the AIR.
//!
//! 5. **PublicInputCommit** — final row(s) bind the wrapper's public
//!    inputs (pi_hash, c_tilde_prime, nist_level) into the FS transcript.
//!
//! # Column layout
//!
//! Columns are organised into named contiguous ranges:
//!
//! - `merkle_path_cols`: sibling hashes for inner-proof Merkle paths
//! - `hash_state_cols`: SHA-3 sponge state for the absorb-sub-AIR
//! - `fri_query_cols`: query positions, leaf values, fold quotients
//! - `constraint_eval_cols`: constraint composition evaluations at queries
//! - `ood_eval_cols`: OOD points + Schwartz-Zippel evaluations
//! - `public_input_cols`: pk, mu, sig, c_tilde_prime echoes
//! - `selector_cols`: region-selector polynomials
//!
//! Total width is fixed per NIST level — see [`WrapperAirLayout::for_level`].

use core::ops::Range;

/// Logical row-regions in the wrapper AIR trace.  Each region's rows
/// are gated by a selector polynomial; constraints only fire in their
/// region.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TraceRegion {
    /// Recompute pi_hash from public inputs and bind to inner's pi_hash.
    PiHashRecompute,
    /// FRI/STIR query verification for one of the 10 sub-proofs.
    SubProofQuery(SubProofKind),
    /// Cross-trace binding check for one of the F2b levels.
    CrossTraceBinding(BindingLevel),
    /// `binding_cells_commit` OOD Schwartz-Zippel cross-trace eval.
    OodConsistency,
    /// Public-input commit row(s) — final FS absorption.
    PublicInputCommit,
}

/// The 10 sub-proofs the modular v2 ML-DSA proof comprises.  Each maps
/// to one entry in [`deep_ali::V2ProofReal`]'s `fri_*` fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SubProofKind {
    /// V17 EQ-region sub-proof (`fri_v17`)
    V17,
    /// INTT sub-proof k ∈ [0..K) (`fri_intt[k]`)
    Intt(u8),
    /// Decompose sub-proof (`fri_decompose`)
    Decompose,
    /// UseHint sub-proof (`fri_use_hint`)
    UseHint,
    /// W1Encode sub-proof (`fri_w1_encode`)
    W1Encode,
    /// Transcript sub-proof (`fri_transcript`)
    Transcript,
}

impl SubProofKind {
    /// All sub-proof kinds for a given inner level, in trace-region
    /// order.  K = 4 for ML-DSA-44, 6 for ML-DSA-65, 8 for ML-DSA-87.
    pub fn all_for_level(nist_level: u8) -> Vec<Self> {
        let k: u8 = match nist_level {
            1 => 4,  // ML-DSA-44
            3 => 6,  // ML-DSA-65
            5 => 8,  // ML-DSA-87
            _ => panic!("SubProofKind::all_for_level: unsupported level {nist_level}"),
        };
        let mut out = vec![Self::V17];
        for i in 0..k {
            out.push(Self::Intt(i));
        }
        out.push(Self::Decompose);
        out.push(Self::UseHint);
        out.push(Self::W1Encode);
        out.push(Self::Transcript);
        out
    }
}

/// F2b cross-trace binding levels (per `binding_cells_commit` design).
/// L0 stays as row-opening-based F2b; L1–L5 use OOD Schwartz-Zippel via
/// `binding_cells_commit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BindingLevel {
    /// INTT output ≡ public w_approx_ntt (L0, F2b row opening)
    L0,
    /// INTT row-0 input ≡ Decompose r-input (L1, F2b row opening)
    L1,
    /// Decompose col_r1 ≡ UseHint COL_R1 (L2a, OOD)
    L2a,
    /// Decompose col_r0_sign ≡ UseHint COL_R0_SIGN (L2b, OOD)
    L2b,
    /// UseHint COL_R1 ≡ Decompose col_r1 (alternative direction, L2c, OOD)
    L2c,
    /// UseHint COL_ADJUSTED_R1 ≡ W1Encode col_r1 (L3, OOD)
    L3,
    /// W1Encode ≡ Transcript w1_bytes window (L4, OOD)
    L4,
    /// V17 EQ-region ≡ public a_ntt / c_ntt / t1d_ntt / w_approx_ntt (L5, OOD)
    L5,
}

impl BindingLevel {
    pub fn all() -> [Self; 8] {
        [
            Self::L0, Self::L1, Self::L2a, Self::L2b,
            Self::L2c, Self::L3, Self::L4, Self::L5,
        ]
    }
}

/// Column layout for the wrapper AIR.  All ranges are exclusive-end
/// (`a..b` covers columns `a, a+1, ..., b-1`).  Sum of all range
/// lengths equals `width`.
#[derive(Clone, Debug)]
pub struct WrapperAirLayout {
    /// Total trace width (columns).
    pub width: usize,
    /// Total trace length (rows).
    pub rows: usize,
    /// Inner-proof Merkle path sibling hashes.  Each query opens
    /// log_2(n_inner_LDE) sibling hashes; one column per sibling slot.
    pub merkle_path_cols: Range<usize>,
    /// SHA-3 sponge state cells — shared with `sha3_absorb_air`.
    /// Width = lanes × words-per-lane = 25 × 8 = 200 bytes packed into
    /// Goldilocks elements at 1 byte per element (conservative; can
    /// be tightened to 8 bytes per element after rate analysis).
    pub hash_state_cols: Range<usize>,
    /// FRI/STIR query position, leaf value, and fold quotient slots.
    pub fri_query_cols: Range<usize>,
    /// Constraint composition evaluations at query points.
    pub constraint_eval_cols: Range<usize>,
    /// OOD evaluation points and Schwartz-Zippel cross-trace evals.
    pub ood_eval_cols: Range<usize>,
    /// Public input echoes: pk, mu, sig, c_tilde_prime, nist_level.
    pub public_input_cols: Range<usize>,
    /// Region-selector polynomials (one per `TraceRegion` variant).
    pub selector_cols: Range<usize>,
}

impl WrapperAirLayout {
    /// Build a layout for the given NIST level.  Column counts are
    /// conservative upper bounds based on the v2 ML-DSA proof shape;
    /// real values will be tightened once the constraint set is
    /// finalised (and each module — sha3_absorb, FRI verify, etc. —
    /// publishes its column budget).
    pub fn for_level(nist_level: u8) -> Self {
        let r = match nist_level {
            1 => 54,
            3 => 79,
            5 => 105,
            _ => panic!("WrapperAirLayout::for_level: unsupported level {nist_level}"),
        };
        let k: usize = match nist_level {
            1 => 4, 3 => 6, 5 => 8, _ => unreachable!(),
        };

        // Conservative column budgets — to be tightened.
        let merkle_path_len      = 32;             // log2(n_LDE) ≤ 32
        let hash_state_len       = 200;            // 25 × 8-byte lanes
        let fri_query_len        = r * 4;          // (pos, leaf, fold_q, dummy) per query
        let constraint_eval_len  = r * 8;          // multi-constraint composition
        let ood_eval_len         = 16;             // a handful of OOD slots
        let public_input_len     = 256;            // pk + mu + sig + c_tilde + pp
        let selector_len         = 12;             // one per TraceRegion variant + reserve

        let mut cursor = 0;
        let merkle_path_cols      = cursor..cursor + merkle_path_len;      cursor += merkle_path_len;
        let hash_state_cols       = cursor..cursor + hash_state_len;       cursor += hash_state_len;
        let fri_query_cols        = cursor..cursor + fri_query_len;        cursor += fri_query_len;
        let constraint_eval_cols  = cursor..cursor + constraint_eval_len;  cursor += constraint_eval_len;
        let ood_eval_cols         = cursor..cursor + ood_eval_len;         cursor += ood_eval_len;
        let public_input_cols     = cursor..cursor + public_input_len;     cursor += public_input_len;
        let selector_cols         = cursor..cursor + selector_len;         cursor += selector_len;

        let width = cursor;

        // Row budget per region (conservative upper bounds).  Total
        // rows must be a power of two for the LDE; we round up at the
        // end.
        let pi_hash_rows         = 256;            // SHA-3 absorb iterations
        let sub_proof_query_rows = r * 64 * (1 + k + 4);  // r queries × cycles × n_sub_proofs
        let cross_binding_rows   = (k * 256) * 8;  // K·N × 8 binding levels
        let ood_rows             = 1024;
        let public_input_rows    = 32;
        let raw_rows = pi_hash_rows + sub_proof_query_rows + cross_binding_rows
                     + ood_rows + public_input_rows;
        let rows = raw_rows.next_power_of_two();

        Self {
            width, rows,
            merkle_path_cols, hash_state_cols, fri_query_cols,
            constraint_eval_cols, ood_eval_cols, public_input_cols,
            selector_cols,
        }
    }

    /// Total cell count = width × rows.  Used for memory-budget checks
    /// and FFT cost estimation.
    pub fn cell_count(&self) -> usize {
        self.width * self.rows
    }
}

/// A wrapper-AIR trace ready for FRI/STIR proving.  Cells are stored
/// row-major as raw `u64` values; the prover converts to field elements
/// when constructing the LDE.  Stub builder produces zero-initialised
/// cells until the real synthesizer lands.
#[derive(Clone, Debug)]
pub struct WrapperTrace {
    pub layout: WrapperAirLayout,
    /// Cells in row-major order: `cells[row * width + col]`.
    pub cells: Vec<u64>,
}

impl WrapperTrace {
    /// Allocate a zero-initialised trace of the given layout.
    pub fn zero(layout: WrapperAirLayout) -> Self {
        let cells = vec![0u64; layout.cell_count()];
        Self { layout, cells }
    }

    /// Read cell at (row, col).  Panics on out-of-bounds.
    pub fn get(&self, row: usize, col: usize) -> u64 {
        self.cells[row * self.layout.width + col]
    }

    /// Write cell at (row, col).  Panics on out-of-bounds.
    pub fn set(&mut self, row: usize, col: usize, val: u64) {
        self.cells[row * self.layout.width + col] = val;
    }
}

/// Estimate the wrapper-AIR trace length (rows) for a given NIST level.
/// Used by [`crate::WrapperParams::defaults_for_level`] before the real
/// layout is computed.  Returns the same value as
/// `WrapperAirLayout::for_level(level).rows` once the layout stabilises.
pub fn estimate_trace_length(nist_level: u8) -> usize {
    WrapperAirLayout::for_level(nist_level).rows
}

/// Build an empty (zero-filled) wrapper trace for the given level.
/// This is the entry point the trace-synthesiser will replace; for
/// now it produces a correctly-sized but content-free trace so the
/// outer FRI prover can be plumbed in parallel.
pub fn build_empty_trace(nist_level: u8) -> WrapperTrace {
    WrapperTrace::zero(WrapperAirLayout::for_level(nist_level))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sub_proof_kind_counts_per_level() {
        // L1 (K=4): V17 + 4 INTT + Decompose + UseHint + W1Encode + Transcript = 9
        assert_eq!(SubProofKind::all_for_level(1).len(), 9);
        // L3 (K=6): 11
        assert_eq!(SubProofKind::all_for_level(3).len(), 11);
        // L5 (K=8): 13
        assert_eq!(SubProofKind::all_for_level(5).len(), 13);
    }

    #[test]
    fn binding_levels_complete() {
        let all = BindingLevel::all();
        assert_eq!(all.len(), 8);
        assert!(all.contains(&BindingLevel::L0));
        assert!(all.contains(&BindingLevel::L5));
    }

    #[test]
    fn layout_ranges_are_contiguous_and_disjoint() {
        let l = WrapperAirLayout::for_level(3);
        // Check each range starts where the previous ended.
        assert_eq!(l.merkle_path_cols.start, 0);
        assert_eq!(l.merkle_path_cols.end, l.hash_state_cols.start);
        assert_eq!(l.hash_state_cols.end, l.fri_query_cols.start);
        assert_eq!(l.fri_query_cols.end, l.constraint_eval_cols.start);
        assert_eq!(l.constraint_eval_cols.end, l.ood_eval_cols.start);
        assert_eq!(l.ood_eval_cols.end, l.public_input_cols.start);
        assert_eq!(l.public_input_cols.end, l.selector_cols.start);
        assert_eq!(l.selector_cols.end, l.width);
    }

    #[test]
    fn layout_scales_with_level() {
        let l1 = WrapperAirLayout::for_level(1);
        let l3 = WrapperAirLayout::for_level(3);
        let l5 = WrapperAirLayout::for_level(5);
        // Higher levels have more queries → wider fri_query_cols.
        assert!(l3.fri_query_cols.len() > l1.fri_query_cols.len());
        assert!(l5.fri_query_cols.len() > l3.fri_query_cols.len());
        // Rows are power-of-two for LDE.
        assert!(l1.rows.is_power_of_two());
        assert!(l3.rows.is_power_of_two());
        assert!(l5.rows.is_power_of_two());
    }

    #[test]
    #[should_panic(expected = "unsupported level")]
    fn layout_rejects_invalid_level() {
        let _ = WrapperAirLayout::for_level(2);
    }

    #[test]
    fn empty_trace_has_correct_shape() {
        let t = build_empty_trace(3);
        assert_eq!(t.cells.len(), t.layout.cell_count());
        // All cells are zero in the stub.
        assert!(t.cells.iter().all(|&c| c == 0));
    }

    #[test]
    fn trace_get_set_roundtrip() {
        let mut t = build_empty_trace(1);
        t.set(10, 5, 0xDEADBEEF);
        assert_eq!(t.get(10, 5), 0xDEADBEEF);
        // Other cells unaffected.
        assert_eq!(t.get(10, 6), 0);
        assert_eq!(t.get(11, 5), 0);
    }

    #[test]
    fn estimate_trace_length_matches_layout() {
        for level in [1, 3, 5] {
            let est = estimate_trace_length(level);
            let actual = WrapperAirLayout::for_level(level).rows;
            assert_eq!(est, actual, "level {level}");
        }
    }
}
