//! T9 scaffold: **v2 verify-AIR composition layout**.
//!
//! Defines the trace dimensions, region offsets, and PI-hash
//! binding for the v2 ML-DSA-44 verify proof.  v2 = "STARK alone
//! proves FIPS 204 §3 Algorithm 3", removing the Layer-1 native
//! `ml_dsa::verify` from the gate's critical path.
//!
//! ## Architecture: 5 separate FRI sub-proofs
//!
//! A single composite AIR with all v2 work in one trace would need
//! ~32 K rows × ~12 K cols = 380 M cells, blowup=32 → 96 GB
//! working set — infeasible on consumer hardware.  The Keccak
//! region (`ml_dsa_transcript`) drives the col count up; the v1.7
//! polynomial-arithmetic region drives the row count up.
//!
//! v2 instead composes **5 separate FRI sub-proofs**, each over a
//! tightly-fitted trace.  PI-hash binding (Fiat-Shamir feeding the
//! same public-input digest into every sub-proof) makes them
//! collectively sound: the verifier accepts iff every sub-proof
//! passes AND every sub-proof commits to the same `pi_hash`, which
//! includes all shared values (e.g., `w_approx_ntt[k]` referenced
//! in both v1.7's poly-arithmetic region AND T-INTT's NTT regions).
//!
//! ### Sub-proof inventory
//!
//! | Sub-proof | Trace dims    | LDE @ b=32  | What it proves                                        |
//! |-----------|---------------|-------------|-------------------------------------------------------|
//! | V17       | 8192 × 323    | ~84 M cells | v1.7's existing 5-region AIR (poly-eq + norm + 4×NTT) |
//! | INTT      | 4096 × 260    | ~34 M cells | 4× chained NTT proving `w_approx[k]` → `w_approx_ntt[k]` |
//! | COEFF     | 1024 × ~80    | ~2.6 M      | per-coefficient (Decompose + UseHint + W1Encode) chain |
//! | TRANSCRIPT| 256 × 11520   | ~94 M       | T-Transcript SHAKE-256(µ ‖ w1bytes) → c̃' |
//! | T_MEM     | 16384 × 8     | ~4 M        | cross-region equality bindings                        |
//!
//! Total LDE: ~218 M cells = ~1.7 GiB working set across the 5
//! sub-proofs.  Total prove time projected: **~50–70 s** (FFT
//! dominated; the 5 proofs run sequentially or in parallel
//! depending on rayon scheduling).
//!
//! ### PI-hash binding (shared values)
//!
//! Every sub-proof feeds the same digest into Fiat-Shamir:
//!
//! ```text
//! pi_hash = SHA3-256(
//!     "mmiyc/v2/ml-dsa-pok/public-inputs"
//!     || pk_bytes  || message  || sig_bytes
//!     || a_ntt     || c_ntt    || t1d_ntt
//!     || w_approx_ntt          // shared between V17 and INTT
//!     || h_bytes               // hint, drives UseHint in COEFF
//!     || mu_bytes              // drives TRANSCRIPT's absorb prefix
//! )
//! ```
//!
//! Mismatches anywhere break Fiat-Shamir consistency across
//! sub-proofs and the verifier rejects.
//!
//! ### T_MEM bindings (cross-region equalities)
//!
//! Four binding sets, all routed through a single permutation
//! argument with tagged addresses:
//!
//! - **B1**: `w_approx[k][i]` cells in INTT region 0 ↔ `r` inputs
//!   to Decompose in COEFF region.  K·N = 1024 read+write pairs.
//! - **B2**: `(r1, r0_sign)` outputs from Decompose ↔ inputs to
//!   UseHint in COEFF region.  2·K·N pairs.
//! - **B3**: `adjusted_r1` outputs from UseHint ↔ inputs to
//!   W1Encode in COEFF region.  K·N pairs.
//! - **B4**: `w1bytes` outputs from W1Encode ↔ absorb-input bytes
//!   at the start of TRANSCRIPT's first block.  768 byte pairs.
//!
//! Total log entries: 2·(K·N + 2·K·N + K·N + 768) = 2·(4·1024 +
//! 768) = 9728 entries.  Plus a final-boundary equality
//! `RP[N−1] == WP[N−1]` enforced via PI-hash binding the running
//! products to a known value (`1 = ε`).

#![allow(non_snake_case, dead_code)]

use crate::ml_dsa::params::{K, L, N};

// ─── Per-sub-proof trace shapes ───────────────────────────────────

/// V17: v1.7's existing verify-AIR (`ml_dsa_verify_air_v17`).
pub mod v17 {
    use crate::ml_dsa_verify_air_v17::{VERIFY_AIR_V17_ACTIVE_ROWS, WIDTH};
    pub const N_ROWS_ACTIVE: usize = VERIFY_AIR_V17_ACTIVE_ROWS;       // 6148
    pub const N_ROWS_POW2:   usize = 8192;                             // next_power_of_two(6148)
    pub const N_COLS:        usize = WIDTH;                            // 323
}

/// INTT: 4× chained NTT for `w_approx[k]` → `w_approx_ntt[k]`.
pub mod intt {
    use crate::ml_dsa::params::{K, N};
    use crate::ml_dsa_ntt_chained_air::{BUTTERFLIES_PER_NTT, WIDTH};
    /// Each instance: 1024 butterfly rows + 1 output row = 1025.
    pub const ROWS_PER_INSTANCE: usize = BUTTERFLIES_PER_NTT + 1;      // 1025
    pub const N_INSTANCES:       usize = K;                            // 4
    pub const N_ROWS_ACTIVE:     usize = N_INSTANCES * ROWS_PER_INSTANCE; // 4100
    /// next_power_of_two(4100) = 8192.  4100 doesn't fit in 4096
    /// because 4·1025 = 4100, slightly over 2¹².
    pub const N_ROWS_POW2:       usize = 8192;
    pub const N_COLS:            usize = WIDTH;                        // 260
}

/// COEFF: per-coefficient (Decompose + UseHint + W1Encode) chain.
pub mod coeff_chain {
    use crate::ml_dsa::params::{K, N};
    use crate::ml_dsa_decompose_air::WIDTH as DECOMPOSE_WIDTH;
    use crate::ml_dsa_use_hint_air::WIDTH as USE_HINT_WIDTH;
    use crate::ml_dsa_w1_encode_air::WIDTH as W1ENCODE_WIDTH;

    pub const N_ROWS_ACTIVE: usize = K * N;                            // 1024
    pub const N_ROWS_POW2:   usize = 1024;
    /// 3 sub-AIR widths stacked side-by-side (disjoint cols).
    pub const N_COLS: usize = DECOMPOSE_WIDTH + USE_HINT_WIDTH + W1ENCODE_WIDTH;
}

/// TRANSCRIPT: SHAKE-256(µ ‖ w1bytes)[0..32] = c̃'.  Multi-block
/// absorb (T1.5) over a 832-byte input ⇒ 7 blocks × 24 rows.
pub mod transcript {
    use crate::keccak_f1600::ROUNDS;
    use crate::keccak_f1600_air::ROUND_WIDTH;
    /// 7 absorb blocks × 24 keccak rounds each.
    pub const N_ROWS_ACTIVE: usize = 7 * ROUNDS;                       // 168
    pub const N_ROWS_POW2:   usize = 256;
    pub const N_COLS:        usize = ROUND_WIDTH;                      // 11520
}

/// T_MEM: permutation argument trace covering all 4 cross-region
/// binding sets.  ~9 728 active entries; pad to next pow2.
pub mod t_mem {
    use crate::ml_dsa::params::{K, N};
    use crate::permutation_argument::WIDTH;

    /// Bindings:
    /// - B1: w_approx[k][i] ↔ Decompose r-input.  K·N = 1024 pairs.
    /// - B2: (r1, r0_sign) ↔ UseHint inputs.  2·K·N = 2048 pairs.
    /// - B3: adjusted_r1 ↔ W1Encode input.  K·N = 1024 pairs.
    /// - B4: w1bytes ↔ Transcript absorb input.  768 pairs (1 byte each).
    pub const TOTAL_PAIRS: usize = (K * N) + (2 * K * N) + (K * N) + 768; // 4864
    pub const N_ROWS_ACTIVE: usize = 2 * TOTAL_PAIRS;                  // 9728 (read + write per pair)
    pub const N_ROWS_POW2:   usize = 16384;                            // next_power_of_two(9728)
    pub const N_COLS:        usize = WIDTH;                            // 8
}

// ─── Aggregate v2 layout ──────────────────────────────────────────

/// Full descriptor for a v2 prove/verify session.  Each sub-proof
/// is an independent FRI run.
#[derive(Clone, Copy, Debug)]
pub struct V2Layout {
    pub blowup: usize,
}

impl V2Layout {
    pub const fn new() -> Self {
        Self { blowup: 32 }
    }

    pub const fn n_lde_v17(&self)        -> usize { v17::N_ROWS_POW2        * self.blowup }
    pub const fn n_lde_intt(&self)       -> usize { intt::N_ROWS_POW2 * self.blowup }
    pub const fn n_lde_coeff(&self)      -> usize { coeff_chain::N_ROWS_POW2 * self.blowup }
    pub const fn n_lde_transcript(&self) -> usize { transcript::N_ROWS_POW2 * self.blowup }
    pub const fn n_lde_t_mem(&self)      -> usize { t_mem::N_ROWS_POW2     * self.blowup }

    /// Total LDE cells across all 5 sub-proofs.
    pub const fn total_lde_cells(&self) -> usize {
          self.n_lde_v17()        * v17::N_COLS
        + self.n_lde_intt()       * intt::N_COLS
        + self.n_lde_coeff()      * coeff_chain::N_COLS
        + self.n_lde_transcript() * transcript::N_COLS
        + self.n_lde_t_mem()      * t_mem::N_COLS
    }
}

// ─── PI-hash domain tag and shape ─────────────────────────────────

pub const PI_HASH_DOMAIN_V2: &[u8] = b"mmiyc/v2/ml-dsa-pok/public-inputs";

/// Public-input field set for v2.  All shared values that any
/// sub-proof uses are committed in this single hash, ensuring
/// Fiat-Shamir consistency across the 5 FRI runs.
#[derive(Clone)]
pub struct V2PublicInputs {
    pub pk_bytes:       Vec<u8>,             // 1312 B
    pub message:        Vec<u8>,             // variable
    pub sig_bytes:      Vec<u8>,             // 2420 B
    pub a_ntt:          Box<[[[u32; N]; L]; K]>,
    pub c_ntt:          Box<[u32; N]>,
    pub t1d_ntt:        Box<[[u32; N]; K]>,
    pub w_approx_ntt:   Box<[[u32; N]; K]>,  // SHARED between V17 and INTT
    pub h_bytes:        Vec<u8>,             // hint (TR + h)
    pub mu_bytes:       [u8; 64],            // SHAKE-256(tr ‖ M)
    pub c_tilde_bytes:  [u8; 32],            // c̃ from sigDecode
}

// ─── Cost projection ──────────────────────────────────────────────

/// Quick numerical sanity at compile time.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_dimensions_sane() {
        let l = V2Layout::new();
        // Each sub-proof's row count is sane.
        assert!(v17::N_ROWS_ACTIVE <= v17::N_ROWS_POW2);
        assert!(intt::N_ROWS_ACTIVE <= intt::N_ROWS_POW2);
        assert!(coeff_chain::N_ROWS_ACTIVE <= coeff_chain::N_ROWS_POW2);
        assert!(transcript::N_ROWS_ACTIVE <= transcript::N_ROWS_POW2);
        assert!(t_mem::N_ROWS_ACTIVE <= t_mem::N_ROWS_POW2);

        // Total LDE cells, with INTT's 4100 active rows rounded up
        // to 8192 (just over 2¹²): ~253 M cells = ~2 GiB working
        // set across all 5 sub-proofs at blowup = 32.  Production
        // tuning could shrink with column sharing across sub-AIRs.
        let total = l.total_lde_cells();
        assert!(total < 280_000_000,
            "v2 LDE total > 280 M cells: {total}");

        eprintln!("v2 LDE breakdown @ blowup=32:");
        eprintln!("  V17        : {:>10} cells ({:.1} MiB)",
            l.n_lde_v17() * v17::N_COLS,
            (l.n_lde_v17() * v17::N_COLS * 8) as f64 / 1024.0 / 1024.0);
        eprintln!("  INTT       : {:>10} cells ({:.1} MiB)",
            l.n_lde_intt() * intt::N_COLS,
            (l.n_lde_intt() * intt::N_COLS * 8) as f64 / 1024.0 / 1024.0);
        eprintln!("  COEFF      : {:>10} cells ({:.1} MiB)",
            l.n_lde_coeff() * coeff_chain::N_COLS,
            (l.n_lde_coeff() * coeff_chain::N_COLS * 8) as f64 / 1024.0 / 1024.0);
        eprintln!("  TRANSCRIPT : {:>10} cells ({:.1} MiB)",
            l.n_lde_transcript() * transcript::N_COLS,
            (l.n_lde_transcript() * transcript::N_COLS * 8) as f64 / 1024.0 / 1024.0);
        eprintln!("  T_MEM      : {:>10} cells ({:.1} MiB)",
            l.n_lde_t_mem() * t_mem::N_COLS,
            (l.n_lde_t_mem() * t_mem::N_COLS * 8) as f64 / 1024.0 / 1024.0);
        eprintln!("  TOTAL      : {:>10} cells ({:.1} MiB)",
            total, (total * 8) as f64 / 1024.0 / 1024.0);
    }

    #[test]
    fn pi_hash_domain_v2_is_distinct_from_v17() {
        // Sanity: v2's domain tag must differ from v1.5/v1.7's so
        // proofs from different protocol versions are non-interchangeable.
        assert_eq!(PI_HASH_DOMAIN_V2, b"mmiyc/v2/ml-dsa-pok/public-inputs");
        assert_ne!(PI_HASH_DOMAIN_V2, b"mmiyc/v1.7/ml-dsa-pok/public-inputs");
        assert_ne!(PI_HASH_DOMAIN_V2, b"mmiyc/v1.5/ml-dsa-pok/public-inputs");
        assert_ne!(PI_HASH_DOMAIN_V2, b"mmiyc/v1/ml-dsa-pok/public-inputs");
    }

    #[test]
    fn t_mem_total_pairs_matches_v2_bindings() {
        // 4 binding sets × specified counts:
        //   B1: K·N      (w_approx[k][i] ↔ Decompose input)
        //   B2: 2·K·N    ((r1, r0_sign) ↔ UseHint inputs)
        //   B3: K·N      (adjusted_r1 ↔ W1Encode input)
        //   B4: 768      (w1bytes ↔ Transcript bytes)
        let expected = (K * N) + (2 * K * N) + (K * N) + 768;
        assert_eq!(t_mem::TOTAL_PAIRS, expected);
        assert_eq!(t_mem::TOTAL_PAIRS, 4864);  // = 4·1024 + 768
    }
}
