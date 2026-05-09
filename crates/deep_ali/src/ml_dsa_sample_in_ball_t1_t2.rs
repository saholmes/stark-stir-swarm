//! T4-native: **SampleInBall via T1 + T2 primitives**.
//!
//! Native composition of T1 (single-block SHAKE-256 absorb) + T2
//! (multi-block squeeze) implementing FIPS 204 §3.7 Algorithm 23
//! `SampleInBall`, cross-checked against the existing
//! `ml_dsa_sample_in_ball::sample_in_ball` (which uses
//! `sha3::Shake256` directly).
//!
//! ## Why this matters for v2
//!
//! Validates that my SHAKE primitives are correct end-to-end for
//! the second-largest call site in ML-DSA verify (after ExpandA).
//! The full T4 AIR (with in-circuit rejection sampling +
//! swap-with-position-i logic) is the next session's brick; this
//! native validation proves T1 + T2 is the right substrate.
//!
//! ## SampleInBall recap (FIPS 204 §3.7)
//!
//! Input: `c̃` (32 bytes).
//! Output: a polynomial `c ∈ R_q` with exactly τ = 39 nonzero
//! coefficients, each in `{+1, −1}` (lifted to `{1, q−1}` in Z_q).
//!
//! Procedure:
//! 1. Initialise SHAKE-256 with `c̃`.
//! 2. Read 8 bytes → `signs ∈ {0, 1}^64` (lowest τ bits used).
//! 3. For `i = N − τ .. N`:
//!    - Repeatedly read 1 byte until the value `j ≤ i` (rejection).
//!    - Swap `c[i] = c[j]` and set `c[j] = ±1` per `signs[i − (N−τ)]`.
//!
//! ## What this module does
//!
//! Replaces step 1 + the byte-reading inside step 3 with the AIR
//! primitives' helpers:
//! - `ml_dsa_shake_absorb_air::build_absorbed_state` for the absorb.
//! - `ml_dsa_shake_squeeze_air::squeeze_native` for the byte stream.
//! - The rejection / swap logic stays native (it's what T4's AIR
//!   layer will lift in-circuit).

#![allow(non_snake_case, dead_code)]

use crate::keccak_f1600;
use crate::ml_dsa::params::{N, Q, TAU};
use crate::ml_dsa_shake_absorb_air::{build_absorbed_state, SHAKE_256_RATE_BYTES};
use crate::ml_dsa_shake_squeeze_air::{squeeze_native, SqueezeLayout};

/// Provisioning: how many rate-blocks of SHAKE-256 squeeze to
/// pre-allocate.  After the first 8 bytes for sign bits, we need
/// enough additional bytes to find τ unique indices ≤ N − 1, with
/// rejection rate dependent on i (the current target slot).
///
/// For τ = 39 and the rejection schedule, ~50 bytes of input is
/// almost always enough.  We allocate 5 rate-blocks (5 × 136 = 680
/// bytes) to comfortably cover all realistic cases.
pub const N_SQUEEZE_BLOCKS_PROVISION: usize = 5;

/// Compute SampleInBall using T1 + T2 primitives + native rejection
/// sampling.  Mirrors `ml_dsa_sample_in_ball::sample_in_ball`'s
/// algorithm bit-for-bit; the only difference is where the SHAKE
/// bytes come from (this version uses my AIR primitives instead of
/// `sha3::Shake256`).
pub fn sample_in_ball_via_primitives(c_tilde: &[u8; crate::ml_dsa::params::C_TILDE_BYTES]) -> [u32; N] {
    // ── Absorb (T1): single-block SHAKE-256 of c̃ (32 < rate=136) ──
    let pre_permute = build_absorbed_state(c_tilde, SHAKE_256_RATE_BYTES);
    let mut post_absorb_state = pre_permute;
    keccak_f1600::keccak_f(&mut post_absorb_state);

    // ── Squeeze (T2): N_SQUEEZE_BLOCKS_PROVISION rate-blocks ──
    let layout = SqueezeLayout::new(
        post_absorb_state,
        N_SQUEEZE_BLOCKS_PROVISION - 1,  // n_f1600_calls = blocks − 1
        SHAKE_256_RATE_BYTES,
    );
    let stream = squeeze_native(&layout);

    // ── Apply rejection-sampling + swap logic ──
    // First 8 bytes carry the sign bits.
    let mut sign_buf = [0u8; 8];
    sign_buf.copy_from_slice(&stream[..8]);
    let mut signs = u64::from_le_bytes(sign_buf);
    let mut pos = 8;  // index into the stream

    let mut c = [0u32; N];
    for i in (N - TAU)..N {
        // Read bytes until we get one ≤ i.
        let j = loop {
            assert!(pos < stream.len(),
                "T4 squeeze provisioning insufficient: ran out of bytes at pos={pos}, target i={i}");
            let b = stream[pos] as usize;
            pos += 1;
            if b <= i { break b; }
        };
        c[i] = c[j];
        c[j] = if signs & 1 == 0 { 1 } else { Q - 1 };
        signs >>= 1;
    }
    c
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa_sample_in_ball;

    /// Cross-check: T1+T2-driven SampleInBall must produce the same
    /// output as the existing `sha3::Shake256`-based reference, for
    /// multiple distinct `c̃` seeds.
    #[test]
    fn t1_t2_sample_in_ball_matches_native_reference() {
        use crate::ml_dsa::params::C_TILDE_BYTES;
        for seed in 0u8..8 {
            let mut c_tilde = [0u8; C_TILDE_BYTES];
            for k in 0..C_TILDE_BYTES {
                c_tilde[k] = seed.wrapping_mul(13).wrapping_add(k as u8);
            }

            let theirs = ml_dsa_sample_in_ball::sample_in_ball(&c_tilde);
            let ours = sample_in_ball_via_primitives(&c_tilde);

            assert_eq!(ours, theirs,
                "T4 native via primitives must match reference SampleInBall (seed={seed})");
        }
    }

    /// Output structure sanity: exactly τ nonzero entries, each ±1.
    #[test]
    fn output_has_exactly_tau_nonzero_pm1() {
        let c_tilde = [0x42u8; crate::ml_dsa::params::C_TILDE_BYTES];
        let c = sample_in_ball_via_primitives(&c_tilde);
        let nonzero: Vec<u32> = c.iter().copied().filter(|&v| v != 0).collect();
        assert_eq!(nonzero.len(), TAU,
            "T4 primitive composition produced {} nonzero coefficients, expected τ = {}",
            nonzero.len(), TAU);
        for &v in &nonzero {
            assert!(v == 1 || v == Q - 1, "non-±1 coefficient: {v}");
        }
    }

    /// Determinism: same `c̃` yields same output.
    #[test]
    fn deterministic_on_input() {
        let c_tilde = [0x07u8; crate::ml_dsa::params::C_TILDE_BYTES];
        let a = sample_in_ball_via_primitives(&c_tilde);
        let b = sample_in_ball_via_primitives(&c_tilde);
        assert_eq!(a, b);
    }

    /// Different inputs yield different outputs (with overwhelming probability).
    #[test]
    fn distinct_inputs_yield_distinct_outputs() {
        let c0 = [0x11u8; crate::ml_dsa::params::C_TILDE_BYTES];
        let mut c1 = c0;
        c1[0] ^= 0xFF;
        assert_ne!(
            sample_in_ball_via_primitives(&c0),
            sample_in_ball_via_primitives(&c1),
        );
    }

    /// Provisioning: 5 rate-blocks of SHAKE-256 (680 bytes total)
    /// must suffice for the worst-case rejection-sampling depth in
    /// realistic ML-DSA-44 traces.  We sample many seeds to surface
    /// any provisioning gap empirically.
    #[test]
    fn provisioning_sufficient_for_64_seeds() {
        use crate::ml_dsa::params::C_TILDE_BYTES;
        for seed in 0u32..64 {
            let mut c_tilde = [0u8; C_TILDE_BYTES];
            for k in 0..C_TILDE_BYTES {
                c_tilde[k] = ((seed as u8).wrapping_mul(31)).wrapping_add(k as u8);
            }
            // Should not panic on any seed under our provisioning.
            let _ = sample_in_ball_via_primitives(&c_tilde);
        }
    }
}
