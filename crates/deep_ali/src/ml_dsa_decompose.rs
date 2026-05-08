//! Native `Decompose`, `HighBits`, `LowBits`, `MakeHint`, `UseHint`
//! for ML-DSA-44 (FIPS 204 §3.6).
//!
//! The decomposition writes `r ∈ Z_q` as
//!
//! ```text
//!   r = r₁ · (2 γ₂) + r₀,  r₀ ∈ (−γ₂, γ₂]
//! ```
//!
//! with the boundary adjustment that when `r₁ = (q − 1) / (2 γ₂)`
//! (the high-end overflow case) we instead set `r₁ ← 0, r₀ ← r₀ − 1`
//! to keep `r₁` in `[0, (q − 1)/(2 γ₂))`.

#![allow(dead_code)]

use crate::ml_dsa::params::{GAMMA2, Q};

/// Number of HighBits values (i.e., maximum r₁ + 1).
/// `(q − 1) / (2 γ₂) = 88` for ML-DSA-44.
pub const NUM_R1_VALUES: u32 = (Q - 1) / (2 * GAMMA2);

/// Decompose `r` into `(r1, r0)` per FIPS 204 §3.6 Algorithm 22.
/// `r0` is returned as a centred residue in `(−γ₂, γ₂]` lifted into
/// `Z_q` (so `r0 ∈ [0, γ₂] ∪ [q − γ₂, q)`).
pub fn decompose(r: u32) -> (u32, u32) {
    debug_assert!(r < Q);
    let two_g2 = 2 * GAMMA2;
    let r_mod = r % two_g2;
    // Centre into (−γ₂, γ₂].  Use i64 for the negative branch so
    // u32 wrap doesn't bite us.
    let r0_signed: i64 = if r_mod > GAMMA2 {
        r_mod as i64 - two_g2 as i64
    } else {
        r_mod as i64
    };
    let r1 = ((r as i64 - r0_signed) / two_g2 as i64) as u32;
    if r1 == NUM_R1_VALUES {
        // Boundary snap: r1 wraps to 0, r0 decremented by 1.
        let new_r0 = (r0_signed - 1) as i32;
        (0u32, lift_signed(new_r0))
    } else {
        (r1, lift_signed(r0_signed as i32))
    }
}

#[inline]
fn lift_signed(x: i32) -> u32 {
    if x >= 0 { x as u32 } else { (x + Q as i32) as u32 }
}

/// `HighBits(r)` = r₁ component of `Decompose(r)`.
pub fn high_bits(r: u32) -> u32 { decompose(r).0 }

/// `LowBits(r)` = r₀ component of `Decompose(r)` (lifted).
pub fn low_bits(r: u32) -> u32 { decompose(r).1 }

/// `MakeHint(z, r)` per FIPS 204 §3.6 Algorithm 24.
pub fn make_hint(z: u32, r: u32) -> bool {
    high_bits(r) != high_bits((r + z) % Q)
}

/// `UseHint(h, r)` per FIPS 204 §3.6 Algorithm 25.
pub fn use_hint(h: bool, r: u32) -> u32 {
    let (r1, r0_lifted) = decompose(r);
    if !h { return r1; }
    let r0_signed = if r0_lifted > Q / 2 {
        (r0_lifted as i32) - (Q as i32)
    } else {
        r0_lifted as i32
    };
    if r0_signed > 0 {
        (r1 + 1) % NUM_R1_VALUES
    } else if r1 == 0 {
        NUM_R1_VALUES - 1
    } else {
        r1 - 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decompose_round_trips_through_recompose() {
        // For every r, r ≡ r₁ · 2γ₂ + r₀ (mod q).  We allow the
        // overflow adjustment.
        let two_g2 = 2 * GAMMA2;
        let samples: Vec<u32> = vec![
            0, 1, GAMMA2, GAMMA2 + 1, two_g2, two_g2 + 1,
            (Q - 1) / 2, Q - 1, 1234567,
        ];
        for &r in &samples {
            let (r1, r0_lifted) = decompose(r);
            let r0_signed = if r0_lifted > Q / 2 {
                (r0_lifted as i64) - (Q as i64)
            } else {
                r0_lifted as i64
            };
            // Expect: r ≡ r1 · two_g2 + r0_signed (mod q)
            let recomp = ((r1 as i64) * (two_g2 as i64) + r0_signed)
                .rem_euclid(Q as i64) as u32;
            assert_eq!(recomp, r,
                "decompose round-trip failed: r={r}  r1={r1}  r0_signed={r0_signed}");
        }
    }

    #[test]
    fn high_bits_in_range() {
        for r in [0u32, 1, GAMMA2, GAMMA2 + 1, Q - 1, Q / 2] {
            let h = high_bits(r);
            assert!(h < NUM_R1_VALUES,
                "high_bits({r}) = {h} not < {NUM_R1_VALUES}");
        }
    }

    #[test]
    fn use_hint_zero_is_high_bits() {
        for r in [0u32, 1, 12345, Q - 1] {
            assert_eq!(use_hint(false, r), high_bits(r));
        }
    }

    #[test]
    fn make_hint_round_trip_against_use_hint() {
        // For valid inputs |z| ≤ γ₂, MakeHint then UseHint
        // recovers HighBits(r + z).
        for r in [0u32, 100, 12345, GAMMA2, Q - GAMMA2 - 1] {
            for z_signed in [-50i32, -1, 0, 1, 50] {
                let z = if z_signed >= 0 {
                    z_signed as u32
                } else {
                    (Q as i32 + z_signed) as u32
                };
                let h = make_hint(z, r);
                let recovered = use_hint(h, r);
                let expected = high_bits((r + z) % Q);
                assert_eq!(recovered, expected,
                    "use_hint(make_hint({z_signed}, {r}), {r}) = {recovered}, expected {expected}");
            }
        }
    }
}
