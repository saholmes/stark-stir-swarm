//! Native arithmetic in Z_q for q = 8_380_417 (FIPS 204 §3.7).
//!
//! Coefficients are 23-bit; embedding in our Goldilocks base field
//! is straightforward (every `u32` < q fits in one Goldilocks cell).
//! Used as the reference against `ml_dsa_field_air`.
//!
//! Conventions: `add_q`, `sub_q`, `mul_q` accept inputs in [0, q) and
//! return outputs in [0, q).  `from_signed` lifts a centred-residue
//! `i32` in (-q/2, q/2] into [0, q); `to_signed` is its inverse.

#![allow(dead_code)]

use crate::ml_dsa::params::Q;

/// Reduce a u64 product mod q; both inputs assumed < q so the
/// product fits in 46 bits and a single subtraction suffices after
/// the modular reduction.
#[inline]
pub fn mul_q(a: u32, b: u32) -> u32 {
    debug_assert!(a < Q && b < Q);
    let prod = (a as u64) * (b as u64);
    (prod % (Q as u64)) as u32
}

#[inline]
pub fn add_q(a: u32, b: u32) -> u32 {
    debug_assert!(a < Q && b < Q);
    let s = a + b;
    if s >= Q { s - Q } else { s }
}

#[inline]
pub fn sub_q(a: u32, b: u32) -> u32 {
    debug_assert!(a < Q && b < Q);
    if a >= b { a - b } else { a + Q - b }
}

#[inline]
pub fn neg_q(a: u32) -> u32 {
    debug_assert!(a < Q);
    if a == 0 { 0 } else { Q - a }
}

/// Lift a centred residue (-q/2, q/2] into [0, q).
#[inline]
pub fn from_signed(x: i32) -> u32 {
    debug_assert!(x as i64 > -(Q as i64) && (x as i64) < (Q as i64));
    if x >= 0 { x as u32 } else { (x + (Q as i32)) as u32 }
}

/// Drop into centred residue (-q/2, q/2].  Useful for norm checks.
#[inline]
pub fn to_signed(x: u32) -> i32 {
    debug_assert!(x < Q);
    if x > Q / 2 { (x as i32) - (Q as i32) } else { x as i32 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_wraps_correctly() {
        assert_eq!(add_q(Q - 1, 1), 0);
        assert_eq!(add_q(Q - 1, 2), 1);
    }

    #[test]
    fn sub_wraps_correctly() {
        assert_eq!(sub_q(0, 1), Q - 1);
        assert_eq!(sub_q(3, 5), Q - 2);
    }

    #[test]
    fn mul_matches_bigint() {
        let cases: &[(u32, u32)] = &[
            (1, 1), (2, 3), (Q - 1, Q - 1), (1234567, 7654321),
        ];
        for &(a, b) in cases {
            let expected = ((a as u64) * (b as u64)) % (Q as u64);
            assert_eq!(mul_q(a, b) as u64, expected);
        }
    }

    #[test]
    fn signed_round_trip() {
        for x in &[-3, -1, 0, 1, 1_000_000, (Q as i32) / 2 - 1] {
            let lifted = from_signed(*x);
            assert!(lifted < Q);
            assert_eq!(to_signed(lifted), *x);
        }
    }

    #[test]
    fn neg_is_additive_inverse() {
        for &x in &[0u32, 1, 17, 1_000, Q - 1] {
            assert_eq!(add_q(x, neg_q(x)), 0);
        }
    }
}
