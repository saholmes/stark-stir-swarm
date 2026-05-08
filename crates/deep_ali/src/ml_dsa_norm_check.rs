//! Native infinity-norm bound check.
//!
//! Used by ML-DSA verify to enforce `‖z‖∞ < γ₁ − β` (FIPS 204
//! §3 Algorithm 3 step 8).  A coefficient `c ∈ Z_q` is "in bounds"
//! iff its centred residue satisfies `|c'| < bound`, equivalently
//! `c' ∈ (−bound, bound)`.

#![allow(dead_code)]

use crate::ml_dsa::params::{BETA, GAMMA1, Q};

/// Bound used for `‖z‖∞ < γ₁ − β` in Algorithm 3 step 8.
pub const Z_BOUND: u32 = GAMMA1 - (BETA as u32);

/// Returns `true` iff the centred residue of `c` (mod q) lies in
/// `(−bound, bound)`.
pub fn coeff_in_norm(c: u32, bound: u32) -> bool {
    debug_assert!(c < Q);
    let centred = if c > Q / 2 {
        (c as i64) - (Q as i64)
    } else {
        c as i64
    };
    centred.unsigned_abs() < bound as u64
}

/// Returns `true` iff every coefficient of `poly` passes the bound.
pub fn poly_in_norm(poly: &[u32], bound: u32) -> bool {
    poly.iter().all(|&c| coeff_in_norm(c, bound))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boundary_cases() {
        // |c'| < bound ⇒ pass
        assert!(coeff_in_norm(0, 100));
        assert!(coeff_in_norm(99, 100));
        assert!(!coeff_in_norm(100, 100));
        // Negative side via wrap
        assert!(coeff_in_norm(Q - 99, 100));
        assert!(!coeff_in_norm(Q - 100, 100));
    }

    #[test]
    fn z_bound_is_correct() {
        // Z_BOUND = γ₁ − β, level-dependent:
        // L1 (mldsa-44): 2¹⁷ − 78 = 130994
        // L3 (mldsa-65): 2¹⁹ − 196 = 524092
        // L5 (mldsa-87): 2¹⁹ − 120 = 524168
        assert_eq!(Z_BOUND, GAMMA1 - (BETA as u32));
        #[cfg(feature = "mldsa-44")]
        assert_eq!(Z_BOUND, 130994);
        #[cfg(feature = "mldsa-65")]
        assert_eq!(Z_BOUND, 524092);
        #[cfg(feature = "mldsa-87")]
        assert_eq!(Z_BOUND, 524168);
    }
}
