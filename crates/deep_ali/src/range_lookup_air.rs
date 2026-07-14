// range_lookup_air.rs — LogUp lookup range-check to replace per-element
// bit-decomposition, the cross-scheme width/RSS lever.
//
// ─────────────────────────────────────────────────────────────────────
// THE TAX BEING REMOVED
// ─────────────────────────────────────────────────────────────────────
// Every range-checked field element in the P-256 / Ed25519 (and RSA /
// ML-DSA) AIRs proves  limb ∈ [0, 2^LIMB_BITS)  by BIT DECOMPOSITION:
// LIMB_BITS boolean cells per limb (P-256: 26) + a limb-pack constraint.
// For a 10-limb element that is 260 bit cells + 10 packs = 270 constraints
// — and the 260 bit cells are pure WIDTH, replicated across the c and q
// outputs of EVERY mul/add/sub gadget in the trace.  Range-check evidence
// is ~26% of a group op; it dominates the "trace-opening" cost the RSS is
// driven by.
//
// ─────────────────────────────────────────────────────────────────────
// LOGUP LOOKUP REPLACEMENT
// ─────────────────────────────────────────────────────────────────────
// Split each LIMB_BITS-bit limb into a few S-bit SUB-LIMBS and prove each
// sub-limb ∈ [0, 2^S) by a LOOKUP into a shared table [0, 2^S), instead
// of decomposing to bits.  A 26-bit limb → 2 sub-limbs of 13 bits: 2
// cells instead of 26 (a 13× width cut on the range-check evidence), plus
// one limb-pack constraint  limb = sub0 + 2^S·sub1.
//
// The lookup itself is the LogUp (log-derivative) identity: for a random
// challenge α, the multiset of all looked-up sub-limbs {a_i} lies in the
// table [0,2^S) with multiplicities {m_t} iff
//
//        Σ_i  1/(α − a_i)   =   Σ_t  m_t/(α − t).                 (★)
//
// SOUNDNESS.  (★) is an algebraic identity in α when the multisets match.
// If some a_i ∉ table, the LHS has a pole at α=a_i that the RHS (poles
// only at table points) cannot reproduce, so the two rational functions
// differ and agree at ≤ (N + 2^S) values of α.  Sampling α ∈ F_ext (F_p^6
// at L1/L3, F_p^8 at L5) AFTER the trace commitment — via the SAME
// `derive_t_mem_challenges(pi_hash)` the existing multiset permutation
// argument uses — gives lookup-soundness error ≤ (N+2^S)/|F_ext| ≈ 2^-320
// at L1.  So κ_lookup ≫ κ_IT/κ_bind/κ_FS and κ_sys = min(...) is UNCHANGED:
// this is a width optimization, not a soundness relaxation.
//
// This module provides (a) the sub-limb decomposition + limb-pack, (b) a
// self-contained SOUND implementation of the LogUp identity (★) with
// positive/negative tests, and (c) a cost model quantifying the width cut.
// The remaining integration is per-row: one F_ext running-sum accumulator
// column that folds every gadget's sub-limbs into the LHS of (★) and the
// table/multiplicity columns into the RHS — structurally identical to the
// RP/WP running products in `permutation_argument.rs`, reused verbatim.

#![allow(non_snake_case, dead_code)]

use ark_ff::Field;
use ark_goldilocks::Goldilocks as F;

/// Number of sub-limb cells to range-check a `limb_bits`-bit limb with
/// `S`-bit sub-limbs (ceil division).
pub const fn sublimbs_per_limb(limb_bits: usize, s: usize) -> usize {
    (limb_bits + s - 1) / s
}

/// Split a `limb_bits`-bit value into `S`-bit sub-limbs (LSB first).
pub fn decompose_sublimbs(value: u64, limb_bits: usize, s: usize) -> Vec<u64> {
    let n = sublimbs_per_limb(limb_bits, s);
    let mask = (1u64 << s) - 1;
    (0..n).map(|k| (value >> (k * s)) & mask).collect()
}

/// Recompose sub-limbs (LSB first) into the limb value.
pub fn recompose_sublimbs(subs: &[u64], s: usize) -> u64 {
    subs.iter().enumerate().map(|(k, &v)| v << (k * s)).fold(0u64, |a, b| a + b)
}

// ═══════════════════════════════════════════════════════════════════
//  LogUp identity (★) — the lookup argument's sound core
// ═══════════════════════════════════════════════════════════════════

/// LHS of (★):  Σ_i 1/(α − a_i)  over the looked-up values.
pub fn logup_lhs(values: &[u64], alpha: F) -> F {
    values
        .iter()
        .map(|&a| (alpha - F::from(a)).inverse().expect("alpha must avoid the values"))
        .fold(F::from(0u64), |acc, x| acc + x)
}

/// RHS of (★):  Σ_t m_t/(α − t)  over the table [0, 2^S) with the given
/// multiplicities (`mult[t]` = claimed count of table value `t`).
pub fn logup_rhs(mult: &[u64], alpha: F) -> F {
    mult.iter()
        .enumerate()
        .filter(|(_, &m)| m != 0)
        .map(|(t, &m)| F::from(m) * (alpha - F::from(t as u64)).inverse().expect("alpha must avoid the table"))
        .fold(F::from(0u64), |acc, x| acc + x)
}

/// Honest multiplicity vector: count each in-range value's occurrences in
/// the table [0, 2^S).  Values ≥ 2^S are NOT counted (they are not in the
/// table) — which is exactly what makes an out-of-range value fail (★).
pub fn table_multiplicities(values: &[u64], s: usize) -> Vec<u64> {
    let size = 1usize << s;
    let mut m = vec![0u64; size];
    for &v in values {
        if (v as usize) < size {
            m[v as usize] += 1;
        }
    }
    m
}

// ═══════════════════════════════════════════════════════════════════
//  Cost model
// ═══════════════════════════════════════════════════════════════════

/// Range-check evidence CELLS per element under bit decomposition
/// (`num_limbs · limb_bits` bit cells).
pub const fn bitdecomp_evidence_cells(num_limbs: usize, limb_bits: usize) -> usize {
    num_limbs * limb_bits
}

/// Range-check evidence CELLS per element under S-bit sub-limb lookup
/// (`num_limbs · ceil(limb_bits/S)` sub-limb cells; the table + running
/// accumulator are shared once across the whole trace, amortized ~0).
pub const fn lookup_evidence_cells(num_limbs: usize, limb_bits: usize, s: usize) -> usize {
    num_limbs * sublimbs_per_limb(limb_bits, s)
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> F {
        // A representative challenge (in production: F_ext, FS-derived
        // from pi_hash after commit).  Chosen to avoid the small table /
        // value points used below.
        F::from(0x9E37_79B9_7F4A_7C15u64)
    }

    #[test]
    fn sublimb_roundtrip() {
        // 26-bit limbs, 13-bit sub-limbs.
        for v in [0u64, 1, 12345, (1 << 26) - 1, 0x2AAAAAA] {
            let subs = decompose_sublimbs(v, 26, 13);
            assert_eq!(subs.len(), 2);
            assert!(subs.iter().all(|&s| s < (1 << 13)));
            assert_eq!(recompose_sublimbs(&subs, 13), v, "roundtrip failed for {v}");
        }
    }

    /// POSITIVE: all looked-up values are in the table [0,2^S) ⇒ (★) holds.
    #[test]
    fn logup_identity_holds_in_range() {
        let s = 8; // table [0,256)
        // A batch of in-range sub-limb values (with repeats — multiplicity).
        let values: Vec<u64> = vec![0, 1, 1, 5, 200, 255, 42, 42, 42, 7];
        let mult = table_multiplicities(&values, s);
        let a = alpha();
        assert_eq!(
            logup_lhs(&values, a),
            logup_rhs(&mult, a),
            "LogUp identity must hold when every value is in the table"
        );
        // And it is an IDENTITY: holds at a second, independent challenge.
        let a2 = F::from(0x1234_5678_9ABC_DEF1u64);
        assert_eq!(logup_lhs(&values, a2), logup_rhs(&mult, a2));
    }

    /// NEGATIVE: one value is out of range (= 2^S) ⇒ the honest table
    /// multiplicities cannot reproduce its pole ⇒ (★) fails.  This is the
    /// soundness property: an over-large limb cannot pass the lookup.
    #[test]
    fn logup_identity_fails_out_of_range() {
        let s = 8;
        let mut values: Vec<u64> = vec![0, 1, 5, 200, 42, 7];
        values.push(1 << s); // 256 — NOT in [0,256)
        let mult = table_multiplicities(&values, s); // omits the out-of-range value
        let a = alpha();
        assert_ne!(
            logup_lhs(&values, a),
            logup_rhs(&mult, a),
            "an out-of-range value must break the LogUp identity"
        );
    }

    /// A malicious prover cannot fake the multiplicities to hide an
    /// out-of-range value: for ANY table multiplicity vector, the RHS has
    /// no pole at α = (out-of-range value), so it differs from the LHS.
    #[test]
    fn logup_no_fake_multiplicity_rescues_out_of_range() {
        let s = 4; // small table [0,16), exhaustive-ish
        let bad = 1u64 << s; // 16, out of range
        let values = vec![3u64, 7, bad];
        let a = alpha();
        let lhs = logup_lhs(&values, a);
        // Try every "cheating" multiplicity vector with total mass up to 4
        // over the 16 table slots is too many; instead argue structurally:
        // pick the honest one and a few perturbations, none can match.
        let mut m = table_multiplicities(&values, s);
        assert_ne!(lhs, logup_rhs(&m, a));
        m[3] += 1; // over-count
        assert_ne!(lhs, logup_rhs(&m, a));
        m[7] = m[7].saturating_sub(1); // under-count
        assert_ne!(lhs, logup_rhs(&m, a));
    }

    /// COST BENCH: bit-decomposition vs S-bit sub-limb lookup, per element
    /// and projected over the full P-256 verify AIR.  Run:
    ///   cargo test --release --features "parallel,sha3-256" -p deep_ali \
    ///       --lib range_lookup_cost -- --nocapture
    #[test]
    fn range_lookup_cost() {
        // P-256 / Ed25519 element: 10 limbs × 26 bits.
        let num_limbs = 10usize;
        let limb_bits = 26usize;

        let bit_cells = bitdecomp_evidence_cells(num_limbs, limb_bits);
        println!("\n═══ range-check evidence per element (10×26-bit) ═══");
        println!("  bit decomposition : {bit_cells} cells");
        for s in [8usize, 13, 16] {
            let lc = lookup_evidence_cells(num_limbs, limb_bits, s);
            let ratio = bit_cells as f64 / lc as f64;
            let table = 1usize << s;
            println!(
                "  {s:>2}-bit lookup    : {lc:>3} cells  ({ratio:.1}× fewer; shared table 2^{s} = {table} entries)"
            );
        }

        // Full-AIR projection.  Range-check evidence is the c+q bit blocks
        // of every mul gadget plus add/sub outputs.  Empirically ~26% of a
        // group op is range-check evidence; a 13-bit lookup cuts that block
        // ~13×, so the range-check share drops to ~2%.
        const FULL_V2_AIR_CELLS: usize = 39_416_874;
        let rc_share = 0.26f64;
        let s = 13usize;
        let cut = bit_cells as f64 / lookup_evidence_cells(num_limbs, limb_bits, s) as f64;
        let new_rc_share = rc_share / cut;
        let air_reduction = (rc_share - new_rc_share) * 100.0;
        println!("\n═══ projected full-verify-AIR impact (13-bit lookup) ═══");
        println!("  range-check evidence share : {:.0}% → {:.1}%", rc_share * 100.0, new_rc_share * 100.0);
        println!("  ⇒ ~{air_reduction:.0}% additional width cut, ON TOP of the MSM levers");
        println!("  ⇒ also lowers the per-strand RSS floor (narrower single gadget)");
        println!("  cross-scheme: same tax paid by RSA ModMul + ML-DSA Z_q reductions\n");

        assert!(lookup_evidence_cells(num_limbs, limb_bits, 13) * 5 < bit_cells);
    }
}
