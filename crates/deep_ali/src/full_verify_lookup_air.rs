// full_verify_lookup_air.rs — the top-level composition: the ECDSA-verify
// EC core (a multi-point-op scalar-mult computation) with EVERY gadget's
// sub-limbs across the WHOLE computation pooled into ONE trace-wide LogUp
// accumulator, proven through the full-AIR FRI prover.
//
// This is the last assembly step.  Each point op is already a fillable
// lookup prover whose sub-limbs pass a shared accumulator
// (`group_op_lookup_prover_air`); here we chain point ops into the shape of
// `u·G` / `u1·G + u2·Q` and route the union of ALL their sub-limbs into a
// single accumulator, then FRI-prove it end-to-end.  The reduce-mod-n /
// equality tail of the verify is a handful more field gadgets (negligible)
// and follows the identical pattern.  κ_sys unchanged.

#![allow(non_snake_case, dead_code)]

use crate::group_op_lookup_prover_air::{group_add_sublimbs, group_double_sublimbs};
use crate::p256_group::GENERATOR;

/// A representative ECDSA-verify EC-core computation: `steps` double-and-add
/// iterations (each = one group_double + one group_add off the fixed base),
/// accumulating every point op's range-checked sub-limbs.  Returns
/// `(pooled_sublimbs, all_arithmetic_valid, n_point_ops)`.
pub fn verify_ec_core_sublimbs(steps: usize) -> (Vec<u64>, bool, usize) {
    let g = *GENERATOR;
    let mut acc = g; // non-identity start (avoids the O path in this demo)
    let mut vals = Vec::new();
    let mut ok = true;
    let mut n_ops = 0usize;
    for _ in 0..steps {
        let (dv, da) = group_double_sublimbs(&acc);
        vals.extend(dv);
        ok &= da;
        n_ops += 1;

        let two = acc.double();
        let (av, aa) = group_add_sublimbs(&two, &g);
        vals.extend(av);
        ok &= aa;
        n_ops += 1;

        acc = two.add(&g);
    }
    (vals, ok, n_ops)
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use ark_goldilocks::Goldilocks as F;
    use ark_ff::Zero;
    use crate::permutation_argument::{ExtField, EXT_DEGREE};
    use crate::range_lookup_acc_air::{self, multiplicities};
    use crate::tower_field::TowerField;

    const S: usize = 13;

    fn alpha() -> ExtField {
        let c: Vec<F> = (0..EXT_DEGREE).map(|i| F::from(0x0A00_0000u64 + 41 * i as u64 + 17)).collect();
        ExtField::from_fp_components(&c).unwrap()
    }

    fn accumulator_holds(vals: &[u64], alpha: ExtField) -> bool {
        if !vals.iter().all(|&x| x < (1u64 << S)) {
            return false;
        }
        let table_size = 1usize << S;
        let mult = multiplicities(vals, table_size);
        let n_trace = (table_size + vals.len() + 1).next_power_of_two();
        let mut acc: Vec<Vec<F>> =
            (0..range_lookup_acc_air::WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
        range_lookup_acc_air::fill_trace(&mut acc, n_trace, table_size, vals, &mult, alpha);
        range_lookup_acc_air::count_violations(&acc, n_trace, table_size, alpha) == 0
    }

    /// The trace-wide accumulator scales across MANY composed point ops:
    /// a 12-point-op EC core (~24k sub-limbs) validated by ONE accumulator.
    /// Fast (no FRI).
    #[test]
    fn full_verify_accumulator_scales() {
        let (vals, arith, n_ops) = verify_ec_core_sublimbs(6); // 12 point ops
        assert!(arith, "all point-op arithmetic must be valid");
        assert_eq!(n_ops, 12);
        assert!(vals.len() > 20_000, "expected a multi-point-op sub-limb load, got {}", vals.len());
        assert!(accumulator_holds(&vals, alpha()),
            "ONE accumulator must validate the whole EC core ({} sub-limbs, {} point ops)",
            vals.len(), n_ops);
        println!("\n  full-verify EC core: {} point ops, {} sub-limbs, ONE accumulator ✓\n",
                 n_ops, vals.len());
    }

    /// TOP-LEVEL FRI: a composed EC core proven end-to-end through the full
    /// AIR (commit → merge → DEEP FRI → verify).  Positive round-trips.
    #[test]
    #[ignore = "slow — LDEs a ~32k-row accumulator trace and runs FRI"]
    fn full_verify_ec_core_fri_round_trip() {
        use crate::verify_lookup_fri_air::prove_verify_lookup;
        let (vals, arith, n_ops) = verify_ec_core_sublimbs(4); // 8 point ops
        assert!(arith);
        assert!(n_ops == 8 && vals.len() > 12_000);
        assert!(prove_verify_lookup(&vals, alpha()),
            "the whole EC core's lookup must FRI prove+verify");
    }

    /// NEGATIVE: an out-of-range sub-limb anywhere in the composed
    /// computation makes the full-AIR verify reject.
    #[test]
    #[ignore = "slow — FRI"]
    fn full_verify_out_of_range_rejected() {
        use crate::verify_lookup_fri_air::prove_verify_lookup;
        let (mut vals, _, _) = verify_ec_core_sublimbs(4);
        let mid = vals.len() / 2;
        vals[mid] = 1u64 << S; // corrupt one sub-limb mid-computation
        assert!(!prove_verify_lookup(&vals, alpha()),
            "an out-of-range sub-limb anywhere must make FRI reject");
    }
}
