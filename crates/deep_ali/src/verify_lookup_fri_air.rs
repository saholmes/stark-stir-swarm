// verify_lookup_fri_air.rs — top-level assembly through the FRI merge.
//
// Runs the LogUp range-check accumulator — loaded with a REAL group_add's
// sub-limbs — end-to-end through the actual prover: LDE → generic per-row
// merge (`deep_ali_merge_per_row_no_layout`) → deep_fri_prove →
// deep_fri_verify.  This closes the loop: the multi-row lookup argument
// (the soundness-critical, previously only unit-tested component) is now
// FRI-proven on genuine point-op data.
//
// The point-op LOCAL constraints (sub-limb-pack + RCB arithmetic) are
// single-row and already proven satisfiable+sound in the fillable-gadget
// modules; the multi-row ACCUMULATOR is the part that requires the FRI
// merge to enforce the global lookup, so proving IT through FRI is exactly
// the missing end-to-end validation.  κ_sys unchanged (the challenge α is
// fixed here for the round-trip; production derives it in F_ext via the
// same T-MEM Fiat–Shamir path).

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;

use crate::deep_ali_merge_per_row_no_layout;
use crate::fri::DeepFriParams;
use crate::permutation_argument::ExtField;
use crate::range_lookup_acc_air::{self, eval_per_row, multiplicities, NUM_CONSTRAINTS, WIDTH};
use crate::sub_air_with_trace::{prove_one_sub_air_with_trace, verify_one_sub_air_with_trace};

const S: usize = 13; // sub-limb bits → table [0, 2^13)

fn fri_params(n0: usize, _aug: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r: 8,
        seed_z: 0xDEEF,
        coeff_commit_final: true,
        d_final: 1,
        stir: false,
        s0: 8,
        public_inputs_hash: Some([0u8; 32]),
    }
}

/// Build the accumulator trace for `vals` and run it through the FULL AIR
/// prover: commit trace → merge → DEEP FRI → verify (trace openings +
/// c_eval·Z_H = phi per query, which ENFORCES the constraints).  Returns
/// whether it verifies.
pub fn prove_verify_lookup(vals: &[u64], alpha: ExtField) -> bool {
    let table_size = 1usize << S;
    let mult = multiplicities(vals, table_size);
    let n_trace = (table_size + vals.len() + 1).next_power_of_two();
    let blowup = 4usize;

    let mut trace: Vec<Vec<F>> = (0..WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
    range_lookup_acc_air::fill_trace(&mut trace, n_trace, table_size, vals, &mult, alpha);

    let pi_hash = [0u8; 32];
    let ds: &[u8] = b"logup-rangecheck";
    // Per-row constraint evaluator, shared verbatim by prover and verifier.
    let ec = |cur: &[F], nxt: &[F], row: usize| eval_per_row(cur, nxt, row, table_size, alpha);

    let proof = prove_one_sub_air_with_trace(
        &trace, n_trace, blowup, pi_hash, ds, NUM_CONSTRAINTS,
        |lde, nt, bl, coeffs| {
            deep_ali_merge_per_row_no_layout(lde, coeffs, F::from(1u64), nt, bl, WIDTH, NUM_CONSTRAINTS, &ec).0
        },
        fri_params,
    );

    verify_one_sub_air_with_trace(
        &proof, n_trace, blowup, pi_hash, ds, WIDTH, NUM_CONSTRAINTS, &ec, fri_params,
    )
    .is_ok()
}

// ═══════════════════════════════════════════════════════════════════
//  Tests
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::group_op_lookup_prover_air::group_add_sublimbs;
    use crate::p256_group::GENERATOR;
    use crate::permutation_argument::EXT_DEGREE;
    use crate::tower_field::TowerField;

    fn alpha() -> ExtField {
        let c: Vec<F> = (0..EXT_DEGREE).map(|i| F::from(0x0900_0000u64 + 37 * i as u64 + 5)).collect();
        ExtField::from_fp_components(&c).unwrap()
    }

    /// TOP-LEVEL: a real group_add's range-check load, proven through the
    /// actual FRI merge + prove + verify.
    #[test]
    #[ignore = "slow — LDEs the 16k-row accumulator trace and runs FRI"]
    fn group_add_lookup_fri_round_trip() {
        let g = *GENERATOR;
        let p1 = g.double().add(&g);           // 3G
        let p2 = g.double().double().add(&g);   // 5G
        let (vals, arith) = group_add_sublimbs(&p1, &p2);
        assert!(arith, "real group_add arithmetic must be valid");
        assert!(vals.len() > 2000);

        let ok = prove_verify_lookup(&vals, alpha());
        assert!(ok, "the group_add lookup accumulator must FRI prove+verify");
    }

    /// NEGATIVE: an out-of-range sub-limb makes the accumulator boundary
    /// non-vanishing, so the composition is not low-degree and FRI rejects.
    #[test]
    #[ignore = "slow — FRI on the accumulator trace"]
    fn out_of_range_sublimb_fails_fri() {
        let g = *GENERATOR;
        let p1 = g.double().add(&g);
        let p2 = g.double().double().add(&g);
        let (mut vals, _) = group_add_sublimbs(&p1, &p2);
        vals[0] = 1u64 << S; // out of range → uncancellable pole
        let ok = prove_verify_lookup(&vals, alpha());
        assert!(!ok, "out-of-range sub-limb must make FRI reject");
    }
}
