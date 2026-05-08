//! NTT orchestration: emits the FieldOp sequence corresponding to
//! a 256-point Cooley-Tukey forward / inverse NTT, ready to feed
//! into `ml_dsa_field_air::fill_trace`.
//!
//! **Phase 6 v1 — informational scaffolding only.**  The AIR
//! proper would need cross-row memory constraints (each butterfly's
//! output is read by a butterfly two stages later) to bind values
//! across rows.  Building those constraints is non-trivial — it's a
//! permutation / memory argument analogous to the ones used in
//! Cairo / RISC-V STARKs.  We skip that for v1: the verify AIR
//! treats NTT as a native pre-computation (prover commits the
//! NTT-domain polynomials as public inputs) and the AIR proves
//! only the final pointwise equation.
//!
//! This emitter is therefore documentation + testing infrastructure.
//! It cross-checks that the FieldOp sequence we'd emit matches the
//! native NTT result (so that when the chained-AIR version lands, we
//! have a pre-validated reference oracle).

#![allow(dead_code)]

use crate::ml_dsa::params::N;
use crate::ml_dsa_field::{add_q, mul_q, sub_q};
use crate::ml_dsa_field_air::FieldOp;
use crate::ml_dsa_ntt::compute_zetas;
use crate::ml_dsa::params::Q;

/// One full 256-point NTT consumes this many `FieldOp` rows of the
/// field-AIR.  3 ops per butterfly × 128 butterflies × 8 stages = 3072.
pub const NTT_FIELD_AIR_ROWS: usize = 3072;

/// One full inverse NTT plus the final `1/N` scaling pass.
pub const NTT_INV_FIELD_AIR_ROWS: usize = NTT_FIELD_AIR_ROWS + N;

/// Emit the FieldOp sequence for a forward NTT applied to `input`.
/// Returns `(ops, output)` where `output` is the NTT-domain
/// polynomial — equal to `ntt(input)` from `ml_dsa_ntt`.
pub fn ntt_field_ops(input: &[u32; N]) -> (Vec<FieldOp>, [u32; N]) {
    let mut a = *input;
    let zetas = compute_zetas();
    let mut ops = Vec::with_capacity(NTT_FIELD_AIR_ROWS);

    let mut k = 0usize;
    let mut len = 128usize;
    while len > 0 {
        let mut start = 0usize;
        while start < N {
            k += 1;
            let zeta = zetas[k];
            for j in start..start + len {
                let a_low  = a[j];
                let a_high = a[j + len];
                let t = mul_q(zeta, a_high);
                ops.push(FieldOp::Mul { a: zeta,  b: a_high });
                ops.push(FieldOp::Sub { a: a_low, b: t      });
                ops.push(FieldOp::Add { a: a_low, b: t      });
                a[j]       = add_q(a_low, t);
                a[j + len] = sub_q(a_low, t);
            }
            start += 2 * len;
        }
        len >>= 1;
    }
    (ops, a)
}

/// Emit the FieldOp sequence for an inverse NTT.  Mirrors
/// `ml_dsa_ntt::ntt_inv`; includes the final 1/N scaling pass as
/// `N` MUL ops.
pub fn ntt_inv_field_ops(input: &[u32; N]) -> (Vec<FieldOp>, [u32; N]) {
    let mut a = *input;
    let zetas = compute_zetas();
    let mut ops = Vec::with_capacity(NTT_INV_FIELD_AIR_ROWS);

    let mut k = N;
    let mut len = 1usize;
    while len < N {
        let mut start = 0usize;
        while start < N {
            k -= 1;
            let zeta = Q - zetas[k];
            for j in start..start + len {
                let a_low  = a[j];
                let a_high = a[j + len];
                let s = sub_q(a_low, a_high);
                ops.push(FieldOp::Add { a: a_low, b: a_high });
                ops.push(FieldOp::Sub { a: a_low, b: a_high });
                ops.push(FieldOp::Mul { a: zeta,  b: s      });
                a[j]       = add_q(a_low, a_high);
                a[j + len] = mul_q(zeta, s);
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    const N_INV: u32 = 8_347_681;
    for v in a.iter_mut() {
        ops.push(FieldOp::Mul { a: N_INV, b: *v });
        *v = mul_q(N_INV, *v);
    }
    (ops, a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa_ntt;

    #[test]
    fn ntt_field_ops_count_is_correct() {
        let input = [0u32; N];
        let (ops, _) = ntt_field_ops(&input);
        assert_eq!(ops.len(), NTT_FIELD_AIR_ROWS);
    }

    #[test]
    fn ntt_field_ops_output_matches_native() {
        let mut input = [0u32; N];
        for i in 0..N {
            input[i] = (i as u32 * 12345) % Q;
        }
        let (_, emitted) = ntt_field_ops(&input);

        let mut expected = input;
        ml_dsa_ntt::ntt(&mut expected);

        assert_eq!(emitted, expected);
    }

    #[test]
    fn ntt_inv_field_ops_round_trip() {
        let mut input = [0u32; N];
        for i in 0..N {
            input[i] = (i as u32 * 7919) % Q;
        }
        let (_, ntt_out) = ntt_field_ops(&input);
        let (_, restored) = ntt_inv_field_ops(&ntt_out);
        assert_eq!(restored, input);
    }

    #[test]
    fn ntt_inv_field_ops_count_includes_n_scaling() {
        let input = [0u32; N];
        let (ops, _) = ntt_inv_field_ops(&input);
        assert_eq!(ops.len(), NTT_INV_FIELD_AIR_ROWS);
    }
}
