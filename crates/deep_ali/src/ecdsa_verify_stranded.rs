// ecdsa_verify_stranded.rs — LOW-MEMORY "stranded" PROVER PoC for the
// END-TO-END P256 ECDSA-verify AIR (`p256_ecdsa_verify_multirow_air`).
//
// ## What this is
//
// A memory optimisation of the *prover only*.  The monolithic verify
// AIR has ~196k columns (chain A = u1·G, chain B = u2·Q, plus a small
// TAIL that finishes the verify).  Proving it in one shot LDEs the
// whole ~196k-col trace at once → ~5.9 GB peak RSS at blowup=4.
//
// This module proves the SAME AIR as TWO column-group **strands**,
// each holding only its own columns' trace + LDE, so the peak LDE
// (the dominant allocation) is roughly halved.  The strands are bound
// by ONE out-of-domain (OOD) seam on the shared interface columns
// `r_a_proj` (chain A's projective output, consumed by the TAIL in
// strand B).  The result is a spliced proof that still verifies with
// the SAME soundness as the monolith.
//
// ## The strand cut
//
//   Strand A = chain-A columns  [step_a.acc_x_base .. step_b.acc_x_base)
//              + the shared interface columns r_a_proj (3·NUM_LIMBS).
//   Strand B = chain-B columns  [step_b.acc_x_base .. r_a_proj_x_base)
//              + r_a_proj (shared, consumed by the TAIL group_add)
//              + r_b_proj (produced AND consumed in strand B)
//              + the TAIL columns [dsm.width .. layout.width).
//
// `r_a_proj` is the ONE seam: it is bound to chain-A's true output in
// strand A (boundary at row k-1 + column-constancy) and consumed by
// the TAIL's group_add in strand B.  The OOD seam forces strand B's
// `r_a_proj` polynomial to equal strand A's, so the TAIL provably
// consumes chain A's real output.  `r_b_proj` never crosses strands,
// so it needs no seam.
//
// ## Why the cut is clean (no dropped constraint)
//
// The two `scalar_mul_step` chains are INDEPENDENT: chain A's
// constraints read only chain-A columns, chain B's only chain-B
// columns.  The TAIL gadgets read only r_a_proj / r_b_proj / TAIL
// columns.  The public-input pins split per chain (u1/G→A, u2/Q/r→B).
// Every constraint of the monolith lands in exactly one strand, and
// each strand's evaluator REUSES the monolith's gadget evaluators
// (`eval_scalar_mul_step_gadget`, `eval_group_add_gadget`, …) verbatim
// via a full-width scatter — so no constraint is re-derived or
// altered.  The only shared cells (r_a_proj) are bound by the seam.
//
// ## Soundness
//
//  * Each strand is a standard `sub_air_with_trace` proof: trace-LDE
//    Merkle commitment bound into pi_hash, per-query trace openings,
//    per-query `c_eval·Z_H == Σ α_j Φ_j` re-check.  A tampered strand
//    trace makes some Φ_j non-zero on H → the strand's FRI / per-query
//    check rejects.
//  * The seam uses `commit_binding_cells` + `verify_ood_consistency`
//    on each r_a_proj limb-column (single-column BCCs, exactly the
//    tested v2 pattern).  If strand A's and strand B's r_a_proj differ
//    as polynomials, the OOD check at the shared FS point z_0 rejects
//    (Schwartz-Zippel over F_ext).
//
// This module adds NO changes to the AIR, its evaluator, its filler,
// or the verifier core — it only orchestrates existing primitives.

#![allow(non_snake_case, clippy::too_many_arguments)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::p256_field::NUM_LIMBS;
use crate::p256_ecdsa_verify_multirow_air::{
    ecdsa_verify_tail_constraints, order_n_field, EcdsaVerifyMultirowLayout,
    EcdsaVerifyPublicInputs,
};
use crate::p256_scalar_mul_air::{
    eval_scalar_mul_step_gadget, scalar_mul_step_gadget_constraints,
};
use crate::p256_group_air::eval_group_add_gadget;
use crate::p256_field_air::{
    eval_add_gadget, eval_freeze_gadget, eval_mul_gadget, eval_select_gadget,
};
use crate::binding_cells_commit::{
    commit_binding_cells, verify_ood_consistency, BindingCellsCommit,
};
use crate::fri::DeepFriParams;
use crate::sub_air_with_trace::{
    prove_one_sub_air_with_trace_capturing, verify_one_sub_air_with_trace,
    SubAirProofWithTrace,
};

// ─── domain separators ───────────────────────────────────────────────

pub const DOMAIN_A: &[u8] = b"ecdsa_verify_stranded/strand_A/v1";
pub const DOMAIN_B: &[u8] = b"ecdsa_verify_stranded/strand_B/v1";
/// SAME separator on BOTH sides of the seam so the OOD points align.
pub const SEAM_SEP: &[u8] = b"ecdsa_verify_stranded/seam_r_a_proj/v1";

// ─── strand cut description ──────────────────────────────────────────

/// The column partition + per-strand constraint counts for the cut.
#[derive(Clone, Debug)]
pub struct StrandCut {
    /// Full-layout absolute column indices held by strand A.
    pub cols_a: Vec<usize>,
    /// Full-layout absolute column indices held by strand B.
    pub cols_b: Vec<usize>,
    /// Local indices (into `cols_a`) of the 30 r_a_proj limb columns,
    /// in canonical (x0..x9, y0..y9, z0..z9) order.
    pub ra_local_in_a: Vec<usize>,
    /// Local indices (into `cols_b`) of the same 30 r_a_proj columns.
    pub ra_local_in_b: Vec<usize>,
    pub num_constraints_a: usize,
    pub num_constraints_b: usize,
    pub k: usize,
    pub full_width: usize,
}

impl StrandCut {
    pub fn width_a(&self) -> usize {
        self.cols_a.len()
    }
    pub fn width_b(&self) -> usize {
        self.cols_b.len()
    }
}

/// Derive the strand cut from the full verify-AIR layout.
///
/// Relies on the (documented, contiguous) column allocation of
/// `build_ecdsa_verify_multirow_layout`:
///   [0, step_b.acc_x_base)          = chain A block
///   [step_b.acc_x_base, r_a_proj_x) = chain B block
///   [r_a_proj_x, +30)               = r_a_proj (seam)
///   [r_b_proj_x, +30)               = r_b_proj
///   [dsm.width, layout.width)       = TAIL block
pub fn compute_strand_cut(layout: &EcdsaVerifyMultirowLayout, k: usize) -> StrandCut {
    let d = &layout.dsm;
    let ra = 3 * NUM_LIMBS; // 30 r_a_proj limb columns (x,y,z)

    let chain_a: Vec<usize> = (d.step_a.acc_x_base..d.step_b.acc_x_base).collect();
    let chain_b: Vec<usize> = (d.step_b.acc_x_base..d.r_a_proj_x_base).collect();
    let ra_cols: Vec<usize> = (d.r_a_proj_x_base..d.r_a_proj_x_base + ra).collect();
    let rb_cols: Vec<usize> = (d.r_b_proj_x_base..d.r_b_proj_x_base + ra).collect();
    let tail_cols: Vec<usize> = (d.width..layout.width).collect();

    // strand A = chain A ++ r_a_proj
    let mut cols_a = chain_a;
    let ra_start_a = cols_a.len();
    cols_a.extend_from_slice(&ra_cols);
    let ra_local_in_a: Vec<usize> = (ra_start_a..ra_start_a + ra).collect();

    // strand B = chain B ++ r_a_proj ++ r_b_proj ++ TAIL
    let mut cols_b = chain_b;
    let ra_start_b = cols_b.len();
    cols_b.extend_from_slice(&ra_cols);
    cols_b.extend_from_slice(&rb_cols);
    cols_b.extend_from_slice(&tail_cols);
    let ra_local_in_b: Vec<usize> = (ra_start_b..ra_start_b + ra).collect();

    let step_c = scalar_mul_step_gadget_constraints(&d.step_a);
    let tail_c = ecdsa_verify_tail_constraints(layout);

    // Strand A constraints (see eval_strand_a): DSM-local(step_c)
    //  + boundary(30) + acc-transition(30) + r_a_proj constancy(30)
    //  + pins u1-bit(1) + Gx(10) + Gy(10).
    let num_constraints_a = step_c + 3 * ra + 1 + 2 * NUM_LIMBS;
    // Strand B constraints (see eval_strand_b): DSM-local(step_c)
    //  + boundary(30) + acc-transition(30) + r_b_proj constancy(30)
    //  + TAIL(tail_c) + pins u2-bit(1) + Qx(10) + Qy(10) + r(10).
    let num_constraints_b = step_c + 3 * ra + tail_c + 1 + 3 * NUM_LIMBS;

    StrandCut {
        cols_a,
        cols_b,
        ra_local_in_a,
        ra_local_in_b,
        num_constraints_a,
        num_constraints_b,
        k,
        full_width: layout.width,
    }
}

/// Extract a strand's trace (only its columns) from the full trace.
pub fn extract_strand_trace(full_trace: &[Vec<F>], cols: &[usize]) -> Vec<Vec<F>> {
    cols.iter().map(|&c| full_trace[c].clone()).collect()
}

// ─── per-strand evaluators (reuse monolith gadget evaluators) ────────

/// Scatter a strand-local row (indexed by the strand's local columns)
/// into a full-width row so the monolith's gadget evaluators (which
/// index by ABSOLUTE column positions) can be reused verbatim.  Cells
/// the strand does not hold stay zero — the gadgets never read them.
#[inline]
fn scatter(local: &[F], cols: &[usize], full_width: usize) -> Vec<F> {
    let mut full = vec![F::zero(); full_width];
    for (j, &c) in cols.iter().enumerate() {
        full[c] = local[j];
    }
    full
}

/// Strand-A per-row constraint evaluator.  `cur_local`/`nxt_local` are
/// strand-A-width rows.  Emits EXACTLY `num_constraints_a` values.
///
/// Scatters into a fresh full-width row then delegates to
/// `eval_strand_a_on_full`.  Used by the verifier (few calls).  The
/// hot prover path uses `eval_strand_a_on_full` directly with a reused
/// scatter buffer (see `strand_merge`).
pub fn eval_strand_a(
    cur_local: &[F],
    nxt_local: &[F],
    trace_row: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    cols_a: &[usize],
    k: usize,
) -> Vec<F> {
    let w = layout.width;
    let cur = scatter(cur_local, cols_a, w);
    let nxt = scatter(nxt_local, cols_a, w);
    eval_strand_a_on_full(&cur, &nxt, trace_row, layout, pub_inputs, k)
}

/// Strand-A evaluator body operating on FULL-WIDTH scattered rows (only
/// chain-A + r_a_proj positions are populated; the rest are zero and
/// never read by chain-A gadgets).
pub fn eval_strand_a_on_full(
    cur: &[F],
    nxt: &[F],
    trace_row: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    k: usize,
) -> Vec<F> {
    let d = &layout.dsm;

    let in_chain = trace_row < k;
    let is_chain_last = trace_row + 1 == k;
    let acc_link = trace_row + 1 < k;
    let rproj_link = trace_row < k;

    let mut out = Vec::new();

    // (1) DSM local — chain A step gadget (gated to chain rows).
    let local_a = scalar_mul_step_gadget_constraints(&d.step_a);
    if in_chain {
        out.extend(eval_scalar_mul_step_gadget(&cur, &d.step_a));
        debug_assert_eq!(out.len(), local_a);
    } else {
        out.resize(local_a, F::zero());
    }

    // (2) DSM boundary — chain A: bind select_a → r_a_proj at row k-1.
    for (chain_base, proj_base) in [
        (d.step_a.select_x.c_limbs_base, d.r_a_proj_x_base),
        (d.step_a.select_y.c_limbs_base, d.r_a_proj_y_base),
        (d.step_a.select_z.c_limbs_base, d.r_a_proj_z_base),
    ] {
        for i in 0..NUM_LIMBS {
            out.push(if is_chain_last {
                cur[chain_base + i] - cur[proj_base + i]
            } else {
                F::zero()
            });
        }
    }

    // (3) DSM acc transition — chain A: acc[r+1] = select[r].
    for (acc, sel) in [
        (d.step_a.acc_x_base, d.step_a.select_x.c_limbs_base),
        (d.step_a.acc_y_base, d.step_a.select_y.c_limbs_base),
        (d.step_a.acc_z_base, d.step_a.select_z.c_limbs_base),
    ] {
        for i in 0..NUM_LIMBS {
            out.push(if acc_link {
                nxt[acc + i] - cur[sel + i]
            } else {
                F::zero()
            });
        }
    }

    // (4) r_a_proj column-constancy (this is the seam column; strand A
    //     is its producer, so it enforces constancy here).
    for base in [d.r_a_proj_x_base, d.r_a_proj_y_base, d.r_a_proj_z_base] {
        for i in 0..NUM_LIMBS {
            out.push(if rproj_link {
                nxt[base + i] - cur[base + i]
            } else {
                F::zero()
            });
        }
    }

    // (5) Public-input pins — A: u1-bit, Gx, Gy (per chain row).
    out.push(if in_chain {
        cur[d.step_a.bit_cell] - pub_inputs.u1_bits[trace_row]
    } else {
        F::zero()
    });
    for i in 0..NUM_LIMBS {
        out.push(if in_chain {
            cur[d.step_a.base_x_base + i] - pub_inputs.gx[i]
        } else {
            F::zero()
        });
    }
    for i in 0..NUM_LIMBS {
        out.push(if in_chain {
            cur[d.step_a.base_y_base + i] - pub_inputs.gy[i]
        } else {
            F::zero()
        });
    }

    out
}

/// Strand-B per-row constraint evaluator.  Emits EXACTLY
/// `num_constraints_b` values.  Scatters then delegates (verifier path).
pub fn eval_strand_b(
    cur_local: &[F],
    nxt_local: &[F],
    trace_row: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    cols_b: &[usize],
    k: usize,
) -> Vec<F> {
    let w = layout.width;
    let cur = scatter(cur_local, cols_b, w);
    let nxt = scatter(nxt_local, cols_b, w);
    eval_strand_b_on_full(&cur, &nxt, trace_row, layout, pub_inputs, k)
}

/// Strand-B evaluator body operating on FULL-WIDTH scattered rows.
pub fn eval_strand_b_on_full(
    cur: &[F],
    nxt: &[F],
    trace_row: usize,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    k: usize,
) -> Vec<F> {
    let d = &layout.dsm;

    let in_chain = trace_row < k;
    let is_chain_last = trace_row + 1 == k;
    let is_tail = trace_row == k;
    let acc_link = trace_row + 1 < k;
    let rproj_link = trace_row < k;

    let mut out = Vec::new();

    // (1) DSM local — chain B step gadget.
    let local_b = scalar_mul_step_gadget_constraints(&d.step_b);
    if in_chain {
        out.extend(eval_scalar_mul_step_gadget(&cur, &d.step_b));
        debug_assert_eq!(out.len(), local_b);
    } else {
        out.resize(local_b, F::zero());
    }

    // (2) DSM boundary — chain B: bind select_b → r_b_proj at row k-1.
    for (chain_base, proj_base) in [
        (d.step_b.select_x.c_limbs_base, d.r_b_proj_x_base),
        (d.step_b.select_y.c_limbs_base, d.r_b_proj_y_base),
        (d.step_b.select_z.c_limbs_base, d.r_b_proj_z_base),
    ] {
        for i in 0..NUM_LIMBS {
            out.push(if is_chain_last {
                cur[chain_base + i] - cur[proj_base + i]
            } else {
                F::zero()
            });
        }
    }

    // (3) DSM acc transition — chain B.
    for (acc, sel) in [
        (d.step_b.acc_x_base, d.step_b.select_x.c_limbs_base),
        (d.step_b.acc_y_base, d.step_b.select_y.c_limbs_base),
        (d.step_b.acc_z_base, d.step_b.select_z.c_limbs_base),
    ] {
        for i in 0..NUM_LIMBS {
            out.push(if acc_link {
                nxt[acc + i] - cur[sel + i]
            } else {
                F::zero()
            });
        }
    }

    // (4) r_b_proj column-constancy (produced + consumed in strand B).
    //     NOTE: r_a_proj constancy is enforced in strand A; the seam
    //     binds A's r_a_proj poly to B's, so B needs no local r_a_proj
    //     constraint.
    for base in [d.r_b_proj_x_base, d.r_b_proj_y_base, d.r_b_proj_z_base] {
        for i in 0..NUM_LIMBS {
            out.push(if rproj_link {
                nxt[base + i] - cur[base + i]
            } else {
                F::zero()
            });
        }
    }

    // (5) TAIL at row k — reuse the monolith's tail gadget evaluators
    //     verbatim (they read r_a_proj / r_b_proj / TAIL columns, all
    //     present in strand B).
    let tail_count = ecdsa_verify_tail_constraints(layout);
    if is_tail {
        let start = out.len();
        out.extend(eval_group_add_gadget(&cur, &layout.group_add));
        out.extend(eval_add_gadget(&cur, &layout.add_rn));
        out.extend(eval_freeze_gadget(&cur, &layout.freeze_rn));
        out.extend(eval_mul_gadget(&cur, &layout.mul_r));
        out.extend(eval_mul_gadget(&cur, &layout.mul_rn));
        out.extend(eval_select_gadget(&cur, &layout.select));
        // R.X == selected.
        for i in 0..NUM_LIMBS {
            out.push(
                cur[layout.group_add.result_x3_limbs_base + i]
                    - cur[layout.select.c_limbs_base + i],
            );
        }
        // n column == n constant.
        let n_fe = order_n_field();
        for i in 0..NUM_LIMBS {
            out.push(cur[layout.n_const_base + i] - F::from(n_fe.limbs[i] as u64));
        }
        debug_assert_eq!(out.len() - start, tail_count);
    } else {
        let base = out.len();
        out.resize(base + tail_count, F::zero());
    }

    // (6) Public-input pins — B: u2-bit, Qx, Qy (chain rows), r (tail).
    out.push(if in_chain {
        cur[d.step_b.bit_cell] - pub_inputs.u2_bits[trace_row]
    } else {
        F::zero()
    });
    for i in 0..NUM_LIMBS {
        out.push(if in_chain {
            cur[d.step_b.base_x_base + i] - pub_inputs.qx[i]
        } else {
            F::zero()
        });
    }
    for i in 0..NUM_LIMBS {
        out.push(if in_chain {
            cur[d.step_b.base_y_base + i] - pub_inputs.qy[i]
        } else {
            F::zero()
        });
    }
    for i in 0..NUM_LIMBS {
        out.push(if is_tail {
            cur[layout.r_base + i] - pub_inputs.r[i]
        } else {
            F::zero()
        });
    }

    out
}

// ─── per-strand DEEP-ALI merge (c_eval on the strand LDE) ────────────

/// X^m − 1 polynomial division (copy of lib.rs `poly_div_zh`, which is
/// module-private).  Returns the quotient coefficients.
fn poly_div_zh_local(dividend: &[F], m: usize) -> Vec<F> {
    let n = dividend.len();
    if n <= m {
        return vec![F::zero()];
    }
    let q_len = n - m;
    let mut q = vec![F::zero(); q_len];
    for k in (m..n).rev() {
        let qk = if k < q_len { q[k] } else { F::zero() };
        q[k - m] = dividend[k] + qk;
    }
    q
}

/// Compute the strand's `c_eval` (= Φ̃/Z_H on the LDE) from the strand
/// LDE.  Mirrors `deep_ali_merge_ecdsa_verify_multirow_streaming` but
/// over the strand's LDE and constraint set.
///
/// MEMORY: the per-row constraint evaluators index by ABSOLUTE column
/// positions (so the monolith gadget evaluators can be reused
/// verbatim), which needs a full-width scattered row.  To avoid
/// allocating two `full_width` vectors on every one of the `n` LDE
/// points (crippling allocator churn under rayon), we allocate ONE
/// scatter buffer pair per worker thread and reuse it — only the
/// strand's `cols` positions are overwritten each row, and non-`cols`
/// positions stay zero (they are never read by this strand's gadgets).
fn strand_merge<E>(
    lde: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    comb_coeffs: &[F],
    full_width: usize,
    cols: &[usize],
    eval_on_full: E,
) -> Vec<F>
where
    E: Fn(&[F], &[F], usize) -> Vec<F> + Sync,
{
    let n = n_trace * blowup;
    let kc = comb_coeffs.len();
    for col in lde {
        assert_eq!(col.len(), n);
    }

    // Scatter LDE rows `i` and `i+blowup` into the reusable buffers,
    // evaluate the strand constraints, combine with comb_coeffs.
    let eval_at = |fc: &mut Vec<F>, fx: &mut Vec<F>, i: usize| -> F {
        let nxt_idx = (i + blowup) % n;
        for (j, &c) in cols.iter().enumerate() {
            fc[c] = lde[j][i];
            fx[c] = lde[j][nxt_idx];
        }
        let cvals = eval_on_full(fc, fx, i / blowup);
        debug_assert_eq!(cvals.len(), kc);
        let mut acc = F::zero();
        for j in 0..kc {
            acc += comb_coeffs[j] * cvals[j];
        }
        acc
    };

    let mk_bufs = || (vec![F::zero(); full_width], vec![F::zero(); full_width]);

    #[cfg(feature = "parallel")]
    let phi_eval: Vec<F> = (0..n)
        .into_par_iter()
        .map_init(mk_bufs, |(fc, fx), i| eval_at(fc, fx, i))
        .collect();
    #[cfg(not(feature = "parallel"))]
    let phi_eval: Vec<F> = {
        let (mut fc, mut fx) = mk_bufs();
        (0..n).map(|i| eval_at(&mut fc, &mut fx, i)).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh_local(&phi_coeffs, n_trace);
    let mut padded = c_coeffs;
    padded.resize(n, F::zero());
    domain.fft(&padded)
}

// ─── spliced proof bundle ────────────────────────────────────────────

/// A 2-strand spliced proof: one `sub_air_with_trace` proof per strand
/// plus the per-limb r_a_proj seam commitments (one BCC per limb from
/// each strand).
pub struct StrandedProof {
    pub proof_a: SubAirProofWithTrace,
    pub proof_b: SubAirProofWithTrace,
    /// r_a_proj limb-column commitments from strand A (len = 3·NUM_LIMBS).
    pub seam_a: Vec<BindingCellsCommit>,
    /// r_a_proj limb-column commitments from strand B (same order).
    pub seam_b: Vec<BindingCellsCommit>,
}

// ─── prove ───────────────────────────────────────────────────────────

/// Prove strand A: FRI-prove chain A + r_a_proj, and commit each
/// r_a_proj limb column for the seam.  The strand LDE (the dominant
/// allocation) is built inside, used for the seam commits, then
/// dropped before returning.
pub fn prove_strand_a<P>(
    strand_a: &[Vec<F>],
    cut: &StrandCut,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> (SubAirProofWithTrace, Vec<BindingCellsCommit>)
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    let (proof, lde, _tree) = prove_one_sub_air_with_trace_capturing(
        strand_a,
        n_trace,
        blowup,
        pi_hash,
        DOMAIN_A,
        cut.num_constraints_a,
        |lde, nt, bw, cc| {
            strand_merge(lde, nt, bw, cc, cut.full_width, &cut.cols_a, |c, x, r| {
                eval_strand_a_on_full(c, x, r, layout, pub_inputs, cut.k)
            })
        },
        params_fn,
    );

    let seam: Vec<BindingCellsCommit> = cut
        .ra_local_in_a
        .iter()
        .map(|&col| {
            commit_binding_cells(
                &lde, &[col], n_trace, blowup, pi_hash, SEAM_SEP, params_fn,
            )
            .0
        })
        .collect();

    (proof, seam)
}

/// Prove strand B: FRI-prove chain B + r_a_proj + r_b_proj + TAIL, and
/// commit each (shared) r_a_proj limb column for the seam.
pub fn prove_strand_b<P>(
    strand_b: &[Vec<F>],
    cut: &StrandCut,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> (SubAirProofWithTrace, Vec<BindingCellsCommit>)
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    let (proof, lde, _tree) = prove_one_sub_air_with_trace_capturing(
        strand_b,
        n_trace,
        blowup,
        pi_hash,
        DOMAIN_B,
        cut.num_constraints_b,
        |lde, nt, bw, cc| {
            strand_merge(lde, nt, bw, cc, cut.full_width, &cut.cols_b, |c, x, r| {
                eval_strand_b_on_full(c, x, r, layout, pub_inputs, cut.k)
            })
        },
        params_fn,
    );

    let seam: Vec<BindingCellsCommit> = cut
        .ra_local_in_b
        .iter()
        .map(|&col| {
            commit_binding_cells(
                &lde, &[col], n_trace, blowup, pi_hash, SEAM_SEP, params_fn,
            )
            .0
        })
        .collect();

    (proof, seam)
}

/// Prove both strands and assemble the spliced proof.  Strands are
/// proved SEQUENTIALLY so only one strand LDE is live at a time.
pub fn prove_stranded<P>(
    strand_a: &[Vec<F>],
    strand_b: &[Vec<F>],
    cut: &StrandCut,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> StrandedProof
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    let (proof_a, seam_a) = prove_strand_a(
        strand_a, cut, layout, pub_inputs, n_trace, blowup, pi_hash, params_fn,
    );
    let (proof_b, seam_b) = prove_strand_b(
        strand_b, cut, layout, pub_inputs, n_trace, blowup, pi_hash, params_fn,
    );
    StrandedProof {
        proof_a,
        proof_b,
        seam_a,
        seam_b,
    }
}

// ─── verify ──────────────────────────────────────────────────────────

/// Verify strand A alone (FRI + per-query trace-cell constraint check).
pub fn verify_strand_a<P>(
    proof: &SubAirProofWithTrace,
    cut: &StrandCut,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams,
{
    verify_one_sub_air_with_trace(
        proof,
        n_trace,
        blowup,
        pi_hash,
        DOMAIN_A,
        cut.width_a(),
        cut.num_constraints_a,
        |cur, nxt, row| eval_strand_a(cur, nxt, row, layout, pub_inputs, &cut.cols_a, cut.k),
        params_fn,
    )
    .map_err(|e| format!("strand A: {e}"))
}

/// Verify strand B alone.
pub fn verify_strand_b<P>(
    proof: &SubAirProofWithTrace,
    cut: &StrandCut,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams,
{
    verify_one_sub_air_with_trace(
        proof,
        n_trace,
        blowup,
        pi_hash,
        DOMAIN_B,
        cut.width_b(),
        cut.num_constraints_b,
        |cur, nxt, row| eval_strand_b(cur, nxt, row, layout, pub_inputs, &cut.cols_b, cut.k),
        params_fn,
    )
    .map_err(|e| format!("strand B: {e}"))
}

/// Verify the r_a_proj seam: every limb column of strand A's r_a_proj
/// must OOD-agree with strand B's at the shared FS point z_0.
pub fn verify_seam<P>(
    seam_a: &[BindingCellsCommit],
    seam_b: &[BindingCellsCommit],
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    if seam_a.len() != seam_b.len() {
        return Err(format!(
            "seam: commit count mismatch (a={}, b={})",
            seam_a.len(),
            seam_b.len()
        ));
    }
    for (i, (ca, cb)) in seam_a.iter().zip(seam_b.iter()).enumerate() {
        verify_ood_consistency(ca, cb, pi_hash, params_fn)
            .map_err(|e| format!("seam r_a_proj limb {i}: {e}"))?;
    }
    Ok(())
}

/// Verify a full spliced proof: both strands + the r_a_proj seam.
pub fn verify_stranded<P>(
    proof: &StrandedProof,
    cut: &StrandCut,
    layout: &EcdsaVerifyMultirowLayout,
    pub_inputs: &EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    verify_strand_a(
        &proof.proof_a, cut, layout, pub_inputs, n_trace, blowup, pi_hash, params_fn,
    )?;
    verify_strand_b(
        &proof.proof_b, cut, layout, pub_inputs, n_trace, blowup, pi_hash, params_fn,
    )?;
    verify_seam(&proof.seam_a, &proof.seam_b, pi_hash, params_fn)?;
    Ok(())
}

// ─── tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, fill_ecdsa_verify_multirow,
    };
    use crate::p256_field::FieldElement;
    use crate::p256_group::GENERATOR;

    // Small (K=4) end-to-end stranded prove/verify/tamper check.  Run
    // with `--release` (ark-ff 0.4.2 debug_assert blocker in dev).
    fn tparams(n0: usize, ph: [u8; 32]) -> DeepFriParams {
        DeepFriParams {
            schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
            r: 8,
            seed_z: 0xDEEFu64,
            coeff_commit_final: true,
            d_final: 1,
            stir: false,
            s0: 8,
            public_inputs_hash: Some(ph),
        }
    }

    fn z_one() -> FieldElement {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    }
    fn identity() -> (FieldElement, FieldElement, FieldElement) {
        let mut y = FieldElement::zero();
        y.limbs[0] = 1;
        (FieldElement::zero(), y, FieldElement::zero())
    }

    fn build_k4() -> (
        EcdsaVerifyMultirowLayout,
        StrandCut,
        Vec<Vec<F>>, // strand A
        Vec<Vec<F>>, // strand B
        EcdsaVerifyPublicInputs,
        usize, // n_trace
        [u8; 32],
    ) {
        let k = 4usize;
        let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
        let n_trace = (k + 1).next_power_of_two(); // 8
        let g = *GENERATOR;
        let q = g.double();
        let zo = z_one();
        let (ix, iy, iz) = identity();
        let a_bits = vec![true, false, true, true];
        let b_bits = vec![false, true, true, false];

        // Self-consistent r: fill once with placeholder, read x1, refill.
        let read_fe = |trace: &[Vec<F>], base: usize, row: usize| -> FieldElement {
            let mut limbs = [0i64; NUM_LIMBS];
            for i in 0..NUM_LIMBS {
                limbs[i] = trace[base + i][row].into_bigint().as_ref()[0] as i64;
            }
            FieldElement { limbs }
        };
        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g.x, &g.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits,
            &FieldElement::zero(),
        );
        let r_x3 = read_fe(&trace, layout.group_add.result_x3_limbs_base, k);
        let r_z3 = read_fe(&trace, layout.group_add.result_z3_limbs_base, k);
        let mut x1 = r_x3.mul(&r_z3.invert());
        x1.freeze();
        let r_fe = x1;

        let mut trace = vec![vec![F::zero(); n_trace]; total];
        fill_ecdsa_verify_multirow(
            &mut trace, &layout, n_trace,
            (&ix, &iy, &iz), (&g.x, &g.y, &zo), &a_bits,
            (&ix, &iy, &iz), (&q.x, &q.y, &zo), &b_bits,
            &r_fe,
        );
        let pubin =
            EcdsaVerifyPublicInputs::new(&a_bits, &b_bits, &g.x, &g.y, &q.x, &q.y, &r_fe);

        let cut = compute_strand_cut(&layout, k);
        let sa = extract_strand_trace(&trace, &cut.cols_a);
        let sb = extract_strand_trace(&trace, &cut.cols_b);
        (layout, cut, sa, sb, pubin, n_trace, [0x42u8; 32])
    }

    use ark_ff::PrimeField;

    #[test]
    fn stranded_k4_honest_accepts_and_tampers_reject() {
        let blowup = 4usize;
        let (layout, cut, strand_a, strand_b, pubin, n_trace, pi_hash) = build_k4();
        let params = |n0: usize, ph: [u8; 32]| tparams(n0, ph);

        // Column-count gate (d).
        assert!(cut.width_a() + cut.width_b() >= layout.width);

        // (a) honest → accept.
        let proof = prove_stranded(
            &strand_a, &strand_b, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params,
        );
        verify_stranded(&proof, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params)
            .expect("honest stranded proof must accept");

        // (b1) tamper a chain-B cell → reject.
        {
            let mut bad = strand_b.clone();
            bad[0][1] += F::from(1u64);
            let (pb, sb) =
                prove_strand_b(&bad, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params);
            let spliced = StrandedProof {
                proof_a: proof.proof_a.clone(),
                proof_b: pb,
                seam_a: proof.seam_a.clone(),
                seam_b: sb,
            };
            let res =
                verify_stranded(&spliced, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params);
            assert!(res.is_err(), "chain-B tamper must reject: {res:?}");
        }

        // (b2) tamper r_a_proj in strand A → reject (constancy + seam).
        {
            let mut bad = strand_a.clone();
            let ra0 = cut.ra_local_in_a[0];
            bad[ra0][0] += F::from(1u64);
            let (pa, sa) =
                prove_strand_a(&bad, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params);
            let spliced = StrandedProof {
                proof_a: pa,
                proof_b: proof.proof_b.clone(),
                seam_a: sa,
                seam_b: proof.seam_b.clone(),
            };
            let res =
                verify_stranded(&spliced, &cut, &layout, &pubin, n_trace, blowup, pi_hash, params);
            assert!(res.is_err(), "r_a_proj tamper must reject: {res:?}");
        }
    }
}
