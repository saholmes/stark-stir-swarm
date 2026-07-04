// ml_dsa_v17_stranded.rs — low-memory STRANDED prover/verifier for the
// ML-DSA v2 **V17** sub-AIR (`ml_dsa_verify_air_v17`).
//
// ## Why V17 is stranded
//
// The monolithic V17 sub-AIR is `WIDTH = 341` columns (L5) × `16384` pow2
// rows, proven as ONE Fp8 FRI at r=108.  That single prove sets the whole
// low-mem ML-DSA-87 prover's peak (~1247 MiB > 1 GB); every other v2
// sub-AIR proves < 1 GB.  This module cuts the V17 prove into pieces so no
// single FRI processes all 341 columns at once, and each piece is proved
// one-at-a-time (fill / prove / commit / drop) so the peak collapses to the
// largest single piece.
//
// ## V17's actual structure (read from the layout / evaluator / filler)
//
// V17 has FIVE regions stacked by ROW band, gated by 3 selector columns
// (COL_SEL_EQ=0, COL_SEL_NORM=1, COL_SEL_NTT=2):
//
//   * Region A "EQ"   — cols `[EQ_BASE, EQ_BASE+EQ_WIDTH)`  (poly-arith)
//   * Region B "NORM" — cols `[NORM_BASE, NORM_BASE+NORM_WIDTH)` (norm-check)
//   * Region C "NTT"  — cols `[NTT_BASE, NTT_BASE+NTT_WIDTH)`, L chained-NTT
//     instances (one per response poly `z_l`), each 1025 rows.
//
// Crucially — unlike Ed25519's phase-overlay (shared low columns) — V17's
// three regions occupy **DISJOINT column ranges AND disjoint row bands**,
// and every per-row constraint reads ONLY its own region's columns plus its
// own selector column (see `v17::eval_per_row`: Region A is gated by
// `sel_eq` and reads EQ cols; Region B by `sel_norm`, NORM cols; Region C
// by `sel_ntt`, NTT cols).  So the column-group cut has **ZERO cross-strand
// seams**: no column is read by two strands.
//
//   * Cols `[0, NTT_BASE)` = `{sel_eq, sel_norm, sel_ntt}` ∪ EQ ∪ NORM are a
//     contiguous PREFIX, held by the "TOP" strand.  It owns the FIRST
//     `TOP_NC = 3 + EQ_NC + NORM_NC` constraints of `v17::eval_per_row`'s
//     output (the 3 selector booleans + Region A + Region B); the NTT
//     suffix is discarded (hybrid-slice of the VERIFIED monolith evaluator,
//     exactly the Ed25519 pattern).  The TOP strand stays at the monolith
//     domain (16384) so the **L5 EQ-region binding is byte-identical** (its
//     BCCs pack only the a_ntt / c_ntt / t1d_ntt / w_approx_ntt COLUMN
//     values, which are unchanged — `commit_binding_cells` is
//     column-index-independent).
//
//   * The NTT region (Region C) is the memory floor (260 of 341 cols at
//     L5).  A 256-point NTT butterfly network fully couples all 256 state
//     columns (every state index is paired with a far index at some stage),
//     so NO column partition keeps butterflies within-group — the NTT
//     region CANNOT be column-group split.  Instead it is proven as its L
//     NATURAL INSTANCES at the reduced chained-NTT domain (2048 rows),
//     REUSING the existing, verified `ml_dsa_ntt_chained_air` +
//     `deep_ali_merge_t7_chained_ntt` (the exact machinery v2 already uses
//     for its INTT sub-AIRs).  Each instance proves
//     `z_ntt[l] = NTT(z_cleartext[l])` — identical per-row constraint
//     content to Region C instance `l`.
//
// ## Constraint-cut completeness
//
// The monolith's per-row constraint vector is
//   `[sel_eq_bool, sel_norm_bool, sel_ntt_bool, Region A (EQ_NC),
//     Region B (NORM_NC), Region C (NTT_NC)]`   (len = v17::NUM_CONSTRAINTS)
// The TOP strand owns the prefix `[0, TOP_NC)` and each NTT instance owns a
// Region-C `NTT_NC`-block, so the DISTINCT constraint blocks partition the
// monolith exactly: `TOP_NC + NTT_NC == v17::NUM_CONSTRAINTS` (asserted in
// `assert_cut_complete`).
//
// ## Soundness
//
//   * Each piece is a standard `sub_air_with_trace` proof (trace-LDE Merkle
//     commitment folded into pi_hash, per-query trace openings, per-query
//     `c_eval·Z_H == Σ αⱼ Φⱼ` re-check).  Tampering any interior cell makes
//     some Φⱼ non-zero on H → that piece rejects.
//   * No cross-strand seams are needed (regions are column-disjoint).
//   * The L5 EQ-region F2b binding is re-pointed to the TOP strand's LDE
//     (byte-identical BCCs); the verifier's existing L5 OOD check is
//     UNCHANGED.
//   * Splitting loses nothing the monolith enforced: the monolith's per-row
//     constraints already do NOT couple the three regions (only the
//     selector booleans and the external L5 BCC bind anything), so the
//     pieces prove exactly the monolith's cryptographic content.
//
// This module changes NOTHING in the V17 evaluator's math, the sub-AIR
// prove/verify primitives, the L5 binding logic, or any other sub-AIR — it
// only orchestrates existing primitives.

#![allow(non_snake_case, clippy::too_many_arguments, clippy::type_complexity)]

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::ml_dsa::params::{K, L, N};
use crate::ml_dsa_verify_air_v17 as v17;
use crate::ml_dsa_ntt_chained_air as ntt;
use crate::ml_dsa_verify_air as eq_air;

use crate::binding_cells_commit::commit_binding_cells;
use crate::fri::DeepFriParams;
use crate::sub_air_with_trace::{
    deserialize_proof, prove_one_sub_air_with_trace_capturing, serialize_proof,
    verify_one_sub_air_with_trace,
};

// ─── Cut geometry ──────────────────────────────────────────────────

/// TOP strand = the contiguous column prefix `{sel_eq, sel_norm, sel_ntt}
/// ∪ EQ ∪ NORM` = `[0, NTT_BASE)`.
pub const TOP_WIDTH: usize = v17::NTT_BASE;

/// Constraints owned by the TOP strand: 3 selector booleans + Region A
/// (EQ) + Region B (NORM) — the prefix of `v17::eval_per_row`'s output.
pub const TOP_NC: usize = 3 + eq_air::NUM_CONSTRAINTS + ml_dsa_norm_nc();

const fn ml_dsa_norm_nc() -> usize {
    crate::ml_dsa_norm_check_air::NUM_CONSTRAINTS
}

/// The NTT instances are proven at the chained-NTT sub-AIR's natural
/// domain (same as v2's INTT sub-AIRs).
pub fn ntt_instance_n_trace() -> usize {
    (ntt::BUTTERFLIES_PER_NTT + 16).next_power_of_two()
}

/// Domain separators (distinct FS context per piece).
pub const TOP_SEP: &[u8] = b"v17_top";
pub fn ntt_instance_sep(l: usize) -> Vec<u8> {
    let mut v = b"v17_ntt:".to_vec();
    v.push(l as u8);
    v
}

/// Magic prefix marking a stranded-V17 blob packed into `fri_v17`
/// (a monolithic `serialize_proof` never begins with this).
pub const V17_STRANDED_MAGIC: [u8; 4] = *b"V17S";

/// Assert the constraint cut partitions the monolith exactly.
pub fn assert_cut_complete() {
    assert_eq!(
        TOP_NC + ntt::NUM_CONSTRAINTS,
        v17::NUM_CONSTRAINTS,
        "V17 cut incomplete: TOP_NC ({}) + NTT_NC ({}) != monolith ({})",
        TOP_NC,
        ntt::NUM_CONSTRAINTS,
        v17::NUM_CONSTRAINTS,
    );
}

// ─── TOP-strand evaluator (hybrid-slice of the VERIFIED monolith) ──

/// NATIVE TOP-strand evaluator: computes ONLY the strand's owned
/// constraint prefix — the 3 selector booleans + Region A (poly-arith,
/// gated by `sel_eq`) + Region B (norm-check, gated by `sel_norm`) —
/// reading ONLY the strand's `[0, TOP_WIDTH)` LOCAL columns (== global,
/// since TOP_COLS is the `[0, NTT_BASE)` prefix).  This is the exact
/// prefix of `v17::eval_per_row`'s output (see `ml_dsa_verify_air_v17`,
/// lines "1." + "2." + "3."), transcribed verbatim, but WITHOUT the
/// Region C (chained-NTT) block — so it never computes butterflies or
/// `compute_zetas`, and never touches the 260 NTT columns.
///
/// Byte-identical to `v17::eval_per_row(&scatter, .., row)[..TOP_NC]`
/// (asserted by `native_top_matches_v17` for every row).
#[inline]
fn eval_top(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    use ark_ff::One;
    let one = F::one();
    let mut out = Vec::with_capacity(TOP_NC);

    let sel_eq = cur[v17::COL_SEL_EQ];
    let sel_norm = cur[v17::COL_SEL_NORM];
    let sel_ntt = cur[v17::COL_SEL_NTT];

    // 1. Three selector booleans.
    out.push(sel_eq * (sel_eq - one));
    out.push(sel_norm * (sel_norm - one));
    out.push(sel_ntt * (sel_ntt - one));

    // 2. Region A — poly-arithmetic, gated by sel_eq (reads EQ cols).
    let eq_view: Vec<F> = (0..v17::EQ_WIDTH).map(|c| cur[v17::EQ_BASE + c]).collect();
    let nxt_eq: Vec<F> = (0..v17::EQ_WIDTH).map(|c| nxt[v17::EQ_BASE + c]).collect();
    for v in eq_air::eval_per_row(&eq_view, &nxt_eq, row) {
        out.push(sel_eq * v);
    }

    // 3. Region B — norm-check, gated by sel_norm (reads NORM cols).
    let norm_view: Vec<F> = (0..v17::NORM_WIDTH).map(|c| cur[v17::NORM_BASE + c]).collect();
    let norm_nxt: Vec<F> = (0..v17::NORM_WIDTH).map(|c| nxt[v17::NORM_BASE + c]).collect();
    for v in crate::ml_dsa_norm_check_air::eval_per_row(
        &norm_view, &norm_nxt, row, crate::ml_dsa_norm_check::Z_BOUND,
    ) {
        out.push(sel_norm * v);
    }

    debug_assert_eq!(out.len(), TOP_NC);
    out
}

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

/// DEEP-ALI merge for the TOP strand (mirrors `deep_ali_merge_ml_dsa_v17`
/// but evaluates only the TOP prefix over the narrow TOP-width LDE).
fn top_merge(lde: &[Vec<F>], n_trace: usize, blowup: usize, comb_coeffs: &[F]) -> Vec<F> {
    let n = n_trace * blowup;
    let kc = comb_coeffs.len();
    debug_assert_eq!(kc, TOP_NC);
    for col in lde {
        assert_eq!(col.len(), n);
    }
    // Persistent narrow (TOP_WIDTH) row buffers per thread; the native
    // evaluator reads only these — no full-width scatter, no NTT compute.
    let eval_at = |lc: &mut Vec<F>, lx: &mut Vec<F>, i: usize| -> F {
        let nxt_idx = (i + blowup) % n;
        for j in 0..TOP_WIDTH {
            lc[j] = lde[j][i];
            lx[j] = lde[j][nxt_idx];
        }
        let cvals = eval_top(lc, lx, i / blowup);
        let mut acc = F::zero();
        for j in 0..kc {
            acc += comb_coeffs[j] * cvals[j];
        }
        acc
    };
    let mk_bufs = || (vec![F::zero(); TOP_WIDTH], vec![F::zero(); TOP_WIDTH]);

    #[cfg(feature = "parallel")]
    let phi_eval: Vec<F> = (0..n)
        .into_par_iter()
        .map_init(mk_bufs, |(lc, lx), i| eval_at(lc, lx, i))
        .collect();
    #[cfg(not(feature = "parallel"))]
    let phi_eval: Vec<F> = {
        let (mut lc, mut lx) = mk_bufs();
        (0..n).map(|i| eval_at(&mut lc, &mut lx, i)).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh_local(&phi_coeffs, n_trace);
    let mut padded = c_coeffs;
    padded.resize(n, F::zero());
    domain.fft(&padded)
}

// ─── Blob (de)serialization ────────────────────────────────────────

fn put_vec(out: &mut Vec<u8>, v: &[u8]) {
    out.extend_from_slice(&(v.len() as u32).to_le_bytes());
    out.extend_from_slice(v);
}
fn take_vec(data: &[u8], pos: &mut usize) -> Result<Vec<u8>, String> {
    if *pos + 4 > data.len() {
        return Err("v17-stranded: truncated length".into());
    }
    let len = u32::from_le_bytes(data[*pos..*pos + 4].try_into().unwrap()) as usize;
    *pos += 4;
    if *pos + len > data.len() {
        return Err("v17-stranded: truncated body".into());
    }
    let v = data[*pos..*pos + len].to_vec();
    *pos += len;
    Ok(v)
}

/// A stranded V17 proof: TOP strand + L NTT-instance sub-proofs.
pub struct V17StrandedProof {
    pub top: Vec<u8>,
    pub ntt: Vec<Vec<u8>>,
}

impl V17StrandedProof {
    pub fn to_blob(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&V17_STRANDED_MAGIC);
        put_vec(&mut out, &self.top);
        out.extend_from_slice(&(self.ntt.len() as u32).to_le_bytes());
        for p in &self.ntt {
            put_vec(&mut out, p);
        }
        out
    }
    pub fn from_blob(data: &[u8]) -> Result<Self, String> {
        if data.len() < 4 || data[..4] != V17_STRANDED_MAGIC {
            return Err("v17-stranded: bad magic".into());
        }
        let mut pos = 4usize;
        let top = take_vec(data, &mut pos)?;
        if pos + 4 > data.len() {
            return Err("v17-stranded: truncated ntt count".into());
        }
        let n = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap()) as usize;
        pos += 4;
        let mut ntt = Vec::with_capacity(n);
        for _ in 0..n {
            ntt.push(take_vec(data, &mut pos)?);
        }
        Ok(Self { top, ntt })
    }
}

/// Is this `fri_v17` blob a stranded proof?
pub fn is_stranded(fri_v17: &[u8]) -> bool {
    fri_v17.len() >= 4 && fri_v17[..4] == V17_STRANDED_MAGIC
}

// ─── Prover ────────────────────────────────────────────────────────

/// Prove V17 stranded, one piece at a time (fill / prove / commit /
/// drop), and build the L5 EQ-region BCCs from the TOP strand's LDE.
///
/// Returns `(fri_v17_blob, l5_v17_eq_bccs)` where `fri_v17_blob` is the
/// magic-tagged stranded bundle to place in `V2ProofReal::fri_v17`, and
/// the BCCs are byte-identical to the monolith's (packed from the same
/// a_ntt / c_ntt / t1d_ntt / w_approx_ntt column values at domain 16384).
pub fn prove_v17_stranded<P>(
    a_ntt: &[[[u32; N]; L]; K],
    z_ntt: &[[u32; N]; L],
    c_ntt: &[u32; N],
    t1d_ntt: &[[u32; N]; K],
    w_approx_ntt: &[[u32; N]; K],
    z_cleartext: &[[u32; N]; L],
    pi_hash: [u8; 32],
    blowup: usize,
    params_fn: P,
) -> (Vec<u8>, Vec<Vec<u8>>)
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    assert_cut_complete();
    let v17_n_trace = v17::VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();

    // ── TOP strand (selectors + EQ + NORM) @ 16384 → prove + L5 BCCs ──
    let (top_bytes, l5_bccs) = {
        // Build the full V17 trace (reuses the tested filler) then keep
        // only the TOP prefix columns; the full trace is dropped before
        // the LDE/prove phase.
        let mut full: Vec<Vec<F>> = (0..v17::WIDTH)
            .map(|_| vec![F::zero(); v17_n_trace])
            .collect();
        v17::fill_trace(
            &mut full, v17_n_trace, a_ntt, z_ntt, c_ntt, t1d_ntt, w_approx_ntt, z_cleartext,
        );
        let mut top_trace: Vec<Vec<F>> = Vec::with_capacity(TOP_WIDTH);
        for c in 0..TOP_WIDTH {
            top_trace.push(std::mem::take(&mut full[c]));
        }
        drop(full);

        let (proof, lde, _tree) = prove_one_sub_air_with_trace_capturing(
            &top_trace,
            v17_n_trace,
            blowup,
            pi_hash,
            TOP_SEP,
            TOP_NC,
            |lde, nt, bw, cc| top_merge(lde, nt, bw, cc),
            params_fn,
        );
        drop(top_trace);
        let top_bytes = serialize_proof(&proof);
        drop(proof);

        // L5 EQ-region binding: re-pointed to the TOP strand's LDE.
        // TOP_COLS == [0, TOP_WIDTH) with local index == global index,
        // so the EQ columns sit at `EQ_BASE + col_*` exactly as in the
        // monolith V17 LDE → byte-identical BCCs.
        let eq_base = v17::EQ_BASE;
        let mut bccs = Vec::with_capacity(L + 3);
        for ll in 0..L {
            let col_idx = eq_base + eq_air::col_a_ntt(ll);
            let ds = format!("l5_v17_a_ntt_{ll}").into_bytes();
            let (commit, _) = commit_binding_cells(
                &lde, &[col_idx], v17_n_trace, blowup, pi_hash, &ds, params_fn,
            );
            bccs.push(commit.to_bytes());
        }
        for (col_fn, ds) in [
            (eq_air::col_c_ntt(), b"l5_v17_c_ntt" as &[u8]),
            (eq_air::col_t1d_ntt(), b"l5_v17_t1d_ntt"),
            (eq_air::col_w_approx_ntt(), b"l5_v17_w_approx_ntt"),
        ] {
            let col_idx = eq_base + col_fn;
            let (commit, _) = commit_binding_cells(
                &lde, &[col_idx], v17_n_trace, blowup, pi_hash, ds, params_fn,
            );
            bccs.push(commit.to_bytes());
        }
        drop(lde);
        (top_bytes, bccs)
    };

    // ── NTT region as L instances @ reduced domain (2048) ──
    let ntt_n = ntt_instance_n_trace();
    let mut ntt_proofs: Vec<Vec<u8>> = Vec::with_capacity(L);
    for l in 0..L {
        let mut sub: Vec<Vec<F>> = (0..ntt::WIDTH).map(|_| vec![F::zero(); ntt_n]).collect();
        ntt::fill_trace(&mut sub, ntt_n, &z_cleartext[l]);
        let sep = ntt_instance_sep(l);
        let (proof, _lde, _tree) = prove_one_sub_air_with_trace_capturing(
            &sub,
            ntt_n,
            blowup,
            pi_hash,
            &sep,
            ntt::NUM_CONSTRAINTS,
            |lde, nt, bw, cc| {
                crate::deep_ali_merge_t7_chained_ntt(lde, cc, F::zero(), nt, bw).0
            },
            params_fn,
        );
        drop(sub);
        ntt_proofs.push(serialize_proof(&proof));
    }

    let blob = V17StrandedProof { top: top_bytes, ntt: ntt_proofs }.to_blob();
    (blob, l5_bccs)
}

// ─── Verifier ──────────────────────────────────────────────────────

/// Verify a stranded-V17 `fri_v17` blob: the TOP strand + L NTT
/// instances.  (The L5 EQ-region OOD binding is verified UNCHANGED by
/// the caller's existing L5 check against `l5_v17_eq_bccs`.)
pub fn verify_v17_stranded<P>(
    fri_v17: &[u8],
    pi_hash: [u8; 32],
    blowup: usize,
    params_fn: P,
) -> Result<(), String>
where
    P: Fn(usize, [u8; 32]) -> DeepFriParams + Copy,
{
    assert_cut_complete();
    let bundle = V17StrandedProof::from_blob(fri_v17)?;
    if bundle.ntt.len() != L {
        return Err(format!(
            "v17-stranded: expected {L} NTT instances, got {}",
            bundle.ntt.len()
        ));
    }
    let v17_n_trace = v17::VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();

    // TOP strand.
    let top = deserialize_proof(&bundle.top)?;
    verify_one_sub_air_with_trace(
        &top,
        v17_n_trace,
        blowup,
        pi_hash,
        TOP_SEP,
        TOP_WIDTH,
        TOP_NC,
        |cur, nxt, row| eval_top(cur, nxt, row),
        params_fn,
    )
    .map_err(|e| format!("v17-stranded TOP: {e}"))?;

    // NTT instances.
    let ntt_n = ntt_instance_n_trace();
    for l in 0..L {
        let p = deserialize_proof(&bundle.ntt[l])?;
        let sep = ntt_instance_sep(l);
        verify_one_sub_air_with_trace(
            &p,
            ntt_n,
            blowup,
            pi_hash,
            &sep,
            ntt::WIDTH,
            ntt::NUM_CONSTRAINTS,
            |cur, nxt, row| ntt::eval_per_row(cur, nxt, row),
            params_fn,
        )
        .map_err(|e| format!("v17-stranded NTT[{l}]: {e}"))?;
    }
    Ok(())
}

// ─── Tests ─────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::PrimeField;

    /// The NATIVE top-strand evaluator is BYTE-IDENTICAL to the prefix
    /// `[0, TOP_NC)` of the VERIFIED monolith `v17::eval_per_row` — for
    /// arbitrary column data and every row band.  (The prefix reads only
    /// cols `[0, TOP_WIDTH)`, so equality on random full-width buffers
    /// certifies the transcription.)  Identical per-row values ⇒ identical
    /// composition ⇒ every existing soundness gate is preserved.
    #[test]
    fn native_top_matches_v17_prefix() {
        assert_cut_complete();
        let w = v17::WIDTH;
        // Deterministic pseudo-random full-width rows.
        let mk = |seed: u64| -> Vec<F> {
            (0..w)
                .map(|c| F::from_le_bytes_mod_order(
                    &((seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(c as u64 * 0xD1B54A32D192ED03))
                        .to_le_bytes())))
                .collect()
        };
        // Cover EQ rows, NORM rows, an NTT butterfly row, an NTT output
        // row, and padding.
        let rows = [
            0usize,
            v17::N_EQ_ROWS - 1,
            v17::N_EQ_ROWS,
            v17::N_EQ_ROWS + v17::N_NORM_ROWS - 1,
            v17::NTT_REGION_BASE + 5,
            v17::NTT_REGION_BASE + ntt::BUTTERFLIES_PER_NTT,
            v17::VERIFY_AIR_V17_ACTIVE_ROWS + 3,
        ];
        for (t, &row) in rows.iter().enumerate() {
            let cur = mk(row as u64 * 2 + 1 + t as u64 * 7);
            let nxt = mk(row as u64 * 2 + 2 + t as u64 * 7);
            let full = v17::eval_per_row(&cur, &nxt, row);
            let native = eval_top(&cur[..TOP_WIDTH], &nxt[..TOP_WIDTH], row);
            assert_eq!(native.len(), TOP_NC);
            for i in 0..TOP_NC {
                assert_eq!(
                    native[i], full[i],
                    "native TOP != v17 prefix at row {row} constraint {i}"
                );
            }
        }
    }

    /// Constraint-cut completeness: TOP + one NTT-instance block partition
    /// the monolith's per-row constraint vector exactly.
    #[test]
    fn cut_is_complete() {
        assert_cut_complete();
        assert_eq!(TOP_NC + ntt::NUM_CONSTRAINTS, v17::NUM_CONSTRAINTS);
    }
}
