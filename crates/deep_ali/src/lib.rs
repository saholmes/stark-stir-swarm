// lib.rs — replacement DEEP-ALI merge

#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(unused_macros)]
use ark_ff::{Field, Zero};
use ark_goldilocks::Goldilocks as F;

pub mod trace_import;

/// **STARK calibration constants** auto-derived from the active
/// `sha3-256` / `sha3-384` / `sha3-512` Cargo feature.
///
/// Provides `NUM_QUERIES_LEVEL` (the unconditional Johnson-regime
/// query count needed to reach the target NIST PQ Level's IT
/// soundness) and `NIST_LEVEL` (the named level: 1, 3, or 5).
///
/// The per-query rate is the **slack** Johnson yield (ISC 2026):
/// `−log₂(√ρ_0 + η_0)` with ρ_0 = 1/32 and η_0 ≤ √ρ_0/20, i.e.
/// `½·log₂(1/ρ_0) − log₂(1.05) ≈ 2.43` bits/query (BCIKS / STIR
/// Theorem 1, unconditional).  This supersedes the ESORICS ideal η=0
/// figure (2.5 b/q, r=54/79/105): the slack floor spends a few extra
/// queries per level to *provably* clear each NIST target under the
/// η-included proximity gap.  Capacity-regime (~5 b/q) is conjectural
/// and not used; see `feedback_stir_johnson_unconditional_only.md`.
///
/// |  Active feature  | NUM_QUERIES_LEVEL | NIST_LEVEL | IT bits |
/// |------------------|--------------------|------------|----------|
/// |  sha3-256        |  55                |  1         | 133.6    |
/// |  sha3-384        |  81                |  3         | 196.8    |
/// |  sha3-512        |  108               |  5         | 262.4    |
///
/// Downstream callers (mmiyc-prover/verifier) just write
/// `const NUM_QUERIES: usize = deep_ali::stark_level::NUM_QUERIES_LEVEL;`
/// and the right value flows through from the workspace Cargo.toml's
/// `deep_ali = { features = [...] }` line.
pub mod stark_level {
    /// Per-query soundness bits at ρ_0 = 1/32, **slack** Johnson regime
    /// (ISC 2026): the η-included yield −log₂(√ρ_0 + η_0), η_0 ≤ √ρ_0/20,
    /// = ½·log₂(1/ρ_0) − log₂(1.05) ≈ 2.43 (unconditional, BCIKS / STIR
    /// Theorem 1).  Supersedes the ESORICS ideal η=0 rate (2.5 b/q).
    pub const PER_QUERY_BITS_JOHNSON: f64 = 2.43;

    // Slack Johnson production query counts at blowup=32 (ISC 2026):
    // r·2.43 = 133.6 / 196.8 / 262.4 IT bits ≥ 128 / 192 / 256 targets.
    #[cfg(feature = "sha3-256")]
    pub const NUM_QUERIES_LEVEL: usize = 55;
    #[cfg(feature = "sha3-384")]
    pub const NUM_QUERIES_LEVEL: usize = 81;
    #[cfg(feature = "sha3-512")]
    pub const NUM_QUERIES_LEVEL: usize = 108;

    #[cfg(feature = "sha3-256")]
    pub const NIST_LEVEL: u8 = 1;
    #[cfg(feature = "sha3-384")]
    pub const NIST_LEVEL: u8 = 3;
    #[cfg(feature = "sha3-512")]
    pub const NIST_LEVEL: u8 = 5;

    /// IT-soundness target in bits for the active NIST PQ level.
    ///   sha3-256 → 128 (Level 1)
    ///   sha3-384 → 192 (Level 3)
    ///   sha3-512 → 256 (Level 5)
    #[cfg(feature = "sha3-256")]
    pub const TARGET_IT_BITS: usize = 128;
    #[cfg(feature = "sha3-384")]
    pub const TARGET_IT_BITS: usize = 192;
    #[cfg(feature = "sha3-512")]
    pub const TARGET_IT_BITS: usize = 256;

    /// Compute the FRI query count `r` to reach the active NIST PQ
    /// Level's IT soundness at a given `blowup`, in the **slack** Johnson
    /// regime (ISC 2026).  Per-query yield is the η-included floor
    /// `−log₂(√ρ_0 + η_0)` with ρ_0 = 1/blowup and η_0 ≤ √ρ_0/20, i.e.
    /// `½·log₂(blowup) − log₂(1.05)` (= 2.43 b/q at blowup=32).
    ///
    /// The count is *anchored* on the level's production value
    /// `NUM_QUERIES_LEVEL` (which holds at the canonical blowup=32) and
    /// scaled inversely with the per-query yield, so it returns exactly
    /// `NUM_QUERIES_LEVEL` at blowup=32 and provably delivers at least
    /// the same IT bits (`NUM_QUERIES_LEVEL · 2.43 ≥ TARGET_IT_BITS`) at
    /// every blowup.
    ///
    /// Examples (sha3-256, NUM_QUERIES_LEVEL=55, ≈133.6 IT bits):
    ///   blowup= 4 → r = 144  (0.93 b/q)
    ///   blowup= 8 → r =  94  (1.43 b/q)
    ///   blowup=16 → r =  70  (1.93 b/q)
    ///   blowup=32 → r =  55  (2.43 b/q, = NUM_QUERIES_LEVEL)
    ///   blowup=64 → r =  46  (2.93 b/q)
    ///
    /// Callers that VARY blowup (low-mem / IoT streaming, scaling
    /// studies) MUST use this instead of the fixed `NUM_QUERIES_LEVEL`
    /// so `r` tracks the rate change and κ_IT stays ≥ the NIST target.
    pub fn num_queries_for_blowup(blowup: usize) -> usize {
        // Guard against blowup ≤ 1 — the proximity yield is ≤ 0 there.
        if blowup < 2 {
            return usize::MAX; // unreachable in practice; fail loud
        }
        // Slack Johnson per-query yield −log₂(√ρ_0 · 1.05), ρ_0 = 1/blowup:
        // η_0 = √ρ_0/20 inflates the proximity radius by 5% (log₂ 1.05).
        let slack = 1.05_f64.log2();
        let bits_per_q = |b: usize| 0.5_f64 * (b as f64).log2() - slack;
        // Anchor on the production (blowup=32) IT bits so r(32) is exactly
        // NUM_QUERIES_LEVEL and r·bits_per_q ≥ that at every blowup.
        let anchor_bits = NUM_QUERIES_LEVEL as f64 * bits_per_q(32);
        (anchor_bits / bits_per_q(blowup)).ceil() as usize
    }

    /// Target collision-resistance bits (matches `min(n_out, c)` of
    /// the active SHA-3 instance).
    #[cfg(feature = "sha3-256")]
    pub const COLLISION_BITS: u32 = 256;
    #[cfg(feature = "sha3-384")]
    pub const COLLISION_BITS: u32 = 384;
    #[cfg(feature = "sha3-512")]
    pub const COLLISION_BITS: u32 = 512;

    /// SHA-3 sponge capacity bits (governs QROM ε_bind ≤ O(q³/2^c)).
    #[cfg(feature = "sha3-256")]
    pub const SPONGE_CAPACITY: u32 = 512;
    #[cfg(feature = "sha3-384")]
    pub const SPONGE_CAPACITY: u32 = 768;
    #[cfg(feature = "sha3-512")]
    pub const SPONGE_CAPACITY: u32 = 1024;
}

/// Returns `true` if `BENCH_LDT` is set to `"stir"` (case-insensitive).
///
/// Centralised LDT mode toggle for all `DeepFriParams.stir` callsites
/// across the workspace.  Paired with the per-bench env var the
/// `aws-bench/run-matrix.sh` harness already exports.  Default is FRI
/// (returns `false`) — preserves the historical behaviour of every
/// callsite that previously hardcoded `stir: false`.
///
/// Callsites that historically hardcoded `stir: true` (e.g. the
/// RSA-2048 PoK gate in `mmiyc-prover` / `mmiyc-verifier`) should NOT
/// migrate to this helper unless the deployment explicitly wants
/// the env-controlled toggle there too.
pub fn use_stir_from_env() -> bool {
    matches!(
        std::env::var("BENCH_LDT").as_deref(),
        Ok("stir") | Ok("STIR"),
    )
}

use ark_poly::{
    EvaluationDomain,
    GeneralEvaluationDomain,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

const PARALLEL_MIN_ELEMS: usize = 1 << 12;

#[inline]
fn enable_parallel(len: usize) -> bool {
    #[cfg(feature = "parallel")]
    {
        len >= PARALLEL_MIN_ELEMS && rayon::current_num_threads() > 1
    }
    #[cfg(not(feature = "parallel"))]
    {
        let _ = len;
        false
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Soundness budget
// ═══════════════════════════════════════════════════════════════════

/// Soundness breakdown for the full DEEP-ALI + FRI pipeline.
///
/// The total security level (in bits) is the minimum across all
/// contributing terms.  When `r` changes due to a more conservative
/// proximity gap bound, `fri_bits` changes, and the bottleneck may
/// shift from FRI to ALI or vice versa.
#[derive(Clone, Debug)]
pub struct SoundnessBudget {
    /// ALI reduction error: ≤ (num_constraints * max_degree * (width + 1)) / |F_ext|
    /// In bits: -log2(ε_ALI).
    pub ali_bits: f64,

    /// FRI proximity testing: depends on r, eps_eff, PoW bits.
    pub fri_bits: f64,

    /// Proof-of-work grinding bits (0 if not used).
    pub pow_bits: f64,

    /// Total: min(ali_bits, fri_bits + pow_bits).
    pub total_bits: f64,
}

impl SoundnessBudget {
    /// Compute the soundness budget from protocol parameters.
    ///
    /// `ext_field_log_size`: log2(|F_ext|), e.g. 192 for Fp3, 384 for Fp6.
    /// `num_constraints`:    number of transition constraints in the AIR.
    /// `max_constraint_deg`: maximum degree of any single constraint.
    /// `trace_width`:        number of trace columns (w).
    /// `fri_bits`:           bits of security from FRI queries (r * bits_per_query).
    /// `pow_bits`:           bits from proof-of-work grinding.
    pub fn compute(
        ext_field_log_size: f64,
        num_constraints: usize,
        max_constraint_deg: usize,
        trace_width: usize,
        fri_bits: f64,
        pow_bits: f64,
    ) -> Self {
        // ALI reduction error bound:
        //   ε_ALI ≤ num_constraints * max_degree * (width + 1) / |F_ext|
        //
        // This is the probability that the random combination of
        // unsatisfied constraint quotients lands in the RS code.
        // The (width + 1) factor accounts for the DEEP sampling
        // adding one evaluation point per trace column plus one
        // for the composition column.
        let numerator_log2 = (num_constraints as f64
            * max_constraint_deg as f64
            * (trace_width + 1) as f64)
            .log2();
        let ali_bits = ext_field_log_size - numerator_log2;

        let total_bits = ali_bits.min(fri_bits + pow_bits);

        SoundnessBudget {
            ali_bits,
            fri_bits,
            pow_bits,
            total_bits,
        }
    }

    pub fn is_secure(&self, target_bits: f64) -> bool {
        self.total_bits >= target_bits
    }

    /// Identify which component is the bottleneck.
    pub fn bottleneck(&self) -> &'static str {
        if self.ali_bits <= self.fri_bits + self.pow_bits {
            "ALI reduction"
        } else {
            "FRI queries"
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Proximity gap bounds
// ═══════════════════════════════════════════════════════════════════

/// Which proximity gap lower bound to use for FRI soundness.
///
/// When you move to a more conservative bound, `eps_eff_per_query`
/// decreases and `r` must increase to maintain the target security.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ProximityGapBound {
    /// Standard DEEP bound: δ ≥ 1 − √ρ  (Ben-Sasson et al., DEEP-FRI).
    /// Gives the best (largest) per-query soundness.
    Johnson,

    /// One-and-a-half Johnson: δ ≥ 1 − ρ^{1/3}.
    /// More conservative; used when the full Johnson analysis
    /// is not applicable (e.g., non-standard field/code parameters).
    OneAndHalfJohnson,

    /// Double Johnson: δ ≥ 1 − ρ^{1/4}.
    /// Most conservative; the original DEEP-FRI bound before
    /// the improved proximity gap analysis.
    DoubleJohnson,

    /// Custom bound: provide δ directly.
    Custom(f64),
}

impl ProximityGapBound {
    /// Compute the proximity gap δ for a given rate ρ = deg/domain_size.
    pub fn delta(&self, rho: f64) -> f64 {
        match self {
            ProximityGapBound::Johnson => 1.0 - rho.sqrt(),
            ProximityGapBound::OneAndHalfJohnson => 1.0 - rho.cbrt(),
            ProximityGapBound::DoubleJohnson => 1.0 - rho.powf(0.25),
            ProximityGapBound::Custom(d) => *d,
        }
    }

    /// Per-query soundness: probability of rejecting a word at distance ≥ δ.
    ///
    /// For FRI with rate ρ and proximity gap δ, each query rejects
    /// with probability ≥ 1 - (1 - δ) = δ when the codeword is δ-far.
    /// The per-query error is at most max(√ρ, 1 - δ) for the standard
    /// bound.  We use the conservative formula:
    ///   ε_per_query = 1 − δ   (upper bound on non-rejection probability)
    pub fn per_query_error(&self, rho: f64) -> f64 {
        1.0 - self.delta(rho)
    }

    /// Bits of soundness per FRI query.
    pub fn bits_per_query(&self, rho: f64) -> f64 {
        let err = self.per_query_error(rho);
        if err >= 1.0 {
            return 0.0;
        }
        -(err.log2())
    }

    /// Number of queries needed for `target_bits` of FRI soundness.
    pub fn queries_for_target(&self, rho: f64, target_bits: f64) -> usize {
        let bpq = self.bits_per_query(rho);
        if bpq <= 0.0 {
            return usize::MAX;
        }
        (target_bits / bpq).ceil() as usize
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Polynomial division by Z_H(X) = X^m − 1
// ═══════════════════════════════════════════════════════════════════

/// Exact polynomial division of `dividend` by Z_H(X) = X^m − 1.
fn poly_div_zh(dividend: &[F], m: usize) -> Vec<F> {
    let n = dividend.len();
    if n <= m {
        #[cfg(debug_assertions)]
        for (i, &c) in dividend.iter().enumerate() {
            debug_assert!(
                c.is_zero(),
                "poly_div_zh: Φ̃ has degree < m={} but coeff[{}] is nonzero — \
                 constraints are not satisfied on the trace domain",
                m, i,
            );
        }
        return vec![F::zero()];
    }

    let q_len = n - m;
    let mut q = vec![F::zero(); q_len];

    for k in (m..n).rev() {
        let qk = if k < q_len { q[k] } else { F::zero() };
        q[k - m] = dividend[k] + qk;
    }

    #[cfg(debug_assertions)]
    {
        for k in 0..m.min(n) {
            let qk = if k < q_len { q[k] } else { F::zero() };
            let remainder = dividend[k] + qk;
            debug_assert!(
                remainder.is_zero(),
                "poly_div_zh: nonzero remainder at coeff index {} \
                 (remainder = {:?}) — constraints not satisfied on H",
                k, remainder,
            );
        }
    }

    q
}

// ═══════════════════════════════════════════════════════════════════
//  DEEP-ALI constraint merge — GENERALIZED
// ═══════════════════════════════════════════════════════════════════

/// Metadata about the composition for downstream soundness accounting.
#[derive(Clone, Debug)]
pub struct CompositionInfo {
    /// Degree of Φ̃(X) before dividing by Z_H.
    pub phi_degree_bound: usize,
    /// Degree of c(X) = Φ̃/Z_H.
    pub quotient_degree_bound: usize,
    /// Rate ρ = quotient_degree_bound / n.
    pub rate: f64,
    /// Number of constraints that were combined.
    pub num_constraints: usize,
    /// Maximum individual constraint degree.
    pub max_constraint_degree: usize,
    /// Trace width (number of columns).
    pub trace_width: usize,
}

/// Evaluate all transition constraints for a given AIR on the full
/// FRI domain, returning one evaluation vector per constraint.
///
/// Each returned vector has length `n` (the FRI domain size).
/// Constraint evaluations are zero on the trace subdomain H when
/// the execution trace is valid.
///
/// # Arguments
///
/// * `trace_evals_on_lde` — trace columns, each LDE-evaluated on the
///   n-point FRI domain.  `trace_evals_on_lde[col][i]` is column `col`
///   evaluated at ω^i.
///
/// * `air` — which AIR workload to evaluate.
///
/// * `n_trace` — number of rows in the execution trace (= n / blowup).
///   Constraints are meaningful on rows 0..n_trace−2 of H.
///
/// * `blowup` — LDE blowup factor (n / n_trace).
fn evaluate_all_constraints_on_lde(
    trace_evals_on_lde: &[Vec<F>],
    air: crate::air_workloads::AirType,
    n: usize,
    n_trace: usize,
    blowup: usize,
) -> Vec<Vec<F>> {
    let w = air.width();
    let k = air.num_constraints();
    assert_eq!(trace_evals_on_lde.len(), w);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    let mut constraint_evals = vec![vec![F::zero(); n]; k];

    // The LDE domain is D = {ω^0, ω^1, ..., ω^{n-1}}.
    // The trace subdomain is H = {ω^{blowup·0}, ω^{blowup·1}, ..., ω^{blowup·(n_trace-1)}}.
    // The "next row" for H-row j is H-row (j+1) mod n_trace,
    // which corresponds to LDE index (j+1)*blowup mod n.
    //
    // For the constraint polynomial, we evaluate at EVERY LDE point:
    //   C(ω^i) using cur = trace(ω^i) and nxt = trace(ω^{i + blowup} mod n).
    //
    // This produces a polynomial that vanishes on H (rows 0..n_trace-2)
    // when constraints are satisfied.

    for i in 0..n {
        let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();

        // Determine the trace-domain row index for round-constant lookup
        // (relevant for Poseidon).  LDE index i corresponds to trace row
        // i / blowup when i is a multiple of blowup.  For non-H points
        // we use i / blowup as a reasonable approximation (the round
        // constants are deterministic from the row index).
        let trace_row = i / blowup;

        let cvals = crate::air_workloads::evaluate_constraints(
            air, &cur, &nxt, trace_row,
        );

        for j in 0..k {
            constraint_evals[j][i] = cvals[j];
        }
    }

    constraint_evals
}

/// Generalized DEEP-ALI merge for arbitrary multi-constraint AIRs.
///
/// Computes the composition quotient c(X) = Φ̃(X) / Z_H(X) where
///   Φ̃(X) = Σ_{j=0}^{k-1} λ_j · C_j(trace(X))
/// and λ_j are the verifier's random combination coefficients.
///
/// # Arguments
///
/// * `trace_evals_on_lde` — all trace columns, LDE-evaluated on the
///   n-point FRI domain.
/// * `combination_coeffs` — random base-field coefficients λ_j, one per
///   constraint.  In a real protocol these come from the Fiat–Shamir
///   transcript AFTER the prover commits to the trace.
/// * `air` — which AIR workload.
/// * `omega` — generator of the FRI domain.
/// * `n_trace` — trace domain size.
/// * `blowup` — LDE blowup factor.
///
/// # Returns
///
/// `(Vec<F>, CompositionInfo)`:  evaluations of c(X) on the FRI domain,
/// plus metadata for soundness accounting.
pub fn deep_ali_merge_general(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    air: crate::air_workloads::AirType,
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    let w = air.width();
    let k = air.num_constraints();
    let n = n_trace * blowup;

    assert_eq!(trace_evals_on_lde.len(), w, "trace width mismatch");
    assert_eq!(
        combination_coeffs.len(), k,
        "need one combination coefficient per constraint, got {} for {} constraints",
        combination_coeffs.len(), k
    );
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n, "trace column length mismatch");
    }

    // ── Step 1: Evaluate all constraints on the LDE domain ──
    let constraint_evals = evaluate_all_constraints_on_lde(
        trace_evals_on_lde, air, n, n_trace, blowup,
    );

    // ── Step 2: Random linear combination ──
    //   Φ̃(ω^i) = Σ_j λ_j · C_j(ω^i)
    let mut phi_eval = vec![F::zero(); n];

    if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        {
            phi_eval.par_iter_mut().enumerate().for_each(|(i, phi_i)| {
                let mut acc = F::zero();
                for j in 0..k {
                    acc += combination_coeffs[j] * constraint_evals[j][i];
                }
                *phi_i = acc;
            });
        }
    }

    // Sequential fallback (also used when parallel is disabled)
    #[cfg(not(feature = "parallel"))]
    {
        for i in 0..n {
            let mut acc = F::zero();
            for j in 0..k {
                acc += combination_coeffs[j] * constraint_evals[j][i];
            }
            phi_eval[i] = acc;
        }
    }

    // ── Step 3: IFFT → coefficient representation ──
    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);

    // ── Step 4: Divide by Z_H(X) = X^{n_trace} − 1 ──
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);

    // ── Step 5: FFT back to evaluations ──
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // ── Composition metadata ──
    let max_deg = air.max_constraint_degree();
    // Φ̃ has degree ≤ max_deg * (n_trace - 1)  (transition constraints
    // applied to polynomials of degree n_trace - 1).
    // After dividing by Z_H (degree n_trace), the quotient has degree
    // ≤ max_deg * (n_trace - 1) - n_trace = (max_deg - 1) * n_trace - max_deg.
    // In practice, the effective bound is:
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else {
        0
    };
    let rate = quotient_degree_bound as f64 / n as f64;

    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate,
        num_constraints: k,
        max_constraint_degree: max_deg,
        trace_width: w,
    };

    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  SHA-256 multi-block merge (parameterised by n_blocks)
// ═══════════════════════════════════════════════════════════════════

/// DEEP-ALI merge for the SHA-256 AIR with arbitrary `n_blocks`.
///
/// Mirrors `deep_ali_merge_general` but routes constraint evaluation
/// through `sha256_air::eval_sha256_constraints(cur, nxt, row, n_blocks)`
/// instead of the registry dispatcher (which fixes `n_blocks = 1`).
///
/// `swarm-dns::prove_ds_ksk_binding` invokes this directly so that
/// multi-block DNSKEYs (RSA-2048, ECDSA-P256, multi-block Ed25519
/// concatenations) can be proved with a single STARK rather than
/// composing per-block proofs at the API layer.
pub fn deep_ali_merge_sha256(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
    n_blocks: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::sha256_air::{WIDTH as SHA_W, NUM_CONSTRAINTS as SHA_K};

    let _ = omega;
    let n = n_trace * blowup;

    assert_eq!(trace_evals_on_lde.len(), SHA_W, "trace width mismatch");
    assert_eq!(
        combination_coeffs.len(), SHA_K,
        "need one combination coefficient per constraint, got {} for {} constraints",
        combination_coeffs.len(), SHA_K
    );
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n, "trace column length mismatch");
    }

    // ── Step 1: evaluate constraints on the LDE domain ──
    let mut constraint_evals = vec![vec![F::zero(); n]; SHA_K];
    for i in 0..n {
        // Gate the final trace row's contribution to zero, matching the
        // verifier's `trace_row >= n_trace-1` skip in
        // `sub_air_with_trace::verify_one_sub_air_with_trace`.  The wrap
        // transition row (n_trace-1 → 0) is not a real AIR transition
        // (the SHA-256 digest-state row does not equal the IV row), so its
        // constraint residual is intentionally unenforced.  Without this
        // gate the merge bakes a nonzero residual at the last H-row into
        // phi, phi fails to vanish on H, `poly_div_zh` drops a remainder,
        // and the witness-binding identity `c_eval·Z_H = phi` then fails at
        // OTHER (off-H) query points.  (The bare low-degree path never
        // re-evaluated constraints off-H, so it was unaffected.)
        let trace_row = i / blowup;
        if trace_row == n_trace - 1 {
            continue;
        }
        let cur: Vec<F> = (0..SHA_W).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..SHA_W).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = crate::sha256_air::eval_sha256_constraints(
            &cur, &nxt, trace_row, n_blocks,
        );
        for j in 0..SHA_K {
            constraint_evals[j][i] = cvals[j];
        }
    }

    // ── Step 2: random linear combination Φ̃(ω^i) ──
    let mut phi_eval = vec![F::zero(); n];
    if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        {
            phi_eval.par_iter_mut().enumerate().for_each(|(i, phi_i)| {
                let mut acc = F::zero();
                for j in 0..SHA_K {
                    acc += combination_coeffs[j] * constraint_evals[j][i];
                }
                *phi_i = acc;
            });
        }
    }
    #[cfg(not(feature = "parallel"))]
    {
        for i in 0..n {
            let mut acc = F::zero();
            for j in 0..SHA_K {
                acc += combination_coeffs[j] * constraint_evals[j][i];
            }
            phi_eval[i] = acc;
        }
    }

    // ── Step 3: IFFT → coefficients ──
    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);

    // ── Step 4: divide by Z_H(X) = X^{n_trace} − 1 ──
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);

    // ── Step 5: FFT back to evaluations ──
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // ── Composition metadata (max_deg = 2 globally) ──
    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: SHA_K,
        max_constraint_degree: max_deg,
        trace_width: SHA_W,
    };

    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  SHA-512 multi-block merge (parameterised by n_blocks)
// ═══════════════════════════════════════════════════════════════════

/// DEEP-ALI merge for the SHA-512 AIR with arbitrary `n_blocks`.
///
/// Twin of `deep_ali_merge_sha256` for the SHA-512 AIR (1510 cols,
/// 1526 transition constraints).  Routes constraint evaluation through
/// `sha512_air::eval_sha512_constraints(cur, nxt, row, n_blocks)`.
///
/// Used by `swarm-dns::prove_zsk_ksk_binding` (planned) for the
/// in-circuit SHA-512 stage of Ed25519 verification (RFC 8032 §5.1.7),
/// where the input to the hash is `R || A || M` and the output digest
/// is reduced mod L to form the verification scalar k.
pub fn deep_ali_merge_sha512(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
    n_blocks: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::sha512_air::{WIDTH as SHA_W, NUM_CONSTRAINTS as SHA_K};

    let _ = omega;
    let n = n_trace * blowup;

    assert_eq!(trace_evals_on_lde.len(), SHA_W, "trace width mismatch");
    assert_eq!(
        combination_coeffs.len(), SHA_K,
        "need one combination coefficient per constraint, got {} for {} constraints",
        combination_coeffs.len(), SHA_K
    );
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n, "trace column length mismatch");
    }

    // ── Step 1: evaluate constraints on the LDE domain ──
    let mut constraint_evals = vec![vec![F::zero(); n]; SHA_K];
    for i in 0..n {
        let cur: Vec<F> = (0..SHA_W).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..SHA_W).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let trace_row = i / blowup;
        let cvals = crate::sha512_air::eval_sha512_constraints(
            &cur, &nxt, trace_row, n_blocks,
        );
        for j in 0..SHA_K {
            constraint_evals[j][i] = cvals[j];
        }
    }

    // ── Step 2: random linear combination Φ̃(ω^i) ──
    let mut phi_eval = vec![F::zero(); n];
    if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        {
            phi_eval.par_iter_mut().enumerate().for_each(|(i, phi_i)| {
                let mut acc = F::zero();
                for j in 0..SHA_K {
                    acc += combination_coeffs[j] * constraint_evals[j][i];
                }
                *phi_i = acc;
            });
        }
    }
    #[cfg(not(feature = "parallel"))]
    {
        for i in 0..n {
            let mut acc = F::zero();
            for j in 0..SHA_K {
                acc += combination_coeffs[j] * constraint_evals[j][i];
            }
            phi_eval[i] = acc;
        }
    }

    // ── Step 3: IFFT → coefficients ──
    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);

    // ── Step 4: divide by Z_H(X) = X^{n_trace} − 1 ──
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);

    // ── Step 5: FFT back to evaluations ──
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // ── Composition metadata (max_deg = 2 globally) ──
    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: SHA_K,
        max_constraint_degree: max_deg,
        trace_width: SHA_W,
    };

    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  ML-DSA-44 verify AIR v1.7 merge (v1.5 + chained NTT regions)
// ═══════════════════════════════════════════════════════════════════

/// DEEP-ALI merge for the v1.7 ML-DSA-44 verify AIR.
///
/// Mirrors `deep_ali_merge_general` but routes constraint evaluation
/// through `ml_dsa_verify_air_v17::eval_per_row(cur, nxt, row)`,
/// which has no static-registry entry (the v1.5 / v1.7 AIRs aren't
/// registered as `AirType` because their fixed shape is fully
/// determined by `K, L, N` constants and they don't need a layout
/// parameter).
///
/// Callers (mmiyc-prover's `prove_ml_dsa_signature_pok_v17`) build
/// the trace via `ml_dsa_verify_air_v17::fill_trace`, LDE-extend each
/// column, then invoke this to produce the composition quotient
/// for FRI.
pub fn deep_ali_merge_ml_dsa_v17(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::ml_dsa_verify_air_v17::{
        eval_per_row, NUM_CONSTRAINTS as V17_K, WIDTH as V17_W,
    };

    let _ = omega;
    let n = n_trace * blowup;
    let w = V17_W;
    let k = V17_K;

    assert_eq!(trace_evals_on_lde.len(), w, "v1.7 trace width mismatch");
    assert_eq!(
        combination_coeffs.len(), k,
        "v1.7: need one combination coefficient per constraint, got {} for {} constraints",
        combination_coeffs.len(), k,
    );
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n, "v1.7 trace column length mismatch");
    }

    // ── Step 1+2: per-row eval + linear combination ──
    // Sequential is fine for v1.7 (n ≤ 2^18 in practice).
    let mut phi_eval = vec![F::zero(); n];
    if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        {
            phi_eval = (0..n).into_par_iter().map(|i| {
                let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
                let nxt_idx = (i + blowup) % n;
                let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
                let trace_row = i / blowup;
                let cvals = eval_per_row(&cur, &nxt, trace_row);
                debug_assert_eq!(cvals.len(), k);
                let mut acc = F::zero();
                for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
                acc
            }).collect();
        }
        #[cfg(not(feature = "parallel"))]
        {
            for i in 0..n {
                let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
                let nxt_idx = (i + blowup) % n;
                let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
                let trace_row = i / blowup;
                let cvals = eval_per_row(&cur, &nxt, trace_row);
                debug_assert_eq!(cvals.len(), k);
                let mut acc = F::zero();
                for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
                phi_eval[i] = acc;
            }
        }
    } else {
        for i in 0..n {
            let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
            let nxt_idx = (i + blowup) % n;
            let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
            let trace_row = i / blowup;
            let cvals = eval_per_row(&cur, &nxt, trace_row);
            debug_assert_eq!(cvals.len(), k);
            let mut acc = F::zero();
            for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
            phi_eval[i] = acc;
        }
    }

    // ── Step 3: IFFT → coefficients ──
    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);

    // ── Step 4: divide by Z_H(X) = X^{n_trace} − 1 ──
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);

    // ── Step 5: FFT back to evaluations ──
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // ── Composition metadata (max_deg = 2 globally) ──
    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k,
        max_constraint_degree: max_deg,
        trace_width: w,
    };

    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  ML-DSA v2 sub-AIR merges (T7 / Decompose / UseHint / W1Encode / T-MEM)
// ═══════════════════════════════════════════════════════════════════

/// DEEP-ALI merge for the chained-NTT AIR (T7).  v2 uses this 4×
/// (one per `(w_approx[k], w_approx_ntt[k])` polynomial pair) in
/// the INTT sub-region.  Per-row evaluator is
/// `ml_dsa_ntt_chained_air::eval_per_row(cur, nxt, row)`.
///
/// **Cyclic-wrap handling**: T7's `eval_per_row` at trace row
/// `n_trace − 1` references `nxt = row 0` (FRI-domain wraparound),
/// which violates the passthrough constraint (post-NTT output ≠
/// pre-NTT input).  The merge gates the constraints at the very
/// last trace row to zero — a standard AIR pattern when the AIR
/// itself has no boundary selector to suppress the wraparound.
/// (v1.7's `verify_air_v17` handles this via per-region selectors.)
pub fn deep_ali_merge_t7_chained_ntt(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::ml_dsa_ntt_chained_air::{
        eval_per_row, NUM_CONSTRAINTS as T7_K, WIDTH as T7_W,
    };
    let _ = omega;
    let n = n_trace * blowup;
    assert_eq!(trace_evals_on_lde.len(), T7_W, "T7 trace width mismatch");
    assert_eq!(combination_coeffs.len(), T7_K,
        "T7: need one combination coefficient per constraint");
    for col in trace_evals_on_lde { assert_eq!(col.len(), n); }

    // Gate: skip constraint emission for LDE points whose trace_row
    // == n_trace - 1 (the cyclic-wrap row).  At those points Φ̃ = 0.
    let last_trace_row = n_trace - 1;
    let eval_gated = |i: usize| -> F {
        let trace_row = i / blowup;
        if trace_row >= last_trace_row {
            return F::zero();
        }
        let cur: Vec<F> = (0..T7_W).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..T7_W).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = eval_per_row(&cur, &nxt, trace_row);
        let mut acc = F::zero();
        for j in 0..T7_K { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_gated).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_gated).collect() }
    } else {
        (0..n).map(eval_gated).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: T7_K,
        max_constraint_degree: max_deg,
        trace_width: T7_W,
    };
    (c_eval, info)
}

/// DEEP-ALI merge for `ml_dsa_decompose_air`.  Used in v2 COEFF
/// sub-region (1024 rows = K·N coefficients, no row-to-row chain).
/// Per-row eval has no `nxt` reference, so cyclic-wrap is not an
/// issue here — but we still gate the LAST row's constraint to
/// zero for uniformity.
pub fn deep_ali_merge_t_decompose(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::ml_dsa_decompose_air::{eval_per_row, NUM_CONSTRAINTS as KK, WIDTH as WW};
    deep_ali_merge_per_row_no_layout(
        trace_evals_on_lde, combination_coeffs, omega, n_trace, blowup,
        WW, KK, eval_per_row,
    )
}

/// DEEP-ALI merge for `ml_dsa_use_hint_air`.
pub fn deep_ali_merge_t_use_hint(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::ml_dsa_use_hint_air::{eval_per_row, NUM_CONSTRAINTS as KK, WIDTH as WW};
    deep_ali_merge_per_row_no_layout(
        trace_evals_on_lde, combination_coeffs, omega, n_trace, blowup,
        WW, KK, eval_per_row,
    )
}

/// DEEP-ALI merge for `ml_dsa_w1_encode_air`.
pub fn deep_ali_merge_t_w1_encode(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::ml_dsa_w1_encode_air::{eval_per_row, NUM_CONSTRAINTS as KK, WIDTH as WW};
    deep_ali_merge_per_row_no_layout(
        trace_evals_on_lde, combination_coeffs, omega, n_trace, blowup,
        WW, KK, eval_per_row,
    )
}

/// DEEP-ALI merge for `permutation_argument` (T-MEM).  Takes the
/// Fiat-Shamir challenges γ and α as **F_ext** elements (Fp6 for
/// L1/L3, Fp8 for L5) — see `permutation_argument::ExtField`.
pub fn deep_ali_merge_t_mem(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
    gamma: crate::permutation_argument::ExtField,
    alpha: crate::permutation_argument::ExtField,
) -> (Vec<F>, CompositionInfo) {
    use crate::permutation_argument::{eval_per_row, NUM_CONSTRAINTS as KK, WIDTH as WW};
    let _ = omega;
    let n = n_trace * blowup;
    assert_eq!(trace_evals_on_lde.len(), WW);
    assert_eq!(combination_coeffs.len(), KK);
    for col in trace_evals_on_lde { assert_eq!(col.len(), n); }

    let last_trace_row = n_trace - 1;
    let eval_gated = |i: usize| -> F {
        let trace_row = i / blowup;
        if trace_row >= last_trace_row { return F::zero(); }
        let cur: Vec<F> = (0..WW).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..WW).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = eval_per_row(&cur, &nxt, trace_row, gamma, alpha);
        let mut acc = F::zero();
        for j in 0..KK { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_gated).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_gated).collect() }
    } else {
        (0..n).map(eval_gated).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two");
    let phi_coeffs = domain.ifft(&phi);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: KK,
        max_constraint_degree: max_deg,
        trace_width: WW,
    };
    (c_eval, info)
}

/// DEEP-ALI merge for the T-Transcript (T1.5 multi-block SHAKE
/// absorb).  Takes the `MultiAbsorbLayout` describing the message
/// + rate.
pub fn deep_ali_merge_t_transcript(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    omega: F,
    n_trace: usize,
    blowup: usize,
    layout: &crate::ml_dsa_shake_absorb_multi_air::MultiAbsorbLayout,
) -> (Vec<F>, CompositionInfo) {
    use crate::ml_dsa_shake_absorb_multi_air::{eval_per_row, num_constraints, WIDTH as WW};
    let _ = omega;
    let n = n_trace * blowup;
    let kk = num_constraints(layout);
    assert_eq!(trace_evals_on_lde.len(), WW);
    assert_eq!(combination_coeffs.len(), kk);
    for col in trace_evals_on_lde { assert_eq!(col.len(), n); }

    let last_trace_row = n_trace - 1;
    let eval_gated = |i: usize| -> F {
        let trace_row = i / blowup;
        if trace_row >= last_trace_row { return F::zero(); }
        let cur: Vec<F> = (0..WW).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..WW).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = eval_per_row(&cur, &nxt, trace_row, layout);
        let mut acc = F::zero();
        for j in 0..kk { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_gated).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_gated).collect() }
    } else {
        (0..n).map(eval_gated).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two");
    let phi_coeffs = domain.ifft(&phi);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: kk,
        max_constraint_degree: max_deg,
        trace_width: WW,
    };
    (c_eval, info)
}

/// Generic DEEP-ALI merge for sub-AIRs whose `eval_per_row` takes
/// `(cur, nxt, row)` and no extra layout/parameters.  Used by the
/// COEFF sub-AIRs (Decompose, UseHint, W1Encode).
pub fn deep_ali_merge_per_row_no_layout(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    _omega: F,
    n_trace: usize,
    blowup: usize,
    width: usize,
    num_constraints: usize,
    // `impl Fn + Sync` (not a bare `fn` pointer) so callers can pass a
    // closure that *captures public values* — used by the witness-binding
    // bound provers to append public-input PIN constraints (cell − public)
    // to the AIR's own constraints, while sharing the identical eval with the
    // verifier.  `fn` pointers still coerce, so existing callers are
    // unaffected.
    eval_per_row: impl Fn(&[F], &[F], usize) -> Vec<F> + Sync,
) -> (Vec<F>, CompositionInfo) {
    let n = n_trace * blowup;
    assert_eq!(trace_evals_on_lde.len(), width);
    assert_eq!(combination_coeffs.len(), num_constraints);
    for col in trace_evals_on_lde { assert_eq!(col.len(), n); }

    let last_trace_row = n_trace - 1;
    let eval_gated = |i: usize| -> F {
        let trace_row = i / blowup;
        if trace_row >= last_trace_row { return F::zero(); }
        let cur: Vec<F> = (0..width).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..width).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = eval_per_row(&cur, &nxt, trace_row);
        let mut acc = F::zero();
        for j in 0..num_constraints { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_gated).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_gated).collect() }
    } else {
        (0..n).map(eval_gated).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two");
    let phi_coeffs = domain.ifft(&phi);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints,
        max_constraint_degree: max_deg,
        trace_width: width,
    };
    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  Ed25519 verify AIR — parametric merge (Phase 6 v2 wiring)
// ═══════════════════════════════════════════════════════════════════

/// Sequential (no-rayon) fallback for `deep_ali_merge_ed25519_verify`.
/// Used when the `parallel` feature is off OR when n is below the
/// `enable_parallel` threshold.  Mirrors the parallel path's fused
/// Step 1+2 so behaviour matches.
fn sequential_step1_step2(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::ed25519_verify_air::VerifyAirLayoutV16,
    n: usize,
    w: usize,
    blowup: usize,
    k: usize,
) -> Vec<F> {
    let mut phi = vec![F::zero(); n];
    for i in 0..n {
        let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let trace_row = i / blowup;
        let cvals = crate::ed25519_verify_air::eval_verify_air_v16_per_row(
            &cur, &nxt, trace_row, layout,
        );
        debug_assert_eq!(cvals.len(), k);
        let mut acc = F::zero();
        for j in 0..k {
            acc += combination_coeffs[j] * cvals[j];
        }
        phi[i] = acc;
    }
    phi
}

/// DEEP-ALI merge for the parametric Ed25519 verify AIR (v16
/// composition in `crate::ed25519_verify_air`).
///
/// Mirrors `deep_ali_merge_sha256` / `deep_ali_merge_general` but
/// routes constraint evaluation through
/// `eval_verify_air_v16_per_row(cur, nxt, row, layout)`, which
/// requires the per-call `&VerifyAirLayoutV16` (the layout carries
/// the per-call public-input scalar bits, R/A coords, k_scalar, and
/// row/column offsets, none of which the static `AirType` registry
/// can express).
///
/// Production callers (K=256) invoke this directly from
/// `swarm-dns::prove_zsk_ksk_binding_v2`; the registry path
/// (`AirType::Ed25519ZskKsk`, K=8 stub) routes through
/// `deep_ali_merge_general` and produces an identical c-polynomial
/// when the stub layout is passed here.
pub fn deep_ali_merge_ed25519_verify(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::ed25519_verify_air::VerifyAirLayoutV16,
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::ed25519_verify_air::{
        eval_verify_air_v16_per_row, verify_v16_per_row_constraints,
    };

    let _ = omega;
    let n = n_trace * blowup;
    let w = layout.width;
    let k = verify_v16_per_row_constraints(layout.k_scalar);

    assert_eq!(trace_evals_on_lde.len(), w, "trace width mismatch");
    assert_eq!(
        combination_coeffs.len(), k,
        "need one combination coefficient per constraint, got {} for {} constraints",
        combination_coeffs.len(), k,
    );
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n, "trace column length mismatch");
    }

    // ── Step 1+2 fused: evaluate constraints + linear combination,
    //    in parallel over LDE points.
    //
    // Allocator-aware design:
    //
    //   1. **Transpose the LDE once at the start** to a row-major
    //      buffer `lde_rm[i] = [F; w]`.  This is an O(n·w) one-time
    //      cost (~32K × 40K ≈ 0.5 s of data movement at 20 GB/s) but
    //      converts the inner loop's column-major scattered reads
    //      into contiguous slice borrows.  No per-iteration
    //      allocation; cache-friendly.
    //
    //   2. **Pass &[F] slice borrows** for cur and nxt into the
    //      per-row evaluator instead of Vec<F>.  Eliminates 2·n large
    //      heap allocations (~64K × 320 KB = 20 GiB of allocator
    //      churn at K=256) that were serialising threads on the
    //      global allocator lock.
    //
    // Memory footprint: O(n·w) for the row-major transpose
    //                   PLUS O(n·w) original column-major LDE
    //                   = 2× the LDE size (~20 GB at K=256).
    // Wall-clock: should saturate all rayon threads (one allocation
    //             per thread for the cvals output Vec).
    let lde_row_major: Vec<Vec<F>> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        {
            (0..n).into_par_iter().map(|i| {
                (0..w).map(|c| trace_evals_on_lde[c][i]).collect::<Vec<F>>()
            }).collect()
        }
        #[cfg(not(feature = "parallel"))]
        {
            (0..n).map(|i| {
                (0..w).map(|c| trace_evals_on_lde[c][i]).collect::<Vec<F>>()
            }).collect()
        }
    } else {
        (0..n).map(|i| {
            (0..w).map(|c| trace_evals_on_lde[c][i]).collect::<Vec<F>>()
        }).collect()
    };

    let phi_eval: Vec<F>;
    if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        {
            phi_eval = (0..n).into_par_iter().map(|i| {
                let cur: &[F] = &lde_row_major[i];
                let nxt_idx = (i + blowup) % n;
                let nxt: &[F] = &lde_row_major[nxt_idx];
                let trace_row = i / blowup;
                let cvals = eval_verify_air_v16_per_row(cur, nxt, trace_row, layout);
                debug_assert_eq!(cvals.len(), k);
                let mut acc = F::zero();
                for j in 0..k {
                    acc += combination_coeffs[j] * cvals[j];
                }
                acc
            }).collect();
        }
        #[cfg(not(feature = "parallel"))]
        {
            phi_eval = sequential_step1_step2(
                trace_evals_on_lde, combination_coeffs, layout,
                n, w, blowup, k,
            );
        }
    } else {
        phi_eval = sequential_step1_step2(
            trace_evals_on_lde, combination_coeffs, layout,
            n, w, blowup, k,
        );
    }
    drop(lde_row_major);    // release the transpose ASAP

    // ── Step 3: IFFT → coefficients ──
    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);

    // ── Step 4: divide by Z_H(X) = X^{n_trace} − 1 ──
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);

    // ── Step 5: FFT back to evaluations ──
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // ── Composition metadata (max_deg = 2 globally) ──
    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k,
        max_constraint_degree: max_deg,
        trace_width: w,
    };

    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  Streaming stacked-RSA merge (N records side-by-side, 1 FRI proof)
//  — ported from the stark-dns deep_ali fork (2026-05-07).
// ═══════════════════════════════════════════════════════════════════
pub fn deep_ali_merge_rsa_stacked_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::rsa2048_stacked_air::RsaStackedLayout,
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::rsa2048_stacked_air::{
        eval_rsa_stacked_per_row, rsa_stacked_constraints,
    };

    let _ = omega;
    let n = n_trace * blowup;
    let w = layout.width;
    let k = rsa_stacked_constraints(layout);

    assert_eq!(trace_evals_on_lde.len(), w);
    assert_eq!(combination_coeffs.len(), k);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    let build_chunk = |base: usize| -> Vec<Vec<F>> {
        #[cfg(feature = "parallel")]
        {
            (0..blowup)
                .into_par_iter()
                .map(|idx| (0..w).map(|c| trace_evals_on_lde[c][base + idx]).collect())
                .collect()
        }
        #[cfg(not(feature = "parallel"))]
        {
            (0..blowup)
                .map(|idx| (0..w).map(|c| trace_evals_on_lde[c][base + idx]).collect())
                .collect()
        }
    };

    let mut phi_eval = vec![F::zero(); n];
    let mut cur_chunk = build_chunk(0);
    let chunk0_for_wrap = cur_chunk.clone();

    for r in 0..n_trace {
        let nxt_chunk: Vec<Vec<F>> = if r + 1 < n_trace {
            build_chunk((r + 1) * blowup)
        } else {
            chunk0_for_wrap.clone()
        };
        let base = r * blowup;
        let trace_row = r;
        let chunk_phi: Vec<F>;
        #[cfg(feature = "parallel")]
        {
            chunk_phi = (0..blowup)
                .into_par_iter()
                .map(|idx| {
                    let cur: &[F] = &cur_chunk[idx];
                    let nxt: &[F] = &nxt_chunk[idx];
                    let cvals = eval_rsa_stacked_per_row(cur, nxt, trace_row, n_trace, layout);
                    let mut acc = F::zero();
                    for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
                    acc
                })
                .collect();
        }
        #[cfg(not(feature = "parallel"))]
        {
            chunk_phi = (0..blowup)
                .map(|idx| {
                    let cur: &[F] = &cur_chunk[idx];
                    let nxt: &[F] = &nxt_chunk[idx];
                    let cvals = eval_rsa_stacked_per_row(cur, nxt, trace_row, n_trace, layout);
                    let mut acc = F::zero();
                    for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
                    acc
                })
                .collect();
        }
        for (idx, v) in chunk_phi.into_iter().enumerate() { phi_eval[base + idx] = v; }
        cur_chunk = nxt_chunk;
    }

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace { phi_degree_bound - n_trace } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k, max_constraint_degree: max_deg, trace_width: w,
    };
    (c_eval, info)
}

/// Composition merge for the **compact** RSA-2048 exp-chain AIR
/// (`rsa2048_exp_air`, 17 active rows, `n_trace = 32`).  This is the
/// short-wide layout the paper reports (`n0 = 1024`); the stacked
/// variant above is the tall-narrow bit-serial layout.  Identical
/// IFFT -> Z_H -> FFT pipeline to
/// [`deep_ali_merge_rsa_stacked_streaming`]; only the per-row
/// constraint evaluator and layout type differ, so soundness carries
/// (every transition + the row-16 boundary constraint enters `c_eval`).
pub fn deep_ali_merge_rsa_exp_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::rsa2048_exp_air::RsaExpMultirowLayout,
    omega: F,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::rsa2048_exp_air::{
        eval_rsa_exp_multirow_per_row, rsa_exp_multirow_constraints,
    };

    let _ = omega;
    let n = n_trace * blowup;
    let w = layout.width;
    let k = rsa_exp_multirow_constraints(layout);

    assert_eq!(trace_evals_on_lde.len(), w);
    assert_eq!(combination_coeffs.len(), k);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    let build_chunk = |base: usize| -> Vec<Vec<F>> {
        #[cfg(feature = "parallel")]
        {
            (0..blowup)
                .into_par_iter()
                .map(|idx| (0..w).map(|c| trace_evals_on_lde[c][base + idx]).collect())
                .collect()
        }
        #[cfg(not(feature = "parallel"))]
        {
            (0..blowup)
                .map(|idx| (0..w).map(|c| trace_evals_on_lde[c][base + idx]).collect())
                .collect()
        }
    };

    let mut phi_eval = vec![F::zero(); n];
    let mut cur_chunk = build_chunk(0);
    let chunk0_for_wrap = cur_chunk.clone();

    for r in 0..n_trace {
        let nxt_chunk: Vec<Vec<F>> = if r + 1 < n_trace {
            build_chunk((r + 1) * blowup)
        } else {
            chunk0_for_wrap.clone()
        };
        let base = r * blowup;
        let trace_row = r;
        let chunk_phi: Vec<F>;
        #[cfg(feature = "parallel")]
        {
            chunk_phi = (0..blowup)
                .into_par_iter()
                .map(|idx| {
                    let cur: &[F] = &cur_chunk[idx];
                    let nxt: &[F] = &nxt_chunk[idx];
                    let cvals = eval_rsa_exp_multirow_per_row(cur, nxt, trace_row, n_trace, layout);
                    let mut acc = F::zero();
                    for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
                    acc
                })
                .collect();
        }
        #[cfg(not(feature = "parallel"))]
        {
            chunk_phi = (0..blowup)
                .map(|idx| {
                    let cur: &[F] = &cur_chunk[idx];
                    let nxt: &[F] = &nxt_chunk[idx];
                    let cvals = eval_rsa_exp_multirow_per_row(cur, nxt, trace_row, n_trace, layout);
                    let mut acc = F::zero();
                    for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
                    acc
                })
                .collect();
        }
        for (idx, v) in chunk_phi.into_iter().enumerate() { phi_eval[base + idx] = v; }
        cur_chunk = nxt_chunk;
    }

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 2usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace { phi_degree_bound - n_trace } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k, max_constraint_degree: max_deg, trace_width: w,
    };
    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  Streaming P-256 ECDSA verify merge — paper §IV-A Step 2b S_ic path.
//  Wraps the ported `p256_ecdsa_air::eval_ecdsa_verify_demo` AIR (10 116
//  LOC across 13 files; commit history `61e6dfd → 6f5e3c4`) into a FRI
//  c_eval polynomial that `deep_fri_prove` consumes.
//
//  The ECDSA AIR is a SINGLE-ROW composition (witness placed in trace
//  row 0; rows 1..n_trace zero-padded).  All constraints are row-
//  uniform with no cross-row references, so the merge has no `nxt`
//  argument unlike the RSA stacked merge.  Padding rows trivially
//  satisfy the AIR's polynomial constraints (boolean × bit, mul × mul,
//  group-add × group-add — every constraint is zero when its operand
//  cells are zero).
// ═══════════════════════════════════════════════════════════════════
pub fn deep_ali_merge_p256_ecdsa_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::p256_ecdsa_air::EcdsaVerifyDemoLayout,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::p256_ecdsa_air::{
        ecdsa_verify_demo_constraints, eval_ecdsa_verify_demo,
    };

    let n = n_trace * blowup;
    let w = trace_evals_on_lde.len();
    let k = ecdsa_verify_demo_constraints(layout);

    assert_eq!(combination_coeffs.len(), k);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    // Per-LDE-point: read the column values into a row buffer, evaluate
    // the AIR's `k` per-row constraints, then α-combine into one F.
    // Parallelised over LDE points since the AIR has no cross-row deps.
    let phi_eval: Vec<F> = {
        #[cfg(feature = "parallel")]
        {
            (0..n)
                .into_par_iter()
                .map(|i| {
                    let cur: Vec<F> =
                        (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
                    let cvals = eval_ecdsa_verify_demo(&cur, layout);
                    let mut acc = F::zero();
                    for j in 0..k {
                        acc += combination_coeffs[j] * cvals[j];
                    }
                    acc
                })
                .collect()
        }
        #[cfg(not(feature = "parallel"))]
        {
            (0..n)
                .map(|i| {
                    let cur: Vec<F> =
                        (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
                    let cvals = eval_ecdsa_verify_demo(&cur, layout);
                    let mut acc = F::zero();
                    for j in 0..k {
                        acc += combination_coeffs[j] * cvals[j];
                    }
                    acc
                })
                .collect()
        }
    };

    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // ECDSA AIR max constraint degree: group_add gadget uses degree-3
    // mults (projective coordinate adds); scalar_mul uses degree-2;
    // scalar_eq is degree-2.  Conservative bound: 3.
    let max_deg = 3usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else {
        0
    };
    let info = CompositionInfo {
        phi_degree_bound,
        quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k,
        max_constraint_degree: max_deg,
        trace_width: w,
    };
    (c_eval, info)
}

/// Row-0 Lagrange indicator polynomial s_0(X) evaluated on the LDE
/// domain.  s_0 is the unique polynomial of degree < n_trace that
/// satisfies s_0(ω_trace^0) = 1, s_0(ω_trace^j) = 0 for j ≠ 0.
/// Multiplying a boundary constraint by s_0 makes it fire only at
/// trace row 0 (and vanish on the padded rows of a single-row AIR).
pub(crate) fn compute_row0_indicator_lde(n_trace: usize, blowup: usize) -> Vec<F> {
    use ark_ff::One;
    let n_lde = n_trace * blowup;
    let mut trace_vals = vec![F::zero(); n_trace];
    trace_vals[0] = <F as One>::one();
    let trace_dom = GeneralEvaluationDomain::<F>::new(n_trace)
        .expect("trace domain radix-2");
    let coeffs = trace_dom.ifft(&trace_vals);
    let mut padded = coeffs;
    padded.resize(n_lde, F::zero());
    let lde_dom = GeneralEvaluationDomain::<F>::new(n_lde)
        .expect("LDE domain radix-2");
    lde_dom.fft(&padded)
}

// ═══════════════════════════════════════════════════════════════════
//  Streaming P-256 ECDSA verify merge — Phase 5 v2 AIR.
//  Same structure as `deep_ali_merge_p256_ecdsa_streaming` (v0) but
//  evaluates the v2 AIR which includes the Fp Fermat-inversion chain
//  + Fp mul gadget that converts projective R to affine x.  This is
//  the path that proves REAL ECDSA signatures (FIPS 186-4 §6.4.2).
// ═══════════════════════════════════════════════════════════════════
pub fn deep_ali_merge_p256_ecdsa_v2_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::p256_ecdsa_air_v2::EcdsaVerifyV2Layout,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::p256_ecdsa_air_v2::{
        ecdsa_verify_v2_constraints, ecdsa_verify_v2_row_uniform_constraints,
        eval_ecdsa_verify_v2_row0_boundary, eval_ecdsa_verify_v2_row_uniform,
    };

    let n = n_trace * blowup;
    let w = trace_evals_on_lde.len();
    let k_row_uniform = ecdsa_verify_v2_row_uniform_constraints(layout);
    let k_total = ecdsa_verify_v2_constraints(layout);

    assert_eq!(combination_coeffs.len(), k_total);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    // ─── Row-0 Lagrange indicator on the LDE domain ────────────────
    //
    // Pins the row-0 boundary constraints (the 256 (p-2) bit-cell
    // equality checks at the end of `combination_coeffs`) to fire
    // only at the trace-row-0 LDE points.  On padded rows (where the
    // bit cells are 0 even when the constant is 1), the indicator is
    // 0 → boundary constraint contribution vanishes.
    let row0_indicator: Vec<F> = compute_row0_indicator_lde(n_trace, blowup);

    let phi_eval: Vec<F> = {
        #[cfg(feature = "parallel")]
        {
            (0..n).into_par_iter().map(|i| {
                let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
                let row_uniform = eval_ecdsa_verify_v2_row_uniform(&cur, layout);
                let boundary = eval_ecdsa_verify_v2_row0_boundary(&cur, layout);
                let mut acc = F::zero();
                for j in 0..k_row_uniform {
                    acc += combination_coeffs[j] * row_uniform[j];
                }
                let ind = row0_indicator[i];
                for j in 0..boundary.len() {
                    acc += combination_coeffs[k_row_uniform + j] * ind * boundary[j];
                }
                acc
            }).collect()
        }
        #[cfg(not(feature = "parallel"))]
        {
            (0..n).map(|i| {
                let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
                let row_uniform = eval_ecdsa_verify_v2_row_uniform(&cur, layout);
                let boundary = eval_ecdsa_verify_v2_row0_boundary(&cur, layout);
                let mut acc = F::zero();
                for j in 0..k_row_uniform {
                    acc += combination_coeffs[j] * row_uniform[j];
                }
                let ind = row0_indicator[i];
                for j in 0..boundary.len() {
                    acc += combination_coeffs[k_row_uniform + j] * ind * boundary[j];
                }
                acc
            }).collect()
        }
    };
    let k = k_total;

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    // Max constraint degree across v2 components: degree-3 group_add
    // mults dominate; Fp Fermat steps and mul gadgets are degree 2-3.
    let max_deg = 3usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace {
        phi_degree_bound - n_trace
    } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k, max_constraint_degree: max_deg, trace_width: w,
    };
    (c_eval, info)
}

/// Witness-binding-compatible merge for the single-row ECDSA-P256 v2 AIR.
/// Gates the row-0 boundary by a `trace_row == 0` step (via
/// [`crate::p256_ecdsa_air_v2::eval_ecdsa_verify_v2_rowgated_per_row`])
/// instead of the Lagrange `row0_indicator` of
/// [`deep_ali_merge_p256_ecdsa_v2_streaming`], so the prover's `c_eval`
/// and the generic `sub_air_with_trace` verifier (which re-checks the
/// same per-row evaluator at query openings) agree.  Enables an
/// end-to-end witness-binding ECDSA verifier.
pub fn deep_ali_merge_p256_ecdsa_v2_rowgated_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::p256_ecdsa_air_v2::EcdsaVerifyV2Layout,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::p256_ecdsa_air_v2::{
        ecdsa_verify_v2_constraints, eval_ecdsa_verify_v2_rowgated_per_row,
    };
    let n = n_trace * blowup;
    let w = trace_evals_on_lde.len();
    let k = ecdsa_verify_v2_constraints(layout);
    assert_eq!(combination_coeffs.len(), k);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    let eval_at = |i: usize| -> F {
        let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
        let cvals = eval_ecdsa_verify_v2_rowgated_per_row(&cur, i / blowup, layout);
        let mut acc = F::zero();
        for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi_eval: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_at).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_at).collect() }
    } else {
        (0..n).map(eval_at).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 3usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace { phi_degree_bound - n_trace } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k, max_constraint_degree: max_deg, trace_width: w,
    };
    (c_eval, info)
}

/// Composition merge for the **narrow multi-row** P256 ECDSA double-scalar-mult
/// AIR (`p256_ecdsa_double_multirow_air`): one scalar-mult step per row, ~256
/// narrow rows, accumulator threaded row-to-row by transition constraints
/// (the StarkWare-style layout).  This is the width-efficient, bindable form:
/// per-row width is one step (not the entire unrolled chain), so
/// `sub_air_with_trace` openings (`r × per-row-width`) stay small.  The
/// evaluator reads `cur` AND `nxt` (transition), so the FULL binding (with
/// next-row openings) is required.
pub fn deep_ali_merge_ecdsa_double_multirow_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::p256_ecdsa_double_multirow_air::EcdsaDoubleMultirowLayout,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::p256_ecdsa_double_multirow_air::{
        ecdsa_double_multirow_constraints, eval_ecdsa_double_multirow_per_row,
    };
    let n = n_trace * blowup;
    let w = trace_evals_on_lde.len();
    let k = ecdsa_double_multirow_constraints(layout);
    assert_eq!(combination_coeffs.len(), k);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    let eval_at = |i: usize| -> F {
        let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = eval_ecdsa_double_multirow_per_row(&cur, &nxt, i / blowup, n_trace, layout);
        let mut acc = F::zero();
        for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi_eval: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_at).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_at).collect() }
    } else {
        (0..n).map(eval_at).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 3usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace { phi_degree_bound - n_trace } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k, max_constraint_degree: max_deg, trace_width: w,
    };
    (c_eval, info)
}

/// Composition merge for the END-TO-END **multi-row P256 ECDSA verify**
/// AIR (`p256_ecdsa_verify_multirow_air`): the narrow double-scalar-mult
/// kernel (rows 0..K-1) plus the verify TAIL (row K) — group_add, the
/// inverse-free cross-multiply `R.X ≡ {r, r+n}·R.Z (mod p)`, and the
/// final equality.  Transition-aware (`cur` AND `nxt`), so the FULL
/// witness-binding path (with next-row openings) is required.
pub fn deep_ali_merge_ecdsa_verify_multirow_streaming(
    trace_evals_on_lde: &[Vec<F>],
    combination_coeffs: &[F],
    layout: &crate::p256_ecdsa_verify_multirow_air::EcdsaVerifyMultirowLayout,
    pub_inputs: &crate::p256_ecdsa_verify_multirow_air::EcdsaVerifyPublicInputs,
    n_trace: usize,
    blowup: usize,
) -> (Vec<F>, CompositionInfo) {
    use crate::p256_ecdsa_verify_multirow_air::{
        ecdsa_verify_multirow_constraints, eval_ecdsa_verify_multirow_per_row,
    };
    let n = n_trace * blowup;
    let w = trace_evals_on_lde.len();
    let k = ecdsa_verify_multirow_constraints(layout);
    assert_eq!(combination_coeffs.len(), k);
    for col in trace_evals_on_lde {
        assert_eq!(col.len(), n);
    }

    let eval_at = |i: usize| -> F {
        let cur: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][i]).collect();
        let nxt_idx = (i + blowup) % n;
        let nxt: Vec<F> = (0..w).map(|c| trace_evals_on_lde[c][nxt_idx]).collect();
        let cvals = eval_ecdsa_verify_multirow_per_row(&cur, &nxt, i / blowup, n_trace, layout, pub_inputs);
        let mut acc = F::zero();
        for j in 0..k { acc += combination_coeffs[j] * cvals[j]; }
        acc
    };
    let phi_eval: Vec<F> = if enable_parallel(n) {
        #[cfg(feature = "parallel")]
        { (0..n).into_par_iter().map(eval_at).collect() }
        #[cfg(not(feature = "parallel"))]
        { (0..n).map(eval_at).collect() }
    } else {
        (0..n).map(eval_at).collect()
    };

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs.clone();
    padded.resize(n, F::zero());
    let c_eval = domain.fft(&padded);

    let max_deg = 3usize;
    let phi_degree_bound = max_deg * n_trace;
    let quotient_degree_bound = if phi_degree_bound > n_trace { phi_degree_bound - n_trace } else { 0 };
    let info = CompositionInfo {
        phi_degree_bound, quotient_degree_bound,
        rate: quotient_degree_bound as f64 / n as f64,
        num_constraints: k, max_constraint_degree: max_deg, trace_width: w,
    };
    (c_eval, info)
}

// ═══════════════════════════════════════════════════════════════════
//  Legacy single-constraint merge (Fibonacci: Φ̃ = a·s + e − t)
// ═══════════════════════════════════════════════════════════════════

/// Base-field DEEP-ALI merge for the single-constraint Fibonacci AIR.
///
/// Computes c(X) = Φ̃(X) / Z_H(X) where Φ̃(X) = a(X)·s(X) + e(X) − t(X),
/// returning evaluations of c on the FRI domain.
///
/// This is the entry point used by the benchmark harness.
pub fn deep_ali_merge_evals(
    a_eval: &[F],
    s_eval: &[F],
    e_eval: &[F],
    t_eval: &[F],
    omega: F,
    n_trace: usize,
) -> Vec<F> {
    let n = a_eval.len();
    assert!(n > 1 && n.is_power_of_two());
    assert!(n_trace > 0 && n_trace < n);
    assert_eq!(n % n_trace, 0);
    assert_eq!(s_eval.len(), n);
    assert_eq!(e_eval.len(), n);
    assert_eq!(t_eval.len(), n);

    // Φ̃(ω^i) = a(ω^i)·s(ω^i) + e(ω^i) − t(ω^i)
    let mut phi_eval = vec![F::zero(); n];
    for i in 0..n {
        phi_eval[i] = a_eval[i] * s_eval[i] + e_eval[i] - t_eval[i];
    }

    // IFFT → coefficients → divide by Z_H → FFT back
    let domain =
        GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);

    let mut padded = c_coeffs;
    padded.resize(n, F::zero());
    domain.fft(&padded)
}

/// Legacy blinded merge (backward-compatible wrapper).
pub fn deep_ali_merge_evals_blinded(
    a_eval: &[F],
    s_eval: &[F],
    e_eval: &[F],
    t_eval: &[F],
    r_eval_opt: Option<&[F]>,
    beta: F,
    omega: F,
    n_trace: usize,
) -> Vec<F> {
    let n = a_eval.len();
    assert!(n > 1);
    assert!(n.is_power_of_two());
    assert!(n_trace > 0 && n_trace < n);
    assert!(n % n_trace == 0);
    assert_eq!(s_eval.len(), n);
    assert_eq!(e_eval.len(), n);
    assert_eq!(t_eval.len(), n);
    if let Some(r_eval) = r_eval_opt {
        assert_eq!(r_eval.len(), n);
    }

    let mut phi_eval = vec![F::zero(); n];
    for i in 0..n {
        let base = a_eval[i] * s_eval[i] + e_eval[i] - t_eval[i];
        phi_eval[i] = if let Some(r) = r_eval_opt {
            base + beta * r[i]
        } else {
            base
        };
    }

    let domain = GeneralEvaluationDomain::<F>::new(n).expect("power-of-two domain");
    let phi_coeffs = domain.ifft(&phi_eval);
    let c_coeffs = poly_div_zh(&phi_coeffs, n_trace);
    let mut padded = c_coeffs;
    padded.resize(n, F::zero());
    domain.fft(&padded)
}

pub mod fri;
pub mod streaming;
pub mod deep_tower;
pub mod deep;
pub mod cubic_ext;
pub mod tower_field;
pub mod sextic_ext;
pub mod octic_ext;
pub mod air_workloads;
pub mod sha256_air;
pub mod sha512_air;
pub mod ed25519_field;
pub mod ed25519_field_air;
pub mod ed25519_group;
pub mod ed25519_group_air;
pub mod ed25519_scalar;
pub mod ed25519_scalar_air;
pub mod ed25519_scalar_mult_air;
pub mod ed25519_verify;
pub mod ed25519_verify_air;
pub mod ed25519_verify_stranded_gway;
pub mod ed25519_air;
// Ported from the stark-dns fork of deep_ali (2026-05-07): RSA-2048-
// SHA256 PKCS#1 v1.5 native verifier + AIR scaffolding for the
// in-circuit verify gadget.  Used by mmiyc as a designated-verifier
// PoK for the income gate.
pub mod rsa2048;
pub mod rsa2048_field_air;
pub mod rsa2048_exp_air;
pub mod rsa2048_stacked_air;

// ECDSA-P256 (FIPS 186-4) verify AIR — ported from the stark-swarm
// fork's `deep_ali` (commits 61e6dfd → 6f5e3c4 across 4 sprints).
// Composes F_p, F_n, group, scalar-mul, Fermat-inversion sub-AIRs
// into a top-level verify gadget.  Phase 5 v0 takes pre-computed
// (u_1, u_2) — the Fermat-inversion gadget for deriving them lives
// in `p256_fermat_air` and is wired-ready for the full composition.
pub mod p256_field;
pub mod p256_field_air;
pub mod p256_scalar;
pub mod p256_scalar_air;
pub mod p256_group;
pub mod p256_group_air;
pub mod p256_scalar_mul_air;
pub mod p256_scalar_mul_multirow_air;
pub mod p256_fermat_air;
pub mod p256_fp_fermat_air;
pub mod p256_ecdsa_double_multirow_air;
pub mod p256_ecdsa_verify_multirow_air;
pub mod ecdsa_verify_stranded;
pub mod ecdsa_verify_stranded_gway;
pub mod p256_ecdsa;
pub mod p256_ecdsa_air;
pub mod p256_ecdsa_air_v2;
pub mod p256_ecdsa_air_v2_wi;
pub mod p256_joint_msm_air;
pub mod p256_const_mux_air;
pub mod p256_windowed_q_air;
pub mod ed25519_msm_air;
pub mod range_lookup_air;
pub mod range_lookup_acc_air;
pub mod range_lookup_wire_air;

// ML-DSA-44 (FIPS 204) verify AIR — phase 1 scaffolding (2026-05-07).
// Native references + Z_q field AIR + NTT layout + Keccak-f[1600]
// θ-step framework.  The full AIR is multi-session work; see
// `match-me-if-you-can/docs/ml_dsa_air_plan.md` for phasing.
pub mod ml_dsa;
pub mod ml_dsa_field;
pub mod ml_dsa_field_air;
pub mod ml_dsa_ntt;
pub mod ml_dsa_ntt_air;
pub mod ml_dsa_decompose;
pub mod ml_dsa_decompose_air;
pub mod ml_dsa_norm_check;
pub mod ml_dsa_norm_check_air;
pub mod ml_dsa_w1_encode;
pub mod ml_dsa_w1_encode_air;
pub mod ml_dsa_sample_in_ball;
pub mod ml_dsa_verify_air;
pub mod ml_dsa_verify_air_v15;
pub mod ml_dsa_ntt_chained_air;
pub mod ml_dsa_verify_air_v17;
pub mod ml_dsa_v17_stranded;
pub mod ml_dsa_codec;
pub mod keccak_f1600;
pub mod keccak_f1600_air;
pub mod ml_dsa_shake_absorb_air;
pub mod ml_dsa_shake_absorb_multi_air;
pub mod ml_dsa_shake_squeeze_air;
pub mod ml_dsa_rej_chunk_air;
pub mod ml_dsa_rej_count_air;
pub mod ml_dsa_expand_a_one_lite;
pub mod ml_dsa_sample_in_ball_t1_t2;
pub mod permutation_argument;
pub mod ml_dsa_use_hint_air;
pub mod ml_dsa_transcript;
pub mod ml_dsa_intt_via_t7;
pub mod ml_dsa_verify_air_v2_layout;
pub mod ml_dsa_verify_air_v2_orchestration;
pub mod sub_air_with_trace;
/// v2 perm-arg rebuild foundation (Session 4): FRI commit on a
/// sub-AIR's binding cells, packed into a single polynomial.  The
/// OOD-eval cross-trace consistency check (Session 5+) will build
/// on top of this.  See module docstring + memory entry
/// `project_mmiyc_v2_soundness_gap.md`.
pub mod binding_cells_commit;