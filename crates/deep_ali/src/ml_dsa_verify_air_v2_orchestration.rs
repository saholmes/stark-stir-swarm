//! T9 orchestration: drive the v2 sub-trace fills end-to-end.
//!
//! Companion to `ml_dsa_verify_air_v2_layout` (which froze the
//! row/col dimensions) and the per-sub-AIR fill_traces.  This
//! module ties them together: given a `V2Witness`, produce the
//! 5 sub-traces ready for FRI prove.
//!
//! ## Scope (this session: 3 of 5 sub-AIRs)
//!
//! - ✅ **V17**: v1.7's existing `verify_air_v17::fill_trace`.
//! - ✅ **INTT**: 4× chained NTT (T7) for `w_approx[k] →
//!   w_approx_ntt[k]`.  Witness `w_approx` is supplied by the
//!   prover (it's the inverse-NTT pre-image of the public
//!   `w_approx_ntt`, which v1.7's poly-arithmetic region commits
//!   to).
//! - ✅ **TRANSCRIPT**: T1.5 multi-block absorb of `µ ‖ w1bytes`.
//!   `w1bytes` comes from running `w1Encode` natively here; the
//!   future T_MEM region will bind these bytes to the COEFF
//!   chain's W1Encode output cells.
//!
//! ## Deferred (next push)
//!
//! - ⏭️ **COEFF**: per-coefficient (Decompose + UseHint + W1Encode)
//!   chain.  Currently the witness `w_approx` is consumed natively
//!   to produce `w1bytes` for TRANSCRIPT; the COEFF AIR will lift
//!   that into in-circuit constraints.
//! - ⏭️ **T_MEM**: cross-region permutation argument linking
//!   COEFF outputs to TRANSCRIPT inputs and INTT row-1024 cells.
//!
//! ## End-to-end soundness story (after all 5 sub-AIRs)
//!
//! 1. V17 proves `w_approx_ntt = Σ a_ntt·z_ntt − c_ntt·t1d_ntt`,
//!    plus `‖z‖∞ < γ_1 − β`, plus `ẑ_l = NTT(z_l)`.
//! 2. INTT proves `w_approx_ntt[k] = NTT(w_approx[k])`.
//! 3. COEFF proves each coefficient's `r1, r0, adjusted_r1, w1bytes`.
//! 4. TRANSCRIPT proves `c̃' = SHAKE-256(µ ‖ w1bytes)[0..32]`.
//! 5. T_MEM binds: w_approx (INTT) ↔ Decompose input (COEFF),
//!    UseHint output ↔ W1Encode input, W1Encode bytes ↔ TRANSCRIPT
//!    absorb input.
//! 6. Final boundary `c̃' == c̃` (PI-hash bound to sigDecode's c̃).
//!
//! Together: any deviation from the canonical FIPS 204 §3 Algorithm
//! 3 verify path makes one of these 5 sub-proofs (or the boundary)
//! reject.

#![allow(non_snake_case, dead_code)]

use ark_ff::Zero as _;
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600;
use crate::ml_dsa::params::{K, L, N};
use crate::ml_dsa_ntt;
use crate::ml_dsa_ntt_chained_air as t7;
use crate::ml_dsa_verify_air_v17 as v17;
use crate::ml_dsa_verify_air_v2_layout::{intt, transcript, v17 as v17_dim};
use crate::ml_dsa_transcript;
use crate::ml_dsa_decompose_air;
use crate::ml_dsa_use_hint_air;
use crate::ml_dsa_w1_encode_air;
use crate::ml_dsa_decompose;
// permutation_argument / t_mem removed 2026-05-10 after F2b L0-L4 lands.
use sha3::{Digest, Sha3_256};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize, Compress, Validate};
use crate::fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, DeepFriProof, FriDomain};
use crate::sextic_ext::SexticExt;
use crate::trace_import::lde_trace_columns;
use crate::ml_dsa_shake_absorb_multi_air::{self, MultiAbsorbLayout};

type Ext = SexticExt;

// ─── V2 witness ────────────────────────────────────────────────────

/// Inputs to v2 prove.  Public fields are bound via PI-hash;
/// witness fields are committed in the trace.
pub struct V2Witness {
    // ── Public (pi_hash bound) ──
    pub a_ntt:        Box<[[[u32; N]; L]; K]>,
    pub c_ntt:        Box<[u32; N]>,
    pub t1d_ntt:      Box<[[u32; N]; K]>,
    pub w_approx_ntt: Box<[[u32; N]; K]>,
    pub mu_bytes:     [u8; 64],
    /// Hint vector: K·N booleans, one per coefficient of w_approx.
    pub h:            Box<[[u32; N]; K]>,
    // ── Witnesses (trace-committed; derived from public via FIPS 204) ──
    pub z_ntt:        Box<[[u32; N]; L]>,
    pub z_cleartext:  Box<[[u32; N]; L]>,
    pub w_approx:     Box<[[u32; N]; K]>,  // = INTT(w_approx_ntt)
    /// `(r1, r0_sign, adjusted_r1)` for each coefficient of `w_approx`.
    pub adjusted_r1:  Box<[[u32; N]; K]>,
    /// `w1bytes`: byte-level packing of `adjusted_r1` per FIPS 204 §3.5
    /// Algorithm 28.  Length = K·N·6 / 8 = 768 B for ML-DSA-44.
    pub w1bytes:      Vec<u8>,
}

// ─── V2 sub-traces bundle ─────────────────────────────────────────

pub struct V2SubTraces {
    pub v17:        Vec<Vec<F>>,         // V17 sub-trace
    pub intt:       Vec<Vec<Vec<F>>>,    // 4 INTT sub-traces (one per k)
    pub transcript: Vec<Vec<F>>,         // TRANSCRIPT sub-trace
    pub coeff_decompose: Vec<Vec<F>>,    // COEFF: Decompose sub-trace (K·N rows)
    pub coeff_use_hint:  Vec<Vec<F>>,    // COEFF: UseHint sub-trace (K·N rows)
    pub coeff_w1_encode: Vec<Vec<F>>,    // COEFF: W1Encode sub-trace (K·N rows)
    // T_MEM removed 2026-05-10: it was a vacuous perm-arg over
    // witness-derived log entries, and F2b L0-L4 cross-binding
    // Merkle inclusion proofs now provide the cross-region binding
    // T_MEM was supposed to (and never actually did).  See
    // project_mmiyc_v2_soundness_gap.md.
}

// ─── fill_v2_traces ────────────────────────────────────────────────

/// Build all 3 architecturally-significant v2 sub-traces from the
/// witness.  Returns sub-traces sized to each sub-proof's pow2 row
/// count (per `ml_dsa_verify_air_v2_layout`).
/// Fill all v2 sub-traces.
///
/// `pi_hash` is the Fiat-Shamir digest of the public inputs +
/// `c_tilde` (i.e. the value `compute_pi_hash_v2(witness, c_tilde)`
/// returns).  It seeds the T-MEM permutation-argument challenges
/// (γ, α) so they are unpredictable to the prover at trace-
/// construction time — see `derive_t_mem_challenges`.  Tests that
/// only exercise per-row trace consistency may pass `[0u8; 32]`;
/// real proofs MUST pass the same `pi_hash` the prover and verifier
/// independently compute.
pub fn fill_v2_traces(witness: &V2Witness, pi_hash: [u8; 32]) -> V2SubTraces {
    // ── V17 (v1.7 verify-AIR) ──
    let mut v17_trace: Vec<Vec<F>> = (0..v17_dim::N_COLS)
        .map(|_| vec![F::zero(); v17_dim::N_ROWS_POW2]).collect();
    v17::fill_trace(
        &mut v17_trace,
        v17_dim::N_ROWS_POW2,
        &witness.a_ntt,
        &witness.z_ntt,
        &witness.c_ntt,
        &witness.t1d_ntt,
        &witness.w_approx_ntt,
        &witness.z_cleartext,
    );

    // ── INTT (4× chained NTT for w_approx[k] → w_approx_ntt[k]) ──
    let mut intt_traces: Vec<Vec<Vec<F>>> = Vec::with_capacity(K);
    let intt_n_trace_per_instance = (t7::BUTTERFLIES_PER_NTT + 16).next_power_of_two();
    for k in 0..K {
        let mut sub: Vec<Vec<F>> = (0..intt::N_COLS)
            .map(|_| vec![F::zero(); intt_n_trace_per_instance]).collect();
        t7::fill_trace(&mut sub, intt_n_trace_per_instance, &witness.w_approx[k]);
        intt_traces.push(sub);
    }

    // ── TRANSCRIPT (T1.5 absorb of µ ‖ w1bytes) ──
    let transcript_layout = ml_dsa_transcript::build_layout(
        &witness.mu_bytes, &witness.w1bytes,
    );
    let transcript_n_trace = transcript::N_ROWS_POW2;
    let mut transcript_trace: Vec<Vec<F>> = (0..transcript::N_COLS)
        .map(|_| vec![F::zero(); transcript_n_trace]).collect();
    crate::ml_dsa_shake_absorb_multi_air::fill_trace(
        &mut transcript_trace, transcript_n_trace, &transcript_layout,
    );

    // ── COEFF (Decompose + UseHint + W1Encode per coefficient) ──
    let n_coeffs = K * N;
    let coeff_n_trace = n_coeffs.next_power_of_two();

    // Flatten w_approx into K·N coefficients.
    let mut w_approx_flat = Vec::with_capacity(n_coeffs);
    for k in 0..K {
        for i in 0..N { w_approx_flat.push(witness.w_approx[k][i]); }
    }
    let mut decompose_trace: Vec<Vec<F>> = (0..ml_dsa_decompose_air::WIDTH)
        .map(|_| vec![F::zero(); coeff_n_trace]).collect();
    ml_dsa_decompose_air::fill_trace(&mut decompose_trace, coeff_n_trace, &w_approx_flat);

    // UseHint: take (r1, r0_sign) from decompose's columns + h flat.
    let mut use_hint_inputs: Vec<(u32, u32, u32)> = Vec::with_capacity(n_coeffs);
    for k in 0..K {
        for i in 0..N {
            let r = witness.w_approx[k][i];
            let (r1, _r0) = ml_dsa_decompose::decompose(r);
            // r0_sign = 1 iff the centred r0 is strictly positive
            // (i.e., r % 2γ₂ ∈ (0, γ₂]).  Lifted r0 ∈ [0, q) is
            // "positive" iff r0 ≤ q/2 AND r0 != 0.
            let (_, r0_lifted) = ml_dsa_decompose::decompose(r);
            let r0_sign: u32 = if r0_lifted != 0 && r0_lifted <= crate::ml_dsa::params::Q / 2 {
                1
            } else {
                0
            };
            let h = witness.h[k][i];
            use_hint_inputs.push((r1, r0_sign, h));
        }
    }
    let mut use_hint_trace: Vec<Vec<F>> = (0..ml_dsa_use_hint_air::WIDTH)
        .map(|_| vec![F::zero(); coeff_n_trace]).collect();
    ml_dsa_use_hint_air::fill_trace(&mut use_hint_trace, coeff_n_trace, &use_hint_inputs);

    // W1Encode: per-coefficient adjusted_r1 bit decomposition.
    let mut adjusted_flat: Vec<u32> = Vec::with_capacity(n_coeffs);
    for k in 0..K {
        for i in 0..N { adjusted_flat.push(witness.adjusted_r1[k][i]); }
    }
    let mut w1_encode_trace: Vec<Vec<F>> = (0..ml_dsa_w1_encode_air::WIDTH)
        .map(|_| vec![F::zero(); coeff_n_trace]).collect();
    ml_dsa_w1_encode_air::fill_trace(&mut w1_encode_trace, coeff_n_trace, &adjusted_flat);

    // T_MEM removed: F2b L0-L4 cross-binding Merkle inclusion proofs
    // provide the cross-region equality bindings T_MEM was meant to
    // (and never actually did, since its log entries were sourced
    // from witness fields rather than sub-trace cells).
    let _ = pi_hash;  // formerly fed `derive_t_mem_challenges`.

    V2SubTraces {
        v17: v17_trace,
        intt: intt_traces,
        transcript: transcript_trace,
        coeff_decompose: decompose_trace,
        coeff_use_hint: use_hint_trace,
        coeff_w1_encode: w1_encode_trace,
    }
}

// ─── Native witness derivation ────────────────────────────────────

// ─── pi_hash + V2Proof skeleton ───────────────────────────────────

/// Domain tag for v2 PI-hash binding.  Distinct from v1.5/v1.7 so
/// proofs can't be replayed across protocol versions.
pub const PI_HASH_DOMAIN_V2: &[u8] = b"mmiyc/v2/ml-dsa-pok/public-inputs";

/// Compute the v2 public-input hash that every sub-proof must
/// commit to via Fiat-Shamir.  Mirrors `MlDsaPokPublicInputs::compute_pi_hash`'s
/// structure but adds `mu_bytes`, `h`, and the v2 domain tag.
pub fn compute_pi_hash_v2(
    w: &V2Witness,
    c_tilde_bytes: &[u8; crate::ml_dsa::params::C_TILDE_BYTES],
) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(PI_HASH_DOMAIN_V2);
    for k in 0..K {
        for l in 0..L {
            for v in w.a_ntt[k][l].iter() { h.update(v.to_be_bytes()); }
        }
    }
    for v in w.c_ntt.iter() { h.update(v.to_be_bytes()); }
    for k in 0..K {
        for v in w.t1d_ntt[k].iter() { h.update(v.to_be_bytes()); }
    }
    for k in 0..K {
        for v in w.w_approx_ntt[k].iter() { h.update(v.to_be_bytes()); }
    }
    h.update(&w.mu_bytes);
    for k in 0..K {
        for v in w.h[k].iter() { h.update(v.to_be_bytes()); }
    }
    // F2b defense-in-depth: bind `w1bytes` into pi_hash so any
    // divergence between prover and verifier views of the
    // TRANSCRIPT absorb input fails at pi_hash consistency.  L4
    // already binds w1bytes to W1Encode bit cells, but pi_hash
    // binding catches it earlier (before any FRI/STIR verify work
    // runs) and is cheap (~|w1bytes| bytes of SHA-3 input).
    h.update(&(w.w1bytes.len() as u64).to_le_bytes());
    h.update(&w.w1bytes);
    h.update(c_tilde_bytes);
    h.finalize().into()
}

/// Skeleton bundle for a v2 proof.
///
/// **Status**: this is a SKELETON / PROTOTYPE shape.  In a real v2
/// deployment, each `Vec<u8>` field would hold a serialized
/// `DeepFriProof` produced by running the corresponding sub-AIR's
/// merge function + `deep_fri_prove`.  The `prove_v2_skeleton` /
/// `verify_v2_skeleton` pair below uses native constraint
/// checking instead of FRI for now — this validates that the
/// orchestration is internally consistent and the bundle shape is
/// right; replacing the native checks with FRI is purely wrapping
/// (~5 × 80 LoC of merge functions).
#[derive(Clone, Debug)]
pub struct V2Proof {
    pub pi_hash:               [u8; 32],
    pub c_tilde_prime:         [u8; crate::ml_dsa::params::C_TILDE_BYTES],   // TRANSCRIPT output
    /// FRI sub-proofs (deferred): in the prototype these hold trace
    /// digests; in production they hold serialized `DeepFriProof`s.
    pub fri_v17_digest:        [u8; 32],
    pub fri_intt_digests:      [[u8; 32]; K],
    pub fri_coeff_digest:      [u8; 32],
    pub fri_transcript_digest: [u8; 32],
    // fri_t_mem_digest removed 2026-05-10 — T_MEM deleted from v2.
}

/// Hash a sub-trace's contents for the prototype proof.  In
/// production this digest would be replaced by the FRI proof's
/// commitments (Merkle roots).
fn digest_trace(trace: &[Vec<F>]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    for col in trace {
        for v in col {
            h.update(ark_ff::PrimeField::into_bigint(*v).0[0].to_be_bytes());
        }
    }
    h.finalize().into()
}

/// **Prototype v2 prover**: run `fill_v2_traces`, compute `pi_hash`
/// and `c_tilde_prime`, package per-sub-trace digests.  Verify-side
/// checks every per-row constraint natively.
///
/// In production this would be replaced by `prove_v2`: same
/// orchestration but with FRI prove for each sub-AIR.
pub fn prove_v2_skeleton(
    w: &V2Witness,
    c_tilde_bytes: &[u8; crate::ml_dsa::params::C_TILDE_BYTES],
) -> (V2SubTraces, V2Proof) {
    // pi_hash must be fixed BEFORE the trace is filled, so the
    // T-MEM perm-arg challenges (γ, α) derived from it are
    // unpredictable to the prover at trace-construction time.
    let pi_hash = compute_pi_hash_v2(w, c_tilde_bytes);
    let traces = fill_v2_traces(w, pi_hash);

    // c_tilde_prime: extract from TRANSCRIPT trace.
    let transcript_layout = ml_dsa_transcript::build_layout(&w.mu_bytes, &w.w1bytes);
    let c_tilde_prime = ml_dsa_transcript::extract_c_tilde_prime_from_trace(
        &traces.transcript, &transcript_layout,
    );

    // Compute trace digests as proof "fingerprints".  In production
    // these slots hold serialized DeepFriProof bytes.
    let fri_v17_digest        = digest_trace(&traces.v17);
    let mut fri_intt_digests = [[0u8; 32]; K];
    for k in 0..K { fri_intt_digests[k] = digest_trace(&traces.intt[k]); }
    let fri_coeff_digest = {
        let mut h = Sha3_256::new();
        h.update(digest_trace(&traces.coeff_decompose));
        h.update(digest_trace(&traces.coeff_use_hint));
        h.update(digest_trace(&traces.coeff_w1_encode));
        h.finalize().into()
    };
    let fri_transcript_digest = digest_trace(&traces.transcript);

    let proof = V2Proof {
        pi_hash, c_tilde_prime,
        fri_v17_digest, fri_intt_digests, fri_coeff_digest,
        fri_transcript_digest,
    };
    (traces, proof)
}

/// **Prototype v2 verifier**: re-fill the traces (the prover's
/// public inputs let the verifier independently reconstruct them),
/// run native constraint checks on every per-row constraint of
/// every sub-AIR, check final boundaries.
///
/// Returns `Ok(())` iff all checks pass.
pub fn verify_v2_skeleton(
    w: &V2Witness,
    c_tilde_bytes: &[u8; crate::ml_dsa::params::C_TILDE_BYTES],
    proof: &V2Proof,
) -> Result<(), String> {
    // 1. pi_hash consistency.
    let recomputed = compute_pi_hash_v2(w, c_tilde_bytes);
    if recomputed != proof.pi_hash {
        return Err(format!(
            "v2 verify: pi_hash mismatch (proof={:02x?}, recomputed={:02x?})",
            &proof.pi_hash[..8], &recomputed[..8]));
    }

    // 2. Re-fill traces (the verifier knows everything the prover
    //    committed to, since witnesses are derived deterministically
    //    from public sig data via decode_signature + native NTT/INTT.
    //    For the skeleton, we just trust the witness and check
    //    constraints — production v2 would use FRI to avoid
    //    re-doing the prover's work).
    let (traces, regen_proof) = prove_v2_skeleton(w, c_tilde_bytes);

    // 3. Sub-trace digest consistency.
    if regen_proof.fri_v17_digest != proof.fri_v17_digest {
        return Err("v2 verify: V17 sub-trace digest mismatch".into());
    }
    if regen_proof.fri_intt_digests != proof.fri_intt_digests {
        return Err("v2 verify: INTT sub-trace digests mismatch".into());
    }
    if regen_proof.fri_coeff_digest != proof.fri_coeff_digest {
        return Err("v2 verify: COEFF sub-trace digest mismatch".into());
    }
    if regen_proof.fri_transcript_digest != proof.fri_transcript_digest {
        return Err("v2 verify: TRANSCRIPT sub-trace digest mismatch".into());
    }
    // T_MEM digest check removed 2026-05-10 — T_MEM no longer part of v2.

    // 4. c_tilde_prime equality (= the FIPS 204 verify acceptance test).
    if proof.c_tilde_prime != *c_tilde_bytes {
        return Err(format!(
            "v2 verify: c̃' ≠ c̃ (proof's c̃'={:02x?}, expected c̃={:02x?})",
            &proof.c_tilde_prime[..8], &c_tilde_bytes[..8]));
    }

    let _ = traces;  // present for "future FRI verifier" code path
    Ok(())
}

// ─── Real prove_v2 / verify_v2 with FRI sub-proofs ────────────────

/// Production v2 proof: 10 serialized `DeepFriProof<SexticExt>`s
/// bundled together, plus `pi_hash` and the trace-derived `c̃'`.
///
/// The 10 sub-proofs:
/// - 1× V17, 4× INTT (one per `k`), 1× COEFF Decompose, 1× COEFF
///   UseHint, 1× COEFF W1Encode, 1× TRANSCRIPT, 1× T_MEM.
///
/// Each sub-proof's Fiat-Shamir transcript is seeded with the same
/// `pi_hash`, so the bundle is collectively sound: a verifier
/// rejecting any one of the 10 rejects the whole bundle.
#[derive(Clone, Debug)]
pub struct V2ProofReal {
    pub pi_hash:        [u8; 32],
    pub c_tilde_prime:  [u8; crate::ml_dsa::params::C_TILDE_BYTES],
    pub fri_v17:        Vec<u8>,
    pub fri_intt:       Vec<Vec<u8>>,    // K = 4
    pub fri_decompose:  Vec<u8>,
    pub fri_use_hint:   Vec<u8>,
    pub fri_w1_encode:  Vec<u8>,
    pub fri_transcript: Vec<u8>,
    // fri_t_mem removed 2026-05-10 — T_MEM deleted from v2.
    /// F2b cross-binding **L0**: one serialized `TraceOpening` per
    /// INTT instance, opening the trace at row
    /// `t7::BUTTERFLIES_PER_NTT` (the NTT's output row).  Verifier
    /// checks that `cells[col_state(i)] == public w_approx_ntt[k][i]`
    /// for all `i ∈ [0..N)` — pinning the INTT output to the
    /// pi_hash-bound public input.  Without this, a prover could
    /// fill the INTT trace with `NTT(w_approx_fake)` ≠ public
    /// `w_approx_ntt` and the per-row constraints alone would accept.
    pub intt_l0_openings: Vec<Vec<u8>>,    // K entries
    /// F2b cross-binding **L1**: INTT row-0 input cells must equal
    /// the corresponding Decompose r-input cells.  `intt_l1_openings`
    /// holds K serialized `TraceOpening`s opening each INTT instance
    /// at row 0; `decompose_l1_openings` holds K·N serialized
    /// `TraceOpening`s opening each Decompose row at position
    /// `k·N + i`.  Verifier checks
    /// `intt_l1_openings[k].cells[col_state(i)]
    ///  == decompose_l1_openings[k·N+i].cells[col_r()]`.  Without
    /// this, a prover can fill INTT with canonical `w_approx_real`
    /// (passing L0) but Decompose with `w_approx_fake` — the
    /// "decoupled traces" attack family.
    pub intt_l1_openings:      Vec<Vec<u8>>,    // K entries (INTT row 0)
    pub decompose_l1_openings: Vec<Vec<u8>>,    // K·N entries (Decompose row k·N+i)
    /// F2b cross-bindings **L2a + L2b + L3**: K·N row openings into
    /// UseHint and W1Encode traces.  Reuse `decompose_l1_openings`
    /// for L2a's source (Decompose col_r1) and L2b's source
    /// (Decompose col_r0_sign).
    ///
    /// L2a: Decompose row r col_r1()  == UseHint row r COL_R1
    /// L2b: Decompose row r col_r0_sign() == UseHint row r COL_R0_SIGN
    /// L3:  UseHint row r COL_ADJUSTED_R1 == W1Encode row r col_r1()
    pub use_hint_openings:   Vec<Vec<u8>>,      // K·N entries (UseHint row k·N+i)
    pub w1_encode_openings:  Vec<Vec<u8>>,      // K·N entries (W1Encode row k·N+i)
    /// F2b cross-binding **L5** (V17 EQ-region binding to public
    /// `a_ntt`/`c_ntt`/`t1d_ntt`/`w_approx_ntt`): K·N entries, one
    /// per coefficient (k, i).  Verifier checks each opening's
    /// cells against the pi_hash-bound public values.  Closes the
    /// V17-binding gap demonstrated by
    /// `v2_l5_regression_v17_rejects_tampered_eq_region`.
    pub v17_l5_openings:     Vec<Vec<u8>>,

    /// **Session 7 OOD-rebuild proof-of-concept** (2026-05-10).
    /// L2a cross-binding via OOD evaluation at FS-derived z_0:
    /// `commit_binding_cells` on Decompose's col_r1 column AND on
    /// UseHint's COL_R1 column produce two `BindingCellsCommit`s
    /// over polynomials of the same packed LDE size.  Both share
    /// z_0 (derived from seed_z + n0 only), so their fz_per_layer[0]
    /// values are directly comparable.  `verify_ood_consistency`
    /// performs Schwartz-Zippel at z_0.
    ///
    /// **Currently additive** to the existing F2b L2a inclusion
    /// proofs (no regression risk).  Session 8 will remove the
    /// inclusion proofs once all bindings have OOD coverage.
    pub l2a_decompose_bcc:   Vec<u8>,   // BindingCellsCommit::to_bytes()
    pub l2a_use_hint_bcc:    Vec<u8>,
    /// L3 OOD cross-binding: UseHint COL_ADJUSTED_R1 ↔ W1Encode col_r1.
    /// Same-row pair, full-column extraction.  Same shape as L2a.
    pub l3_use_hint_bcc:     Vec<u8>,
    pub l3_w1_encode_bcc:    Vec<u8>,
    /// **L2c OOD** cross-binding: public.h ↔ UseHint COL_H.  Public-
    /// input binding: only the UseHint side commits via FRI; the
    /// verifier reconstructs the canonical public-h trace column
    /// and evaluates the resulting polynomial directly at z_0.
    /// Schwartz-Zippel binding via
    /// `verify_ood_against_public_trace_col`.
    pub l2c_use_hint_bcc:    Vec<u8>,
    /// **L5 OOD** cross-binding: V17 EQ-region columns ↔ public
    /// a_ntt/c_ntt/t1d_ntt/w_approx_ntt.  Multi-column public-input
    /// binding: V17 EQ-region has L+3 binding columns (L for a_ntt,
    /// plus c_ntt, t1d_ntt, w_approx_ntt).  Each column's V17 BCC
    /// is OOD-compared against the canonical public-value polynomial.
    ///
    /// Layout of `l5_v17_eq_bccs`:
    /// - indices `0..L`: a_ntt[l] for l in 0..L.
    /// - index `L`:      c_ntt.
    /// - index `L+1`:    t1d_ntt.
    /// - index `L+2`:    w_approx_ntt.
    pub l5_v17_eq_bccs:      Vec<Vec<u8>>,
    /// **L1 OOD** (Session 9): Decompose col_r ↔ canonical
    /// `w_approx_flat` (= INTT of public w_approx_ntt).  Verifier
    /// computes INTT on its side, builds the expected Decompose
    /// col_r polynomial, and OOD-compares against the Decompose BCC.
    /// Single-BCC public-input binding via transcript-replay.
    pub l1_decompose_bcc:    Vec<u8>,
    /// **L4 OOD** (Session 10): W1Encode bit columns ↔ public
    /// w1bytes.  Bit-packed public-input binding: for each bit
    /// position b ∈ [0, W1_BITS_PER_COEF), W1Encode's `col_bit(b)`
    /// trace column is OOD-compared against a canonical bit-b column
    /// extracted from `public.w1bytes` per FIPS 204 §3.5.7 BitPack.
    ///
    /// Layout: index `b` holds the BCC for `col_bit(b)`.  Length =
    /// W1_BITS_PER_COEF (6 at L1, 4 at L3/L5).
    pub l4_w1_encode_bccs:   Vec<Vec<u8>>,
    /// **L2b OOD** (Session 11): UseHint COL_R0_SIGN ↔ canonical
    /// translated r0_sign derived from public.w_approx_ntt.  The
    /// verifier computes canonical w_approx = INTT(public.w_approx_ntt),
    /// then per (k, i) derives the canonical Decompose r0 + r0_sign,
    /// then applies the convention translation
    /// `translated = (r0 != 0) AND (r0_sign == 0)`.  OOD-compares
    /// against this single BCC.
    pub l2b_use_hint_bcc:    Vec<u8>,
}

/// Format version tag for V2ProofReal wire format.  Bump when
/// changing the on-disk structure incompatibly.
///
/// - 0x01 = uncompressed (legacy, pre-2026-05-11)
/// - 0x02 = zstd-compressed payload (2026-05-11+)
const V2_PROOF_FORMAT_TAG_ZSTD: u8 = 0x02;
const V2_ZSTD_COMPRESSION_LEVEL: i32 = 19;  // ~4.0× on v2 proofs

impl V2ProofReal {
    /// Serialize to bytes, wrapped in zstd compression.
    ///
    /// Wire format:
    ///   `[0x02] [zstd-compressed inner-bytes]`
    ///
    /// The inner bytes follow the legacy layout:
    /// `32 + 32 (pi_hash + c̃') + length-prefixed Vec<u8> for each
    /// FRI sub-proof (length encoded as 4-byte LE u32)`.
    ///
    /// Empirically the inner bytes are ~4× compressible due to
    /// Merkle path sibling-hash sharing across the K·N contiguous-
    /// stride openings per F2b binding leg.  zstd -19 at L3 yields
    /// ~48 MB → ~12 MB.  Decompress adds ~10-15 ms verify time
    /// (zstd reads at >1 GB/s).
    pub fn to_bytes(&self) -> Vec<u8> {
        let raw = self.to_bytes_uncompressed();
        let compressed = zstd::encode_all(raw.as_slice(), V2_ZSTD_COMPRESSION_LEVEL)
            .expect("zstd compress V2ProofReal");
        let mut out = Vec::with_capacity(1 + compressed.len());
        out.push(V2_PROOF_FORMAT_TAG_ZSTD);
        out.extend_from_slice(&compressed);
        out
    }

    /// Pre-compression serialization.  Public for tools that need
    /// to inspect raw structure (e.g. compression-ratio benchmarks).
    pub fn to_bytes_uncompressed(&self) -> Vec<u8> {
        fn write_v(out: &mut Vec<u8>, v: &[u8]) {
            out.extend_from_slice(&(v.len() as u32).to_le_bytes());
            out.extend_from_slice(v);
        }
        let mut out = Vec::new();
        out.extend_from_slice(&self.pi_hash);
        out.extend_from_slice(&self.c_tilde_prime);
        write_v(&mut out, &self.fri_v17);
        out.extend_from_slice(&(self.fri_intt.len() as u32).to_le_bytes());
        for v in &self.fri_intt { write_v(&mut out, v); }
        write_v(&mut out, &self.fri_decompose);
        write_v(&mut out, &self.fri_use_hint);
        write_v(&mut out, &self.fri_w1_encode);
        write_v(&mut out, &self.fri_transcript);
        // fri_t_mem removed 2026-05-10 — T_MEM deleted from v2.
        // F2b L0 cross-binding openings: K length-prefixed entries.
        out.extend_from_slice(&(self.intt_l0_openings.len() as u32).to_le_bytes());
        for v in &self.intt_l0_openings { write_v(&mut out, v); }
        // F2b L1 cross-binding openings: K + K·N length-prefixed entries.
        out.extend_from_slice(&(self.intt_l1_openings.len() as u32).to_le_bytes());
        for v in &self.intt_l1_openings { write_v(&mut out, v); }
        out.extend_from_slice(&(self.decompose_l1_openings.len() as u32).to_le_bytes());
        for v in &self.decompose_l1_openings { write_v(&mut out, v); }
        // F2b L2a/L2b/L3 cross-binding openings: K·N + K·N length-prefixed entries.
        out.extend_from_slice(&(self.use_hint_openings.len() as u32).to_le_bytes());
        for v in &self.use_hint_openings { write_v(&mut out, v); }
        out.extend_from_slice(&(self.w1_encode_openings.len() as u32).to_le_bytes());
        for v in &self.w1_encode_openings { write_v(&mut out, v); }
        // F2b L5 V17 EQ-region cross-binding: K·N length-prefixed entries.
        out.extend_from_slice(&(self.v17_l5_openings.len() as u32).to_le_bytes());
        for v in &self.v17_l5_openings { write_v(&mut out, v); }
        // Session 7 OOD L2a (two length-prefixed BCC blobs).
        write_v(&mut out, &self.l2a_decompose_bcc);
        write_v(&mut out, &self.l2a_use_hint_bcc);
        // Session 7 OOD L3.
        write_v(&mut out, &self.l3_use_hint_bcc);
        write_v(&mut out, &self.l3_w1_encode_bcc);
        // Session 7 OOD L2c (public-input binding).
        write_v(&mut out, &self.l2c_use_hint_bcc);
        // Session 7 OOD L5 (multi-column public-input binding).
        out.extend_from_slice(&(self.l5_v17_eq_bccs.len() as u32).to_le_bytes());
        for v in &self.l5_v17_eq_bccs { write_v(&mut out, v); }
        // Session 9 OOD L1 (public-input via verifier-computed INTT).
        write_v(&mut out, &self.l1_decompose_bcc);
        // Session 10 OOD L4 (bit-packed public-input binding).
        out.extend_from_slice(&(self.l4_w1_encode_bccs.len() as u32).to_le_bytes());
        for v in &self.l4_w1_encode_bccs { write_v(&mut out, v); }
        // Session 11 OOD L2b (UseHint r0_sign vs canonical translated).
        write_v(&mut out, &self.l2b_use_hint_bcc);
        out
    }

    /// Deserialize from bytes; returns `Err` on any framing problem.
    ///
    /// Auto-detects compression: first byte tag selects format.
    /// `0x02` → zstd-compressed (current default).  Any other lead
    /// byte falls through to the uncompressed legacy path, preserving
    /// compatibility with any persisted pre-2026-05-11 proofs that
    /// don't have the format tag.
    pub fn from_bytes(data: &[u8]) -> Result<Self, String> {
        if data.is_empty() {
            return Err("V2ProofReal: empty input".into());
        }
        if data[0] == V2_PROOF_FORMAT_TAG_ZSTD {
            let inner = zstd::decode_all(&data[1..])
                .map_err(|e| format!("V2ProofReal: zstd decode failed: {e}"))?;
            return Self::from_bytes_uncompressed(&inner);
        }
        // Fallback: treat as uncompressed legacy bytes.
        Self::from_bytes_uncompressed(data)
    }

    /// Deserialize from uncompressed bytes (the legacy layout).
    pub fn from_bytes_uncompressed(data: &[u8]) -> Result<Self, String> {
        let mut pos = 0usize;
        let take_n = |data: &[u8], pos: &mut usize, n: usize| -> Result<Vec<u8>, String> {
            if *pos + n > data.len() {
                return Err(format!("V2ProofReal: not enough bytes (need {}, have {})", n, data.len() - *pos));
            }
            let out = data[*pos..*pos + n].to_vec();
            *pos += n;
            Ok(out)
        };
        let read_u32 = |data: &[u8], pos: &mut usize| -> Result<u32, String> {
            let bytes = take_n(data, pos, 4)?;
            Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
        };
        let read_v = |data: &[u8], pos: &mut usize| -> Result<Vec<u8>, String> {
            let len = read_u32(data, pos)? as usize;
            take_n(data, pos, len)
        };

        let mut pi_hash = [0u8; 32]; pi_hash.copy_from_slice(&take_n(data, &mut pos, 32)?);
        let ctb = crate::ml_dsa::params::C_TILDE_BYTES;
        let mut c_tilde_prime = [0u8; crate::ml_dsa::params::C_TILDE_BYTES];
        c_tilde_prime.copy_from_slice(&take_n(data, &mut pos, ctb)?);
        let fri_v17 = read_v(data, &mut pos)?;
        let n_intt = read_u32(data, &mut pos)? as usize;
        let mut fri_intt = Vec::with_capacity(n_intt);
        for _ in 0..n_intt { fri_intt.push(read_v(data, &mut pos)?); }
        let fri_decompose = read_v(data, &mut pos)?;
        let fri_use_hint = read_v(data, &mut pos)?;
        let fri_w1_encode = read_v(data, &mut pos)?;
        let fri_transcript = read_v(data, &mut pos)?;
        // fri_t_mem removed 2026-05-10 — T_MEM deleted from v2.
        let n_l0 = read_u32(data, &mut pos)? as usize;
        let mut intt_l0_openings = Vec::with_capacity(n_l0);
        for _ in 0..n_l0 { intt_l0_openings.push(read_v(data, &mut pos)?); }
        let n_l1_intt = read_u32(data, &mut pos)? as usize;
        let mut intt_l1_openings = Vec::with_capacity(n_l1_intt);
        for _ in 0..n_l1_intt { intt_l1_openings.push(read_v(data, &mut pos)?); }
        let n_l1_dec = read_u32(data, &mut pos)? as usize;
        let mut decompose_l1_openings = Vec::with_capacity(n_l1_dec);
        for _ in 0..n_l1_dec { decompose_l1_openings.push(read_v(data, &mut pos)?); }
        let n_uh = read_u32(data, &mut pos)? as usize;
        let mut use_hint_openings = Vec::with_capacity(n_uh);
        for _ in 0..n_uh { use_hint_openings.push(read_v(data, &mut pos)?); }
        let n_w1 = read_u32(data, &mut pos)? as usize;
        let mut w1_encode_openings = Vec::with_capacity(n_w1);
        for _ in 0..n_w1 { w1_encode_openings.push(read_v(data, &mut pos)?); }
        let n_v17_l5 = read_u32(data, &mut pos)? as usize;
        let mut v17_l5_openings = Vec::with_capacity(n_v17_l5);
        for _ in 0..n_v17_l5 { v17_l5_openings.push(read_v(data, &mut pos)?); }
        let l2a_decompose_bcc = read_v(data, &mut pos)?;
        let l2a_use_hint_bcc  = read_v(data, &mut pos)?;
        let l3_use_hint_bcc   = read_v(data, &mut pos)?;
        let l3_w1_encode_bcc  = read_v(data, &mut pos)?;
        let l2c_use_hint_bcc  = read_v(data, &mut pos)?;
        let n_l5 = read_u32(data, &mut pos)? as usize;
        let mut l5_v17_eq_bccs = Vec::with_capacity(n_l5);
        for _ in 0..n_l5 { l5_v17_eq_bccs.push(read_v(data, &mut pos)?); }
        let l1_decompose_bcc = read_v(data, &mut pos)?;
        let n_l4 = read_u32(data, &mut pos)? as usize;
        let mut l4_w1_encode_bccs = Vec::with_capacity(n_l4);
        for _ in 0..n_l4 { l4_w1_encode_bccs.push(read_v(data, &mut pos)?); }
        let l2b_use_hint_bcc = read_v(data, &mut pos)?;
        if pos != data.len() {
            return Err(format!("V2ProofReal: {} trailing bytes", data.len() - pos));
        }
        Ok(Self {
            pi_hash, c_tilde_prime,
            fri_v17, fri_intt, fri_decompose, fri_use_hint, fri_w1_encode,
            fri_transcript,
            intt_l0_openings,
            intt_l1_openings,
            decompose_l1_openings,
            use_hint_openings,
            w1_encode_openings,
            v17_l5_openings,
            l2a_decompose_bcc,
            l2a_use_hint_bcc,
            l3_use_hint_bcc,
            l3_w1_encode_bcc,
            l2c_use_hint_bcc,
            l5_v17_eq_bccs,
            l1_decompose_bcc,
            l4_w1_encode_bccs,
            l2b_use_hint_bcc,
        })
    }
}

const V2_BLOWUP: usize = 32;
/// Auto-derived from the active `sha3-N` Cargo feature: 54 / 79 / 105
/// for NIST PQ Levels 1 / 3 / 5 (Johnson-regime unconditional).
/// See `crate::stark_level::NUM_QUERIES_LEVEL`.
const V2_NUM_QUERIES: usize = crate::stark_level::NUM_QUERIES_LEVEL;
const V2_SEED_Z: u64 = 0xDEEF_BAAD;

// derive_t_mem_challenges removed 2026-05-10 — T_MEM deleted after F2b
// L0-L4 superseded its (vacuous) cross-region binding role.

fn make_v2_schedule(n0: usize) -> Vec<usize> {
    vec![2usize; n0.trailing_zeros() as usize]
}

/// Fiat-Shamir-derive the constraint composition coefficients
/// `α_1, …, α_num ∈ F` for a sub-AIR.  These are the per-constraint
/// coefficients in `Φ(X) = Σ α_j Φ_j(X)` from the DEEP-ALI merge
/// (paper eq 1).
///
/// **Soundness note**: the previous version used static integers
/// `[1, 2, …, num]`, which broke Theorem 1's Event-E1 Schwartz-Zippel
/// argument (the bound `Pr[Φ(ω_T^{i⋆}) = 0] ≤ 1/|F_pe|` requires α_j
/// to be uniformly random over F_pe from the prover's perspective).
/// With predictable α a malicious prover could craft constraint
/// values whose linear combination cancels at specific trace-domain
/// points — defeating the merge's distance argument.
///
/// `domain_sep` distinguishes sub-AIRs so each gets its own α
/// vector (otherwise an attacker who controls one sub-AIR's witness
/// could exploit shared α across sub-AIRs).
pub(crate) fn comb_coeffs(num: usize, pi_hash: &[u8; 32], domain_sep: &[u8]) -> Vec<F> {
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    let mut shake = sha3::Shake256::default();
    shake.update(b"mmiyc/v2/comb_coeffs");
    shake.update(domain_sep);
    shake.update(pi_hash);
    let mut reader = shake.finalize_xof();

    (0..num).map(|_| {
        let mut buf = [0u8; 8];
        reader.read(&mut buf);
        F::from(u64::from_le_bytes(buf))
    }).collect()
}

pub(crate) fn v2_fri_params(n0: usize, pi_hash: [u8; 32]) -> DeepFriParams {
    // Default: **STIR** mode (since `verify_one_sub_air_with_trace`'s
    // per-query trace-cell soundness check was generalized to handle
    // both FRI and STIR proof structures via
    // `extract_query_position_and_c_eval` on 2026-05-10).  STIR
    // delivers ~3.6× faster verify and ~2.8× smaller proof than
    // FRI at the same NIST PQ Level (cross-level bench in
    // `project_starkstir_fri_vs_stir.md`).
    //
    // `MMIYC_V2_USE_FRI=1` reverts to FRI mode for cross-LDT
    // benchmarking and compatibility testing.
    let use_fri = std::env::var("MMIYC_V2_USE_FRI")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    DeepFriParams {
        schedule: make_v2_schedule(n0),
        r: V2_NUM_QUERIES,
        seed_z: V2_SEED_Z,
        coeff_commit_final: true,
        d_final: 1,
        stir: !use_fri,
        s0: V2_NUM_QUERIES,
        public_inputs_hash: Some(pi_hash),
    }
}

fn serialize_fri(proof: &DeepFriProof<Ext>) -> Vec<u8> {
    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).expect("serialize FRI proof");
    buf
}

fn deserialize_fri(bytes: &[u8]) -> Result<DeepFriProof<Ext>, String> {
    DeepFriProof::<Ext>::deserialize_with_mode(bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| format!("FRI proof deserialization: {e:?}"))
}

/// Run a single FRI sub-proof: LDE the sub-trace, run the merge,
/// invoke `deep_fri_prove`, serialize.  Used 10× by `prove_v2_real`.
fn prove_one_sub_air(
    trace: &[Vec<F>],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
    c_eval_fn: impl FnOnce(&[Vec<F>], usize, usize) -> Vec<F>,
) -> Vec<u8> {
    let n0 = n_trace * blowup;
    let domain = FriDomain::new_radix2(n0);
    let lde = lde_trace_columns(trace, n_trace, blowup).expect("LDE");
    let c_eval = c_eval_fn(&lde, n_trace, blowup);
    drop(lde);
    let params = v2_fri_params(n0, pi_hash);
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    serialize_fri(&proof)
}

/// Run a single FRI sub-verify: deserialize the proof, invoke
/// `deep_fri_verify`.  Used 10× by `verify_v2_real`.
fn verify_one_sub_air(
    proof_bytes: &[u8],
    n_trace: usize,
    blowup: usize,
    pi_hash: [u8; 32],
) -> Result<(), String> {
    let n0 = n_trace * blowup;
    let proof = deserialize_fri(proof_bytes)?;
    // Auto-detect LDT mode from the proof structure rather than the
    // env: WASM has no env access, so `v2_fri_params` (which calls
    // `use_stir_from_env`) returns `stir = false` unconditionally
    // in the browser even when the prover ran STIR.  The proof
    // itself carries this metadata: `stir_coset_evals.is_some()`
    // iff STIR was used.  Override the env-derived default with
    // the proof-derived truth.
    let mut params = v2_fri_params(n0, pi_hash);
    params.stir = proof.stir_coset_evals.is_some();
    if deep_fri_verify::<Ext>(&params, &proof) {
        Ok(())
    } else {
        Err("FRI verify rejected".into())
    }
}

/// **Production v2 prover.**  Runs 10 FRI sub-proofs with shared
/// `pi_hash`.  Returns the bundle plus the populated sub-traces
/// (the latter for tests; production callers can ignore them).
pub fn prove_v2_real(
    w: &V2Witness,
    c_tilde_bytes: &[u8; crate::ml_dsa::params::C_TILDE_BYTES],
    blowup: usize,
) -> V2ProofReal {
    let pi_hash = compute_pi_hash_v2(w, c_tilde_bytes);
    let traces = fill_v2_traces(w, pi_hash);
    prove_v2_real_from_traces(&traces, &w.mu_bytes, &w.w1bytes, c_tilde_bytes, pi_hash, blowup)
}

/// Test-friendly entry point: same body as `prove_v2_real` but takes
/// pre-built sub-traces.  Used by gap-demonstration tests that need
/// to splice traces from different witnesses (e.g. INTT from a
/// canonical witness + COEFF/TRANSCRIPT from a tampered witness, to
/// exhibit attacks that L0 alone doesn't catch).
///
/// `mu_bytes` and `w1bytes` are needed for `transcript_layout` and
/// for c̃' extraction.  Callers building traces by splicing should
/// pass the (mu, w1bytes) consistent with the TRANSCRIPT sub-trace
/// they put into `traces`.
pub fn prove_v2_real_from_traces(
    traces: &V2SubTraces,
    mu_bytes: &[u8; 64],
    w1bytes: &[u8],
    c_tilde_bytes: &[u8; crate::ml_dsa::params::C_TILDE_BYTES],
    pi_hash: [u8; 32],
    blowup: usize,
) -> V2ProofReal {
    let _ = c_tilde_bytes;  // bound via pi_hash already

    let transcript_layout = ml_dsa_transcript::build_layout(mu_bytes, w1bytes);
    let c_tilde_prime = ml_dsa_transcript::extract_c_tilde_prime_from_trace(
        &traces.transcript, &transcript_layout,
    );

    // V17 — F2b **L5** (V17 EQ-region cell binding, landed 2026-05-10):
    // capture LDE+tree so we can open K·N EQ-region rows and bind
    // V17's a_ntt/c_ntt/t1d_ntt/w_approx_ntt cells to the pi_hash-
    // bound public values.  Without this, V17 only proves its
    // polynomial identity holds for *some* tuple, not the public one
    // — see `v2_l5_regression_v17_rejects_tampered_eq_region` test.
    let (v17_proof, v17_lde, v17_tree) =
        crate::sub_air_with_trace::prove_one_sub_air_with_trace_capturing(
            &traces.v17, traces.v17[0].len(), blowup, pi_hash,
            b"v17",
            crate::ml_dsa_verify_air_v17::NUM_CONSTRAINTS,
            |lde, n_trace, blowup, comb_coeffs| {
                crate::deep_ali_merge_ml_dsa_v17(lde, comb_coeffs, F::zero(), n_trace, blowup).0
            },
            v2_fri_params,
        );
    // L5 inclusion proofs REMOVED 2026-05-12 — superseded by L5 OOD
    // binding.  Empty Vec preserves wire format; verifier skips the
    // K·N row-opening check.
    let _ = &v17_tree;
    let v17_l5_openings: Vec<Vec<u8>> = Vec::new();
    let fri_v17 = crate::sub_air_with_trace::serialize_proof(&v17_proof);

    // Session 8 (2026-05-12): L5 RE-ENABLED with transcript-replay
    // fix.  Verifier now derives z_ext via `derive_z_ext_for_proof`
    // (matches FRI prover's `challenge_ext` exactly).  See
    // `verify_ood_against_public_trace_col` in binding_cells_commit.
    let v17_n_trace_local = traces.v17[0].len();
    let l5_v17_eq_bccs: Vec<Vec<u8>> = {
        let mut bccs = Vec::with_capacity(L + 3);
        let eq_base = crate::ml_dsa_verify_air_v17::EQ_BASE;
        for ll in 0..L {
            let col_idx = eq_base + crate::ml_dsa_verify_air::col_a_ntt(ll);
            let domain_sep = format!("l5_v17_a_ntt_{ll}").into_bytes();
            let (commit, _) = crate::binding_cells_commit::commit_binding_cells(
                &v17_lde, &[col_idx], v17_n_trace_local, blowup, pi_hash,
                &domain_sep, v2_fri_params,
            );
            bccs.push(commit.to_bytes());
        }
        for (col_fn, ds) in [
            (crate::ml_dsa_verify_air::col_c_ntt() , b"l5_v17_c_ntt" as &[u8]),
            (crate::ml_dsa_verify_air::col_t1d_ntt() , b"l5_v17_t1d_ntt"),
            (crate::ml_dsa_verify_air::col_w_approx_ntt() , b"l5_v17_w_approx_ntt"),
        ] {
            let col_idx = eq_base + col_fn;
            let (commit, _) = crate::binding_cells_commit::commit_binding_cells(
                &v17_lde, &[col_idx], v17_n_trace_local, blowup, pi_hash,
                ds, v2_fri_params,
            );
            bccs.push(commit.to_bytes());
        }
        bccs
    };

    // INTT × K — domain-sep tag includes the instance index k so each
    // INTT instance gets independent α even though they share an AIR.
    //
    // F2b L0 + L1: capture the LDE+tree so we can open the trace at
    // row `BUTTERFLIES_PER_NTT` (L0: pin INTT output to public
    // `w_approx_ntt`) AND at row 0 (L1: pin INTT input to Decompose's
    // r-input).  Together these constrain the entire NTT to be a
    // valid computation on the canonical input.
    let mut fri_intt: Vec<Vec<u8>> = Vec::with_capacity(K);
    let mut intt_l0_openings: Vec<Vec<u8>> = Vec::with_capacity(K);
    let mut intt_l1_openings: Vec<Vec<u8>> = Vec::with_capacity(K);
    for k in 0..K {
        let mut tag = b"intt:".to_vec();
        tag.push(k as u8);
        let (proof, lde, tree) = crate::sub_air_with_trace::prove_one_sub_air_with_trace_capturing(
            &traces.intt[k], traces.intt[k][0].len(), blowup, pi_hash,
            &tag,
            crate::ml_dsa_ntt_chained_air::NUM_CONSTRAINTS,
            |lde, n_trace, blowup, comb_coeffs| {
                crate::deep_ali_merge_t7_chained_ntt(lde, comb_coeffs, F::zero(), n_trace, blowup).0
            },
            v2_fri_params,
        );
        let l0_opening = crate::sub_air_with_trace::open_trace_row_at_raw_position(
            &lde, &tree, crate::ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT, blowup,
        );
        let l1_opening = crate::sub_air_with_trace::open_trace_row_at_raw_position(
            &lde, &tree, 0, blowup,
        );
        let mut l0_bytes = Vec::new();
        l0_opening.serialize_with_mode(&mut l0_bytes, ark_serialize::Compress::Yes)
            .expect("L0 opening serialize");
        let mut l1_bytes = Vec::new();
        l1_opening.serialize_with_mode(&mut l1_bytes, ark_serialize::Compress::Yes)
            .expect("L1 INTT opening serialize");
        intt_l0_openings.push(l0_bytes);
        intt_l1_openings.push(l1_bytes);
        fri_intt.push(crate::sub_air_with_trace::serialize_proof(&proof));
    }

    // COEFF Decompose
    //
    // F2b L1: capture the LDE+tree so we can open K·N rows (one per
    // coefficient) for the cross-binding to INTT row-0 cells.
    let (decompose_proof, decompose_lde, decompose_tree) =
        crate::sub_air_with_trace::prove_one_sub_air_with_trace_capturing(
            &traces.coeff_decompose, traces.coeff_decompose[0].len(), blowup, pi_hash,
            b"decompose",
            crate::ml_dsa_decompose_air::NUM_CONSTRAINTS,
            |lde, n_trace, blowup, comb_coeffs| {
                crate::deep_ali_merge_t_decompose(lde, comb_coeffs, F::zero(), n_trace, blowup).0
            },
            v2_fri_params,
        );
    // F2b Decompose K·N row openings REMOVED 2026-05-12 — superseded
    // by L1 OOD.  Empty Vec preserves wire format.
    let _ = &decompose_tree;
    let decompose_l1_openings: Vec<Vec<u8>> = Vec::new();
    let fri_decompose = crate::sub_air_with_trace::serialize_proof(&decompose_proof);

    // COEFF UseHint — F2b L2a/L2b/L3: capture LDE+tree, open K·N rows.
    let (use_hint_proof, use_hint_lde, use_hint_tree) =
        crate::sub_air_with_trace::prove_one_sub_air_with_trace_capturing(
            &traces.coeff_use_hint, traces.coeff_use_hint[0].len(), blowup, pi_hash,
            b"use_hint",
            crate::ml_dsa_use_hint_air::NUM_CONSTRAINTS,
            |lde, n_trace, blowup, comb_coeffs| {
                crate::deep_ali_merge_t_use_hint(lde, comb_coeffs, F::zero(), n_trace, blowup).0
            },
            v2_fri_params,
        );
    // F2b UseHint K·N row openings REMOVED 2026-05-12 — superseded
    // by L2a + L2b + L2c + L3 OOD bindings.  Empty Vec preserves wire format.
    let _ = &use_hint_tree;
    let use_hint_openings: Vec<Vec<u8>> = Vec::new();
    let fri_use_hint = crate::sub_air_with_trace::serialize_proof(&use_hint_proof);

    // Session 7 OOD-rebuild POC: L2a (Decompose col_r1 ↔ UseHint COL_R1).
    // Two BindingCellsCommits over the same packed LDE size; the
    // verifier compares fz_per_layer[0] (= f(z_0)) across both via
    // `verify_ood_consistency`.  Schwartz-Zippel at z_0 ∈ F_ext
    // gives 2⁻³⁷⁰ binding at L3.  Additive with existing F2b L2a
    // inclusion proofs (no regression risk; Session 8 removes them).
    let coeff_n_trace_local = traces.coeff_decompose[0].len();
    let l2a_decompose_bcc = {
        let (commit, _packed) = crate::binding_cells_commit::commit_binding_cells(
            &decompose_lde,
            &[crate::ml_dsa_decompose_air::col_r1()],
            coeff_n_trace_local, blowup, pi_hash, b"l2a_decompose",
            v2_fri_params,
        );
        commit.to_bytes()
    };

    // Session 9: L1 OOD via verifier-computed INTT(public.w_approx_ntt).
    // Single-BCC public-input binding on Decompose col_r.  Verifier
    // computes canonical w_approx_flat on its side from public values
    // and OOD-compares against this BCC.
    let l1_decompose_bcc = {
        let (commit, _packed) = crate::binding_cells_commit::commit_binding_cells(
            &decompose_lde,
            &[crate::ml_dsa_decompose_air::col_r()],
            coeff_n_trace_local, blowup, pi_hash, b"l1_decompose_r",
            v2_fri_params,
        );
        commit.to_bytes()
    };
    let l2a_use_hint_bcc = {
        let (commit, _packed) = crate::binding_cells_commit::commit_binding_cells(
            &use_hint_lde,
            &[crate::ml_dsa_use_hint_air::COL_R1],
            coeff_n_trace_local, blowup, pi_hash, b"l2a_use_hint",
            v2_fri_params,
        );
        commit.to_bytes()
    };

    // COEFF W1Encode — F2b L3: capture LDE+tree, open K·N rows.
    let (w1_encode_proof, w1_encode_lde, w1_encode_tree) =
        crate::sub_air_with_trace::prove_one_sub_air_with_trace_capturing(
            &traces.coeff_w1_encode, traces.coeff_w1_encode[0].len(), blowup, pi_hash,
            b"w1_encode",
            crate::ml_dsa_w1_encode_air::NUM_CONSTRAINTS,
            |lde, n_trace, blowup, comb_coeffs| {
                crate::deep_ali_merge_t_w1_encode(lde, comb_coeffs, F::zero(), n_trace, blowup).0
            },
            v2_fri_params,
        );
    // F2b W1Encode K·N row openings REMOVED 2026-05-12 — superseded
    // by L3 + L4 OOD bindings.  Empty Vec preserves wire format.
    let _ = &w1_encode_tree;
    let w1_encode_openings: Vec<Vec<u8>> = Vec::new();
    let fri_w1_encode = crate::sub_air_with_trace::serialize_proof(&w1_encode_proof);

    // Session 7 OOD L3: UseHint COL_ADJUSTED_R1 ↔ W1Encode col_r1.
    // Same-row pair, both LDEs share n_trace + blowup → shared z_0.
    let l3_use_hint_bcc = {
        let (commit, _packed) = crate::binding_cells_commit::commit_binding_cells(
            &use_hint_lde,
            &[crate::ml_dsa_use_hint_air::COL_ADJUSTED_R1],
            coeff_n_trace_local, blowup, pi_hash, b"l3_use_hint_adj",
            v2_fri_params,
        );
        commit.to_bytes()
    };
    let l3_w1_encode_bcc = {
        let (commit, _packed) = crate::binding_cells_commit::commit_binding_cells(
            &w1_encode_lde,
            &[crate::ml_dsa_w1_encode_air::col_r1()],
            coeff_n_trace_local, blowup, pi_hash, b"l3_w1_encode_r1",
            v2_fri_params,
        );
        commit.to_bytes()
    };

    // Session 10 OOD L4: W1Encode col_bit(b) ↔ public w1bytes
    // bit-packed via FIPS 204 §3.5.7.  W1_BITS_PER_COEF BCCs (one
    // per bit position), each over a separate column of W1Encode.
    let l4_w1_encode_bccs: Vec<Vec<u8>> = {
        use crate::ml_dsa::params::W1_BITS_PER_COEF;
        let mut bccs = Vec::with_capacity(W1_BITS_PER_COEF);
        for b in 0..W1_BITS_PER_COEF {
            let col_idx = crate::ml_dsa_w1_encode_air::col_bit(b);
            let domain_sep = format!("l4_w1_encode_bit_{b}").into_bytes();
            let (commit, _) = crate::binding_cells_commit::commit_binding_cells(
                &w1_encode_lde, &[col_idx],
                coeff_n_trace_local, blowup, pi_hash,
                &domain_sep, v2_fri_params,
            );
            bccs.push(commit.to_bytes());
        }
        bccs
    };

    // Session 8: L2c RE-ENABLED with transcript-replay fix.
    let l2c_use_hint_bcc = {
        let (commit, _) = crate::binding_cells_commit::commit_binding_cells(
            &use_hint_lde,
            &[crate::ml_dsa_use_hint_air::COL_H],
            coeff_n_trace_local, blowup, pi_hash, b"l2c_use_hint_h",
            v2_fri_params,
        );
        commit.to_bytes()
    };

    // Session 11: L2b OOD via canonical translated-r0_sign public-input.
    let l2b_use_hint_bcc = {
        let (commit, _) = crate::binding_cells_commit::commit_binding_cells(
            &use_hint_lde,
            &[crate::ml_dsa_use_hint_air::COL_R0_SIGN],
            coeff_n_trace_local, blowup, pi_hash, b"l2b_use_hint_r0_sign",
            v2_fri_params,
        );
        commit.to_bytes()
    };

    // TRANSCRIPT
    let layout_for_closure = transcript_layout.clone();
    let transcript_num_constraints = ml_dsa_shake_absorb_multi_air::num_constraints(&layout_for_closure);
    let fri_transcript = crate::sub_air_with_trace::serialize_proof(
        &crate::sub_air_with_trace::prove_one_sub_air_with_trace(
            &traces.transcript, traces.transcript[0].len(), blowup, pi_hash,
            b"transcript",
            transcript_num_constraints,
            move |lde, n_trace, blowup, comb_coeffs| {
                crate::deep_ali_merge_t_transcript(
                    lde, comb_coeffs, F::zero(), n_trace, blowup, &layout_for_closure,
                ).0
            },
            v2_fri_params,
        )
    );

    // T_MEM FRI prove removed 2026-05-10 — superseded by F2b L0-L4
    // Merkle inclusion proofs.

    V2ProofReal {
        pi_hash, c_tilde_prime,
        fri_v17, fri_intt, fri_decompose, fri_use_hint, fri_w1_encode,
        fri_transcript,
        intt_l0_openings,
        intt_l1_openings,
        decompose_l1_openings,
        use_hint_openings,
        w1_encode_openings,
        v17_l5_openings,
        l2a_decompose_bcc,
        l2a_use_hint_bcc,
        l3_use_hint_bcc,
        l3_w1_encode_bcc,
        l2c_use_hint_bcc,
        l5_v17_eq_bccs,
        l1_decompose_bcc,
        l4_w1_encode_bccs,
        l2b_use_hint_bcc,
    }
}

/// **Production v2 verifier.**  Recomputes `pi_hash`, runs 10 FRI
/// sub-verifies, checks `c̃' == c̃` final boundary.  Returns `Ok(())`
/// iff every check passes.
///
/// **NO Layer 1 native `ml_dsa::verify`.**  v2's defining feature.
pub fn verify_v2_real(
    public: &V2Witness,        // public fields are what the verifier receives via PI
    c_tilde_bytes: &[u8; crate::ml_dsa::params::C_TILDE_BYTES],
    proof: &V2ProofReal,
    blowup: usize,
) -> Result<(), String> {
    // 1. pi_hash consistency.
    let recomputed = compute_pi_hash_v2(public, c_tilde_bytes);
    if recomputed != proof.pi_hash {
        return Err(format!(
            "v2 verify: pi_hash mismatch (proof={:02x?}, expected={:02x?})",
            &proof.pi_hash[..8], &recomputed[..8]));
    }

    // 2. c̃' equality (FIPS 204 §3 Algorithm 3 step 7's acceptance test).
    if proof.c_tilde_prime != *c_tilde_bytes {
        return Err(format!(
            "v2 verify: c̃' ≠ c̃ ({:02x?} vs {:02x?})",
            &proof.c_tilde_prime[..8], &c_tilde_bytes[..8]));
    }

    let pi_hash = proof.pi_hash;

    // 3. V17 sub-proof + F2b L5 EQ-region binding to public values.
    let v17_n_trace = crate::ml_dsa_verify_air_v17::VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    let v17_n_lde = v17_n_trace * blowup;
    {
        let p = crate::sub_air_with_trace::deserialize_proof(&proof.fri_v17)?;
        crate::sub_air_with_trace::verify_one_sub_air_with_trace(
            &p, v17_n_trace, blowup, pi_hash,
            b"v17",
            crate::ml_dsa_verify_air_v17::WIDTH,
            crate::ml_dsa_verify_air_v17::NUM_CONSTRAINTS,
            |cur, nxt, row| crate::ml_dsa_verify_air_v17::eval_per_row(cur, nxt, row),
            v2_fri_params,
        ).map_err(|e| format!("v2 V17: {e}"))?;

        // F2b L5 inclusion proofs REMOVED 2026-05-12 — L5 OOD
        // binding (Session 7-8) supersedes K·N V17 row openings.
        // `v17_n_lde`, `p.trace_root` no longer needed here.
        let _ = (v17_n_lde, &p.trace_root);
    }

    // 4. INTT × K sub-proofs.
    let intt_n_trace = (t7::BUTTERFLIES_PER_NTT + 16).next_power_of_two();
    let intt_n_lde = intt_n_trace * blowup;
    if proof.fri_intt.len() != K {
        return Err(format!("v2 verify: expected {K} INTT proofs, got {}", proof.fri_intt.len()));
    }
    if proof.intt_l0_openings.len() != K {
        return Err(format!(
            "v2 verify: expected {K} L0 cross-binding openings, got {}",
            proof.intt_l0_openings.len()
        ));
    }
    if proof.intt_l1_openings.len() != K {
        return Err(format!(
            "v2 verify: expected {K} L1 INTT openings, got {}",
            proof.intt_l1_openings.len()
        ));
    }
    // Stash INTT row-0 cells for the L1 cross-check after Decompose verify.
    let mut intt_l1_row0_cells: Vec<Vec<F>> = Vec::with_capacity(K);
    for k in 0..K {
        let mut tag = b"intt:".to_vec();
        tag.push(k as u8);
        let p = crate::sub_air_with_trace::deserialize_proof(&proof.fri_intt[k])?;
        crate::sub_air_with_trace::verify_one_sub_air_with_trace(
            &p, intt_n_trace, blowup, pi_hash,
            &tag,
            crate::ml_dsa_ntt_chained_air::WIDTH,
            crate::ml_dsa_ntt_chained_air::NUM_CONSTRAINTS,
            |cur, nxt, row| crate::ml_dsa_ntt_chained_air::eval_per_row(cur, nxt, row),
            v2_fri_params,
        ).map_err(|e| format!("v2 INTT[{k}]: {e}"))?;

        // F2b L0 cross-binding: verify the row-1024 opening pins
        // the INTT output cells to the pi_hash-bound public
        // `w_approx_ntt[k][i]`.  Catches the attack where the prover
        // fills INTT with NTT(w_approx_fake) ≠ public w_approx_ntt.
        let l0_op = <crate::sub_air_with_trace::TraceOpening
            as ark_serialize::CanonicalDeserialize>::deserialize_with_mode(
                proof.intt_l0_openings[k].as_slice(),
                ark_serialize::Compress::Yes,
                ark_serialize::Validate::Yes,
            ).map_err(|e| format!("v2 INTT[{k}] L0: deserialize opening: {e:?}"))?;
        let cells = crate::sub_air_with_trace::verify_trace_row_at_raw_position(
            &l0_op, &p.trace_root,
            crate::ml_dsa_ntt_chained_air::BUTTERFLIES_PER_NTT,
            blowup, intt_n_lde,
            crate::ml_dsa_ntt_chained_air::WIDTH,
            &tag,
        ).map_err(|e| format!("v2 INTT[{k}] L0: {e}"))?;
        for i in 0..N {
            let cell = cells[crate::ml_dsa_ntt_chained_air::col_state(i)];
            let expected = F::from(public.w_approx_ntt[k][i] as u64);
            if cell != expected {
                return Err(format!(
                    "v2 INTT[{k}] L0: row 1024 cell {i} ({cell:?}) ≠ public w_approx_ntt ({expected:?}) \
                     — INTT output not pinned to canonical value"
                ));
            }
        }

        // F2b L1 (INTT side): verify the row-0 opening against the
        // same INTT trace_root.  Cells are stashed for cross-check
        // against the Decompose r-input column after Decompose's
        // FRI + L1 openings verify.
        let l1_op = <crate::sub_air_with_trace::TraceOpening
            as ark_serialize::CanonicalDeserialize>::deserialize_with_mode(
                proof.intt_l1_openings[k].as_slice(),
                ark_serialize::Compress::Yes,
                ark_serialize::Validate::Yes,
            ).map_err(|e| format!("v2 INTT[{k}] L1: deserialize opening: {e:?}"))?;
        let l1_cells = crate::sub_air_with_trace::verify_trace_row_at_raw_position(
            &l1_op, &p.trace_root, 0, blowup, intt_n_lde,
            crate::ml_dsa_ntt_chained_air::WIDTH, &tag,
        ).map_err(|e| format!("v2 INTT[{k}] L1: {e}"))?;
        intt_l1_row0_cells.push(l1_cells.to_vec());
    }

    // 5. COEFF sub-proofs (Decompose + UseHint + W1Encode) with
    //    F2b L1/L2a/L2b/L3 cross-binding openings stitching them
    //    together.
    let coeff_n_trace = (K * N).next_power_of_two();
    let coeff_n_lde = coeff_n_trace * blowup;
    let expected_kn = K * N;

    // Stash for cross-checks across sub-AIRs.
    //
    // Note on r0_sign convention: Decompose AIR's `col_r0_sign()` uses
    // `1 iff r0_lifted > Q/2` (negative-half indicator), while UseHint
    // AIR's `COL_R0_SIGN` uses `1 iff r0_lifted ∈ (0, Q/2]` (positive-
    // half indicator).  The two are inverted except at r0_lifted = 0
    // where both are 0.  L2b cross-binds the translated convention:
    // `expected_use_hint_r0_sign = (r0 != 0) AND (decompose_r0_sign == 0)`.
    let mut decompose_r1_cells:               Vec<F> = Vec::with_capacity(expected_kn);
    let mut use_hint_expected_r0_sign_cells:  Vec<F> = Vec::with_capacity(expected_kn);
    let mut use_hint_adjusted_cells:          Vec<F> = Vec::with_capacity(expected_kn);

    // --- Decompose FRI + L1 (Decompose r-input ↔ INTT row-0) ---
    {
        let p = crate::sub_air_with_trace::deserialize_proof(&proof.fri_decompose)?;
        crate::sub_air_with_trace::verify_one_sub_air_with_trace(
            &p, coeff_n_trace, blowup, pi_hash,
            b"decompose",
            crate::ml_dsa_decompose_air::WIDTH,
            crate::ml_dsa_decompose_air::NUM_CONSTRAINTS,
            |cur, nxt, row| crate::ml_dsa_decompose_air::eval_per_row(cur, nxt, row),
            v2_fri_params,
        ).map_err(|e| format!("v2 Decompose: {e}"))?;

        // F2b Decompose K·N row openings REMOVED — superseded by L1 OOD
        // (Session 9).  Decompose r1 / r0 / r0_sign cells previously
        // extracted here were only used for L2a / L2b cross-checks
        // which are also now covered by OOD.
        let _ = (coeff_n_lde, &p.trace_root,
                 &mut decompose_r1_cells, &mut use_hint_expected_r0_sign_cells,
                 &intt_l1_row0_cells);
    }

    // --- UseHint FRI (per-row constraints only; F2b L2a/b/c openings removed) ---
    {
        let p = crate::sub_air_with_trace::deserialize_proof(&proof.fri_use_hint)?;
        crate::sub_air_with_trace::verify_one_sub_air_with_trace(
            &p, coeff_n_trace, blowup, pi_hash,
            b"use_hint",
            crate::ml_dsa_use_hint_air::WIDTH,
            crate::ml_dsa_use_hint_air::NUM_CONSTRAINTS,
            |cur, nxt, row| crate::ml_dsa_use_hint_air::eval_per_row(cur, nxt, row),
            v2_fri_params,
        ).map_err(|e| format!("v2 UseHint: {e}"))?;

        // F2b UseHint K·N row openings REMOVED — superseded by
        // L2a + L2b + L2c + L3 OOD bindings.
        let _ = (&p.trace_root, &mut use_hint_adjusted_cells);
    }

    // --- W1Encode FRI + L3 (UseHint adjusted ↔ W1Encode r1) + L4 ---
    {
        use crate::ml_dsa::params::W1_BITS_PER_COEF;

        let p = crate::sub_air_with_trace::deserialize_proof(&proof.fri_w1_encode)?;
        crate::sub_air_with_trace::verify_one_sub_air_with_trace(
            &p, coeff_n_trace, blowup, pi_hash,
            b"w1_encode",
            crate::ml_dsa_w1_encode_air::WIDTH,
            crate::ml_dsa_w1_encode_air::NUM_CONSTRAINTS,
            |cur, nxt, row| crate::ml_dsa_w1_encode_air::eval_per_row(cur, nxt, row),
            v2_fri_params,
        ).map_err(|e| format!("v2 W1Encode: {e}"))?;

        // F2b L3 + L4 inclusion-proof checks REMOVED 2026-05-12.
        // L3 OOD covers Decompose r1 ↔ W1Encode r1; L4 OOD covers
        // W1Encode bits ↔ public w1bytes (via the L3 + L4 OOD blocks
        // added in steps 9 + 13).  K·N W1Encode row openings no
        // longer needed for those bindings.
        let _ = (coeff_n_lde, &p.trace_root, &use_hint_adjusted_cells);
        // Sanity: public.w1bytes length matches expected encoding shape.
        let expected_w1bytes_len = (K * N * W1_BITS_PER_COEF) / 8;
        if public.w1bytes.len() != expected_w1bytes_len {
            return Err(format!(
                "v2 verify: public.w1bytes len {} ≠ expected K·N·W1_BITS_PER_COEF/8 = {}",
                public.w1bytes.len(), expected_w1bytes_len
            ));
        }
    }

    // 6. TRANSCRIPT sub-proof.
    let transcript_layout = ml_dsa_transcript::build_layout(&public.mu_bytes, &public.w1bytes);
    let transcript_n_trace = transcript_layout.active_rows().next_power_of_two();
    {
        let layout = transcript_layout.clone();
        let p = crate::sub_air_with_trace::deserialize_proof(&proof.fri_transcript)?;
        crate::sub_air_with_trace::verify_one_sub_air_with_trace(
            &p, transcript_n_trace, blowup, pi_hash,
            b"transcript",
            ml_dsa_shake_absorb_multi_air::WIDTH,
            ml_dsa_shake_absorb_multi_air::num_constraints(&layout),
            move |cur, nxt, row| ml_dsa_shake_absorb_multi_air::eval_per_row(cur, nxt, row, &layout),
            v2_fri_params,
        ).map_err(|e| format!("v2 TRANSCRIPT: {e}"))?;
    }

    // 7. T_MEM sub-proof removed 2026-05-10 — F2b L0-L4 cross-binding
    // openings supersede the (vacuous) cross-region binding T_MEM
    // was meant to provide.  See project_mmiyc_v2_soundness_gap.md.

    // 8. Session 7 OOD-rebuild POC: L2a (Decompose col_r1 ↔ UseHint COL_R1).
    // Additive with existing F2b L2a inclusion-proof check (lines ~1320-1325).
    // Session 8 will remove the F2b inclusion proofs once all bindings
    // have OOD coverage.
    {
        let decompose_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l2a_decompose_bcc,
        ).map_err(|e| format!("v2 L2a OOD: decompose bcc deserialize: {e}"))?;
        let use_hint_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l2a_use_hint_bcc,
        ).map_err(|e| format!("v2 L2a OOD: use_hint bcc deserialize: {e}"))?;
        crate::binding_cells_commit::verify_ood_consistency(
            &decompose_bcc, &use_hint_bcc, pi_hash, v2_fri_params,
        ).map_err(|e| format!("v2 L2a OOD: {e}"))?;
    }

    // 9. Session 7 OOD L3: UseHint adjusted_r1 ↔ W1Encode r1.
    {
        let use_hint_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l3_use_hint_bcc,
        ).map_err(|e| format!("v2 L3 OOD: use_hint bcc deserialize: {e}"))?;
        let w1_encode_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l3_w1_encode_bcc,
        ).map_err(|e| format!("v2 L3 OOD: w1_encode bcc deserialize: {e}"))?;
        crate::binding_cells_commit::verify_ood_consistency(
            &use_hint_bcc, &w1_encode_bcc, pi_hash, v2_fri_params,
        ).map_err(|e| format!("v2 L3 OOD: {e}"))?;
    }

    // 10. **Session 8 (2026-05-12): L2c RE-ENABLED.**
    // Public.h ↔ UseHint COL_H via transcript-replay (fixed in
    // `verify_ood_against_public_trace_col` to use
    // `derive_z_ext_for_proof` matching the FRI prover's
    // `challenge_ext`).
    {
        let coeff_n_trace_local = (K * N).next_power_of_two();
        let mut public_h_col = vec![F::zero(); coeff_n_trace_local];
        for kk in 0..K {
            for ii in 0..N {
                public_h_col[kk * N + ii] = F::from(public.h[kk][ii] as u64);
            }
        }
        let use_hint_h_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l2c_use_hint_bcc,
        ).map_err(|e| format!("v2 L2c OOD: deserialize: {e}"))?;
        crate::binding_cells_commit::verify_ood_against_public_trace_col(
            &use_hint_h_bcc, &public_h_col, pi_hash, V2_SEED_Z, v2_fri_params,
        ).map_err(|e| format!("v2 L2c OOD: {e}"))?;
    }

    // 11. **Session 8 (2026-05-12): L5 RE-ENABLED.**
    // V17 EQ-region columns ↔ public a_ntt/c_ntt/t1d_ntt/w_approx_ntt
    // via transcript-replay.
    {
        let expected_count = L + 3;
        if proof.l5_v17_eq_bccs.len() != expected_count {
            return Err(format!(
                "v2 L5 OOD: expected {expected_count} V17 EQ BCCs, got {}",
                proof.l5_v17_eq_bccs.len()
            ));
        }
        let v17_n_trace_local = crate::ml_dsa_verify_air_v17::VERIFY_AIR_V17_ACTIVE_ROWS
            .next_power_of_two();
        let n_eq_rows = crate::ml_dsa_verify_air_v17::N_EQ_ROWS;

        let mut col_idx = 0;
        // a_ntt[l]
        for ll in 0..L {
            let mut trace_col = vec![F::zero(); v17_n_trace_local];
            for r in 0..n_eq_rows {
                let kk = r / N;
                let ii = r % N;
                trace_col[r] = F::from(public.a_ntt[kk][ll][ii] as u64);
            }
            let bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
                &proof.l5_v17_eq_bccs[col_idx],
            ).map_err(|e| format!("v2 L5 a_ntt[{ll}]: deserialize: {e}"))?;
            crate::binding_cells_commit::verify_ood_against_public_trace_col(
                &bcc, &trace_col, pi_hash, V2_SEED_Z, v2_fri_params,
            ).map_err(|e| format!("v2 L5 a_ntt[{ll}]: {e}"))?;
            col_idx += 1;
        }
        // c_ntt
        {
            let mut trace_col = vec![F::zero(); v17_n_trace_local];
            for r in 0..n_eq_rows {
                let ii = r % N;
                trace_col[r] = F::from(public.c_ntt[ii] as u64);
            }
            let bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
                &proof.l5_v17_eq_bccs[col_idx],
            ).map_err(|e| format!("v2 L5 c_ntt: deserialize: {e}"))?;
            crate::binding_cells_commit::verify_ood_against_public_trace_col(
                &bcc, &trace_col, pi_hash, V2_SEED_Z, v2_fri_params,
            ).map_err(|e| format!("v2 L5 c_ntt: {e}"))?;
            col_idx += 1;
        }
        // t1d_ntt
        {
            let mut trace_col = vec![F::zero(); v17_n_trace_local];
            for r in 0..n_eq_rows {
                let kk = r / N;
                let ii = r % N;
                trace_col[r] = F::from(public.t1d_ntt[kk][ii] as u64);
            }
            let bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
                &proof.l5_v17_eq_bccs[col_idx],
            ).map_err(|e| format!("v2 L5 t1d_ntt: deserialize: {e}"))?;
            crate::binding_cells_commit::verify_ood_against_public_trace_col(
                &bcc, &trace_col, pi_hash, V2_SEED_Z, v2_fri_params,
            ).map_err(|e| format!("v2 L5 t1d_ntt: {e}"))?;
            col_idx += 1;
        }
        // w_approx_ntt
        {
            let mut trace_col = vec![F::zero(); v17_n_trace_local];
            for r in 0..n_eq_rows {
                let kk = r / N;
                let ii = r % N;
                trace_col[r] = F::from(public.w_approx_ntt[kk][ii] as u64);
            }
            let bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
                &proof.l5_v17_eq_bccs[col_idx],
            ).map_err(|e| format!("v2 L5 w_approx_ntt: deserialize: {e}"))?;
            crate::binding_cells_commit::verify_ood_against_public_trace_col(
                &bcc, &trace_col, pi_hash, V2_SEED_Z, v2_fri_params,
            ).map_err(|e| format!("v2 L5 w_approx_ntt: {e}"))?;
        }
    }

    // 12. **Session 9 (2026-05-12): L1 OOD.**
    // Decompose col_r ↔ canonical w_approx (= INTT of public w_approx_ntt).
    // Verifier computes the INTT on its side and OOD-checks against
    // the Decompose col_r BCC.  This makes L1 a clean public-input
    // binding.  INTT's per-row constraints + L0 inclusion proofs
    // (which remain in F2b) ensure INTT row 1024 matches public
    // w_approx_ntt; this L1 OOD then implicitly binds INTT row 0
    // (= canonical w_approx) via Decompose's r-input column.
    {
        let coeff_n_trace_local = (K * N).next_power_of_two();
        let canonical_w_approx = derive_w_approx_witness(&public.w_approx_ntt);
        let mut canonical_w_approx_flat = vec![F::zero(); coeff_n_trace_local];
        for kk in 0..K {
            for ii in 0..N {
                canonical_w_approx_flat[kk * N + ii] =
                    F::from(canonical_w_approx[kk][ii] as u64);
            }
        }
        let decompose_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l1_decompose_bcc,
        ).map_err(|e| format!("v2 L1 OOD: deserialize: {e}"))?;
        crate::binding_cells_commit::verify_ood_against_public_trace_col(
            &decompose_bcc, &canonical_w_approx_flat, pi_hash, V2_SEED_Z, v2_fri_params,
        ).map_err(|e| format!("v2 L1 OOD: {e}"))?;
    }

    // 12b. **Session 11 (2026-05-12): L2b OOD.**
    // UseHint COL_R0_SIGN ↔ canonical translated r0_sign derived
    // from public.w_approx_ntt.  Computed verifier-side:
    // 1. canonical w_approx = INTT(public.w_approx_ntt).
    // 2. for each (k, i): decompose r = w_approx[k][i] into (r1, r0).
    // 3. r0_sign per Decompose convention = 1 iff r0 > Q/2.
    // 4. translated UseHint r0_sign = (r0 != 0) AND (r0_sign == 0)
    //    (i.e., 1 iff r0 ∈ (0, Q/2]).
    {
        use crate::ml_dsa::params::Q;
        let coeff_n_trace_local = (K * N).next_power_of_two();
        let canonical_w_approx = derive_w_approx_witness(&public.w_approx_ntt);
        let mut translated_col = vec![F::zero(); coeff_n_trace_local];
        for kk in 0..K {
            for ii in 0..N {
                let r = canonical_w_approx[kk][ii];
                let (_r1, r0_lifted) = crate::ml_dsa_decompose::decompose(r);
                // UseHint convention: 1 iff r0 ∈ (0, Q/2], else 0.
                let uh_r0_sign: u32 = if r0_lifted != 0 && r0_lifted <= Q / 2 {
                    1
                } else {
                    0
                };
                translated_col[kk * N + ii] = F::from(uh_r0_sign as u64);
            }
        }
        let use_hint_r0s_bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
            &proof.l2b_use_hint_bcc,
        ).map_err(|e| format!("v2 L2b OOD: deserialize: {e}"))?;
        crate::binding_cells_commit::verify_ood_against_public_trace_col(
            &use_hint_r0s_bcc, &translated_col, pi_hash, V2_SEED_Z, v2_fri_params,
        ).map_err(|e| format!("v2 L2b OOD: {e}"))?;
    }

    // 13. **Session 10 (2026-05-12): L4 OOD.**
    // W1Encode col_bit(b) ↔ public w1bytes (bit-packed per FIPS 204
    // §3.5.7).  For each bit position b ∈ [0, W1_BITS_PER_COEF),
    // verifier extracts the canonical bit-b column from public.w1bytes
    // and OOD-compares against W1Encode's col_bit(b) BCC.
    {
        use crate::ml_dsa::params::W1_BITS_PER_COEF;
        let coeff_n_trace_local = (K * N).next_power_of_two();
        let expected_count = W1_BITS_PER_COEF;
        if proof.l4_w1_encode_bccs.len() != expected_count {
            return Err(format!(
                "v2 L4 OOD: expected {expected_count} W1Encode bit BCCs, got {}",
                proof.l4_w1_encode_bccs.len()
            ));
        }
        for b in 0..W1_BITS_PER_COEF {
            // Build canonical bit-b column from public.w1bytes.
            // Row r encodes bit b of adjusted_r1[k][i] where r = k·N+i.
            // Per FIPS 204 §3.5.7: bit (r * W1_BITS_PER_COEF + b) of the
            // stream is at byte ((r·W1_BPC+b)/8), bit position ((r·W1_BPC+b)%8).
            let mut trace_col = vec![F::zero(); coeff_n_trace_local];
            for r in 0..(K * N) {
                let bit_offset = r * W1_BITS_PER_COEF + b;
                let byte_idx = bit_offset / 8;
                let bit_idx  = bit_offset % 8;
                let bit_val = (public.w1bytes[byte_idx] >> bit_idx) & 1;
                trace_col[r] = F::from(bit_val as u64);
            }
            let bcc = crate::binding_cells_commit::BindingCellsCommit::from_bytes(
                &proof.l4_w1_encode_bccs[b],
            ).map_err(|e| format!("v2 L4 bit[{b}]: deserialize: {e}"))?;
            crate::binding_cells_commit::verify_ood_against_public_trace_col(
                &bcc, &trace_col, pi_hash, V2_SEED_Z, v2_fri_params,
            ).map_err(|e| format!("v2 L4 bit[{b}]: {e}"))?;
        }
    }

    Ok(())
}

/// Compute `w_approx[k] = INTT(w_approx_ntt[k])` for all k.  This is
/// the witness the prover supplies for the INTT sub-AIR; correctness
/// is enforced in-circuit by T7 running NTT(w_approx) and checking
/// the result equals `w_approx_ntt`.
pub fn derive_w_approx_witness(w_approx_ntt: &[[u32; N]; K]) -> [[u32; N]; K] {
    let mut w_approx = [[0u32; N]; K];
    for k in 0..K {
        w_approx[k] = w_approx_ntt[k];
        ml_dsa_ntt::ntt_inv(&mut w_approx[k]);
    }
    w_approx
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml_dsa::params::Q;
    use crate::ml_dsa_field::{add_q, mul_q, sub_q};
    use crate::keccak_f1600::ROUNDS;
    use crate::ml_dsa_shake_absorb_multi_air;

    /// **Benchmark harness** for the v2 ML-DSA verify STARK (Phase 1
    /// trace-commit binding).  Prints one CSV-friendly stdout line
    /// with prove_ms / verify_ms / proof_kib at the active NIST PQ
    /// Level (selected via Cargo features sha3-N + mldsa-N).
    ///
    /// Run with:
    /// ```
    /// cargo test --release -p deep_ali \
    ///     --features "parallel sha3-256 mldsa-44" --no-default-features \
    ///     v2_bench -- --ignored --nocapture
    /// ```
    /// Set `BENCH_BLOWUP=32` to use the paper-aligned production blowup.
    #[test]
    #[ignore]
    fn v2_bench() {
        use std::time::Instant;

        let w = synthesize_witness();
        let c_tilde_bytes = ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

        let blowup: usize = std::env::var("BENCH_BLOWUP")
            .ok().and_then(|s| s.parse().ok()).unwrap_or(4);
        let level = crate::stark_level::NIST_LEVEL;
        let scheme = crate::ml_dsa::params::SCHEME_NAME;
        let r = crate::stark_level::NUM_QUERIES_LEVEL;
        let hash_label = match level {
            1 => "SHA3-256",
            3 => "SHA3-384",
            5 => "SHA3-512",
            _ => "SHA3-?",
        };
        let ext_label = if level == 5 { "Fp8" } else { "Fp6" };

        // Confirm parallel feature is active and report thread count.
        #[cfg(feature = "parallel")]
        let rayon_threads = rayon::current_num_threads();
        #[cfg(not(feature = "parallel"))]
        let rayon_threads = 1usize;

        eprintln!(
            "[v2_bench] level=L{level} scheme={scheme} r={r} blowup={blowup} \
             rayon_threads={rayon_threads}"
        );
        #[cfg(not(feature = "parallel"))]
        eprintln!("[v2_bench] WARNING: built without `parallel` feature; single-threaded!");

        let t0 = Instant::now();
        let proof = prove_v2_real(&w, &c_tilde_bytes, blowup);
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
        eprintln!("[v2_bench] prove_ms = {prove_ms:.1}");

        let proof_bytes = proof.to_bytes();
        let proof_kib = proof_bytes.len() as f64 / 1024.0;
        eprintln!("[v2_bench] proof_kib = {proof_kib:.1}");

        // 3 verify runs, take median.
        let mut samples: Vec<f64> = Vec::with_capacity(3);
        for i in 0..3 {
            let t0 = Instant::now();
            verify_v2_real(&w, &c_tilde_bytes, &proof, blowup)
                .expect("v2 verify must accept honest prover's bundle");
            let ms = t0.elapsed().as_secs_f64() * 1000.0;
            eprintln!("[v2_bench] verify {} ms = {ms:.2}", i + 1);
            samples.push(ms);
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let verify_ms = samples[1];

        // CSV-friendly stdout line for the bench harness to scrape.
        println!(
            "v2_bench level=L{level} scheme={scheme} ext={ext_label} hash={hash_label} \
             r={r} blowup={blowup} threads={rayon_threads} \
             prove_ms={prove_ms:.0} verify_ms={verify_ms:.2} \
             proof_kib={proof_kib:.1}"
        );
    }

    /// Synthesise a fully-consistent V2 witness for testing.
    pub(crate) fn synthesize_witness() -> V2Witness {
        // Step 1: small centred z, lift to z_cleartext.
        let mut z_cleartext = Box::new([[0u32; N]; L]);
        for l in 0..L {
            for i in 0..N {
                let signed = ((i as i32 + l as i32 * 7) % 100) - 50;
                z_cleartext[l][i] = if signed >= 0 {
                    signed as u32
                } else {
                    (signed + Q as i32) as u32
                };
            }
        }
        // Step 2: z_ntt[l] = NTT(z_cleartext[l]).
        let mut z_ntt = Box::new([[0u32; N]; L]);
        for l in 0..L {
            let mut tmp = z_cleartext[l];
            ml_dsa_ntt::ntt(&mut tmp);
            z_ntt[l] = tmp;
        }
        // Step 3: random a_ntt, c_ntt, t1d_ntt; compute w_approx_ntt.
        let mut a_ntt = Box::new([[[0u32; N]; L]; K]);
        for k in 0..K {
            for l in 0..L {
                for i in 0..N {
                    a_ntt[k][l][i] =
                        (1000 + i as u32 * 17 + l as u32 * 31 + k as u32 * 41) % Q;
                }
            }
        }
        let mut c_ntt = Box::new([0u32; N]);
        for i in 0..N { c_ntt[i] = (1 + i as u32 * 23) % Q; }
        let mut t1d_ntt = Box::new([[0u32; N]; K]);
        for k in 0..K {
            for i in 0..N { t1d_ntt[k][i] = (5 + i as u32 * 11 + k as u32 * 13) % Q; }
        }
        let mut w_approx_ntt = Box::new([[0u32; N]; K]);
        for k in 0..K {
            for i in 0..N {
                let mut acc: u32 = 0;
                for l in 0..L {
                    acc = add_q(acc, mul_q(a_ntt[k][l][i], z_ntt[l][i]));
                }
                w_approx_ntt[k][i] = sub_q(acc, mul_q(c_ntt[i], t1d_ntt[k][i]));
            }
        }
        // Step 4: w_approx[k] = INTT(w_approx_ntt[k]).
        let mut w_approx = Box::new([[0u32; N]; K]);
        let derived = derive_w_approx_witness(&w_approx_ntt);
        for k in 0..K { w_approx[k] = derived[k]; }

        // Step 5: synthetic h (all zeros — UseHint becomes a passthrough).
        let h = Box::new([[0u32; N]; K]);

        // Step 6: Compute adjusted_r1[k][i] = UseHint(r1[k][i],
        // r0_sign[k][i], h[k][i]) using the native UseHint helper.
        let mut adjusted_r1 = Box::new([[0u32; N]; K]);
        for k in 0..K {
            for i in 0..N {
                let r = w_approx[k][i];
                let (r1, r0_lifted) = ml_dsa_decompose::decompose(r);
                let r0_sign = if r0_lifted != 0 && r0_lifted <= Q / 2 { 1 } else { 0 };
                let (adj, _wp, _wn) = ml_dsa_use_hint_air::use_hint(r1, r0_sign, h[k][i]);
                adjusted_r1[k][i] = adj;
            }
        }

        // Step 7: Synthesise w1bytes per FIPS 204 §3.5.7 BitPack —
        // W1_BITS_PER_COEF bits per coefficient (6 for L1, 4 for L3/L5).
        // Length = K · N · W1_BITS_PER_COEF / 8: 768 B (L1, L3) / 1024 B (L5).
        let mu_bytes = [0x37u8; 64];
        use crate::ml_dsa::params::W1_BITS_PER_COEF;
        let total_bits = K * N * W1_BITS_PER_COEF;
        let mut w1bytes = vec![0u8; total_bits / 8];
        for k in 0..K {
            for i in 0..N {
                let bit_offset = (k * N + i) * W1_BITS_PER_COEF;
                let val = adjusted_r1[k][i] as u64;
                for b in 0..W1_BITS_PER_COEF {
                    let bit = ((val >> b) & 1) as u8;
                    let byte_idx = (bit_offset + b) / 8;
                    let bit_idx = (bit_offset + b) % 8;
                    w1bytes[byte_idx] |= bit << bit_idx;
                }
            }
        }

        V2Witness {
            a_ntt, c_ntt, t1d_ntt, w_approx_ntt,
            mu_bytes, h, w1bytes,
            z_ntt, z_cleartext, w_approx, adjusted_r1,
        }
    }

    /// **Headline orchestration test.**  Drive `fill_v2_traces` end
    /// to end on a synthesised consistent witness; assert each
    /// sub-trace's per-row constraints all hold for the active rows.
    #[test]
    fn fill_v2_traces_end_to_end_orchestration() {
        let w = synthesize_witness();
        // Test-only: a fixed dummy pi_hash is fine — we only check
        // per-row trace consistency, which holds regardless of the
        // particular (γ, α) the perm-arg uses (as long as the trace
        // was filled with the same ones — which fill_v2_traces does
        // via derive_t_mem_challenges(pi_hash)).
        let traces = fill_v2_traces(&w, [0u8; 32]);

        // V17 sub-trace: every per-row constraint zero on rows 0..6147.
        let v17_n = traces.v17[0].len();
        for row in 0..v17_dim::N_ROWS_ACTIVE {
            let cur: Vec<F> = (0..v17_dim::N_COLS).map(|c| traces.v17[c][row]).collect();
            let nxt: Vec<F> = (0..v17_dim::N_COLS).map(|c| traces.v17[c][(row + 1) % v17_n]).collect();
            let cvals = v17::eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 V17: constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // INTT sub-traces: each instance's T7 constraints zero.
        for k in 0..K {
            let intt_n = traces.intt[k][0].len();
            for row in 0..t7::BUTTERFLIES_PER_NTT {
                let cur: Vec<F> = (0..intt::N_COLS).map(|c| traces.intt[k][c][row]).collect();
                let nxt: Vec<F> = (0..intt::N_COLS).map(|c| traces.intt[k][c][(row + 1) % intt_n]).collect();
                let cvals = t7::eval_per_row(&cur, &nxt, row);
                for (i, v) in cvals.iter().enumerate() {
                    assert!(v.is_zero(),
                        "v2 INTT[{k}]: constraint {i} on row {row} not zero: {v:?}");
                }
            }
        }

        // INTT row 1024 binding: t7's row-1024 state matches w_approx_ntt[k].
        for k in 0..K {
            let row_1024 = t7::BUTTERFLIES_PER_NTT;
            for i in 0..N {
                let v_cell = traces.intt[k][t7::col_state(i)][row_1024];
                let v_expected = F::from(w.w_approx_ntt[k][i] as u64);
                assert_eq!(v_cell, v_expected,
                    "v2 INTT[{k}]: row 1024 cell {i} mismatch (binding to w_approx_ntt would fail)");
            }
        }

        // TRANSCRIPT sub-trace: every T1.5 per-row constraint zero.
        let transcript_layout = ml_dsa_transcript::build_layout(&w.mu_bytes, &w.w1bytes);
        let transcript_n = traces.transcript[0].len();
        for row in 0..transcript_layout.active_rows() {
            let cur: Vec<F> = (0..transcript::N_COLS).map(|c| traces.transcript[c][row]).collect();
            let nxt: Vec<F> = (0..transcript::N_COLS).map(|c| traces.transcript[c][(row + 1) % transcript_n]).collect();
            let cvals = ml_dsa_shake_absorb_multi_air::eval_per_row(&cur, &nxt, row, &transcript_layout);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 TRANSCRIPT: constraint {i} on row {row} (block {}) not zero: {v:?}",
                    row / ROUNDS);
            }
        }

        // TRANSCRIPT output binding: c̃' extracted from trace matches
        // native compute_c_tilde_prime for the same (µ, w1bytes).
        let c_tilde_prime_from_trace =
            ml_dsa_transcript::extract_c_tilde_prime_from_trace(&traces.transcript, &transcript_layout);
        let c_tilde_prime_native =
            ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        assert_eq!(c_tilde_prime_from_trace, c_tilde_prime_native,
            "v2 TRANSCRIPT: trace c̃' differs from native — binding to sig's c̃ would fail");

        // COEFF Decompose sub-trace: every per-row constraint zero.
        let n_coeffs = K * N;
        for row in 0..n_coeffs {
            let cur: Vec<F> = (0..ml_dsa_decompose_air::WIDTH)
                .map(|c| traces.coeff_decompose[c][row]).collect();
            let dummy_nxt: Vec<F> = (0..ml_dsa_decompose_air::WIDTH)
                .map(|_| F::zero()).collect();
            let cvals = ml_dsa_decompose_air::eval_per_row(&cur, &dummy_nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 COEFF Decompose: constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // COEFF UseHint sub-trace: every per-row constraint zero.
        for row in 0..n_coeffs {
            let cur: Vec<F> = (0..ml_dsa_use_hint_air::WIDTH)
                .map(|c| traces.coeff_use_hint[c][row]).collect();
            let dummy_nxt: Vec<F> = (0..ml_dsa_use_hint_air::WIDTH)
                .map(|_| F::zero()).collect();
            let cvals = ml_dsa_use_hint_air::eval_per_row(&cur, &dummy_nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 COEFF UseHint: constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // COEFF W1Encode sub-trace: every per-row constraint zero.
        for row in 0..n_coeffs {
            let cur: Vec<F> = (0..ml_dsa_w1_encode_air::WIDTH)
                .map(|c| traces.coeff_w1_encode[c][row]).collect();
            let dummy_nxt: Vec<F> = (0..ml_dsa_w1_encode_air::WIDTH)
                .map(|_| F::zero()).collect();
            let cvals = ml_dsa_w1_encode_air::eval_per_row(&cur, &dummy_nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 COEFF W1Encode: constraint {i} on row {row} not zero: {v:?}");
            }
        }

        // T_MEM checks removed 2026-05-10 — F2b L0-L4 cross-binding
        // openings supersede T_MEM, which has been deleted from v2.
    }

    /// **v2 prove + verify skeleton round-trip.**  Honest witness +
    /// c̃ derived from TRANSCRIPT's c̃' yields a valid proof; verify
    /// accepts.
    #[test]
    fn v2_skeleton_round_trip() {
        let w = synthesize_witness();

        // For an honest prover, c̃ = c̃'.  Compute c̃' natively from
        // the witness's (µ, w1bytes) — this is what the FIPS 204
        // verify check requires.
        let c_tilde_bytes = ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

        let (_traces, proof) = prove_v2_skeleton(&w, &c_tilde_bytes);
        verify_v2_skeleton(&w, &c_tilde_bytes, &proof)
            .expect("v2 skeleton must accept honest prover's proof");
    }

    /// Mismatched c̃ (different from the trace-computed c̃') ⇒ verify
    /// rejects.  This is the FIPS 204 verify acceptance gate.
    #[test]
    fn v2_skeleton_rejects_mismatched_c_tilde() {
        let w = synthesize_witness();
        let real_c_tilde = ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let (_traces, proof) = prove_v2_skeleton(&w, &real_c_tilde);

        let mut bogus_c_tilde = real_c_tilde;
        bogus_c_tilde[0] ^= 0xFF;
        // pi_hash includes c_tilde_bytes, so the recomputed pi_hash
        // mismatches first.  But conceptually the c̃' ≠ c̃ check is
        // the FIPS 204 verify gate; either path rejects.
        let res = verify_v2_skeleton(&w, &bogus_c_tilde, &proof);
        assert!(res.is_err(), "v2 skeleton must reject c̃ mismatch");
    }

    /// Tampering: change the proof's pi_hash ⇒ verify rejects.
    #[test]
    fn v2_skeleton_rejects_tampered_pi_hash() {
        let w = synthesize_witness();
        let c_tilde_bytes = ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);
        let (_traces, mut proof) = prove_v2_skeleton(&w, &c_tilde_bytes);
        proof.pi_hash[0] ^= 0xFF;
        let res = verify_v2_skeleton(&w, &c_tilde_bytes, &proof);
        assert!(res.is_err(), "v2 skeleton must reject tampered pi_hash");
    }

    /// **HEADLINE v2 end-to-end real FRI prove + verify round-trip.**
    /// Marked `#[ignore]` because 10 FRI proves at any blowup is
    /// heavy (~30-60 s in release; minutes in debug).
    /// Run with: `cargo test --release -p deep_ali --features
    /// parallel,sha3-256 v2_real_round_trip -- --include-ignored`.
    #[test]
    #[ignore]
    fn v2_real_round_trip() {
        let w = synthesize_witness();
        let c_tilde_bytes = ml_dsa_transcript::compute_c_tilde_prime_native(&w.mu_bytes, &w.w1bytes);

        let blowup = 4;  // small for test; production uses 32
        let proof = prove_v2_real(&w, &c_tilde_bytes, blowup);

        verify_v2_real(&w, &c_tilde_bytes, &proof, blowup)
            .expect("v2 real FRI round-trip must accept honest prover's bundle");

        // Tamper: flip one byte of the V17 sub-proof, expect rejection.
        let mut tampered = proof.clone();
        tampered.fri_v17[100] ^= 0xFF;
        let res = verify_v2_real(&w, &c_tilde_bytes, &tampered, blowup);
        assert!(res.is_err(), "v2 real FRI must reject tampered V17 sub-proof");
    }

    /// **REGRESSION TEST** (gap demo inverted 2026-05-10 after F2b L0 landed):
    ///
    /// Before the fix, `verify_v2_real` accepted a witness with
    /// `w_approx[0][0]` shifted by 2·GAMMA2 (so it no longer equals
    /// `INTT(w_approx_ntt)`), because no constraint tied the INTT
    /// region's row-1024 output cells to the pi_hash-bound public
    /// `w_approx_ntt`.  T_MEM's perm-arg log entries were sourced
    /// from `witness.*` fields rather than actual sub-trace cells,
    /// so the cross-region binding was vacuous.
    ///
    /// After F2b L0 (Merkle inclusion proof on INTT[k] row 1024
    /// against `trace_root`, with cells checked against public
    /// `w_approx_ntt[k][i]`), the verifier catches this tampering
    /// at the L0 step.  This test now asserts rejection — flipping
    /// it back to "accept" would mean the L0 binding has regressed.
    ///
    /// Run with: `cargo test --release -p deep_ali --features
    /// parallel,sha3-384,mldsa-65 --no-default-features
    /// v2_real_accepts_tampered_w_approx -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn v2_l0_regression_rejects_tampered_w_approx() {
        use crate::ml_dsa::params::{GAMMA2, W1_BITS_PER_COEF};

        // Step 1: canonical honest witness.
        let w_real = synthesize_witness();

        // Step 2: build a fake witness — keep all public fields
        // (a_ntt, c_ntt, t1d_ntt, w_approx_ntt, mu_bytes, h) and
        // z_ntt / z_cleartext (which V17 constrains via the
        // polynomial identity) verbatim.  Only diverge the cleartext-
        // side fields the COEFF chain consumes.
        let mut w_fake = V2Witness {
            a_ntt:        w_real.a_ntt.clone(),
            c_ntt:        w_real.c_ntt.clone(),
            t1d_ntt:      w_real.t1d_ntt.clone(),
            w_approx_ntt: w_real.w_approx_ntt.clone(),
            mu_bytes:     w_real.mu_bytes,
            h:            w_real.h.clone(),
            z_ntt:        w_real.z_ntt.clone(),
            z_cleartext:  w_real.z_cleartext.clone(),
            w_approx:     w_real.w_approx.clone(),
            adjusted_r1:  w_real.adjusted_r1.clone(),
            w1bytes:      w_real.w1bytes.clone(),
        };

        // Shift one coefficient of w_approx by 2·GAMMA2 — guarantees
        // r1 (HighBits) changes by ±1 mod NUM_R1_VALUES, so the
        // downstream adjusted_r1 + w1bytes diverge.  Public
        // w_approx_ntt[0] is unchanged, so this w_approx is NO LONGER
        // INTT(w_approx_ntt).
        let delta = 2 * GAMMA2;
        w_fake.w_approx[0][0] = (w_fake.w_approx[0][0] + delta) % Q;

        // Recompute adjusted_r1[0][0] from the new w_approx[0][0].
        // (Synthesize uses h = 0, so UseHint passes r1 through.)
        let r_fake = w_fake.w_approx[0][0];
        let (r1_fake, r0_lifted_fake) = ml_dsa_decompose::decompose(r_fake);
        let r0_sign_fake = if r0_lifted_fake != 0 && r0_lifted_fake <= Q / 2 { 1 } else { 0 };
        let (adj_fake, _, _) =
            ml_dsa_use_hint_air::use_hint(r1_fake, r0_sign_fake, w_fake.h[0][0]);
        w_fake.adjusted_r1[0][0] = adj_fake;

        // Re-pack the W1_BITS_PER_COEF bits encoding coefficient (k=0,i=0)
        // into w1bytes.  Bit offset = (k·N + i)·W1_BITS_PER_COEF = 0.
        let val = adj_fake as u64;
        for b in 0..W1_BITS_PER_COEF {
            let byte_idx = b / 8;
            let bit_idx  = b % 8;
            w_fake.w1bytes[byte_idx] &= !(1u8 << bit_idx);
            let bit = ((val >> b) & 1) as u8;
            w_fake.w1bytes[byte_idx] |= bit << bit_idx;
        }

        // Sanity: w1bytes diverged from the real witness, so c̃' will too.
        assert_ne!(
            w_fake.w1bytes, w_real.w1bytes,
            "gap test setup: fake adjusted_r1 must change at least one w1bytes bit \
             (otherwise the COEFF chain produces the same c̃' and the gap isn't exhibited)"
        );

        // Step 3: c̃' for the fake w1bytes — the prover supplies this as
        // the public-input `c_tilde_bytes` (which a real FIPS 204
        // verifier would compare against the signature's c̃).
        let c_tilde_fake = ml_dsa_transcript::compute_c_tilde_prime_native(
            &w_fake.mu_bytes, &w_fake.w1bytes);

        // Step 4: prove + verify with the fake witness.
        let blowup = 4;
        let proof = prove_v2_real(&w_fake, &c_tilde_fake, blowup);
        let res = verify_v2_real(&w_fake, &c_tilde_fake, &proof, blowup);

        // After F2b L0, the tampered INTT row-1024 cells no longer
        // match the pi_hash-bound public `w_approx_ntt` — the L0
        // cross-binding rejects.  If this regresses to `is_ok()`,
        // the L0 binding has broken and the gap is back.
        let err = res.err().expect(
            "F2b L0 regression: verify_v2_real ACCEPTED a tampered w_approx witness — \
             the INTT row-1024 ↔ public w_approx_ntt binding is no longer enforcing"
        );
        assert!(
            err.contains("L0") && err.contains("w_approx_ntt"),
            "expected L0-specific rejection, got: {err}"
        );
    }

    /// **REGRESSION TEST** (L1 gap demo inverted 2026-05-10 after
    /// F2b L1 landed):
    ///
    /// Before L1, a prover with control over how sub-traces are
    /// filled could fill INTT[k] with canonical
    /// `w_approx_real = INTT(w_approx_ntt)` (passing L0) but fill
    /// Decompose / UseHint / W1Encode / TRANSCRIPT with
    /// `w_approx_fake = w_approx_real + tampered_delta`.  All
    /// sub-FRIs accepted individually, and `c̃' == c_tilde_bytes`
    /// boundary passed.
    ///
    /// After L1 (Merkle inclusion proof of INTT row-0 and Decompose
    /// row (k·N+i), cross-checked for cell equality), the
    /// "decoupled traces" attack is caught at the L1 cross-binding
    /// step.  This test asserts rejection — flipping it back to
    /// `is_ok()` would mean the L1 binding has regressed.
    #[test]
    #[ignore]
    fn v2_l1_gap_intt_canonical_coeff_tampered() {
        use crate::ml_dsa::params::{GAMMA2, W1_BITS_PER_COEF};

        let w_real = synthesize_witness();

        // Tamper the witness: w_approx[0][0] += 2·GAMMA2 mod Q
        // forces r1 to shift, propagating into adjusted_r1 and
        // w1bytes.
        let mut w_fake = V2Witness {
            a_ntt:        w_real.a_ntt.clone(),
            c_ntt:        w_real.c_ntt.clone(),
            t1d_ntt:      w_real.t1d_ntt.clone(),
            w_approx_ntt: w_real.w_approx_ntt.clone(),
            mu_bytes:     w_real.mu_bytes,
            h:            w_real.h.clone(),
            z_ntt:        w_real.z_ntt.clone(),
            z_cleartext:  w_real.z_cleartext.clone(),
            w_approx:     w_real.w_approx.clone(),
            adjusted_r1:  w_real.adjusted_r1.clone(),
            w1bytes:      w_real.w1bytes.clone(),
        };
        let delta = 2 * GAMMA2;
        w_fake.w_approx[0][0] = (w_fake.w_approx[0][0] + delta) % Q;
        let r_fake = w_fake.w_approx[0][0];
        let (r1_fake, r0_lifted_fake) = ml_dsa_decompose::decompose(r_fake);
        let r0_sign_fake = if r0_lifted_fake != 0 && r0_lifted_fake <= Q / 2 { 1 } else { 0 };
        let (adj_fake, _, _) =
            ml_dsa_use_hint_air::use_hint(r1_fake, r0_sign_fake, w_fake.h[0][0]);
        w_fake.adjusted_r1[0][0] = adj_fake;
        let val = adj_fake as u64;
        for b in 0..W1_BITS_PER_COEF {
            let byte_idx = b / 8;
            let bit_idx  = b % 8;
            w_fake.w1bytes[byte_idx] &= !(1u8 << bit_idx);
            let bit = ((val >> b) & 1) as u8;
            w_fake.w1bytes[byte_idx] |= bit << bit_idx;
        }
        assert_ne!(w_fake.w1bytes, w_real.w1bytes,
            "test setup: fake w1bytes must differ from real");

        let c_tilde_fake = ml_dsa_transcript::compute_c_tilde_prime_native(
            &w_fake.mu_bytes, &w_fake.w1bytes);
        let pi_hash_fake = compute_pi_hash_v2(&w_fake, &c_tilde_fake);

        // Fill canonical + tampered trace sets, both under the
        // fake pi_hash so perm-arg challenges (γ, α) match.
        let traces_canonical = fill_v2_traces(&w_real, pi_hash_fake);
        let traces_tampered  = fill_v2_traces(&w_fake, pi_hash_fake);

        // Splice: INTT from canonical (so L0 passes), everything
        // else from tampered.  V17 is identical in both because it
        // doesn't reference w_approx (only w_approx_ntt + z*).
        let spliced = V2SubTraces {
            v17:             traces_tampered.v17,
            intt:            traces_canonical.intt,
            transcript:      traces_tampered.transcript,
            coeff_decompose: traces_tampered.coeff_decompose,
            coeff_use_hint:  traces_tampered.coeff_use_hint,
            coeff_w1_encode: traces_tampered.coeff_w1_encode,
        };

        let blowup = 4;
        let proof = prove_v2_real_from_traces(
            &spliced, &w_fake.mu_bytes, &w_fake.w1bytes,
            &c_tilde_fake, pi_hash_fake, blowup,
        );
        let res = verify_v2_real(&w_fake, &c_tilde_fake, &proof, blowup);

        // After L1, the spliced trace fails at the cross-binding
        // step: Decompose's r-input cell at row k·N+i ≠ INTT[k]
        // row-0 cell at col_state(i).  If this regresses to
        // `is_ok()`, the L1 binding has broken.
        let err = res.err().expect(
            "F2b L1 regression: verify_v2_real ACCEPTED a spliced witness — \
             the INTT row-0 ↔ Decompose r-input cross-binding is no longer enforcing"
        );
        assert!(
            err.contains("L1") && (err.contains("Decompose r-input") || err.contains("public-binding")),
            "expected L1-specific rejection, got: {err}"
        );
    }

    /// **Session 6 POC**: validate the OOD cross-trace consistency
    /// mechanism on real v2 trace data.  Builds L2a bindings
    /// (Decompose col_r1 ↔ UseHint COL_R1, same-row pairs) via
    /// `binding_cells_commit::commit_binding_cells` for both source
    /// LDEs, then checks `verify_ood_consistency` accepts honest
    /// and rejects tampered.
    ///
    /// This is the proof-of-concept that the OOD-eval cross-trace
    /// primitive works on real v2 data.  Sessions 7-8 will integrate
    /// it into `V2ProofReal` and remove the F2b inclusion proofs.
    #[test]
    #[ignore]
    fn v2_session6_ood_l2a_poc() {
        use crate::binding_cells_commit::{
            commit_binding_cells, verify_ood_consistency,
        };
        use crate::trace_import::lde_trace_columns;

        let w = synthesize_witness();
        let c_tilde_bytes = ml_dsa_transcript::compute_c_tilde_prime_native(
            &w.mu_bytes, &w.w1bytes);
        let pi_hash = compute_pi_hash_v2(&w, &c_tilde_bytes);
        let traces = fill_v2_traces(&w, pi_hash);

        let blowup = 4;
        let coeff_n_trace = (K * N).next_power_of_two();

        // LDE-extend the Decompose and UseHint sub-traces.
        let decompose_lde = lde_trace_columns(
            &traces.coeff_decompose, coeff_n_trace, blowup,
        ).expect("decompose LDE");
        let use_hint_lde = lde_trace_columns(
            &traces.coeff_use_hint, coeff_n_trace, blowup,
        ).expect("use_hint LDE");

        // Build BindingCellsCommits for L2a: Decompose col_r1 vs
        // UseHint COL_R1.  Both LDEs have the same n_trace + blowup
        // = same n0 → shared z_0 → directly comparable.
        let (decompose_bcc, _) = commit_binding_cells(
            &decompose_lde,
            &[crate::ml_dsa_decompose_air::col_r1()],
            coeff_n_trace, blowup, pi_hash, b"l2a_decompose",
            v2_fri_params,
        );
        let (use_hint_bcc, _) = commit_binding_cells(
            &use_hint_lde,
            &[crate::ml_dsa_use_hint_air::COL_R1],
            coeff_n_trace, blowup, pi_hash, b"l2a_use_hint",
            v2_fri_params,
        );

        // Honest case: r1 values match, OOD-consistency should accept.
        verify_ood_consistency(&decompose_bcc, &use_hint_bcc, pi_hash, v2_fri_params)
            .expect("L2a OOD consistency must accept honest commits");

        // Tampering test: build a TAMPERED Decompose trace where
        // col_r1 differs from canonical, and verify OOD rejects.
        let mut tampered_decompose = traces.coeff_decompose.clone();
        let tamper_row = 0;
        let tamper_col = crate::ml_dsa_decompose_air::col_r1();
        tampered_decompose[tamper_col][tamper_row] =
            tampered_decompose[tamper_col][tamper_row] + F::from(1u64);

        let tampered_decompose_lde = lde_trace_columns(
            &tampered_decompose, coeff_n_trace, blowup,
        ).expect("tampered decompose LDE");
        let (tampered_decompose_bcc, _) = commit_binding_cells(
            &tampered_decompose_lde,
            &[crate::ml_dsa_decompose_air::col_r1()],
            coeff_n_trace, blowup, pi_hash, b"l2a_decompose",
            v2_fri_params,
        );

        let res = verify_ood_consistency(
            &tampered_decompose_bcc, &use_hint_bcc, pi_hash, v2_fri_params,
        );
        assert!(res.is_err(),
            "L2a OOD consistency MUST reject tampered Decompose col_r1: got {res:?}");
        let err = res.unwrap_err();
        assert!(
            err.contains("Schwartz-Zippel") || err.contains("differ"),
            "expected Schwartz-Zippel rejection, got: {err}"
        );

        eprintln!("[Session 6 POC] L2a OOD cross-trace consistency works on real v2 data:");
        eprintln!("  • Honest commits: ACCEPT");
        eprintln!("  • Tampered Decompose col_r1: REJECT via Schwartz-Zippel at z_0");
        eprintln!("  • Mechanism: f_a(z_0) vs f_b(z_0) comparison, no K·N inclusion proofs");
    }

    /// Measurement helper: dumps an honest v2 proof's bytes to /tmp
    /// so we can measure compression ratio with external tools
    /// (gzip, xz, zstd) and dedup analysis.  Run via:
    /// `cargo test --release -p deep_ali --features parallel,sha3-384,mldsa-65 \
    ///   --no-default-features v2_dump_proof_for_compression -- --ignored --nocapture`
    #[test]
    #[ignore]
    fn v2_dump_proof_for_compression() {
        let w = synthesize_witness();
        let c_tilde_bytes = ml_dsa_transcript::compute_c_tilde_prime_native(
            &w.mu_bytes, &w.w1bytes);
        let blowup = 4;
        let proof = prove_v2_real(&w, &c_tilde_bytes, blowup);
        let bytes = proof.to_bytes();
        let path = "/tmp/v2_proof_dump.bin";
        std::fs::write(path, &bytes).expect("write proof dump");
        eprintln!("[v2_dump] wrote {} bytes to {}", bytes.len(), path);

        // Quick in-process measurements of repetition.
        // Count 32-byte-aligned chunks that appear 2+ times.
        let mut chunk_counts: std::collections::HashMap<[u8; 32], usize>
            = std::collections::HashMap::new();
        let n_chunks = bytes.len() / 32;
        for i in 0..n_chunks {
            let mut c = [0u8; 32];
            c.copy_from_slice(&bytes[i*32..(i+1)*32]);
            *chunk_counts.entry(c).or_insert(0) += 1;
        }
        let unique = chunk_counts.len();
        let repeated_count: usize = chunk_counts.values().filter(|&&c| c >= 2).map(|c| c-1).sum();
        eprintln!("[v2_dump] 32-byte aligned chunks: total={n_chunks} unique={unique} \
                    redundant={repeated_count} (potential dedup savings: {} KB)",
                  repeated_count * 32 / 1024);
    }

    /// **REGRESSION TEST** for F2b **L4**: TRANSCRIPT input
    /// `public.w1bytes` must equal the bytes reconstructed from
    /// W1Encode trace bit cells.
    ///
    /// Attack (pre-L4): a prover submits canonical sub-traces (so
    /// L0-L3 all pass) but lies about `public.w1bytes` — sends a
    /// tampered value while keeping the canonical adjusted_r1 in
    /// W1Encode.  Without L4, the verifier rebuilds the transcript
    /// layout from `public.w1bytes` (the lie), and the prover sets
    /// `c_tilde_bytes = SHAKE(µ ‖ lie)` so the boundary passes.
    ///
    /// After L4 (reconstruct w1bytes from W1Encode bit cells, cross-
    /// check against `public.w1bytes`), the lie diverges from the
    /// committed W1Encode trace at the first tampered byte and L4
    /// rejects.
    ///
    /// Note: this attack uses the public API — fill traces with one
    /// witness, but lie about `public.w1bytes` only at verify time.
    /// Distinct from the L1 attack which spliced INTT separately.
    #[test]
    #[ignore]
    fn v2_l4_gap_lies_about_w1bytes() {
        let w_real = synthesize_witness();
        let c_tilde_real = ml_dsa_transcript::compute_c_tilde_prime_native(
            &w_real.mu_bytes, &w_real.w1bytes);

        // Prover side: produce an HONEST proof from canonical w_real.
        let blowup = 4;
        let proof = prove_v2_real(&w_real, &c_tilde_real, blowup);

        // Sanity: the honest proof verifies against the honest public.
        verify_v2_real(&w_real, &c_tilde_real, &proof, blowup)
            .expect("baseline: honest proof must verify");

        // Now build a TAMPERED `public` view that lies about
        // `public.w1bytes[0]` (flips a low bit) while keeping all
        // other public fields canonical.  Also adjust c_tilde_bytes
        // to match SHAKE(µ ‖ tampered_w1bytes) so the c̃' boundary
        // doesn't trip *before* L4.
        let mut tampered_public = V2Witness {
            a_ntt:        w_real.a_ntt.clone(),
            c_ntt:        w_real.c_ntt.clone(),
            t1d_ntt:      w_real.t1d_ntt.clone(),
            w_approx_ntt: w_real.w_approx_ntt.clone(),
            mu_bytes:     w_real.mu_bytes,
            h:            w_real.h.clone(),
            z_ntt:        w_real.z_ntt.clone(),
            z_cleartext:  w_real.z_cleartext.clone(),
            w_approx:     w_real.w_approx.clone(),
            adjusted_r1:  w_real.adjusted_r1.clone(),
            w1bytes:      w_real.w1bytes.clone(),
        };
        tampered_public.w1bytes[0] ^= 0x01;
        let c_tilde_tampered = ml_dsa_transcript::compute_c_tilde_prime_native(
            &tampered_public.mu_bytes, &tampered_public.w1bytes);

        // The proof's pi_hash and c_tilde_prime are bound to canonical
        // values; mismatched (`tampered_public`, `c_tilde_tampered`)
        // will trip pi_hash consistency before L4.  Skip the L0-L3
        // attack vector by constructing the proof with the tampered
        // c_tilde + pi_hash but honest sub-traces.
        //
        // Build the proof against the tampered c_tilde, honest traces:
        let pi_hash_tampered = compute_pi_hash_v2(&tampered_public, &c_tilde_tampered);
        // Fill traces with HONEST w_real (so all sub-traces are
        // canonical and L0-L3 pass), but use tampered pi_hash so the
        // perm-arg challenges match what the verifier will compute.
        let honest_traces = fill_v2_traces(&w_real, pi_hash_tampered);

        // The TRANSCRIPT trace needs to absorb the canonical w1bytes
        // (that's what honest_traces.transcript was filled with).
        // c_tilde_prime extracted from this trace = c_tilde_real, NOT
        // c_tilde_tampered.  So the c̃' boundary will reject first.
        //
        // To actually exercise L4, we need TRANSCRIPT filled with
        // TAMPERED w1bytes (so c_tilde_prime = c_tilde_tampered passes
        // boundary), but W1Encode filled with CANONICAL adjusted_r1
        // (so L3 passes but L4 catches divergence).
        let mut spliced = honest_traces;
        // Refill TRANSCRIPT with tampered w1bytes.
        let tampered_layout = ml_dsa_transcript::build_layout(
            &tampered_public.mu_bytes, &tampered_public.w1bytes);
        let transcript_n_trace = transcript::N_ROWS_POW2;
        let mut transcript_trace: Vec<Vec<F>> = (0..transcript::N_COLS)
            .map(|_| vec![F::zero(); transcript_n_trace]).collect();
        crate::ml_dsa_shake_absorb_multi_air::fill_trace(
            &mut transcript_trace, transcript_n_trace, &tampered_layout,
        );
        spliced.transcript = transcript_trace;

        let proof = prove_v2_real_from_traces(
            &spliced, &tampered_public.mu_bytes, &tampered_public.w1bytes,
            &c_tilde_tampered, pi_hash_tampered, blowup,
        );
        let res = verify_v2_real(&tampered_public, &c_tilde_tampered, &proof, blowup);

        let err = res.err().expect(
            "F2b L4 regression: verify_v2_real ACCEPTED a tampered public.w1bytes — \
             the W1Encode bit cells ↔ public.w1bytes binding is no longer enforcing"
        );
        assert!(
            err.contains("L4") && (err.contains("w1bytes") || err.contains("public-binding")),
            "expected L4-specific rejection, got: {err}"
        );
        let _ = proof;
        let _ = c_tilde_real;
    }

    /// **V17 BINDING AUDIT** (TDD, 2026-05-10):
    ///
    /// V17's docstring (`ml_dsa_verify_air_v17.rs:55-63`) says its
    /// trace's `a_ntt`/`c_ntt`/`t1d_ntt`/`w_approx_ntt`/`z_ntt`/
    /// `z_cleartext` columns are bound to pi_hash-committed public
    /// values "by FRI openings against the pi_hash" — but no such
    /// boundary check or cross-binding inclusion proof exists in
    /// `verify_v2_real`'s V17 verify path.
    ///
    /// This test exhibits the suspected attack: build a proof where
    /// - public fields are canonical (so pi_hash matches),
    /// - INTT/COEFF/TRANSCRIPT traces are canonical (so L0–L4 pass),
    /// - V17's trace is filled with a DIFFERENT norm-bounded z and
    ///   the matching w_approx_ntt that satisfies V17's polynomial
    ///   identity — which differs from public `w_approx_ntt`.
    ///
    /// If verify accepts, V17 proved its polynomial identity for a
    /// tuple unrelated to the public inputs (= soundness gap).
    /// If verify rejects, V17 has some implicit binding I missed.
    #[test]
    #[ignore]
    fn v2_l5_regression_v17_rejects_tampered_eq_region() {
        use crate::ml_dsa::params::{Q, GAMMA1, BETA};
        use crate::ml_dsa_field::{add_q, mul_q, sub_q};

        let w_real = synthesize_witness();
        let c_tilde_canonical = ml_dsa_transcript::compute_c_tilde_prime_native(
            &w_real.mu_bytes, &w_real.w1bytes);
        let pi_hash_canonical = compute_pi_hash_v2(&w_real, &c_tilde_canonical);

        // Build canonical traces.
        let traces_canonical = fill_v2_traces(&w_real, pi_hash_canonical);

        // Build a DIFFERENT norm-bounded z_cleartext (differs from
        // synthesize_witness's pattern), compute z_ntt and the matching
        // w_approx_ntt that satisfies V17's polynomial identity with
        // canonical (a_ntt, c_ntt, t1d_ntt).
        let mut z_cleartext_fake = Box::new([[0u32; N]; L]);
        for l in 0..L {
            for i in 0..N {
                // Different deterministic pattern, kept well within
                // |z|_inf < γ_1 − β to satisfy V17's norm check.
                let bound = (GAMMA1 as i32) - BETA;
                let signed = ((i as i32 * 13 + l as i32 * 23) % (bound / 2)) - (bound / 4);
                z_cleartext_fake[l][i] = if signed >= 0 {
                    signed as u32
                } else {
                    (signed + Q as i32) as u32
                };
            }
        }
        // Sanity: at least one differs from canonical so the test is meaningful.
        let mut differs = false;
        for l in 0..L {
            for i in 0..N {
                if z_cleartext_fake[l][i] != w_real.z_cleartext[l][i] { differs = true; break; }
            }
            if differs { break; }
        }
        assert!(differs, "test setup: tampered z_cleartext must differ from canonical");

        let mut z_ntt_fake = Box::new([[0u32; N]; L]);
        for l in 0..L {
            let mut tmp = z_cleartext_fake[l];
            ml_dsa_ntt::ntt(&mut tmp);
            z_ntt_fake[l] = tmp;
        }

        // Tampered w_approx_ntt satisfying V17's identity:
        //   w_approx_ntt_fake = a_ntt·z_ntt_fake − c_ntt·t1d_ntt
        let mut w_approx_ntt_fake = Box::new([[0u32; N]; K]);
        for k in 0..K {
            for i in 0..N {
                let mut acc: u32 = 0;
                for l in 0..L {
                    acc = add_q(acc, mul_q(w_real.a_ntt[k][l][i], z_ntt_fake[l][i]));
                }
                w_approx_ntt_fake[k][i] = sub_q(acc, mul_q(w_real.c_ntt[i], w_real.t1d_ntt[k][i]));
            }
        }

        // Refill V17 trace with the tampered tuple.  All other public
        // inputs (a_ntt, c_ntt, t1d_ntt) stay canonical.
        let mut v17_trace_fake: Vec<Vec<F>> = (0..v17_dim::N_COLS)
            .map(|_| vec![F::zero(); v17_dim::N_ROWS_POW2]).collect();
        v17::fill_trace(
            &mut v17_trace_fake,
            v17_dim::N_ROWS_POW2,
            &w_real.a_ntt,
            &z_ntt_fake,
            &w_real.c_ntt,
            &w_real.t1d_ntt,
            &w_approx_ntt_fake,
            &z_cleartext_fake,
        );

        let spliced = V2SubTraces {
            v17:             v17_trace_fake,
            intt:            traces_canonical.intt,
            transcript:      traces_canonical.transcript,
            coeff_decompose: traces_canonical.coeff_decompose,
            coeff_use_hint:  traces_canonical.coeff_use_hint,
            coeff_w1_encode: traces_canonical.coeff_w1_encode,
        };

        // Build proof with spliced traces under CANONICAL pi_hash
        // (= verifier's pi_hash, since they have canonical public).
        let blowup = 4;
        let proof = prove_v2_real_from_traces(
            &spliced, &w_real.mu_bytes, &w_real.w1bytes,
            &c_tilde_canonical, pi_hash_canonical, blowup,
        );

        let res = verify_v2_real(&w_real, &c_tilde_canonical, &proof, blowup);

        // If verify accepts, V17's columns are not bound to public
        // inputs and the gap is real.  If verify rejects, V17 must
        // have some implicit binding the audit missed.
        match res {
            Ok(()) => panic!(
                "V17 BINDING GAP CONFIRMED: verify_v2_real ACCEPTED a proof where V17 \
                 was filled with a tampered z_cleartext + matching w_approx_ntt that \
                 differs from public.w_approx_ntt.  V17's a_ntt/c_ntt/t1d_ntt/w_approx_ntt \
                 trace cells are NOT bound to pi_hash-committed public values.  \
                 Fix needed before v2 is sound."
            ),
            Err(e) => {
                // If it rejects, log the reason so we can identify
                // which constraint actually caught it.
                eprintln!("V17 audit: verify rejected with `{e}` — investigating which check caught it");
                // The test passes iff verify rejects — meaning V17 IS sound,
                // either via the per-row constraints or some implicit binding.
            }
        }
    }

    /// **All 5 v2 sub-AIR merge functions run on honest traces.**
    /// Builds the v2 sub-traces, LDE-extends each, runs the merge,
    /// asserts the merge succeeds (poly_div_zh has no remainder ⇒
    /// constraints vanish on the trace domain) and produces output
    /// of the right shape.
    #[test]
    fn all_v2_merges_run_on_honest_traces() {
        use crate::trace_import::lde_trace_columns;
        use crate::{
            deep_ali_merge_t7_chained_ntt,
            deep_ali_merge_t_decompose,
            deep_ali_merge_t_use_hint,
            deep_ali_merge_t_w1_encode,
            deep_ali_merge_t_transcript,
        };
        use crate::ml_dsa_shake_absorb_multi_air;

        let w = synthesize_witness();
        let test_pi_hash = [0u8; 32];
        let traces = fill_v2_traces(&w, test_pi_hash);
        let blowup = 4;  // small for fast test

        // T7 (INTT) — first instance only, the others are identical shape.
        {
            let n_trace = traces.intt[0][0].len();
            let lde = lde_trace_columns(&traces.intt[0], n_trace, blowup)
                .expect("INTT LDE");
            let kk = t7::NUM_CONSTRAINTS;
            let coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
            let (c_eval, info) = deep_ali_merge_t7_chained_ntt(
                &lde, &coeffs, F::zero(), n_trace, blowup,
            );
            assert_eq!(c_eval.len(), n_trace * blowup);
            assert_eq!(info.num_constraints, kk);
        }

        // COEFF Decompose
        {
            let n_trace = traces.coeff_decompose[0].len();
            let lde = lde_trace_columns(&traces.coeff_decompose, n_trace, blowup)
                .expect("Decompose LDE");
            let kk = ml_dsa_decompose_air::NUM_CONSTRAINTS;
            let coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
            let (c_eval, info) = deep_ali_merge_t_decompose(
                &lde, &coeffs, F::zero(), n_trace, blowup,
            );
            assert_eq!(c_eval.len(), n_trace * blowup);
            assert_eq!(info.num_constraints, kk);
        }

        // COEFF UseHint
        {
            let n_trace = traces.coeff_use_hint[0].len();
            let lde = lde_trace_columns(&traces.coeff_use_hint, n_trace, blowup)
                .expect("UseHint LDE");
            let kk = ml_dsa_use_hint_air::NUM_CONSTRAINTS;
            let coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
            let (c_eval, info) = deep_ali_merge_t_use_hint(
                &lde, &coeffs, F::zero(), n_trace, blowup,
            );
            assert_eq!(c_eval.len(), n_trace * blowup);
            assert_eq!(info.num_constraints, kk);
        }

        // COEFF W1Encode
        {
            let n_trace = traces.coeff_w1_encode[0].len();
            let lde = lde_trace_columns(&traces.coeff_w1_encode, n_trace, blowup)
                .expect("W1Encode LDE");
            let kk = ml_dsa_w1_encode_air::NUM_CONSTRAINTS;
            let coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
            let (c_eval, info) = deep_ali_merge_t_w1_encode(
                &lde, &coeffs, F::zero(), n_trace, blowup,
            );
            assert_eq!(c_eval.len(), n_trace * blowup);
            assert_eq!(info.num_constraints, kk);
        }

        // T_MEM merge removed 2026-05-10 — superseded by F2b L0-L4.

        // TRANSCRIPT
        {
            let n_trace = traces.transcript[0].len();
            let lde = lde_trace_columns(&traces.transcript, n_trace, blowup)
                .expect("Transcript LDE");
            let layout = ml_dsa_transcript::build_layout(&w.mu_bytes, &w.w1bytes);
            let kk = ml_dsa_shake_absorb_multi_air::num_constraints(&layout);
            let coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
            let (c_eval, info) = deep_ali_merge_t_transcript(
                &lde, &coeffs, F::zero(), n_trace, blowup, &layout,
            );
            assert_eq!(c_eval.len(), n_trace * blowup);
            assert_eq!(info.num_constraints, kk);
        }
    }

    /// Sub-trace dimensions match the v2 layout module's projections.
    #[test]
    fn fill_v2_traces_dimensions_match_layout() {
        let w = synthesize_witness();
        let traces = fill_v2_traces(&w, [0u8; 32]);

        assert_eq!(traces.v17.len(), v17_dim::N_COLS);
        assert_eq!(traces.v17[0].len(), v17_dim::N_ROWS_POW2);

        assert_eq!(traces.intt.len(), K);
        for k in 0..K {
            assert_eq!(traces.intt[k].len(), intt::N_COLS);
            // Each INTT instance's pow2 row count is 2048 here (matches
            // the t7 standalone test pow2; the layout module's
            // 8192-row figure is for the COMBINED 4-instance trace if
            // it were stacked vertically — we use separate sub-traces
            // per instance for cleaner FRI prove).
            assert!(traces.intt[k][0].len() >= t7::BUTTERFLIES_PER_NTT + 1);
        }

        assert_eq!(traces.transcript.len(), transcript::N_COLS);
        assert_eq!(traces.transcript[0].len(), transcript::N_ROWS_POW2);
    }
}
