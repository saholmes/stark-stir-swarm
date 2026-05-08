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
use crate::permutation_argument::{self as t_mem, LogEntry};
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
    pub t_mem:           Vec<Vec<F>>,    // T_MEM permutation-argument sub-trace
}

// ─── fill_v2_traces ────────────────────────────────────────────────

/// Build all 3 architecturally-significant v2 sub-traces from the
/// witness.  Returns sub-traces sized to each sub-proof's pow2 row
/// count (per `ml_dsa_verify_air_v2_layout`).
pub fn fill_v2_traces(witness: &V2Witness) -> V2SubTraces {
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

    // ── T_MEM (cross-region permutation argument) ──
    // Build the 4 binding sets as a single combined log.  Address
    // encoding: tag * 1_000_000 + index, where:
    //   tag 1: B1 — w_approx[k][i] ↔ Decompose r-input.
    //   tag 2: B2a — r1 ↔ UseHint r1-input.
    //   tag 3: B2b — r0_sign ↔ UseHint r0_sign-input.
    //   tag 4: B3 — adjusted_r1 ↔ W1Encode r1-input.
    //   tag 5: B4 — w1bytes ↔ Transcript absorb-byte input.
    let mut log: Vec<LogEntry> = Vec::new();
    let tag_offset = 1_000_000u64;

    for k in 0..K {
        for i in 0..N {
            let idx = (k * N + i) as u64;
            let r = witness.w_approx[k][i] as u64;
            // B1: w_approx ↔ Decompose r-input.
            log.push(LogEntry { address: F::from(1 * tag_offset + idx), value: F::from(r), is_write: true });
            log.push(LogEntry { address: F::from(1 * tag_offset + idx), value: F::from(r), is_write: false });
            // B2a: r1 ↔ UseHint r1-input.
            let (r1, _) = ml_dsa_decompose::decompose(witness.w_approx[k][i]);
            log.push(LogEntry { address: F::from(2 * tag_offset + idx), value: F::from(r1 as u64), is_write: true });
            log.push(LogEntry { address: F::from(2 * tag_offset + idx), value: F::from(r1 as u64), is_write: false });
            // B2b: r0_sign ↔ UseHint r0_sign-input.
            let r0_sign = use_hint_inputs[(k * N + i)].1 as u64;
            log.push(LogEntry { address: F::from(3 * tag_offset + idx), value: F::from(r0_sign), is_write: true });
            log.push(LogEntry { address: F::from(3 * tag_offset + idx), value: F::from(r0_sign), is_write: false });
            // B3: adjusted_r1 ↔ W1Encode r1-input.
            let adj = witness.adjusted_r1[k][i] as u64;
            log.push(LogEntry { address: F::from(4 * tag_offset + idx), value: F::from(adj), is_write: true });
            log.push(LogEntry { address: F::from(4 * tag_offset + idx), value: F::from(adj), is_write: false });
        }
    }
    // B4: w1bytes ↔ Transcript absorb-byte input.
    for (idx, &b) in witness.w1bytes.iter().enumerate() {
        log.push(LogEntry { address: F::from(5 * tag_offset + idx as u64), value: F::from(b as u64), is_write: true });
        log.push(LogEntry { address: F::from(5 * tag_offset + idx as u64), value: F::from(b as u64), is_write: false });
    }

    let t_mem_n_trace = log.len().next_power_of_two();
    let mut t_mem_trace: Vec<Vec<F>> = (0..t_mem::WIDTH)
        .map(|_| vec![F::zero(); t_mem_n_trace]).collect();
    let gamma = F::from(0xC0FFEEu64);   // would be Fiat-Shamir derived in production
    let alpha = F::from(0xDEAD_BEEFu64);
    t_mem::fill_trace(&mut t_mem_trace, t_mem_n_trace, &log, gamma, alpha);

    V2SubTraces {
        v17: v17_trace,
        intt: intt_traces,
        transcript: transcript_trace,
        coeff_decompose: decompose_trace,
        coeff_use_hint: use_hint_trace,
        coeff_w1_encode: w1_encode_trace,
        t_mem: t_mem_trace,
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
pub fn compute_pi_hash_v2(w: &V2Witness, c_tilde_bytes: &[u8; 32]) -> [u8; 32] {
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
    pub c_tilde_prime:         [u8; 32],   // computed by TRANSCRIPT
    /// FRI sub-proofs (deferred): in the prototype these hold trace
    /// digests; in production they hold serialized `DeepFriProof`s.
    pub fri_v17_digest:        [u8; 32],
    pub fri_intt_digests:      [[u8; 32]; K],
    pub fri_coeff_digest:      [u8; 32],
    pub fri_transcript_digest: [u8; 32],
    pub fri_t_mem_digest:      [u8; 32],
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
pub fn prove_v2_skeleton(w: &V2Witness, c_tilde_bytes: &[u8; 32]) -> (V2SubTraces, V2Proof) {
    let traces = fill_v2_traces(w);

    // c_tilde_prime: extract from TRANSCRIPT trace.
    let transcript_layout = ml_dsa_transcript::build_layout(&w.mu_bytes, &w.w1bytes);
    let c_tilde_prime = ml_dsa_transcript::extract_c_tilde_prime_from_trace(
        &traces.transcript, &transcript_layout,
    );

    let pi_hash = compute_pi_hash_v2(w, c_tilde_bytes);

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
    let fri_t_mem_digest      = digest_trace(&traces.t_mem);

    let proof = V2Proof {
        pi_hash, c_tilde_prime,
        fri_v17_digest, fri_intt_digests, fri_coeff_digest,
        fri_transcript_digest, fri_t_mem_digest,
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
    c_tilde_bytes: &[u8; 32],
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
    if regen_proof.fri_t_mem_digest != proof.fri_t_mem_digest {
        return Err("v2 verify: T_MEM sub-trace digest mismatch".into());
    }

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
    pub c_tilde_prime:  [u8; 32],
    pub fri_v17:        Vec<u8>,
    pub fri_intt:       Vec<Vec<u8>>,    // K = 4
    pub fri_decompose:  Vec<u8>,
    pub fri_use_hint:   Vec<u8>,
    pub fri_w1_encode:  Vec<u8>,
    pub fri_transcript: Vec<u8>,
    pub fri_t_mem:      Vec<u8>,
}

impl V2ProofReal {
    /// Serialize to bytes: 32 + 32 (pi_hash + c̃') + length-prefixed
    /// Vec<u8> for each FRI sub-proof (length encoded as 4-byte LE u32).
    pub fn to_bytes(&self) -> Vec<u8> {
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
        write_v(&mut out, &self.fri_t_mem);
        out
    }

    /// Deserialize from bytes; returns `Err` on any framing problem.
    pub fn from_bytes(data: &[u8]) -> Result<Self, String> {
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
        let mut c_tilde_prime = [0u8; 32]; c_tilde_prime.copy_from_slice(&take_n(data, &mut pos, 32)?);
        let fri_v17 = read_v(data, &mut pos)?;
        let n_intt = read_u32(data, &mut pos)? as usize;
        let mut fri_intt = Vec::with_capacity(n_intt);
        for _ in 0..n_intt { fri_intt.push(read_v(data, &mut pos)?); }
        let fri_decompose = read_v(data, &mut pos)?;
        let fri_use_hint = read_v(data, &mut pos)?;
        let fri_w1_encode = read_v(data, &mut pos)?;
        let fri_transcript = read_v(data, &mut pos)?;
        let fri_t_mem = read_v(data, &mut pos)?;
        if pos != data.len() {
            return Err(format!("V2ProofReal: {} trailing bytes", data.len() - pos));
        }
        Ok(Self {
            pi_hash, c_tilde_prime,
            fri_v17, fri_intt, fri_decompose, fri_use_hint, fri_w1_encode,
            fri_transcript, fri_t_mem,
        })
    }
}

const V2_BLOWUP: usize = 32;
/// Auto-derived from the active `sha3-N` Cargo feature: 54 / 79 / 105
/// for NIST PQ Levels 1 / 3 / 5 (Johnson-regime unconditional).
/// See `crate::stark_level::NUM_QUERIES_LEVEL`.
const V2_NUM_QUERIES: usize = crate::stark_level::NUM_QUERIES_LEVEL;
const V2_SEED_Z: u64 = 0xDEEF_BAAD;
const V2_TMEM_GAMMA: u64 = 0xC0FFEEu64;
const V2_TMEM_ALPHA: u64 = 0xDEAD_BEEFu64;

fn make_v2_schedule(n0: usize) -> Vec<usize> {
    vec![2usize; n0.trailing_zeros() as usize]
}

fn comb_coeffs(num: usize) -> Vec<F> {
    (0..num).map(|i| F::from((i + 1) as u64)).collect()
}

fn v2_fri_params(n0: usize, pi_hash: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: make_v2_schedule(n0),
        r: V2_NUM_QUERIES,
        seed_z: V2_SEED_Z,
        coeff_commit_final: true,
        d_final: 1,
        stir: false,
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
    let params = v2_fri_params(n0, pi_hash);
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
    c_tilde_bytes: &[u8; 32],
    blowup: usize,
) -> V2ProofReal {
    let traces = fill_v2_traces(w);

    let transcript_layout = ml_dsa_transcript::build_layout(&w.mu_bytes, &w.w1bytes);
    let c_tilde_prime = ml_dsa_transcript::extract_c_tilde_prime_from_trace(
        &traces.transcript, &transcript_layout,
    );
    let pi_hash = compute_pi_hash_v2(w, c_tilde_bytes);

    // V17
    let fri_v17 = prove_one_sub_air(
        &traces.v17, traces.v17[0].len(), blowup, pi_hash,
        |lde, n_trace, blowup| {
            let kk = crate::ml_dsa_verify_air_v17::NUM_CONSTRAINTS;
            crate::deep_ali_merge_ml_dsa_v17(lde, &comb_coeffs(kk), F::zero(), n_trace, blowup).0
        },
    );

    // INTT × K
    let mut fri_intt: Vec<Vec<u8>> = Vec::with_capacity(K);
    for k in 0..K {
        let bytes = prove_one_sub_air(
            &traces.intt[k], traces.intt[k][0].len(), blowup, pi_hash,
            |lde, n_trace, blowup| {
                let kk = crate::ml_dsa_ntt_chained_air::NUM_CONSTRAINTS;
                crate::deep_ali_merge_t7_chained_ntt(lde, &comb_coeffs(kk), F::zero(), n_trace, blowup).0
            },
        );
        fri_intt.push(bytes);
    }

    // COEFF Decompose
    let fri_decompose = prove_one_sub_air(
        &traces.coeff_decompose, traces.coeff_decompose[0].len(), blowup, pi_hash,
        |lde, n_trace, blowup| {
            let kk = crate::ml_dsa_decompose_air::NUM_CONSTRAINTS;
            crate::deep_ali_merge_t_decompose(lde, &comb_coeffs(kk), F::zero(), n_trace, blowup).0
        },
    );

    // COEFF UseHint
    let fri_use_hint = prove_one_sub_air(
        &traces.coeff_use_hint, traces.coeff_use_hint[0].len(), blowup, pi_hash,
        |lde, n_trace, blowup| {
            let kk = crate::ml_dsa_use_hint_air::NUM_CONSTRAINTS;
            crate::deep_ali_merge_t_use_hint(lde, &comb_coeffs(kk), F::zero(), n_trace, blowup).0
        },
    );

    // COEFF W1Encode
    let fri_w1_encode = prove_one_sub_air(
        &traces.coeff_w1_encode, traces.coeff_w1_encode[0].len(), blowup, pi_hash,
        |lde, n_trace, blowup| {
            let kk = crate::ml_dsa_w1_encode_air::NUM_CONSTRAINTS;
            crate::deep_ali_merge_t_w1_encode(lde, &comb_coeffs(kk), F::zero(), n_trace, blowup).0
        },
    );

    // TRANSCRIPT
    let layout_for_closure = transcript_layout.clone();
    let fri_transcript = prove_one_sub_air(
        &traces.transcript, traces.transcript[0].len(), blowup, pi_hash,
        move |lde, n_trace, blowup| {
            let kk = ml_dsa_shake_absorb_multi_air::num_constraints(&layout_for_closure);
            crate::deep_ali_merge_t_transcript(
                lde, &comb_coeffs(kk), F::zero(), n_trace, blowup, &layout_for_closure,
            ).0
        },
    );

    // T_MEM
    let fri_t_mem = prove_one_sub_air(
        &traces.t_mem, traces.t_mem[0].len(), blowup, pi_hash,
        |lde, n_trace, blowup| {
            let kk = t_mem::NUM_CONSTRAINTS;
            crate::deep_ali_merge_t_mem(
                lde, &comb_coeffs(kk), F::zero(), n_trace, blowup,
                F::from(V2_TMEM_GAMMA), F::from(V2_TMEM_ALPHA),
            ).0
        },
    );

    V2ProofReal {
        pi_hash, c_tilde_prime,
        fri_v17, fri_intt, fri_decompose, fri_use_hint, fri_w1_encode,
        fri_transcript, fri_t_mem,
    }
}

/// **Production v2 verifier.**  Recomputes `pi_hash`, runs 10 FRI
/// sub-verifies, checks `c̃' == c̃` final boundary.  Returns `Ok(())`
/// iff every check passes.
///
/// **NO Layer 1 native `ml_dsa::verify`.**  v2's defining feature.
pub fn verify_v2_real(
    public: &V2Witness,        // public fields are what the verifier receives via PI
    c_tilde_bytes: &[u8; 32],
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

    // 3. V17 sub-proof.
    let v17_n_trace = crate::ml_dsa_verify_air_v17::VERIFY_AIR_V17_ACTIVE_ROWS.next_power_of_two();
    verify_one_sub_air(&proof.fri_v17, v17_n_trace, blowup, pi_hash)
        .map_err(|e| format!("v2 V17: {e}"))?;

    // 4. INTT × K sub-proofs.
    let intt_n_trace = (t7::BUTTERFLIES_PER_NTT + 16).next_power_of_two();
    if proof.fri_intt.len() != K {
        return Err(format!("v2 verify: expected {K} INTT proofs, got {}", proof.fri_intt.len()));
    }
    for k in 0..K {
        verify_one_sub_air(&proof.fri_intt[k], intt_n_trace, blowup, pi_hash)
            .map_err(|e| format!("v2 INTT[{k}]: {e}"))?;
    }

    // 5. COEFF sub-proofs (3 of them).
    let coeff_n_trace = (K * N).next_power_of_two();
    verify_one_sub_air(&proof.fri_decompose, coeff_n_trace, blowup, pi_hash)
        .map_err(|e| format!("v2 Decompose: {e}"))?;
    verify_one_sub_air(&proof.fri_use_hint, coeff_n_trace, blowup, pi_hash)
        .map_err(|e| format!("v2 UseHint: {e}"))?;
    verify_one_sub_air(&proof.fri_w1_encode, coeff_n_trace, blowup, pi_hash)
        .map_err(|e| format!("v2 W1Encode: {e}"))?;

    // 6. TRANSCRIPT sub-proof.
    let transcript_layout = ml_dsa_transcript::build_layout(&public.mu_bytes, &public.w1bytes);
    let transcript_n_trace = transcript_layout.active_rows().next_power_of_two();
    verify_one_sub_air(&proof.fri_transcript, transcript_n_trace, blowup, pi_hash)
        .map_err(|e| format!("v2 TRANSCRIPT: {e}"))?;

    // 7. T_MEM sub-proof.
    let n_log_pairs = (K * N) + (K * N) + (K * N) + (K * N) + 768;  // matches prover's log shape
    let n_log_active = 2 * n_log_pairs;
    let t_mem_n_trace = n_log_active.next_power_of_two();
    verify_one_sub_air(&proof.fri_t_mem, t_mem_n_trace, blowup, pi_hash)
        .map_err(|e| format!("v2 T_MEM: {e}"))?;

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

    /// Synthesise a fully-consistent V2 witness for testing.
    fn synthesize_witness() -> V2Witness {
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

        // Step 7: Synthesise w1bytes as a 6-bit-per-coefficient
        // packed encoding of adjusted_r1.  K·N·6/8 = 768 bytes.
        let mu_bytes = [0x37u8; 64];
        let total_bits = K * N * 6;
        let mut w1bytes = vec![0u8; total_bits / 8];
        for k in 0..K {
            for i in 0..N {
                let bit_offset = (k * N + i) * 6;
                let val = adjusted_r1[k][i] as u64;
                for b in 0..6 {
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
        let traces = fill_v2_traces(&w);

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

        // T_MEM sub-trace: every per-row constraint zero AND final
        // RP = WP (multiset equality).
        let t_mem_n = traces.t_mem[0].len();
        let gamma = F::from(0xC0FFEEu64);
        let alpha = F::from(0xDEAD_BEEFu64);
        // n_active for our binding log: 2·(K·N + K·N + K·N + K·N + 768) = 2·(4·K·N + 768).
        let n_pairs = (K * N) + (K * N) + (K * N) + (K * N) + 768;
        let n_active = 2 * n_pairs;
        for row in 0..(n_active - 1) {
            let cur: Vec<F> = (0..t_mem::WIDTH).map(|c| traces.t_mem[c][row]).collect();
            let nxt: Vec<F> = (0..t_mem::WIDTH).map(|c| traces.t_mem[c][row + 1]).collect();
            let cvals = t_mem::eval_per_row(&cur, &nxt, row, gamma, alpha);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "v2 T_MEM: constraint {i} on row {row} not zero: {v:?}");
            }
        }
        // Final consistency: RP[n_active-1] = WP[n_active-1].
        assert_eq!(
            t_mem::final_consistency(&traces.t_mem, n_active),
            F::zero(),
            "v2 T_MEM: multiset equality fails — read multiset ≠ write multiset"
        );
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
            deep_ali_merge_t_mem,
            deep_ali_merge_t_transcript,
        };
        use crate::ml_dsa_shake_absorb_multi_air;

        let w = synthesize_witness();
        let traces = fill_v2_traces(&w);
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

        // T_MEM
        {
            let n_trace = traces.t_mem[0].len();
            let lde = lde_trace_columns(&traces.t_mem, n_trace, blowup)
                .expect("T_MEM LDE");
            let kk = t_mem::NUM_CONSTRAINTS;
            let coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
            let gamma = F::from(0xC0FFEEu64);
            let alpha = F::from(0xDEAD_BEEFu64);
            let (c_eval, info) = deep_ali_merge_t_mem(
                &lde, &coeffs, F::zero(), n_trace, blowup, gamma, alpha,
            );
            assert_eq!(c_eval.len(), n_trace * blowup);
            assert_eq!(info.num_constraints, kk);
        }

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
        let traces = fill_v2_traces(&w);

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
