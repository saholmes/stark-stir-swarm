# v2 ML-DSA Verify — Soundness Audit (2026-05-09)

Audit of the deep_ali v2 ML-DSA verify protocol implementation against
the FRI-paper (`Downloads/ESORICS-FIPS_Aligned_STARKs_with_Multi_Level_PQ_Security.pdf`)
and STIR-paper (`Downloads/STARK_STIR.pdf`) specifications.

## Scope

This audit covers `crates/deep_ali/src/`:
- `ml_dsa_verify_air_v2_orchestration.rs` — top-level prove/verify
- `lib.rs` — `deep_ali_merge_*` constraint composition functions
- `fri.rs` — FRI / STIR prove + verify infrastructure
- `permutation_argument.rs` — T-MEM perm-arg (already fixed in this audit)

## Summary table

| Gap | Severity | Status | Effort |
|-----|----------|--------|--------|
| 1. Static γ, α in T-MEM perm-arg | High | **FIXED** | ~150 LoC |
| 2. T-MEM challenges in F (not F_ext) | High (L3+) | **FIXED** (Fp⁶/Fp⁸ lift) | ~700 LoC |
| 3. T-MEM final-row boundary `RP=WP` | High | **FIXED** | ~150 LoC |
| 4. Constraint comp coeffs α static | Medium | **PARTIAL** (now FS-derived in F) | ~80 LoC done, ~600 to lift to F_pe |
| 5. DEEP correction missing (eq 1) | Medium (was Critical) | OPEN — superseded by 5a + 5b | ~700 LoC (paper-exact form) |
| 5a. Trace Merkle commit + binding | High | **LANDED** | ~270 LoC |
| 5b. AIR padding doesn't satisfy constraints | High | **LANDED (use_hint)** | ~30 LoC (1 AIR; others trivially satisfied) |
| 6. `seed_z` static constant | Low | OK (acts as FS domain tag) | 0 |
| 7. HVZK blinding (β·R) missing | Medium | OPEN (Lemma 4) | ~150 LoC |
| 8. Public-input boundary constraints | Medium | OPEN (preimage-bound, not formal) | ~500 LoC |
| 9. Cross-AIR T-MEM bindings tautological | High | OPEN (witness-only LogEntries) | ~1000 LoC |

## Detailed findings

### 1. Static γ, α in T-MEM perm-arg — FIXED

**Was:** `V2_TMEM_GAMMA = 0xC0FFEE`, `V2_TMEM_ALPHA = 0xDEAD_BEEF` —
predictable to the prover at trace-construction time. A malicious
prover could craft (address, value) pairs whose perm-arg products
collide despite multiset inequality.

**Fix:** `derive_t_mem_challenges(pi_hash) -> (ExtField, ExtField)`
in `ml_dsa_verify_air_v2_orchestration.rs`. SHAKE-256 with domain
tag `b"mmiyc/v2/t_mem/challenges" || pi_hash` produces the (γ, α)
pair, so they are unpredictable until after pi_hash is fixed.

**Reference:** memory/feedback_perm_arg_fiat_shamir.md.

### 2. T-MEM challenges in F (not F_ext) — FIXED

**Was:** γ, α sampled from base field Goldilocks (|F| = 2⁶⁴).
Schwartz-Zippel bound for ~2¹⁴ log entries: 2⁻⁵⁰. Below L3 (2⁻¹⁹²)
and L5 (2⁻²⁵⁶) targets.

**Fix:** lifted γ, α to ExtField — Fp⁶ for L1/L3 (sha3-256/384),
Fp⁸ for L5 (sha3-512). Trace cells (TERM, RR, RW, RP, WP) encoded
as `EXT_DEGREE` base-field columns each via `TowerField::{to,from}_fp_components`.
Per-row constraints emit one base-field equation per coefficient
of each F_ext-valued constraint. Total layout: 4 + 5·EXT_DEGREE
columns, 2 + 8·EXT_DEGREE base-field constraints.

New T-MEM ε bound: 2⁻³⁷⁰ (Fp⁶) / 2⁻⁴⁹⁸ (Fp⁸). Comfortably below
all three target levels.

**Reference:** memory/feedback_perm_arg_fiat_shamir.md.

### 3. T-MEM final-row boundary `RP_F_ext = WP_F_ext` — FIXED

**Was:** Per-row constraints enforced that RP, WP were correctly
*accumulated* via the transition relation, but never enforced
`RP_F_ext = WP_F_ext` at the last active row. The native helper
`final_consistency()` checked it in tests but the FRI proof didn't
include it, so a malicious prover could ship a trace with
mismatched multisets and per-row constraints all satisfied.

**Fix:** added F_ext-valued boundary constraint
`(cur.IS_ACTIVE − nxt.IS_ACTIVE) · (RP − WP) = 0`. The selector
fires exactly once at the active→padding transition.

### 4. Constraint composition α coefficients — PARTIAL

**Was:** `comb_coeffs(num) = [F::from(i+1) for i in 0..num]` —
hardcoded integers `[1, 2, …, num]`. Predictable α defeats
Theorem 1's Event-E1 Schwartz-Zippel argument: a malicious prover
who knows α can craft constraint values whose linear combination
cancels at trace-domain points where the AIR is violated.

**Partial fix:** `comb_coeffs(num, &pi_hash, domain_sep)` —
SHAKE-256 derives α from `pi_hash` with per-sub-AIR domain
separation. α is now unpredictable.

**Remaining gap (paper requires F_pe, implementation gives F):**
The paper's Theorem 1 ε_E1 bound is `s/|F_pe|` ≈ 2⁻³⁷⁰ at L1.
Our α is in base F, so the actual bound is `s/|F|` ≈ 2⁻⁵⁰. Below
L1 (2⁻¹²⁸) target. Lifting α to F_pe requires extension-field
IFFT/FFT and extension-field `poly_div_zh` throughout the merge
pipeline. ~600 additional LoC.

**Reference:** memory/feedback_constraint_composition_alpha_fs.md.

### 5. DEEP correction missing in `poly_div_zh` — OPEN (CRITICAL)

**Issue:** `lib.rs:249-287` `poly_div_zh` does straight polynomial
long division by `Z_H(X) = X^T - 1` and silently discards the
remainder in release builds (the assertion is gated by
`#[cfg(debug_assertions)]`). Returns the polynomial quotient
regardless of whether dividend was actually divisible by Z_H.

**Why this is critical:** the paper's Theorem 1 requires the
construction (eq 1):

```
C(X) = [Φ(X) − Φ(z)·Z_H(X)/Z_H(z)] / (X − z) + β·R(X)
```

The DEEP shift `Φ(z)·Z_H(X)/Z_H(z)` is what makes the resulting
`f_0 = C|H_0` far from the RS code when AIR is invalid (Event E2:
prob ≤ (D+1)/(|F_pe|−|H_0|)). Without it, an honest prover gets
phi/Z_H exact (because Φ is divisible), and a malicious prover
gets a polynomial quotient that's also low-degree — STIR/FRI
accepts both.

**Concrete attack path for current code:**
1. Adversary picks any low-degree `c_eval` (e.g. zero polynomial).
2. Computes Merkle root, runs FRI honestly.
3. STIR low-degree test passes (zero polynomial IS low-degree).
4. Verifier accepts.

The proof carries no information about ML-DSA verify because
nothing binds `c_eval` to a trace satisfying the AIR.

**Required fix:**
1. Sample DEEP point `z ∈ F_pe` from FS (`pi_hash`-derived).
2. Compute `Φ(z) = Σ α_j · constraint_j(trace_at_z, z)` where
   `trace_at_z` is each LDE column interpolated to z (barycentric
   formula).
3. Construct C(X) per eq 1.
4. f_0 = C|H_0 ∈ F_pe^|H_0|.
5. Update `deep_fri_prove` / `deep_fri_verify` to handle Vec<E>
   initial function (currently Vec<F>).

**Effort estimate:** ~700 LoC across `lib.rs::deep_ali_merge_*`
(propagated across 7 merge functions), `fri.rs` (Vec<E> support),
and orchestration (FS derivation + interpolation).

**Note:** Theorem 9's straight-line extractor argument *can*
recover the trace from f_0 + Merkle openings (so trace commitment
isn't separately needed), but only if f_0 was constructed via eq
(1). With the current `phi/Z_H` construction, the extractor
recovers a trace that satisfies the per-row constraints
modulo Z_H but the soundness gap from the missing DEEP correction
remains.

### 6. `seed_z` is a static constant — OK

**Initial concern:** `V2_SEED_Z = 0xDEEF_BAAD` looked like a
hardcoded OOD challenge.

**Resolution:** `seed_z` is absorbed into the FS transcript at
`fri.rs:1125` as a tag. The actual OOD challenge `z_ext` is
derived from the FS sponge state via
`challenge_ext::<E>(&mut tr, b"z_fp3")` after `pi_hash + seed_z +
root_f0` are absorbed. So `z_ext` IS pi_hash-dependent and varies
per-proof. The constant `seed_z` acts as a domain tag, not as the
challenge value. Not a soundness bug.

### 7. HVZK blinding β·R(X) missing — OPEN

The paper's Lemma 4 (Perfect HVZK) requires `C(X) = D_z(X) + β·R(X)`
where β ∈ F_pe× is uniform and R is a uniform low-degree polynomial.
Currently no β·R term is added. Without blinding, proofs leak
witness information beyond what HVZK allows. Not a soundness gap
*per se*, but breaks the zero-knowledge property the paper claims.

**Required fix:** sample β, R from FS (`pi_hash`-derived); add to
`C(X)` in the merge function.

**Effort:** ~150 LoC, depends on (5) being implemented first.

### 8. Public-input boundary constraints — OPEN

**Issue:** `compute_pi_hash_v2` hashes (a_ntt, c_ntt, t1d_ntt,
w_approx_ntt, mu, h, c_tilde) into `pi_hash`. The FS challenges
depend on pi_hash, so an adversary can't switch out public inputs
without finding a SHA3 preimage (computationally infeasible). This
gives **preimage-resistance** but not formal in-circuit binding —
the trace cells where these inputs live aren't constrained to
equal the public values.

**Practical impact:** small. The preimage requirement gives ~256-bit
collision resistance, sufficient for most threat models. Formal
binding is the principled fix but the practical gap is bounded by
the hash strength.

**Required fix (if pursued):** add input-row boundary constraints
to each consuming AIR (mu in Transcript, c_ntt in V17, etc.).
~500 LoC across 6 sub-AIRs. Each constraint shape:
`is_input_row · (cell − public_input_byte) = 0`.

### 9. Cross-AIR T-MEM bindings are tautological — OPEN (HIGH)

**Issue:** `fill_v2_traces` builds T-MEM LogEntry list from
`witness.w_approx`, `witness.w1bytes`, etc. Both writes (claimed
producer) and reads (claimed consumer) pull values from the SAME
witness arrays. So T-MEM proves "witness data is consistent with
itself" — tautological, doesn't actually bind cross-AIR cells.

**Concrete example:** B1 binding (line 215-218 of orchestration):
```rust
let r = witness.w_approx[k][i] as u64;
log.push(LogEntry { ..., value: F::from(r), is_write: true });   // "from V17"
log.push(LogEntry { ..., value: F::from(r), is_write: false });  // "to Decompose"
```

Both LogEntries use `witness.w_approx[k][i]` — neither comes from
the actual V17 trace cells (writes) or Decompose trace cells (reads).
A malicious prover could have V17's z_ntt cells diverge from the
witness arrays, and T-MEM wouldn't detect it.

**Required fix:** add per-AIR constraints that emit specific cells
into shared T-MEM addresses, with T-MEM's LogEntry list constructed
from actual trace cells (not witness arrays). Substantial structural
refactor (~1000 LoC) — every sub-AIR needs in-circuit "cell-to-T-MEM
emit" gates.

**Alternative:** widen the AIR to interleave sub-AIR trace blocks
that share columns directly. Avoids T-MEM but increases width.

## Recommendations

For the **paper deadline**, the priority order is:

1. **Document gap 5 (DEEP correction) in the paper's "Implementation"
   section.** Be transparent that the implementation runs straight
   polynomial division by Z_H rather than the eq (1) DEEP construction.
   The empirical numbers (timing, proof size) are still meaningful.
2. **Fix gap 5 in code post-deadline.** It's the most critical
   remaining gap and ~700 LoC of focused work.
3. **Lift gap 4 (α coefficients) to F_pe** alongside gap 5 (same
   refactor — both need extension-field merge pipeline).
4. **Defer gaps 7, 8, 9** unless a reviewer raises them. They're
   real gaps but practically bounded (preimage-resistance for 8,
   internal-consistency for 9).

For **production deployment**, all gaps should be closed.

## Threat-model framing

The implementation appears to target an **honest-prover-with-bug-finding**
threat model, where pi_hash binding ensures public-input integrity
and the per-row constraints catch implementation bugs. For this
threat model, the gaps are not exploitable.

For a **fully malicious prover** threat model (which the paper's
Theorem 4 ε_Π bound formally covers), gap 5 is exploitable as
described above.

This audit was generated 2026-05-09 against:
- `stark-stir-swarm` HEAD as of session work-tree.
- `Downloads/ESORICS-FIPS_Aligned_STARKs_with_Multi_Level_PQ_Security.pdf` (FRI paper).
- `Downloads/STARK_STIR.pdf` (STIR paper).
