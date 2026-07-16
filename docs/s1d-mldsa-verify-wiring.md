# Handoff: wiring S1d (in-circuit ML-DSA verify) for model-C trustless validity

**Status:** the sub-slices are proven; the S1d **assembly** is not wired. This is the
prerequisite for C2 trustless validity (`epoch_c2.rs`'s `InCircuitBatch` slot). It is the
heavy piece — expect a ~9–13 s record-AIR at L1. Branch `feature/model-c-trustless`.

Goal: implement `prove_verify_mldsa_b256(pk, M, σ, log_inv_rate, security_bits)` — a real
STARK proof over `B256TowerFamily` that **ML-DSA.Verify(pk, M, σ) = ACCEPT** — then batch N of
them and bind to R\*, so `epoch_c2::verify_epoch_c2` can discharge `InCircuitBatch` (trustless
validity) instead of `NativeVerified` (hybrid).

---

## 1. The relation (FIPS 204 Alg 8; from `mldsa_verify.rs` header)

```
(ρ, t1) ← pkDecode(pk)
(c̃, z, h) ← sigDecode(σ)                              [reject if h malformed]
Â   ← ExpandA(ρ)                                        [S1b — SHAKE-128 + rejection]
tr  ← SHAKE-256(pk, 64);  μ ← SHAKE-256(tr ‖ M', 64)   [S1c-family SHAKE-256]
c   ← SampleInBall(c̃)                                   [S1c — SHAKE-256 Fisher–Yates]
w'Approx ← NTT⁻¹( Â ∘ NTT(z) − NTT(c) ∘ NTT(t1·2ᵈ) )   [S1a — R_q arithmetic]
w1' ← UseHint(h, w'Approx)                              [S1d — Decompose + hint]
c̃'  ← SHAKE-256(μ ‖ w1Encode(w1'), 2λ/8)               [S1c-family SHAKE-256]
ACCEPT ⟺  ‖z‖∞ < γ1 − β   AND   c̃' == c̃   AND   (#1-bits in h) ≤ ω
```

Public boundary columns: `pk, M, c̃` (and derived `μ`). Witness: `z, h, Â, c, w'Approx, w1'`.
Because `c̃` is public and `c̃'` is recomputed in-circuit from the witness, a σ that fails
verification admits **no** accepting witness — the tampered-sig-rejects guarantee, over a
2²⁵⁶ challenge field (FS/sumcheck/FRI clear NIST L1/L3/L5).

## 2. What already exists (reuse — do NOT rebuild)

Native reference + sub-algorithms (unit-gated in `mldsa_verify.rs`): `verify_ref`, `pk_decode`,
`sig_decode`, `decompose`, `high_bits`, `low_bits`, `use_hint`, `w1_encode`, `inf_norm`,
`mldsa_statement_hash`, `mldsa_batch_root`. Constants: `VerifyParams` (44/65/87 → L1/L3/L5).

Proven in-circuit gadgets over B256 (the S1 slices):
- **S1a** (`mldsa_ntt.rs`): R_q = Z_q[X]/(X²⁵⁶+1) add/sub, ζ·v multiply, forward/inverse NTT.
- **S1b** (`mldsa_shake.rs`): `GATE prove-1` SHAKE-128 squeeze; `prove-2/2b/2c` ExpandA
  accept-decision + ordered placement + rank==prefix-sum (Â bound to accepted z's).
- **S1c** (`mldsa_shake.rs`): `GATE prove-3a` SampleInBall j≤i accept-decision.
- STARK entry: `binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256,
  Sha256Compression, HasherChallenger<Sha256>>` (see `b256_prove.rs`, `b256_sha3.rs`,
  `b256_keccak.rs`). In-circuit Keccak-f (for the SHAKE squeezes) is `b256_keccak.rs`.

So S1d is **wiring the proven slices into one constraint system + adding the digit gadgets +
the three ACCEPT boundaries** — "no new hash or field machinery" (header §What S1d adds).

## 3. What S1d must add

1. **Digit gadgets** (Alg 36–40, 28): `Decompose`/`HighBits`/`LowBits`, `UseHint`, `w1Encode`.
   In-circuit these are base-(2γ2) digit-range gadgets whose bounds reuse S0's carry decision
   (`< α`, `< m`), identical in shape to the S1a reduction / S1b–S1c rejection carries. Build
   them as `TableBuilder<B256>` gadgets gated == the native `decompose`/`use_hint`/`w1_encode`.
2. **The three ACCEPT boundaries:**
   - `‖z‖∞ < γ1 − β` — a centered-norm bound per coeff (S0 `< m` carry, m = γ1−β).
   - `c̃' == c̃` — a SHAKE-256 digest equality; `c̃` is a **public** boundary column, so this
     is the load-bearing binding (wrong `w1'` ⇒ wrong μ-hash ⇒ `c̃' ≠ c̃` ⇒ no witness).
   - hint-weight ≤ ω — a popcount bound (B1 sum, S0 `< m` carry, m = ω+1).
3. **The glue (DAG):** ExpandA's Â feeds the S1a matrix–vector product; SampleInBall's c is
   lifted by NTT (S1a); the μ and c̃' SHAKE-256 hashes reuse the S1b multi-block squeeze chain
   (`b256_keccak`). One `ConstraintSystem<B256>`; `pk, M, c̃` as public boundaries.

## 4. The batch + R\* binding (plug into epoch_c2)

`epoch_c2::EpochProofC2.validity = InCircuitBatch(proof_bytes)` and the statements are already
trustlessly committed (C1). S1d wires the validity:

1. Per statement i: `stmt_i = mldsa_statement_hash(SHA3(pk_i), SHA3(M_i))` — already the C2
   leaf identity (`Statement{pk_hash,msg_hash}`). `R*_stmt = mldsa_batch_root(&stmts)`.
2. `prove_batch_mldsa_b256(&[(pk_i, M_i, σ_i)]) -> proof_bytes`: a batched STARK that proves
   ML-DSA.Verify ACCEPT for every i and binds `stmt_i` to `R*_stmt` (each sig's `(pk,M,c̃)`
   public boundary hashed into `stmt_i`). Batch-local by construction (each sig is an
   independent sub-AIR), so it proves in the swarm — parallel, low-RSS — and the combiner
   assembles `R*_stmt` (the decomposition that makes C1 feasible applies identically).
3. `verify_epoch_c2` on `InCircuitBatch`: (a) `verify_batch_mldsa_b256(proof, R*_stmt)`; (b)
   check `R*_stmt` equals the statement set committed by the C1 epoch (recompute
   `mldsa_batch_root` over `proof.statements` and require equality). Then validity is
   trustless: every committed statement is provably validly signed.

## 5. Test plan (gated + adversarial + measured)

- **Correctness (single sig):** `fips204` genuine keygen→sign→verify — a real σ PROVES + VERIFIES
  in-circuit (== `verify_ref` == `fips204` ACCEPT).
- **★ Tampered-sig rejects:** flip a byte of z / c̃ / h / M ⇒ `verify_ref` REJECTs ⇒ the
  in-circuit relation admits NO accepting witness (prove fails / verify rejects). This is the
  load-bearing S1d gate (header §soundness boundary).
- **ACVP KATs:** the FIPS 204 ACVP verify vectors (accept + reject cases), witness-side gated.
- **Batch + R\*:** N sigs prove; `verify_epoch_c2(InCircuitBatch)` accepts; a swapped/forged
  statement ⇒ `R*_stmt` mismatch ⇒ reject.
- **Measure:** single-sig prove/verify/size and batch, at L1/L3/L5 (params 44/65/87). Expect
  the ~9–13 s record-AIR verify at L1 (width-dominated); the epoch resolver verify then =
  C1 (~ms/record) + this validity term (once/epoch), amortized over queries.

## 6. Honest cost + scope

S1d is width-dominated: the assembled ML-DSA verify (NTT + SHAKE squeezes + digit gadgets) is a
wide AIR ⇒ ~9–13 s verify/record at L1 (the number `se_tld_epoch_demo` and `accumulation.rs`
quote). Trustless validity therefore costs seconds/epoch on top of C1's ms — the trust↔cost
tradeoff (`docs/model-c-trustless-epoch.md §1`), acceptable amortized over an epoch of queries.
ECDSA-P256 trustless validity is the sibling (`ec_verify.rs`): its point-ops
(double-and-add rounds, complete-add) PROVE over B256, but the full verify assembly is not
wired — a parallel effort. ML-DSA (S1d) is the recommended first trustless-validity target (its
sub-slices are further along, and it's the PQ signature the standalone-record path uses).

## 7. Build order

1. **Digit gadgets** (Decompose/HighBits/LowBits/UseHint/w1Encode) as B256 tables, gated ==
   native. Small, self-contained.
2. **Assemble S1d single-sig**: wire pkDecode→ExpandA(S1b)→NTT arith(S1a)→UseHint→w1Encode→
   SHAKE c̃'(S1b)→3 ACCEPT boundaries into one `ConstraintSystem<B256>`; implement
   `prove_verify_mldsa_b256`. Gate correctness + tampered-reject vs `fips204`.
3. **Batch + R\* binding**: `prove_batch_mldsa_b256` / `verify_batch_mldsa_b256`; bind to
   `mldsa_batch_root`.
4. **Plug into epoch_c2**: `verify_epoch_c2(InCircuitBatch)` = batch verify + `R*_stmt`
   equality. Measure the full trustless `.se`/ML-DSA epoch (C1 + validity).
5. **L3/L5** (params 65/87) + the ECDSA sibling if needed.

## 8. Gotchas

- The crate builds only under `cargo test` (`mldsa_verify.rs` imports the `#[cfg(test)]`
  `mldsa_ntt::reference`; also `fips204` is a dev-dep). S1d prove paths + `epoch_c2` batch verify
  run under `cargo test --release --lib`.
- The end-to-end ML-DSA gate is `#[ignore]` "until the S1a `full_256` proof frees the shared
  target" — S1d prove tests likewise heavy; keep `#[ignore]`.
- Keccak-f in-circuit (the SHAKE squeezes) is the width driver — reuse `b256_keccak`, do not
  reimplement. The outer commitment stays SHA-256 (FIPS 180-4); the 2²⁵⁶ field carries FS.
- Parameter sets: 44→L1, 65→L3, 87→L5 (`VerifyParams`); the SHAKE output length `2λ/8` for c̃'
  differs per level.

## 9. References

- `mldsa_verify.rs` — the S1d design header (relation, ACCEPT predicates, soundness boundary),
  `verify_ref`, decompose/use_hint/w1_encode, `mldsa_statement_hash`/`mldsa_batch_root`.
- `mldsa_ntt.rs` (S1a), `mldsa_shake.rs` (S1b/S1c, `GATE prove-1/2/2b/2c/3a`), `b256_keccak.rs`
  (in-circuit Keccak), `b256_prove.rs`/`b256_sha3.rs` (the `constraint_system::prove` entry).
- `epoch_c2.rs` (the `InCircuitBatch` slot), `epoch_c1.rs` (trustless commitment/membership),
  `docs/model-c-trustless-epoch.md §3` (C2), `docs/recursion-fold-epoch-integration.md`.
- `ec_verify.rs` — the ECDSA-P256 sibling (point-ops proven, full verify not assembled).
