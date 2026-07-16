# Handoff: model C — the trustless epoch proof (removing aggregator trust)

**Status:** design + honest cost characterization; **not built.** This is the trust-model
upgrade over the shipped `epoch_fold` (model A). It has two independent concerns (C1, C2)
with very different costs; get the trust requirement pinned before building either.

Branch `feature/accumulation-recursion`. See also `docs/recursion-fold-epoch-integration.md`.

---

## 0. What model A actually trusts (the gap to close)

`epoch_fold` (model A, committed `bbeab1c`/`8753560`/`d223d25`) gives the resolver:
`verify_epoch` ≈ **6–16 ms flat in N** + `verify_record` ≈ **µs**. It attests:

- **membership** — `record ∈ R*` (SHA3-Merkle path), and
- **an opening** — the FRI-Binius decider proves *a* committed polynomial P evaluates to
  `opening_value` at the FS point.

The gap: **P is committed with the decider's OWN Merkle commitment (SHA-256), not R\***. So
"the epoch verifies" and "record ∈ R\*" are only about the *same* record set if you **trust
the aggregator committed P = interleave(R\*'s records)**. A malicious aggregator could
commit P′ ≠ interleave(R\*), open P′ (valid decider proof), and the resolver would accept a
membership in R\* whose epoch integrity was proven about P′. Also, model A trusts the
aggregator **native-verified each record's validity** before inclusion (TM-1 baseline).

Two concerns, then:
- **C1 — bind P's commitment to R\*** (structural: the opened P *is* the interleave of the
  R\*-committed records).
- **C2 — attest each record's validity in the proof** (not trusted): the in-circuit
  signature-verify ACCEPT is what's committed/aggregated.

## 1. The honest cost — model A ~ms, model C ~seconds (once/epoch)

The ~8 ms decider is the **un-bound** opening (piop commitment, model A). The **R\*-bound**
opening — "whether R\* is FRI-openable as P's codeword" (`accumulation.rs:127`, the *decider
crux*) — is a **batch-width binius verify ~9–13 s at L1** (measured upper bound,
hash-op-table dominated; `accumulation.rs:582`), and is **NOT wired**. So:

| | resolver verify_epoch | trust |
|---|---|---|
| Model A (shipped) | **~6–16 ms flat in N** | aggregator committed P = interleave(R\*), and validated records |
| Model C (C1-bound) | **~9–13 s** (once/epoch, L1) | none for P↔R\* |
| Model C (C1+C2) | ~9–13 s + validity-AIR term | none |

**This is a real trust↔cost tradeoff, not a bug.** ~9–13 s once per epoch is negligible
amortized over an epoch's worth of DNS queries (each still µs), *if* epochs are coarse
(hourly/daily). State it explicitly in any deployment claim: **the ms resolver number is
model A; trustless P↔R\* is seconds/epoch.**

## 2. C1 — bind P's commitment to R\* (the decider crux)

**Goal:** make R\* itself the commitment the decider opens, so membership (R\* path) and the
epoch opening are the SAME commitment ⇒ P provably = interleave(R\*'s records).

**Mechanism (grounded):** `R* = streaming_interleaved_root(...)` is the Merkle parent over
the N record sub-roots (`accumulation.rs:125`; the zone tree, homomorphism-free). C1 = prove
this R\* is **FRI-openable as P's codeword** at the FS point — via binius's
`commit_interleaved` path. The opening is the ~9–13 s batch-width verify (§1).

**Why it's feasible despite N:** the decomposition (`accumulation.rs:598`) —
`P(a, b) = Σ_i eq(b, bin(i)) · P_i(a)` — means the R\*-committed opening **splits into
batch-local openings**: each record i opens its own `P_i(a)` at the shared inner point `a`
against its own sub-root `R*_i` (bounded RSS, parallel across the swarm), and a combiner does
the eq-weighted sum. So the **prove** decomposes exactly like the batch proves (no monolithic
P on one machine — the architecture "closes", `accumulation.rs:604`); only the **verify** is
the ~9–13 s batch-width term.

**Build (C1):**
1. Replace `epoch_fold`'s piop commitment with the `commit_interleaved` commitment whose root
   is (or is bound to) `R*` — the crux. Study binius `piop::commit_interleaved` /
   `streaming_commit.rs`; confirm the interleaved-coset Merkle parent equals the zone tree
   R\* (or add a proven equality).
2. `verify_epoch`: verify the R\*-committed opening at the FS point. Measure the real verify
   (expect ~9–13 s L1) + RSS.
3. `verify_record`: membership is now an opening of P's codeword block i vs R\* (or keep the
   SHA3 path if R\* is defined as the zone tree AND proven equal to the codeword commitment).
4. Aggregator: batch-local openings (per §above) — parallel, low-RSS; combiner does the eq sum.

**Soundness:** with R\* = P's commitment, a P′≠interleave(R\*) cannot open against R\*; the
membership and epoch are the same commitment. κ_sys unchanged (same FRI/κ_FS; the opening is
just against R\* instead of a fresh root).

## 3. C2 — attest validity in the proof (in-circuit signature verify)

**Goal:** the epoch attests every record's signature verifies, without trusting the
aggregator's native check.

**Mechanism:** the record leaf becomes the **validity-AIR ACCEPT claim**. The in-circuit
verify AIRs exist: `mldsa_verify.rs` (ML-DSA-44/65/87: ACCEPT ⟺ ‖z‖∞<γ1−β ∧ c̃'==c̃ ∧
#1-bits(h)≤ω, three ACCEPT boundaries, gated vs `fips204`) and `ec_verify.rs` (ECDSA-P256,
assembled; note its own caveat that the full in-circuit ECDSA is not yet wired end-to-end).
Each record's ACCEPT wire = 1 is enforced; the batch of ACCEPT claims is committed under R\*
and discharged.

**Cost:** heavy — the record-AIR is width-dominated (this is the "record-AIR decider ~9–13 s
@L1, polylog in N, width-dominated" the `.se` demo references). C2 shares the C1 opening cost
but adds the validity-AIR width. Each in-circuit verify is a real STARK; the swarm proves
them in parallel (batch-local), the aggregator combines, the resolver verifies once.

**Build (C2):**
1. For one record: run `mldsa_verify.rs` (ML-DSA leaf) / assembled `ec_verify.rs` to produce
   a proof with the ACCEPT boundary; expose the ACCEPT claim as the epoch leaf witness.
2. Fold N ACCEPT claims through the C1 R\*-bound opening; measure.
3. `standalone_record.rs` (Outcome 1) upgrades: the registrant's ML-DSA verify becomes the
   in-circuit ACCEPT leaf (vs model A's native verify).

## 4. Recommended build order

1. **C1 first** (structural P↔R\* binding) — it's the smaller, self-contained crux and closes
   the main model-A hole (aggregator-committed-a-different-P). Deliver: R\*-committed
   `verify_epoch` + the **measured** ~9–13 s number (replacing the ~9–13 s *estimate*), and
   the batch-local decomposition prover.
2. **Decision gate:** is ~9–13 s/epoch acceptable for the deployment (epoch cadence)? If not,
   the ms model-A path stays, with the trust caveat documented.
3. **C2** (validity attestation) — only if trustless *validity* is required beyond trustless
   membership. Start with the ML-DSA leaf (`mldsa_verify.rs`, `fips204`-gated), then ECDSA.

## 5. What NOT to do

- Do not claim the ms resolver number for a trustless epoch — it is model A (P↔R\* trusted).
- Do not wire a P↔R\* "binding" that re-commits P separately and hashes it to R\* in the clear
  without a proof — that just moves the trust. The bind must be R\* == the opened commitment.
- Do not attempt proof-carrying recursion (parent verifies child STARK in-circuit) for C2 —
  it's wide/slow; the ACCEPT-claim + batch opening is the intended path.

## 6. References

- `accumulation.rs` — the decider crux (`:127`), the ~9–13 s note (`:582`), the decomposition
  identity `P(a,b)=Σ eq·P_i(a)` (`:598`), `streaming_interleaved_root`, `hybrid_epoch_pipeline_e2e`.
- `committed_decider.rs` — the piop commit/open/verify (model-A commitment); `decider.rs` — the
  callable open/verify + B128↔B256 lift; `epoch_fold.rs` — model A (interleaved single-opening).
- `mldsa_verify.rs`, `ec_verify.rs` — the in-circuit validity AIRs (C2 leaves).
- `streaming_commit.rs` — the low-RSS interleaved-batch commit (C1 batch-local prove).
- `se_tld_epoch_demo.rs` — the real `.se` hybrid epoch; `standalone_record.rs` — Outcome 1.
