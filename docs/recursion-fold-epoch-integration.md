# Handoff: recursion-fold of stranded proofs into a resolver-cheap epoch proof

**Status:** resolver-cost feasibility **MEASURED** (see §2); the fold→decider pipeline
exists in prototype (`accumulation.rs::hybrid_epoch_pipeline_e2e`, `committed_decider.rs`);
**production wiring NOT done.** This is piece 2 of the DNS-STARK end-to-end
(see also `docs/seam-rlc-batch-integration.md` = piece 1).

**Two outcomes this enables**
1. **Standalone record proof** — a registrant signs a record update with **ML-DSA**, submits
   to the registry; its validity proof becomes a *leaf* folded in at the next epoch.
2. **Swarm epoch → resolver-cheap proof** — a low-RSS strand swarm proves the zone in
   parallel; recursion folds it into **one succinct proof whose single public input is the
   zone Merkle root R\***; a resolver verifies that proof once (~ms), then answers each query
   with a **µs Merkle path** from R\* to the record — at DNS-resolution cost.

**Stacks.** Per-record validity = `deep_ali` (Goldilocks, DEEP-FRI). Epoch fold + decider =
`binius-substrate` (B128/B256, FRI-Binius PCS). The bridge between them is the crux (§5).

---

## 1. Cost model (who pays what)

| Stage | Who / when | Cost (measured or target) |
|---|---|---|
| Stranded prove of each record | swarm sliver, parallel | <500 MiB RSS/sliver, ~s each (measured) |
| Aggregate seam verify | aggregator, once/epoch | sub-second w/ RLC seam batch (piece 1) |
| Recursion fold → succinct proof | aggregator, once/epoch | fold O(leaves) µs-folds; decider **prove** ~0.6 s (L1, 2^18) |
| Decider verify (epoch proof) | resolver, once/epoch | **7.4–10.6 ms L1 (MEASURED); ~400–556 KiB** |
| Per-query record proof | resolver, per query | **µs Merkle path** from R\* (verified above) |

The resolver-facing budget is the constraint; §2 shows it is met.

## 2. MEASURED resolver-facing numbers (the go/no-go — GO)

`binius-substrate` tests (2026-07-16):

**`committed_decider_opening`** — succinct-proof verify vs domain size:

| Level | 2^n_vars | VERIFY | proof |
|---|---|---|---|
| L1 | 1,024 | 7.4 ms | 241 KiB |
| L1 | 262,144 | 10.6 ms | 556 KiB |
| L3 | 262,144 | 16.0 ms | 806 KiB |
| L5 | 262,144 | 67.5 ms | 1.8 MiB |

Verify scales **polylog** (256× domain → +3 ms at L1); tamper rejects at all levels.

**`interleaved_decider_verify_vs_leaves`** — one opening verifies all N records (L1, inner=6):

| N records | VERIFY | proof |
|---|---|---|
| 2 | 3.6 ms | 156 KiB |
| 128 | 7.7 ms | 354 KiB |
| 512 | 8.0 ms | 395 KiB |

256× more records → verify +4.4 ms only (polylog in leaf count). ⇒ **whole zone verifies at
~8 ms / ~400 KiB, growing only polylog toward millions of records.**

## 3. What already exists (reuse, do not rebuild)

- **`binius-substrate/src/accumulation.rs`** — the fold primitive + real Hanoi tree:
  - `struct Record { evals: Vec<F>, claim: EvalClaim }`; `struct EvalClaim { point: Vec<F>, value: F }` (`F = BinaryField128b`).
  - `interleave(records) -> Vec<F>` (block-interleave N records into P over `inner+log N` vars).
  - `lifted_claim(rec, i, m) -> EvalClaim`; `accumulate(records, challenges) -> (P, acc_claim, fold_proofs)`;
    `accumulate_verify(record_claims, proofs, challenges) -> Option<EvalClaim>` (width-independent replay).
  - **`#[test] hybrid_epoch_pipeline_e2e`** — the balanced binary fold tree (16→8→4→2→1),
    canonical root R\* via `streaming_interleaved_root`, `leaf_id = SHA3(R* ‖ i ‖ sub_i)`,
    position-binding (permute records → different R\* → different root, measured reject),
    lying-leaf reject. **This is the fold prototype to productionize.**
- **`binius-substrate/src/committed_decider.rs`** — REAL FRI-Binius multilinear commit→open→verify
  (`binius_core::piop::{commit, prove, verify}`); `committed_decider_measure_all`,
  `interleaved_decider_measure_l1`. Verify measured in §2. **This discharges the accumulated claim.**
- **`binius-substrate/src/accumulation_air.rs`** — the *in-circuit* fold-verify (for a fully
  succinct, O(1) resolver replay if the O(leaves) fold-replay is too heavy resolver-side).
- **`deep_ali`** — per-record validity: `verify_stranded_g` (full in-circuit stranded verify) and
  the **hybrid path** (`se_zone_hnpl` / `se_tld_epoch_demo`, `SeEpochPackage`, ~207 KiB / 1.36 ms).
- **`merkle`** — zone Merkle tree (`MerkleTreeChannel`, `commit_compact`/`open_compact`/`verify_opening`).

## 4. Target pipeline

```
per record r:
    validity_proof_r = prove_record_valid(r)          // deep_ali: stranded OR hybrid OR ML-DSA-leaf
    sub_root_r       = SHA3(pos_r ‖ commit(r))          // position-bound record commitment
zone:
    R* = merkle_root({sub_root_r})                      // the SINGLE public input
    leaves[r] = Record{ evals = leaf_witness(r), claim = EvalClaim@(pi-derived point) }
    (P, acc_claim, fold_proofs) = fold_tree(leaves, challenges = FS(pi_hash ‖ R*))
    epoch_proof = { R*, decider_open(P at acc_claim.point), acc_claim, fold_proofs (or accumulation_air proof) }
    // pi_hash = H(zone ‖ epoch ‖ R*)   (statement binding — see §5.4)
resolver (once/epoch): verify epoch_proof   → ~8–10 ms, ~400 KiB   (§2)
resolver (per query) : record + merkle_path(R* → sub_root_r)  → µs
```

## 5. The crux: what the folded claim ATTESTS + the field bridge

This is the real design decision; be explicit about the **trust model** chosen.

### 5.1 Three attestation models

- **(A) Trusted-aggregation baseline (v1).** The aggregator VERIFIES each record's validity
  proof natively (`verify_stranded_g` / hybrid verify / ML-DSA verify), then folds the
  *validated* record set under R\*. The epoch proof attests "R\* commits exactly this set of
  records" (position-bound); record *validity* is trusted-on-aggregation. Matches the shipped
  **TM-1 honest-curious-workers + trusted-coordinator** baseline. Cheapest; resolver gets
  R\*-membership + the aggregator's reputation.
- **(C) Trustless accumulation (target).** Each record's validity is expressed as an **eval
  claim** (the validity AIR's ACCEPT wire = 1 at the FS-derived OOD point), folded into
  `acc_claim`; the **decider** discharges it. The epoch proof then attests "every record under
  R\* has a valid proof" with no aggregator trust. This is the Mode-B decider.
- **(B) Full proof-carrying recursion.** Parent verifies each child STARK in-circuit — REJECTED
  as the default: binius verify is linear in committed width, so in-circuit FRI/Merkle is wide
  → seconds/node (see `b512_recursion.rs`: its primitives are *aggregation, not* proof-carrying
  recursion; "we do NOT overclaim"). Use only where a single hard link genuinely needs it.

**Recommendation:** ship **(A)** first (unblocks the e2e + all measurements), then upgrade the
attestation to **(C)** by making the leaf witnesses the validity-AIR ACCEPT claims. Do NOT
attempt (B).

### 5.2 The field bridge (deep_ali Goldilocks → binius B128)

The per-record validity proof lives in `deep_ali` (Goldilocks). The fold/decider live in
`binius-substrate` (B128). A record becomes an accumulation **leaf** via:
- **v1 (A):** `leaf_witness(r)` = the record's canonical bytes / committed field values,
  re-encoded as a B128 multilinear (`Record.evals`), with `sub_root_r` its SHA3 commitment.
  Validity is checked natively by the aggregator (no field bridge on the *proof*, only on the
  record data). Simplest; correct for the membership attestation.
- **target (C):** `leaf_witness(r)` = the validity-AIR trace (or its ACCEPT-claim witness)
  re-expressed over B128. This is a genuine cross-field re-commitment — the substantive work.
  Two sub-options: (i) run the validity AIR natively in the binius stack for the leaf; (ii)
  carry the Goldilocks OOD ACCEPT value and prove the transcode. Prototype (i) first.

### 5.3 R\* as the single public input

`R* = streaming_interleaved_root(n_records, 1, 0, |i,_| sub_root_i)` (as in
`hybrid_epoch_pipeline_e2e`). It is a CR commitment to exactly the record codewords; a permuted
or substituted record set yields a different R\* (measured). Bind it as the decider's public
input (absorb R\* into `pi_hash`, §5.4). Resolver membership = `merkle_open(R* → sub_root_r)`
via the `merkle` crate.

### 5.4 Fiat–Shamir / public-input binding (carry the seam_aggregation lesson)

- `pi_hash = H(zone_name ‖ epoch ‖ R*)`. Absorb into every FS challenge.
- Fold challenges `t_k = H(pi_hash ‖ R* ‖ accumulator-states-so-far)` in `F_ext` — NOT free
  inputs (the `hybrid_epoch_pipeline_e2e` prototype uses an rng stand-in for
  `t = H(transcript)`; production must derive from the transcript, exactly as
  `seam_rlc_batch`/`seam_aggregation` do). Binding must live in the leaf CLAIMS (leaf points
  FS-derived from `pi_hash`), not only the challenges — see the `seam_aggregation.rs` note
  ("the fold is sound for any challenge; the anchor is pi-derived leaf points").
- The decider opening verifies `P(acc_claim.point) = acc_claim.value` against the same `pi_hash`.

## 6. New surface (proposed)

New module `binius-substrate/src/epoch_fold.rs`:

```rust
pub struct EpochLeaf { pub sub_root: [u8;32], pub record: Vec<F /*B128*/> }   // leaf_witness(r)
pub struct EpochProof {
    pub rstar: [u8;32],                         // the single public input
    pub decider: CommittedOpen,                 // piop open of P at acc_claim.point (committed_decider)
    pub acc_claim: EvalClaim,
    pub fold: FoldEvidence,                     // Vec<FoldProof> (v1) OR accumulation_air proof (fully succinct)
    pub n_records: usize, pub epoch: u64,
}
pub struct RecordOpening { pub sub_root: [u8;32], pub merkle: MerkleOpening }  // resolver per-query

pub fn fold_epoch(leaves: &[EpochLeaf], zone: &str, epoch: u64) -> EpochProof;   // aggregator
pub fn verify_epoch(proof: &EpochProof, zone: &str) -> Result<(), String>;        // resolver, once
pub fn verify_record(proof: &EpochProof, opening: &RecordOpening) -> Result<(), String>; // resolver, per query
```

`fold_epoch`: build sub_roots → R\* → leaves+lifted claims → balanced fold tree (FS challenges
from `pi_hash ‖ R*`) → decider open. `verify_epoch`: `accumulate_verify` (fold replay) or the
`accumulation_air` proof + `committed_decider::verify` of the opening; check `pi_hash`, R\*.
`verify_record`: `MerkleTreeChannel::verify_opening(R*, opening.merkle)`.

## 7. Standalone ML-DSA record proof (Outcome 1)

`prove_record_valid(r)` for the ML-DSA path = the existing ML-DSA verify AIR
(`deep_ali` `ml_dsa_verify_air_v2*`) over `(record_bytes, ml_dsa_sig, registrant_pk)`, public
inputs `(zone, name, rrset, epoch, registrant_pk)`. Output is a leaf with `sub_root =
SHA3(pos ‖ commit(record))`. Submitted to the registry; folded at the next epoch by
`fold_epoch`. No new crypto — a wrapper + public-input schema over the existing AIR. (Model (A):
aggregator verifies the ML-DSA proof before inclusion; model (C): fold its ACCEPT claim.)

## 8. Test plan + e2e measurement

- **Honest epoch** (small N, e.g. 8/64 records) → `verify_epoch` accepts; `verify_record` for
  each accepts. Measure `verify_epoch` ms + proof KiB (expect the §2 curve).
- **Tampered record** (flip a record post-commit) → different sub_root → R\* moves →
  `verify_epoch` (or the membership check) rejects.
- **Substituted / permuted record set** → different R\* → reject (as `hybrid_epoch_pipeline_e2e`).
- **Wrong zone/epoch** at verify → `pi_hash` mismatch → reject.
- **Model (C):** invalid record whose validity claim is false → decider reject (`R(z0)`/ACCEPT≠1).
- **★ E2E `.se` epoch:** drive from `se_zone_hnpl` (real Tranco `.se` records, 7 DNSSEC algos);
  fold the zone → one epoch proof; MEASURE: aggregator prove (fold + decider), epoch proof size,
  resolver `verify_epoch` ms, per-query `verify_record` µs. Compare the resolver total to a
  DNSSEC resolution (native RRSIG verify ~161 µs/sig + network). Target: resolver per-query µs,
  epoch verify ~ms.

## 9. Migration / sequencing

1. `epoch_fold.rs` with **model (A)** over synthetic leaves; port `hybrid_epoch_pipeline_e2e`
   adversarial asserts; wire `committed_decider` open/verify; measure `verify_epoch`.
2. R\* public-input + `verify_record` Merkle path; `pi_hash` binding.
3. `.se` e2e (§8) via `se_zone_hnpl`; the headline resolver numbers.
4. Upgrade attestation to **model (C)** (leaf = validity-AIR ACCEPT claim; the field bridge §5.2).
5. Optional: `accumulation_air` in-circuit fold-replay for O(1) resolver (if O(leaves) replay
   dominates `verify_epoch`).
6. Layer piece 1 (RLC seam batch) to cut the aggregator's per-epoch seam-verify.

## 10. Open questions to resolve during build

- **Trust model** for v1 vs target (A→C) — get product sign-off; it changes what the epoch
  proof *means* to a resolver.
- **Field bridge (§5.2)** for model (C): native binius validity AIR (i) vs Goldilocks transcode
  proof (ii). Prototype (i).
- **Resolver replay cost:** is `accumulate_verify` (O(leaves) µs-folds) fine at zone scale, or is
  the `accumulation_air` in-circuit replay needed to keep `verify_epoch` flat? (§2's ~8 ms is the
  decider opening; add the fold-replay term and re-measure.)
- **Proof size budget:** ~400–556 KiB/epoch — confirm acceptable for resolver epoch fetch/caching
  (it is amortized across all queries in the epoch; per-query is µs).

## 11. References

- `binius-substrate/src/accumulation.rs` (fold, `hybrid_epoch_pipeline_e2e`, `streaming_interleaved_root`)
- `binius-substrate/src/committed_decider.rs` (decider open/verify; §2 measurements)
- `binius-substrate/src/accumulation_air.rs` (in-circuit fold-verify)
- `docs/seam-rlc-batch-integration.md` (piece 1), `docs/accumulation-recursion.md`
- `deep_ali` `ecdsa_verify_stranded_gway.rs` (stranded validity), `se_zone_hnpl` / `se_tld_epoch_demo` (`.se` hybrid epoch)
- Measured resolver numbers: this doc §2 (2026-07-16, `committed_decider_opening` +
  `interleaved_decider_verify_vs_leaves`).
