# Accumulation-based recursion over binius — exploration scope

Branch `feature/accumulation-recursion`, off `feature/tier-b-recursive-master`.
Exploratory / research. The ACNS paper uses **Option 1** (accept seconds-verify +
amortize); this branch chases **Option 3**: ms-verify recursion via accumulation.

## Why (the measured motivation)

Binius verify is **linear in committed width** (`m5_air::verify_vs_width_diagnostic`:
`verify ≈ 20 ms + 1.3 ms × width`), polylog only in rows. Verifying a proof
in-circuit means arithmetizing a FIPS hash (SHA-256 ~2000 cols / Keccak ~575 cols)
to recompute Merkle paths → the recursion circuit is the *widest* possible thing →
`O(width)` verify → **seconds, not the ms the theory promises for a narrow circuit**.

Accumulation attacks this at the root: **don't verify the inner proof in-circuit.**
Fold each new instance into a running accumulator with a *cheap* step (a few field
ops + a small sumcheck), and verify **one** accumulator at the end. The per-step
"circuit" is the fold, not the wide FRI-verifier → narrow → fast.

Target property to preserve from Tier-A: **low-RSS parallel proving** (records proved
separately/sharded). Accumulation should fold those separate instances *without*
re-proving them together, so we keep the sliver RSS win AND get a fast final verify.

## The obstacle: non-homomorphic commitments

Nova/ProtoStar-style IVC folds R1CS/Plonkish instances by taking a **random linear
combination of the commitments** — which requires an *additively homomorphic*
commitment (Pedersen/EC): `Com(a) + λ·Com(b) = Com(a + λ·b)`.

Binius commits with a **Merkle tree over a hash** (SHA-256/Keccak). Hash commitments
are **not homomorphic** — you cannot combine two Merkle roots into the root of the
combined vector. This is the wall. Everything below is about navigating it.

## Candidate approaches (over binius specifically)

### A. Sumcheck / evaluation-claim accumulation (multilinear-native)
Binius's PIOP already reduces "AIR satisfied" to an evaluation claim `M(r) = v` on a
committed multilinear `M`, via a sumcheck. Accumulate the *claims*, not the
commitments:
- Keep a running claim that is a random-linear-combination of each record's zerocheck
  claim. Folding two claims at **different points** `(r_0,v_0),(r_1,v_1)` uses a small
  **point-reduction sumcheck** (log-size) → `O(log)` per fold, not `O(width)`.
- **Where the wall bites:** the final decider still has to *open* the committed `M_i`.
  With separate per-record Merkle commitments those are `N` openings (`O(N)`), each
  cheap (a FRI query set) — but not `O(1)`. Still a big win over in-circuit verify
  (`O(N × width)` → `O(N × log)`).

### B. Split accumulation (ProtoStar / Protogalaxy over hashes)
Separate the **arithmetic** accumulator (folded cheaply, homomorphism-free) from the
**commitment** part (a growing list of deferred openings the *decider* checks natively,
not in-circuit). Non-homomorphic-friendly by construction. Verify is `O(N)` cheap
native openings + one arithmetic check — again no in-circuit FRI-verify.

### C. Batch commitment + sumcheck (the "not really accumulation" baseline)
Commit all `N` records under **one** tree, prove once. Verify = `O(record-AIR width)` +
`polylog(N)` = fast + constant-in-N (verify is row-flat). BUT commits together → loses
the per-record RSS independence at commit time (proving can still shard the trace).
Useful as the **verify-cost lower bound** to measure A/B against.

## What "success" looks like
- **Per-fold cost `O(log)`**, empirically flat as records accumulate (contrast: the
  in-circuit verify is `O(width)` *per record*).
- **Decider verify** small and ~constant (A/B: `O(N)` cheap openings; C: `O(1)`), vs the
  Tier-B in-circuit seconds-per-proof.
- **Low-RSS parallel proving preserved** — folds consume separately-proved instances.
- The FIPS hash appears only at the base commitment + final wrap, never re-arithmetized
  per query. (This is *why* accumulation dodges the FIPS-width tension.)

## First experiments (in order)
1. **Native point-reduction fold** — fold two multilinear evaluation claims
   `(r_0,v_0),(r_1,v_1)` into one via a sumcheck; gate soundness (folded claim ⇒ both);
   measure per-fold cost is `O(log n_vars)`, independent of width. *(the atomic step)*
2. **Fold chain** — accumulate `N` claims; confirm per-fold cost stays flat and the
   accumulator is `O(1)` state. Contrast against `verify_vs_width_diagnostic`.
3. **Decider cost** — model the final opening cost under A (N deferred openings) vs C
   (one batched commitment); measure verify vs N for each.
4. **Only then**: does binius's PIOP expose the seam to slot A/B in? (cf. the STIR trace
   — the sumcheck↔FRI lockstep may resist a clean insertion here too.)

## ★ O(1) collapse — RESOLVED analytically (binius already has the machinery)

Investigating the O(1) decider + instance-folding led to a clean resolution: **binius's PCS
already contains both halves of Nova-style accumulation** — you don't port Nova, you use what's
there.

1. **Instance-fold ≡ binius's batched multi-claim sumcheck.** `front_loaded::BatchVerifier`
   samples one random mixing coefficient per claim and combines N evaluation claims (even at
   different points / n_vars) into ONE sumcheck. That random-linear-combination of claims *is*
   the fold; my custom point-reduction fold was re-deriving it.
2. **O(1) decider ≡ binius's interleaved codes.** `fold_interleaved_chunk` (`log_batch_size`)
   commits a BATCH of codewords and opens the batch at a point in O(1) via the interleave-tensor
   (the tensor product of the first fold challenges). A batch of N record codewords committed
   this way IS a commitment to the block-interleaved multilinear P over `inner + log N` vars,
   openable at ANY point (including the batched-claim point) in one FRI query set — polylog in N.

So **O(1)-verify aggregation over binius is achievable with native machinery**: commit the N
records as ONE interleaved-code batch, prove the aggregation as ONE binius proof whose N record
claims are batched by the sumcheck. Edge verify = one sumcheck + one FRI opening = **O(polylog),
O(1) in N.** No homomorphic commitment, no custom folding scheme.

**Why the detour was still worth it.** The custom narrow fold-verify circuit (accumulation_air,
~48 ms, FIPS-clean) is the primitive you need for STREAMING / bounded-memory IVC — folding one
record at a time in a recursion circuit when you can't hold the batch. For a single aggregation
proof, binius's native batching is simpler and directly O(1). Both live in this branch.

**The residual is RSS, not O(1).** Native batched opening requires the records under ONE
interleaved commitment. Per-record trace/witness generation still shards (low RSS), and each
record's codeword is RS-encoded independently — but the *interleave + Merkle commit* step wants
the codewords together. Whether that commit streams at low RSS (interleave-on-the-fly, à la the
low-mem streaming prover) is the real open question — the same "commit the batch cheaply" problem
the sliver work already attacks. That, not the O(1) verify, is what's left.

## Honesty / risks
- Binius has **no accumulation today**; this is a from-scratch construction over binary
  fields + hash commitments. The non-homomorphism wall is real — A/B give `O(N)`-cheap,
  not `O(1)`, unless a homomorphic-ish commitment is introduced (out of scope: would
  break the hash-based/FIPS posture).
- ROI vs Option 1: accumulation buys a *faster first-contact verify*; Option 1 already
  wins steady-state. Worth it only if sub-second first-contact matters, or as a
  standalone "accumulation over binius" result.
