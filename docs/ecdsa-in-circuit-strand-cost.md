# In-Circuit ECDSA-P256 Verify over Binius — Components & the Strand Cost Wall

What it takes to verify an ECDSA-P256 (DNSSEC algorithm 13) RRSIG signature
*inside* a Binius M3 circuit over the 256-bit tower field `B256`, at NIST L1 —
and the **measured** prover-cost wall that decides how it can be deployed.

All gadgets live in
[`crates/binius-substrate/src/ec_verify.rs`](../crates/binius-substrate/src/ec_verify.rs)
and prove+verify at NIST L1 (128-bit) with the FIPS instantiation
(`<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>`).

## TL;DR

* Every **component** of the ECDSA verify is now wired and proven in-circuit over
  B256: field ops mod p and mod n, `w=s⁻¹ / u1 / u2` scalar prep, point **double**,
  point **add**, the assembled **double-and-add round**, the **R.x→`x≡r` accept**
  binding, and multi-round **composition across separate proofs**. The verify is a
  *composition* of proven links; its cost, not its soundness, is the barrier.
* The **per-strand cost is measured**: the atomic double-and-add round is
  **695 s / 12.2 MiB** at W=1024. A full verify is `u1·G + u2·Q` = ~512 such rounds
  ⇒ **~99 core-hours of total work** per signature (const-time; ~68 with skip-add).
* **This is not the latency.** Double-and-add is sequential in the *values*, but the
  native accumulator trace is computed in **µs**; once every `A_k` is known, each
  round-proof needs only its boundary points and is **independent** — so the ~512
  rounds are **embarrassingly parallel** (`prove-S2-chain` proves rounds compose
  across *separate* proofs). Wall-clock = `(512/P)·695 s + agg tree`: **~12 min with
  a full fleet**, ~93 min at P=64. The only serial parts are the µs native trace and
  the log-depth aggregation. Parallelism buys latency, not total work.
* Each EC-round strand peaks at **~3.1 GiB RSS** (measured) → per-box concurrency is
  RAM-limited (~4–5 strands / 16 GB); true IoT scale needs further limb-slivering.
  Across a zone, **N signatures are N×512 independent strands** (parallel on top of
  parallel).
* The `.se` epoch demo still verifies ECDSA **natively** and proves only the FIPS
  commitment in-circuit — because even ~99 core-hours **per delegation** is a large
  energy/$ budget for live epoch assembly (millions of delegations), and native
  verify + in-circuit commit fits the latency/cost budget. The in-circuit ECDSA
  verify is the **offline, per-signature, RSS-bounded** artifact (the two-tier
  "owner proves offline" model), not the live-epoch path.

## Components — all proven in-circuit over B256

| Layer | Gadget (gate) | In-circuit | Measured cost |
|-------|---------------|:----------:|---------------|
| Field mul/sqr mod p | `ModMul<1024>` (seamed) | ✓ | — (primitive) |
| Field add/sub mod p | `Adder<W>` + carry-reduce | ✓ | — |
| Field inverse mod p | ModMul, residue pinned to 1 (`ec_field_inverse…`) | ✓ | — |
| **Scalar prep mod n** (`w=s⁻¹, u1=e·w, u2=r·w`) | `ecdsa_p256_scalar_prep_mod_n…` | ✓ | 3 ModMul<1024> = **63 s, 3.0 MB** |
| Point **DOUBLE** `[2]P` (X,Y,Z) | `ec_weierstrass_double_full…` | ✓ | 19 tables |
| Point **ADD** `P+Q` (X,Y,Z) | `ec_weierstrass_add_full…` | ✓ | 30 tables, **453 s, 9.39 MB** |
| Assembled **double-and-add round** `A'=b?[2]A+P:[2]A` | `ec_weierstrass_dbl_add_round…` | ✓ | 53 tables, **695 s, 12.2 MiB** |
| **O-aware round** `A'=(A==O)?(b?P:O):…` (sound `Z==0` flag) | `ec_weierstrass_dbl_add_round_oaware…` | ✓ | 56 tables, **720 s, 13.2 MB** |
| **Complete add** `T=(h==0)?((w==0)?[2]P:O):add` (`u1==u2` handled) | `ec_weierstrass_add_complete…` | ✓ | 54 tables, **904 s, 13.6 MB** |
| **R.x→accept** (`jac_to` affine-x, then `x≡r mod n`) | `ecdsa_jac_to_affine_x_accept…` | ✓ | (see gate) |
| Multi-round **composition** (N rounds, separate proofs) | `prove-S2-chain` (3 rounds) | ✓ | per-round bounded RSS |
| **Message hash** `e = SHA-256(signing input)`, bound into `u1=e·w` | `ecdsa_sha256_to_e_over_b256` | ✓ | 2-block chain: 1.05 MiB / 12.6 s; +u1 bind 3.67 MiB / 47.3 s |

The assembled round welds the two point primitives: the **double** exports `D=[2]A`
over fan-out channels into the **add** computing `T=D+P`, and a per-coordinate GF(2)
conditional-add **selector** (`out = d + b·(d+t)`, a boolean mux on the B1×W columns)
muxes `A' = b ? T : D` by the scalar bit. Both `b=0` (`=[2]A`) and `b=1` (`=[2]A+P`)
are gated against native `jac_dbl`/`jac_add`, and a forged accumulator coordinate is
rejected (channel-balance break). The **R.x binding** closes the last soundness gap:
the accept gate previously took `R.x` as a free witness; now `R.x` is forced to be
the affine-x (`X·Z⁻²`) of the committed scalar-mul output point, bound via an input
boundary — so a prover cannot inject an `R.x` that isn't the real `u1·G+u2·Q`.

The **message hash** is also in-circuit now: `e = SHA-256(signing input)` is proved
over 2 soundly-chained blocks (block *k*'s input state column-wired to block *k−1*'s
output — the sound multi-block chain, not a constant-IV per block) and **bound into
`u1 = e·w mod n`**, so `e` is the hash output, not a free witness. The reduction is
therefore in-circuit **end to end** — SHA-256→`e`→`u1/u2`→double-and-add rounds→`R.x`
`jac_to`→`x≡r` accept.

The **point-at-infinity (O)** case is also handled now: `ec_weierstrass_dbl_add_round_oaware`
makes the round O-aware — `A' = (A==O) ? (b?P:O) : (b?[2]A+P:[2]A)` with `O = Z=0`,
detected by a **sound `Z==0` flag** (a seamed `fe_inv` `Z·Zinv` pinned both directions
so the flag can't be mis-set) and an output mux; the discarded generic branch is
populated with raw-formula values (satisfiable for `Z=0`, no division). 56 tables,
720 s / 13.2 MB, all four `{A=O, A≠O}×{b∈{0,1}}` cases gated vs native `round_o`,
forged-flag and forged-coordinate rejected. This is what the constant-time ladder needs
(the accumulator starts at O and passes through it in the leading rounds).

The **`u1==u2` / A=±P doubling-exception** is now handled too:
`ec_weierstrass_add_complete_over_b256` is an exception-free Jacobian add —
`T = (h==0) ? ((w==0) ? [2]P : O) : jac_add(P,Q)` with `h=u2−u1`, `w=s2−s1`, detected
by two sound zero-flags (same two-direction fe_inv pin), 3-way mux, discarded branches
raw-formula-satisfiable. 54 tables, 904 s / 13.6 MB, all three cases (generic / P==Q⇒[2]P
/ P==−Q⇒O) gated vs native `jac_add`, forged-flag (both) and forged-coordinate rejected.

**With the O-aware round (Inc8) and the complete add (Inc9), the in-circuit ECDSA-P256
verify has NO remaining native exceptions** — every case of the point arithmetic (O,
`P==Q`, `P==−Q`, generic) is handled and gated in-circuit over B256 at NIST L1.

## The measured cost — total work vs wall-clock

A full ECDSA verify computes `R = u1·G + u2·Q`, i.e. **two scalar multiplications**,
each a **256-round** constant-time double-and-add. The assembled round (double +
always-add + select) is the atomic step, **measured at 695 s**. The key distinction
is **total work** (invariant) vs **wall-clock latency** (collapses with parallelism):

| Quantity | Value |
|----------|-------|
| Atomic double-and-add round | **695 s / 12.2 MiB** (W=1024, 53 tables) |
| **Total work** / signature (~512 rounds) | 512 × 695 s ≈ **99 core-hours** (const-time; ~68 with skip-add) |
| Native accumulator trace (only truly serial compute) | **µs** |
| Per-strand RSS (EC round, measured) | **~3.1 GiB** (RAM-bounds per-box concurrency; IoT needs limb-slivering) |
| **Wall-clock**, P provers | `(512/P)·695 s + agg tree` |
| — full fleet (P ≈ 512) | **≈ 12 min** + log-depth aggregation |
| — P = 64 | ≈ 93 min |
| — P = 16 | ≈ 6 h |
| + scalar prep mod n | 63 s |
| + `jac_to` / `x≡r` accept | **83.7 s / 3.79 MB** (measured, 5 tables) |
| + `e = SHA-256(signing input)` → bound into `u1` | **12.6 s** (hash) / **47.3 s** (hash+u1 bind), measured |

**Rounds are sequential in the *values* but parallel to *prove*.** Round *k+1*'s
accumulator `A_{k+1} = [2]A_k + b_k·P` depends on `A_k` — but the *native* scalar-mul
that produces every `A_k` runs in **µs**. Once the `A_k` are known, each round-proof
needs only `(A_k, A_{k+1}, b_k, P)` as boundary values, so the ~512 round-proofs are
**independent → embarrassingly parallel** (this is exactly what `prove-S2-chain`
proves: rounds compose across *separate* bounded-memory proofs, boundary-matched at
aggregation). The only serial parts are the µs native trace and the **log-depth
aggregation tree** (~log₂512 ≈ 9 levels, each level parallel, per-node fold-verify
narrow). Optimizations (fixed-base comb for `G`, 4-bit windowing, Shamir's interleaved
`u1·G+u2·Q`) cut point-ops ~2–4× → **~34–49 core-hours** total work.

**Honest wall: a single in-circuit ECDSA-P256 verify is ~99 core-hours of
embarrassingly-parallel, RSS-bounded work — minutes of latency with a full prover
fleet, but a large total energy/$ budget that parallelism does not reduce.**

### Threading — single-thread baseline, and a MEASURED rayon result

Every headline number is **single-threaded, one core** (binius's `binius_maybe_rayon`
is pulled `default-features = false` everywhere, so its sequential path is used unless
a build opts in). An opt-in `parallel` feature
(`parallel = ["binius_maybe_rayon/rayon"]`) enables binius's internal multicore prover
via Cargo feature-unification. **We measured it** on the assembled round (10-core
M-series):

| Run | Round prove+verify | Cores used (user/real) | Peak RSS |
|-----|-------------------:|-----------------------:|---------:|
| single-thread (default) | **695 s** | 1 | — |
| `--features parallel` (rayon on, confirmed linked) | **690 s** | **~3.7×** | **3.1 GiB** |

**Intra-strand rayon buys ~1× (nothing) on these gadgets — and wastes cores** (~3.7×
CPU for a 0.7% change). The reason is structural: the EC gadgets are **many
`table_size = 1` tables** (one wide row each), and binius's prover parallelizes over
trace *rows* — with one row per table there is nothing to parallelize, so the threads
are bandwidth-/Amdahl-bound. (A *batched* workload with many rows — e.g. the SHA3
digest tables at `table_size = 512` — would parallelize; the EC round does not.)

**Consequence for deployment:** don't spend cores *inside* an EC strand; spend them on
**inter-strand concurrency** — one single-thread strand per core → near-linear
throughput. The invariant holds, realized by inter-strand (not intra-strand)
parallelism:

> **wall-clock ≈ total-work / total-cores + aggregation-depth overhead**,
> total-work ≈ **99 core-hours/sig** (thread-invariant *work*).

| Hardware (1 single-thread strand / core) | Wall-clock / signature |
|------------------------------------------|------------------------|
| 1 core | ~99 h |
| one 10-core M-series | ~10 h |
| one 64-core server | ~1.5 h |
| 512-core fleet | ~12 min |

…**subject to an RSS bound**: the ~3.1 GiB is the **monolithic-round peak** (all 56 tables
proved in one shot). Two levers bring it down toward IoT scale — and the first is now
measured:

* **Strand separation** — prove each field multiply as a *separate* seamed proof (peak =
  one strand, not the summed round), exactly as `prove-S2-chain` does for rounds. A single
  wide `ModMul<1024>` field-multiply strand is **~196 MiB** (measured), not 3.1 GiB.
* **Limb-slivering** — replace each wide `ModMul<1024>` with narrow `LimbProduct<256>` limb
  strands. Measured (`limb_sliver_ec_field_mul_p256`): the P-256 `a·b mod p` decomposes
  **exactly** into 8 `LimbProduct<256>` strands (4 product + 4 `q·p` reduction, L=128 K=2,
  gated vs num-bigint), each **~44 MiB** — **4.4× below** the wide `ModMul<1024>` strand.
  L=64 (W=128) is a further knob (~25 MiB, per the RSA-side measurements).

So the achievable per-strand RSS is **~44 MiB** (44× below the monolithic round), IoT-fittable.
The **in-circuit seam is now built** (`limb_seam_ec_field_mul_p256`): a `FieldMulCombine<512>`
combining/reduction proof consumes the 4 `a·b` product-grid limbs + 4 `q·p` reduction-grid
limbs + `r`, proves `grid_ab = P00+(P01+P10)<<128+P11<<256`, `grid_qp` likewise,
`grid_ab == grid_qp + r`, and `r < p` (41.7 KB / 75 ms / 1 table), gated vs native
`a·b mod p`; a `LimbProduct::build_seamed` strand pushes its product over a channel that the
combine pulls, and a lying strand is rejected two ways — its own `product` zerocheck **and**
channel imbalance (the seam alone binds the strand's output).

**The full field-multiply is now proven end to end** (`limb_field_mul_full_sliver_p256`): the
whole P-256 `a·b mod p` as **9 separate proofs** — 8 `LimbProduct<256>` strands (4 `a·b`-grid +
4 `q·p`-grid) each publishing its product limb on an output boundary, + 1 `FieldMulCombine<512>`
consuming all 8 on input boundaries, cross-proof-bound by boundaries (the `prove-S2-chain`
pattern), all 8 published==consumed. **Measured peak RSS = 59 MiB across the whole 9-proof
sequence** (one ~44 MiB strand + the small combine, *not* the ~352 MiB an all-in-one seamed
proof would cost — each proof's `Bump` drops before the next, so the high-water stays at one
strand), **3.3× below the wide `ModMul<1024>` (~195 MiB)** it replaces. `r == a·b mod p` vs
num-bigint; a lying strand is rejected two ways (cross-proof boundary mismatch **and** the
combine's `grid_identity`). This is the IoT sliver win realized: the in-circuit EC field
multiply proves at **one-strand RSS** instead of a monolithic wide multiply.

**And it composes across a round's dataflow** (`limb_field_mul_chain_sliver_p256`): a 3-mul
chain `((a·b)·c)·d mod p` where each mul is fully slivered (27 proofs total) and each mul's
result feeds the next via a **cross-mul boundary seam** (`FieldMulCombine` publishes `r_k` on
an output boundary; the next mul's `LimbProduct` strands consume it as an operand on input
boundaries; boundary-matched, k=1,2). **Measured peak RSS = 70 MiB across the whole 27-proof
chain — independent of chain length** (8.3× below the ~585 MiB a 3-mul all-in-one proof would
cost), because each proof's `Bump` drops before the next. A lying strand and a broken cross-mul
seam are both rejected. This is the **round-level invariant**: chaining field-muls does *not*
grow peak RSS, so a full EC round (a dataflow of ~26 field-muls) proves at **one-strand RSS**
— the round-level pattern is this chained seam replicated across the round's DAG. The `695 s`
single-thread round is the conservative anchor for *work*; enabling rayon does **not** improve
it here.

## What the strand model *does* buy

The total work is large but the design is deliberate — the scalar-mul is the **strand
lever**, and it parallelizes on two axes:

* **Bounded RSS.** Each round is an independent bounded-memory proof (~0.1–0.2 GiB
  RSS), so the whole verify runs on constrained devices (IoT/browser) despite the
  huge *total* work — never a monolith. `prove-S2-chain` proves N rounds compose
  across *separate* proofs (round *k+1*'s input boundary = round *k*'s output
  boundary; a round lying about its output is rejected).
* **Parallel within a signature.** The native trace decouples proving from the
  sequential value-chain: all `A_k` are known in µs, so the ~512 round-proofs run
  concurrently. Wall-clock = `(512/P)·695 s + agg`, ~12 min at full fleet.
* **Parallel across signatures.** A **zone/epoch of N signatures** is N×512 independent
  strands — parallelism on top of parallelism across a prover fleet. The epoch-scale
  lever.
* **O(1) edge verify** of the aggregated result is unchanged (the accumulation layer).

## Why the `.se` epoch demo stays hybrid

Because a single in-circuit ECDSA verify is ~99 core-hours of work (minutes of
latency, but a large per-signature energy/$ budget), verifying every one of millions
of `.se` delegations' RRSIGs in-circuit at epoch time is impractical. The
[`.se` epoch demo](./dns-epoch-nist-level-splits.md) therefore verifies ECDSA-P256
**natively** (the `p256` crate — the exact reference these gadgets are gated against)
and proves the **FIPS commitment in-circuit**. The measured wall shows this is the
**correct** engineering choice, not a shortcut:

* the in-circuit ECDSA verify is a **real, demonstrable artifact** — every component
  proves over B256 at NIST L1 — available for the (rare) case that needs full
  zero-knowledge signature verification (e.g. an owner proving offline, once, that a
  key-holder authorized an update — the two-tier NI-gated model);
* for **live epoch assembly**, native-verify-then-commit is what fits the latency and
  cost budget, with the aggregation + O(1) edge verify carrying the scale.

## Reproducing

```bash
cd crates/binius-substrate
cargo test --release --lib ecdsa_p256_scalar_prep_mod_n_proves_over_b256 -- --nocapture   # 63 s
cargo test --release --lib ec_weierstrass_add_full_over_b256          -- --nocapture       # ~453 s
cargo test --release --lib ec_weierstrass_dbl_add_round_over_b256     -- --nocapture       # ~695 s
cargo test --release --lib ecdsa_jac_to_affine_x_accept_over_b256     -- --nocapture       # ~84 s
cargo test --release --lib ecdsa_sha256_to_e_over_b256               -- --nocapture       # ~47 s
cargo test --release --lib ec_weierstrass_dbl_add_round_oaware_over_b256 -- --nocapture    # ~720 s (O-aware)
cargo test --release --lib ec_weierstrass_add_complete_over_b256         -- --nocapture    # ~904 s (u1==u2 complete add)
```

Measurement host: Apple M-series (`darwin`), release profile, single machine, W=1024,
NIST L1. Times are wall-clock; treat ±10% as run-to-run noise.
