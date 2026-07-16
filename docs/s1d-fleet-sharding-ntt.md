# S1d fleet-sharding: the NTT AIR must go tall-narrow first

**Goal.** Prove the S1d ML-DSA verify across a fleet of processors (cut wall-time) with
**< 500 MiB RSS per shard** (IoT-viable), like `gway_reconstruction` already does for
ECDSA/Ed25519 and the `nonnative` strand chain does at ≈ 44 MiB/strand.

**Finding (blocking).** The S1a NTT AIR is the one component that does **not** shard, and
naive fleet-sharding will not fix it. It is built *wide-single-row* — `table_sizes: vec![1]`,
with every one of the `(n/2)·log₂n` butterflies laid out as **columns** in a single row.
Binius/FRI is optimised for *tall-narrow* B1 traces (many rows × few columns); a 1-row ×
huge-width trace is the pathological case, and RSS/time scale with the trace **area** (≈ width).

## Measured pathology (clean single-process, B256 @ L1, `mldsa_ntt::ntt_prove_scaling`)

| n | butterflies | prove | proof | peak RSS |
|---|-------------|-------|-------|----------|
| 8 | 12 | 5.8 s | 0.66 MB | 64 MiB |
| 16 | 32 | 18.7 s | 1.29 MB | 187 MiB |
| 32 | 80 | 68 s | 2.86 MB | 880 MiB |

≈ 3.2×/doubling (time), ≈ 3.5×/doubling (RSS). At **n = 32 the RSS is already 880 MiB > 500**;
extrapolated to the real **n = 256** transform: ~37 min and multiple GB — per NTT, and the
verify needs ~13 of them (l forward-z, 1 c, k forward-t1, k inverse). Sharding *this* AIR across
a fleet still gives each shard a wide-single-row sub-trace, so each shard stays over budget.
Contrast the low-RSS strands: `nonnative` mod-mul batches use `table_sizes: vec![n_rows]`
(one row per element, ~6 narrow columns) and hold ≈ 44 MiB regardless of batch length.

## The fix: re-architect the NTT AIR row-per-butterfly (tall-narrow)

Lay the transform as a table of **`(n/2)·log₂n` rows**, one per butterfly, each row holding the
fixed ~6 columns of a single Cooley–Tukey/Gentleman–Sande butterfly (the two inputs, the twiddle
ζ, the ζ·v mod-mul with its reduction quotient, and the add/sub outputs — all B1×W, W = 32).
Route coefficients between layers with a **channel** (push each butterfly's two outputs, pull the
next layer's two inputs), exactly the flush/copy-constraint pattern the `nonnative` mod-mul and
`ec_verify` word-routing already use. Result:

- **Tall-narrow trace** ⇒ efficient FRI, RSS ≈ tens of MiB (the ~44 MiB strand regime), well
  under 500 MiB — for the *full* n = 256 transform.
- **Prove-time** drops from area-bound (width × height) to ≈ linear in butterfly count.
- **Shards cleanly**: the butterfly-rows split across fleet processors; a shard proves a
  contiguous block of rows, and the inter-shard coefficient wires become **seams** (OOD / channel
  balance) bound exactly as in `b256_recursion` / `gway_reconstruction`.

## S1d fleet layout (after the tall-narrow NTT lands)

Each strand is an independent low-RSS fleet job, seam-bound into the reconstructed proof
(`gway_reconstruction` model):

1. **NTT strands** — the forward (z, c, t1·2ᵈ) and inverse (w′) transforms, each a tall-narrow
   butterfly table, sharded by row-block across the fleet. Dominant cost; the re-architecture
   above is the enabler.
2. **Combine strands** — `verify_core_combine`: k×256 pointwise `ŵ = Â∘ẑ − ĉ∘t̂1·2ᵈ`
   mod-q, already row-per-coefficient (narrow); shard by coefficient block.
3. **Digit strands** — Decompose → UseHint → w1Encode per coefficient group (proven gadgets,
   already narrow); shard by coefficient block.
4. **Boundary strands** — ‖z‖∞ < γ1−β (prove-5), hint-weight ≤ ω (prove-4c).
5. **Closing-hash strand** — c̃′ = FIPS-202(μ ‖ w1Encode) == c̃ (prove-10; multi-block Keccak
   is its own scale-up — the callable `prove_verify_sha3_b256` is single-block today).

Seam binding across strands is the existing OOD/channel model; reconstruction + verify follow
`gway_reconstruction` (streaming, one strand resident at a time ⇒ peak RSS ≈ one strand).

## Build order

1. **Row-per-butterfly NTT AIR** — ✅ **DONE + MEASURED** (`mldsa_ntt::ButterflyBatch` /
   `ModMulVar` / `forward_butterfly_trace` / `validate_butterflies` / `prove_butterflies`).
   Validates over B256 and == `ntt_ref` for n = 8..256; a corrupted ζ·v output is rejected.
   `butterfly_batch_prove_scaling` vs the wide-row `ntt_prove_scaling`:

   | n | rows | tall-narrow prove / RSS | wide-row prove / RSS |
   |---|------|-------------------------|----------------------|
   | 8 | 16 | 3.4 s / **24 MiB** | 5.8 s / 64 MiB |
   | 16 | 32 | 4.6 s / **27 MiB** | 18.7 s / 187 MiB |
   | 32 | 128 | 7.5 s / **30 MiB** | 68 s / **880 MiB** |
   | 64 | 256 | 9.2 s / **34 MiB** | — |
   | 128 | 512 | 11.7 s / **45 MiB** | — |
   | **256** | **1024** | **15.6 s / 63 MiB** | ~37 min / multi-GB (extrapolated) |

   The full 256-pt NTT proves in **15.6 s at 63 MiB** — IoT-viable with a 7× margin under 500 MiB,
   and ~linear in butterfly count (vs the wide-row's area-bound blow-up). This unblocks S1d
   fleet-sharding. **Still to add here:** in-circuit inter-layer routing (o_add/o_sub of a
   butterfly feeding the next layer's inputs) via a channel/seam — today the batch proves the
   per-butterfly *arithmetic* tall-narrow; the CT connectivity is followed by the witness trace
   (native) and must become a channel copy-constraint for full connectivity soundness.
2. **Inter-layer channel routing** + **row-block sharding** of the butterfly batch with seam
   binding (mirror `gway_reconstruction`); measure per-shard RSS < 500 MiB and fleet wall-time.
3. Wire the combine/digit/boundary/hash strands into the same fleet + reconstruct; measure the
   full sharded S1d ML-DSA verify (fleet latency + per-shard RSS).

## Gotchas (measured this session)

- Heavy NTT proves are dangerous on one host: run **one at a time**, `pkill -9` + verify with
  `pgrep` between runs (stale runs oversubscribe rayon pools across all cores and thrash RAM).
- macOS has no `timeout`; the full 256-pt *wide-row* prove is minutes-to-tens-of-GB — do **not**
  run it. The `ntt_prove_scaling` sweep stops at n = 32 for this reason.
- `mldsa_ntt::validate` (no FRI) exists precisely because the wide-row 256-pt FRI proof is
  impractical — a tall-narrow rebuild is what makes the real FRI prove tractable.
