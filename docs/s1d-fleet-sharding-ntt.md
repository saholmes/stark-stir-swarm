# S1d fleet-sharding: the NTT AIR must go tall-narrow first

> **STATUS: complete end-to-end on a genuine signature.** `fips204_fleet_e2e` drives a real
> ML-DSA-44 signature through all five fleet strands (NTT / combine / digit / z-norm / closing-hash)
> on its real intermediates, folds the outputs into the epoch, and the resolver verifies once.
> **Measured: peak per-shard RSS 53 MiB (< 500 MiB, IoT-viable), parallel fleet wall ~14.7 s
> (combine-bound; shard finer to cut), aggregate 0.4 ms, RESOLVER verify_epoch 0.17 ms +
> verify_record 1.0 µs (sub-ms).** The excessive single-machine prove time is now a fleet of
> small, low-RSS, parallel proofs with a sub-ms resolver verify.



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
2. **Combine strands** — ✅ **DONE + MEASURED** (`CombineBatch` / `run_combine_shard`): the
   NTT-domain `ŵ = Σ_j a_j·z_j − c·td` (Â∘ẑ − ĉ∘t̂1·2ᵈ), row-per-coefficient tall-narrow, every
   input PULLED from `flow` at its position (z_j from the forward-NTT strand's output seam), ŵ
   PUSHED downstream — so it wires into the fleet on the same seam the NTT feeds. Sharded standalone
   proofs (`combine_strand_sharded_across_fleet`: honest validates, tampered coefficient REJECTED).
   Per-shard prove (256 coeffs split G ways, `combine_shard_prove_scaling`): G=4 64c/28.1s/63 MiB;
   G=8 32c/20.5s/71 MiB; G=16 16c/14.7s/73 MiB; G=32 8c/9.4s/**74 MiB** — under 500 MiB, joins the
   fleet. (Slower than the butterfly: 5 var×var mults/row vs 1; RSS stays low, wall-time is per-shard.)
3. **Digit strands** — ✅ **DONE + MEASURED** (`DigitBatch` / `run_digit_shard`): row-per-coefficient
   `w1 = UseHint(h, Decompose(w′))` — the two load-bearing identities `r+γ2 = r1·α+v0+s·q`
   (r1<m, v0∈[1,α]) and `w1+m+h = r1+2·hs+qp·m` (w1<m, qp∈{0,1,2}) in one row (no field mults, just
   shift-sums by constants + carries). w′ PULLED from `flow` (InvNTT output seam), h pulled, w1
   PUSHED downstream (→ w1Encode). Sharded standalone proofs (`digit_strand_sharded_across_fleet`:
   native identities gated, honest validates, flipped hint REJECTED). Per-shard prove (256 coeffs
   split G ways): G=4 64c/2.0s/16 MiB; G=32 8c/0.8s/**19 MiB** — the LIGHTEST strand (no var×var
   mults), well under 500 MiB.
4. **Boundary strands** — ✅ **z-norm DONE + MEASURED** (`BoundaryBatch` / `run_boundary_shard`):
   ‖z‖∞ < γ1−β (prove-5) as a row-per-coefficient check — each row pulls `u = z+γ1` from `flow` and
   asserts `β < u < 2γ1−β` via two carries (upper final-carry 0, lower final-carry 1). A "consumer"
   strand (pulls z, checks, pushes nothing). Sharded standalone proofs
   (`boundary_strand_sharded_across_fleet`: honest validates, out-of-range REJECTED). Per-shard
   prove (256 coeffs split G ways): G=4 64c/229ms/12 MiB; G=32 8c/122ms/**14 MiB** — the LIGHTEST
   strand (2 carries/row). hint-weight ≤ ω (prove-4c) is a single k-count check (already proven,
   not per-coefficient ⇒ one small table, not sharded).
5. **Closing-hash strand** — ✅ **DONE + MEASURED** (`run_closing_hash_shard`): the terminal
   ACCEPT binding c̃′ = SHA3-256(μ ‖ w1Encode(w1′)) == c̃ (prove-10). Unlike the per-coefficient
   strands this is ONE hash (the width driver); it consumes the digit strand's w1Encode output and
   μ, proves the digest over B256, and binds it to the public c̃ — so a wrong w1′ (from any tampered
   upstream shard) changes w1Encode ⇒ different digest ⇒ REJECT (`closing_hash_strand_in_fleet`:
   binds on the genuine w1Encode, a flipped w1′ breaks it). 245 910 B / **19 MiB** at the
   single-Keccak-block anchor (μ ‖ first w1Encode group; the callable b256 SHA3 gadget is
   single-block — multi-block is the same gadget scaled). Original note: prove-10; multi-block Keccak
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
2. **Inter-layer channel routing** — ◐ **seam primitive DONE** (`ButterflyBatch::build_seamed`):
   a butterfly PULLs its input u from a channel and PUSHes o_add / o_sub to channels (a
   coefficient is one B64 lane), so a consumer's input is bound to a producer's output by channel
   balance — a wrong pulled value unbalances the channel ⇒ verify REJECTS
   (`butterfly_seam_routes_and_tamper_rejected`, the exact `nonnative::ModMul` mid-channel seam
   applied to butterfly coefficients). This is the primitive that wires adjacent layers AND binds
   fleet strands. **WHOLE-NETWORK composition DONE** (`validate_ntt_network`): every butterfly of
   a forward n-NTT is wired through per-(slot, version) channels — a source table PUSHes the public
   inputs at version 0, a sink table PULLs the public `ntt_ref` outputs at the final version, and
   channel balance forces the network to carry inputs through the fixed CT topology to the pinned
   outputs. Honest network validates over B256 (n = 4/8/16); corrupting ANY butterfly's twiddle
   unbalances the output channels ⇒ REJECT (`ntt_network_composed_and_tamper_rejected`). This is
   the SOUND, GENERAL composition. **BATCHED (deployment) composition DONE**
   (`validate_ntt_network_batched` / `ButterflyBatch::build_seamed_positional`): each stage's n/2
   butterflies are now ONE tall-narrow positional table (n/2 rows), all routed through a single
   channel whose key is `(position, value)` with `position = version·n + slot`; a source pushes
   the public inputs at version 0, a sink pulls the public `ntt_ref` outputs at version log₂n.
   Honest validates over B256 (n = 4/8/16); a corrupted butterfly mismatches the position the next
   stage pulls ⇒ channel UNBALANCE ⇒ REJECT (`ntt_network_batched_composed_and_tamper_rejected`).
   This keeps the tall-narrow prove regime (n/2 rows per stage — the 15.6 s / 63 MiB curve) with
   single-channel positional routing. **Schedule PINNING DONE** — each stage table PULLs its
   `[pos_u, pos_v, pos_a, pos_s, ζ]` tuple from a per-stage `sched` channel, and the verifier's
   Statement PUSHes the stage's n/2 public schedule tuples as **boundary flushes**
   (`OurB256::from(B64::new(·))`). Channel balance forces every row's committed positions AND
   twiddle to be a genuine public-schedule entry, each used exactly once (row order irrelevant —
   positions pin the routing, ζ is bound to its slots). `ntt_network_batched_composed_and_tamper_rejected`
   now rejects BOTH a corrupted twiddle AND a corrupted position (boundary honest ⇒ the `sched`
   channel is the load-bearing rejecter). This sidesteps M3's `LookupProducer` (B128-only) by using
   the public boundary-flush mechanism. The positional routed network is now fully sound.
3. **Row-block fleet sharding** — ✅ **DONE + MEASURED** (`run_stage_shard` / `stage_shards`). A
   stage's n/2 butterflies split into G independent STANDALONE proofs; each shard's I/O and
   schedule are **seam boundary flushes** (inputs boundary-PUSHed / outputs boundary-PULLed on the
   shard's `net`, `[pos,ζ]` boundary-PUSHed on `sched`), so a shard is a self-contained low-RSS
   proof and the fleet runs G in parallel; reconstruction checks the union of seam tokens is the
   stage's full I/O (positions are global ⇒ tokens balance to the stage). Every honest shard
   validates, a tampered shard is REJECTED, and the shards cover the stage
   (`stage_sharded_across_fleet`). Per-shard FRI-prove of a **256-NTT stage** (128 butterflies)
   split G ways (`stage_shard_prove_scaling`):

   | G | butterflies/shard | prove/shard | proof | peak RSS |
   |---|-------------------|-------------|-------|----------|
   | 2 | 64 | 6.2 s | 561 KB | **25 MiB** |
   | 4 | 32 | 4.7 s | 548 KB | **28 MiB** |
   | 8 | 16 | 3.4 s | 538 KB | **29 MiB** |
   | 16 | 8 | 2.3 s | 453 KB | **30 MiB** |

   Each shard proves independently at **~25–30 MiB** (a ~16× margin under 500 MiB) — IoT-viable —
   and more shards ⇒ faster per-shard prove; run in parallel across the fleet, wall-time is
   per-shard, not the sum. The excessive-single-machine prove time is now a fleet of small,
   low-RSS, parallel proofs.
4a. **Aggregate shards → record/epoch + resolver verify** — ✅ **DONE + MEASURED**
   (`s1d_fleet_to_epoch_e2e`). Fleet-prove the NTT stage shards + a combine shard (validity, low
   RSS, parallel), fold their outputs into the epoch commitment (`epoch_fold`'s interleaved single
   opening), resolver verifies the ONE aggregated proof. Measured (n=32 stage + combine, 4-way):
   FLEET per-shard RSS ≤ 52 MiB / parallel wall ~1152 ms; AGGREGATE (fold) 0.6 ms; **RESOLVER
   verify_epoch 0.16 ms, verify_record 0.9 µs** — sub-millisecond, the network-cost check, NOT the
   seconds-per-shard verify. Fleet-sharding is prover-side; the resolver pays only the decider
   opening (matching the previous signatures' low verify). Validity = the fleet shard proofs
   (verified once by the aggregator = model A, or recursed for trustless — the seconds-per-shard
   verify is that recursion cost).
4b. Wire the digit/boundary/hash strands into the same fleet + reconstruct; measure the
   full sharded S1d ML-DSA verify (fleet latency + per-shard RSS).

## Gotchas (measured this session)

- Heavy NTT proves are dangerous on one host: run **one at a time**, `pkill -9` + verify with
  `pgrep` between runs (stale runs oversubscribe rayon pools across all cores and thrash RAM).
- macOS has no `timeout`; the full 256-pt *wide-row* prove is minutes-to-tens-of-GB — do **not**
  run it. The `ntt_prove_scaling` sweep stops at n = 32 for this reason.
- `mldsa_ntt::validate` (no FRI) exists precisely because the wide-row 256-pt FRI proof is
  impractical — a tall-narrow rebuild is what makes the real FRI prove tractable.
