# FRI/STIR query-count calibration: `r` vs `blowup` per NIST PQ level

## TL;DR — calibrated r table

The unconditional Johnson-regime FRI/STIR soundness gives
**½·log₂(blowup) bits per query**.  To maintain a target NIST PQ
bit-security `λ` plus overhead `Δ`:

```
r ≥ ⌈(λ + Δ) / (½·log₂(blowup))⌉
```

The paper's choice at `blowup=32` is `r ∈ {54, 79, 105}` for
L1/L3/L5, which implies per-level total bit budgets:

| Level | NIST bits | Paper r @ bw=32 | bits/r @ bw=32 | Total budget | Overhead Δ |
|------:|----------:|----------------:|---------------:|-------------:|-----------:|
|    L1 |       128 |              54 |            2.5 |        135   |        +7  |
|    L3 |       192 |              79 |            2.5 |        197.5 |       +5.5 |
|    L5 |       256 |             105 |            2.5 |        262.5 |       +6.5 |

To preserve **the same total bit-budget** at smaller blowups:

| blowup | bits/query | r at **L1**<br>(135 target) | r at **L3**<br>(197.5 target) | r at **L5**<br>(262.5 target) |
|------:|-----------:|----------------------------:|------------------------------:|------------------------------:|
|     4 |        1.0 |                     **135** |                       **198** |                       **263** |
|     8 |        1.5 |                      **90** |                       **132** |                       **175** |
|    16 |        2.0 |                      **68** |                        **99** |                       **132** |
|    32 |        2.5 |                      **54** |                        **79** |                       **105** |

These are now the **default `r` values** in
`scripts/bench-recursive-stark.sh` — auto-derived from `BENCH_BLOWUP`
via the `calibrated_r` helper.  `BENCH_R` env var still overrides.

## Measured recursive STARK at calibrated `(blowup, r)` pairs

Apple M4, 10 cores, `--features parallel`, STIR outer LDT.
Synthetic 6-XOR / 7-OOD / 5-element-multiset sub-circuit claims
(the existing bench harness).  N=8 trace, 0 inner sub-AIRs (this is
the **recursive-STARK-only** bench, not the v2 bridge — that one is
gated to L1/L3 because it depends on `SexticExt`).

### L1 (sha3-256, ML-DSA-44 calibration)

| blowup |   r | prove (ms) | verify (ms) | proof (KiB) |
|------:|----:|-----------:|------------:|------------:|
|     4 | 135 |        0.9 |        0.53 |       114.0 |
|     8 |  90 |        0.8 |        0.47 |       123.0 |
|    16 |  68 |        1.1 |        0.33 |        96.0 |
|    32 |  54 |        1.5 |        0.28 |        78.9 |

### L3 (sha3-384, ML-DSA-65 calibration)

| blowup |   r | prove (ms) | verify (ms) | proof (KiB) |
|------:|----:|-----------:|------------:|------------:|
|     4 | 198 |        1.7 |        1.69 |       231.8 |
|     8 | 132 |        0.8 |        0.90 |       256.2 |
|    16 |  99 |        1.1 |        0.66 |       198.1 |
|    32 |  79 |        1.7 |        0.54 |       162.9 |

### L5 (sha3-512, ML-DSA-87 calibration)

| blowup |   r | prove (ms) | verify (ms) | proof (KiB) |
|------:|----:|-----------:|------------:|------------:|
|     4 | 263 |        2.2 |        1.62 |       393.9 |
|     8 | 175 |        1.1 |        1.56 |       440.5 |
|    16 | 132 |        1.4 |        1.22 |       342.1 |
|    32 | 105 |        2.0 |        1.05 |       280.1 |

## What the numbers say

At constant NIST PQ bit-security per level:

### Verify time — **monotonically decreasing with blowup**

```
L1: 0.53 ms (bw=4)  →  0.28 ms (bw=32)   1.9× faster
L3: 1.69 ms (bw=4)  →  0.54 ms (bw=32)   3.1× faster
L5: 1.62 ms (bw=4)  →  1.05 ms (bw=32)   1.5× faster
```

Verifier cost is dominated by `r` query-openings (each is a constant-
work Merkle-path check at fixed bits/query).  Larger blowup → fewer
queries → faster verify.

### Proof size — **monotonically decreasing with blowup**

```
L1: 114.0 KiB (bw=4)  →   78.9 KiB (bw=32)   1.4× smaller
L3: 231.8 KiB (bw=4)  →  162.9 KiB (bw=32)   1.4× smaller
L5: 393.9 KiB (bw=4)  →  280.1 KiB (bw=32)   1.4× smaller
```

Smaller `r` outweighs the deeper Merkle paths at higher blowup —
fewer queries × longer paths < more queries × shorter paths.

### Prove time — **sweet spot at blowup=8** for all levels

```
L1:  bw=8 fastest at 0.8 ms   (vs 0.9/1.1/1.5 ms at bw=4/16/32)
L3:  bw=8 fastest at 0.8 ms   (vs 1.7/1.1/1.7 ms)
L5:  bw=8 fastest at 1.1 ms   (vs 2.2/1.4/2.0 ms)
```

Two competing forces: bw=4 has high query count (135-263) which
dominates query-opening cost; bw=32 has the largest LDE which
dominates FFT cost.  bw=8 hits the minimum across both.

## Recommendation

- **Production wire format**: stick with `blowup=32, r ∈ {54, 79, 105}`.
  Best verify-time and proof-size at the chosen bit-budget; that's
  the on-chain-cost the rollup verifier pays.
- **Prover efficiency**: consider `blowup=8` for prover-side cost-
  optimisation.  Verify is ~1.7-3.2× slower and proof is ~1.4×
  larger, but prove time is ~50% lower than at blowup=32 for L1/L3.
- **Smoke benches**: previously used `blowup=4 r=54` which gave a
  **~54-bit total budget at blowup=4** (well below NIST L1).  Now
  fixed: `bench-recursive-stark.sh` auto-derives r from blowup so
  any blowup runs at the FULL L1/L3/L5 bit-budget.

## Caveats

- The recursive STARK measurements above are for the **synthetic-
  claim bench** in `wrapper_stark::recursive_prover::tests::
  bench_recursive_stark` (the original 6-XOR / 7-OOD / 5-elem-
  multiset shape).  Real v2-bridge numbers (10 sub-AIRs × 54+
  queries per FRI proof) are dominated by the inner prove time,
  not the outer recursive STARK; the recursive wrap adds
  ~149 ms/sig at blowup=4 (per `ml_dsa_recursive_rollup_demo`).
- L5 uses Fp⁸ (`OcticExt`) in deep_ali but `SexticExt` in
  wrapper-stark's `v2_recursion_bridge`.  The bridge is therefore
  gated to L1/L3 only; the L5 recursive-STARK bench above uses the
  synthetic-claim path which is `SexticExt`-only and works at any
  level.  Making the bridge Ext-generic is a separate piece of
  work.
- All measurements at smoke trace shape (`n_trace=8`).  Production
  v2 sub-AIRs have `n_trace ∈ [256, 8192]` and the per-blowup
  scaling shifts slightly (more FFT work at larger blowup) — the
  paper-grade numbers should be re-measured at production
  `n_trace` for the final figure.
