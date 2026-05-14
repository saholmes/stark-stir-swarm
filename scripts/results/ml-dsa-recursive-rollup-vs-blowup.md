# ML-DSA Recursive Rollup — wire compression vs blowup (calibrated r)

The recursive rollup demo (`crates/swarm-dns/examples/
ml_dsa_recursive_rollup_demo.rs`) now uses calibrated `r` per blowup
to maintain the paper's 135-bit total budget at NIST L1 across all
blowup factors.

**Host**: Apple M4 · 10 cores · STIR outer LDT · N=4 ML-DSA-44
signatures.  Inner v2 blowup fixed at **4** (bridge currently
requires this for sub-AIR residue extraction).  ROLLUP_BLOWUP
controls the OUTER recursive STARK blowup.

## Measurements

| outer bw |   r | Σ rec prove (ms) | Σ rec verify (ms) | per-sig (KiB) | bundle (KiB) | compression |
|---------:|----:|-----------------:|------------------:|--------------:|-------------:|------------:|
|        4 | 135 |            590.0 |             19.91 |        1499.0 |       6081.2 |   **5.0×** |
|        8 |  90 |            986.9 |             14.82 |        1072.3 |       4374.4 |   **6.9×** |
|       16 |  68 |           1757.4 |             12.28 |         868.0 |       3557.2 |   **8.5×** |
|       32 |  54 |           3344.9 |             11.15 |         788.8 |       3240.5 |   **9.4×** |

All bundles include the same outer HashRollup STARK (~85 KiB STIR).
Inner-only baseline (raw v2 proofs aggregated): **30 361 KiB** at N=4
(~7 569 KiB / sig).

## Tradeoff structure

- **Compression improves with blowup**: 5.0× → 9.4× from bw=4 → bw=32.
  At higher blowup, fewer queries (r=54 vs r=135) outweigh deeper
  Merkle paths.
- **Prove time grows with blowup**: 590 ms → 3 345 ms (5.7×).  Larger
  blowup = bigger LDE = more FFT work.
- **Verify time decreases with blowup**: 19.91 ms → 11.15 ms (1.8×).
  Fewer queries to check.

## Correction note re: prior demo claim

The original `ml_dsa_recursive_rollup_demo` commit (`c90b902`)
reported **12.3× compression** at bw=4 with r=54.  That `r` value
gives only **~54 bits** of FRI soundness at bw=4 (1 bit/query × 54),
well below NIST L1's 128-bit target.  The proof was correspondingly
smaller because of fewer queries.

With the **calibrated** r=135 at bw=4 (matching paper L1 bit-budget),
the honest compression is **5.0×** (1 499 KiB / sig).  The legitimate
peak compression remains at bw=32 (`r=54`, which IS L1-secure at
that blowup): **9.4× / 788.8 KiB per signature**.

| Demo claim | Bw | r | Per-sig | Compression | NIST-L1 secure? |
|---|---:|---:|---:|---:|---:|
| Earlier (commit c90b902) | 4 | 54 | 600 KiB | 12.3× | ❌ (only 54 bits) |
| **Calibrated (this doc)** | **32** | **54** | **789 KiB** | **9.4×** | ✓ (135 bits) |

The bw=32 calibrated number is the **authoritative** rollup
compression for NIST L1 security.

## Production recommendation

For on-chain wire format at NIST L1 security:

```
inner v2 blowup:   4  (paper canon — bridge currently requires)
outer rec blowup:  32 (best per-sig wire size at L1 calibration)
outer rec r:       54 (135-bit total budget, paper-canon)
outer rollup LDT:  STIR
```

Per-signature wire: **789 KiB** recursive STARK proof.
Bundle outer rollup: **~85 KiB** STIR (constant in N).
End-to-end verify: **~11 ms** for N=4 (sub-3 ms per sig).

## Reproduce

```bash
ROLLUP_N=4 ROLLUP_BLOWUP=32 ROLLUP_LDT=stir \
    cargo run --release -p swarm-dns \
        --example ml_dsa_recursive_rollup_demo
```

`ROLLUP_R` env var overrides the auto-calibrated r if needed.
