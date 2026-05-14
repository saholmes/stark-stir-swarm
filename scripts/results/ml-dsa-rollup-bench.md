# ML-DSA Signature Rollup — Scaling Bench

**Host:** `Apple M4` · **Cores:** `10` · **Blowup:** `4` (smoke) · **Git:** `d928e11`

N inner ML-DSA-44 verify STARKs (each via `prove_v2_real`) aggregated into ONE outer HashRollup STARK via `prove_outer_rollup`. The outer rollup AIR is signature-algorithm-oblivious — it only commits to N×32-byte pi_hashes.

| N | Outer LDT | Inner Σ Prove (ms) | Inner Σ Verify (ms) | Inner Σ Size (KiB) | Outer Prove (ms) | Outer Verify (ms) | Outer Size (KiB) | Outer Size Overhead |
|---:|:---|---:|---:|---:|---:|---:|---:|---:|
| 2 | fri | 6681.3 | 151.20 | 15164.2 | 2.5 | 0.91 | 188.1 | 1.24% |
| 2 | stir | 6710.6 | 157.67 | 15164.2 | 1.0 | 0.43 | 84.9 | 0.56% |
| 4 | fri | 13467.9 | 298.52 | 30276.1 | 4.7 | 1.12 | 238.0 | 0.79% |
| 4 | stir | 13519.1 | 298.39 | 30276.1 | 1.9 | 0.44 | 85.2 | 0.28% |
| 8 | fri | 27236.8 | 601.62 | 60467.3 | 7.7 | 1.27 | 264.2 | 0.44% |
| 8 | stir | 27349.2 | 613.90 | 60467.3 | 3.2 | 0.46 | 96.9 | 0.16% |

## Scaling notes

- **Inner cost is linear in N** — every additional signature adds one full `prove_v2_real` invocation (~3.3 s/sig at L1 smoke, M4).
- **Outer cost is polylog(N)** — the HashRollup AIR's trace length is `next_pow2(N · 4)` (4 Goldilocks limbs per 32-byte pi_hash), so trace doubles only when N crosses a power of 4.
- **Outer overhead → 0** as N grows (STIR: 0.56% at N=2 → 0.16% at N=8). The outer FRI proof is a fixed-ish polylog cost; the inner total grows linearly.
- **STIR vs FRI outer at N=8**: STIR 96.9 KiB vs FRI 264.2 KiB (2.7× smaller) and 0.46 ms vs 1.27 ms verify (2.8× faster).
- **Per-sig is constant** — every cell shows inner Σ prove ≈ N × 3.4 s and inner Σ size ≈ N × 7.5 MiB. Per-sig STARK soundness (FIPS-202 verifier path) is the dominant cost; the rollup is essentially free.

## Reproduce

```bash
# Single point:
ROLLUP_N=4 ROLLUP_BLOWUP=4 ROLLUP_LDT=stir \
  cargo run --release -p swarm-dns --example ml_dsa_rollup_demo

# Full sweep:
BENCH_NS="2 4 8" ./scripts/bench-ml-dsa-rollup.sh
```
