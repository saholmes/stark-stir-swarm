# Recursive ML-DSA Rollup — Full Quantum Matrix (measured, all NIST levels)

End-to-end rollup demo (`crates/swarm-dns/examples/
ml_dsa_recursive_rollup_demo.rs`) measured at every valid
`(NIST Level × quantum query budget q)` cell, with the active
extension field `Fp^x` annotated.  Both swarm-dns/prover.rs
(HASH_BYTES-generic, commit `145365e`) and wrapper-stark/
v2_recursion_bridge (Ext-generic, commit `33ce712`) compile and
run at every cell.

**Host**: Apple M4 · 10 cores · STIR outer LDT · N=2 ML-DSA
signatures · inner v2 blowup=4 · outer recursive blowup=4 (smoke).

## Hash variant + Fp^x per (Level, q)

| Level | q ≤ 2^40       | q ≤ 2^65       | q ≤ 2^90        |
|------:|---------------:|---------------:|----------------:|
|    L1 | sha3-256 / Fp⁶ | sha3-384 / Fp⁶ | sha3-512 / Fp⁸  |
|    L3 | sha3-384 / Fp⁶ | sha3-384 / Fp⁶ | sha3-512 / Fp⁸  |
|    L5 | sha3-512 / Fp⁸ | sha3-512 / Fp⁸ | NOT POSSIBLE    |

- **Fp⁶** = `SexticExt` = `QuadExt<GoldilocksSexticConfig>` — selected by sha3-256 and sha3-384 builds.
- **Fp⁸** = `OcticExt` = `QuadExt<GoldilocksOcticConfig>` — selected by sha3-512 builds.

## Full measurements (N=2, bw=4 smoke, calibrated r)

| Level | q          | sha3      | Fp^x  |   r | Inner v2 (KiB/sig) | Per-sig rec (KiB) | Compression |
|------:|-----------:|----------:|-------|----:|-------------------:|------------------:|------------:|
| **L1** | classical (q=2^40) | sha3-256 | **Fp⁶** | 135 |              7 582 |             1 499 |        5.1× |
| **L1** | q=2^65     | sha3-384  | **Fp⁶** | 135 |             11 696 |             2 150 |        5.4× |
| **L1** | q=2^90     | sha3-512  | **Fp⁸** | 135 |             16 579 |             2 692 |        6.2× |
| **L3** | q ≤ 2^65   | sha3-384  | **Fp⁶** | 198 |             12 598 |             3 153 |        4.0× |
| **L3** | q=2^90     | sha3-512  | **Fp⁸** | 198 |             18 457 |             4 220 |        4.4× |
| **L5** | q ≤ 2^65   | sha3-512  | **Fp⁸** | 263 |             20 236 |             5 605 |        3.6× |
| **L5** | q=2^90     | —         | —      |   — |                  — |                 — | NOT POSSIBLE |

(L3 q=2^40 entry uses sha3-384 because the classical STARK ≥ sig
constraint requires sha3-N ≥ mldsa-level; same hash as L3 q=2^65 so
the row is shared.  Likewise L5 q=2^40 shares the sha3-512 row with
L5 q=2^65.)

## Prove times (N=2 = full bundle, ms)

| Level | q       | inner Σ (ms) | rec Σ prove (ms) | rec Σ verify (ms) |
|------:|--------:|-------------:|-----------------:|------------------:|
|    L1 | classical |     ~ 6 800 |              285 |               2.0 |
|    L1 | q=2^65  |       ~ 7 200 |              564 |               3.3 |
|    L1 | q=2^90  |       ~ 8 500 |              693 |               4.6 |
|    L3 | q ≤ 2^65 |       ~ 8 400 |              584 |               3.3 |
|    L3 | q=2^90  |       ~10 000 |             1177 |               5.0 |
|    L5 | q ≤ 2^65 |       ~15 900 |             1305 |               5.0 |
|    L5 | q=2^90  |             —  |                — |                 — |

## Bundle sizes (N=2 = bundle on-wire, KiB)

| Level | q       | inner-only bundle | recursive bundle | bundle compression |
|------:|--------:|------------------:|-----------------:|-------------------:|
|    L1 | classical |           15 249 |            3 083 |               4.9× |
|    L1 | q=2^65  |             23 516 |            4 424 |               5.3× |
|    L1 | q=2^90  |             33 322 |            5 549 |               6.0× |
|    L3 | q ≤ 2^65 |             25 319 |            6 429 |               3.9× |
|    L3 | q=2^90  |             37 077 |            8 605 |               4.3× |
|    L5 | q ≤ 2^65 |             40 635 |           11 374 |               3.6× |
|    L5 | q=2^90  |                  — |                — | NOT POSSIBLE |

(Outer HashRollup STARK adds ~85 KiB STIR commitment in all cells.)

## Observations

1. **Compression IMPROVES with quantum-q at fixed level** for L1 and L3:
   - L1: 5.1× → 5.4× → 6.2× as q grows from 2^40 → 2^65 → 2^90
   - L3: 4.0× → 4.4× as q grows from ≤2^65 → 2^90
   - Counter-intuitive but real: the inner v2 grows faster than the
     recursive STARK because the inner proof shape includes many
     more FRI Merkle paths than the outer (sub-AIR × queries layers).

2. **Compression DECREASES with NIST level**:
   - L1: 5–6× · L3: 4× · L5: 3.6×
   - Higher levels need more queries (r=135 → 198 → 263), so the
     recursive STARK proof itself grows faster than at L1.

3. **Fp⁸ (sha3-512) cells** are at:
   - L1 q=2^90, L3 q=2^90, L5 q≤2^65
   - These pay ~33% more per-sig vs the matching Fp⁶ cell at the
     same NIST level (e.g., L3 Fp⁶ q≤2^65 = 3 153 KiB → L3 Fp⁸ q=2^90
     = 4 220 KiB, +33%).

4. **L5 q=2^90 is mathematically impossible** under the strict-
   Brassard bound (no SHA3 variant satisfies `n/3 ≥ λ_q + log₂(q)
   = 128 + 90 = 218`; would need `n ≥ 654`, exceeding SHA3-512's
   512-bit output).

## Coverage statement

| Status | Cells |
|---|---|
| ✓ Measured end-to-end | 6 unique (Level, hash) cells covering all 8 valid (Level, q) cells |
| ✓ Builds + runs | All combinations the deep_ali workspace allows |
| ✗ Mathematically impossible | L5 at q=2^90 (1 cell) |

## Build feature recipes

```bash
# L1 q=2^40 (classical) — Fp⁶
cargo run --release -p swarm-dns --example ml_dsa_recursive_rollup_demo \
    --features "sha3-256 mldsa-44 parallel" --no-default-features

# L1 q=2^65 — Fp⁶ (over-provisioned sha3-384 STARK at L1 sig)
cargo run ... --features "sha3-384 mldsa-44 parallel" ...

# L1 q=2^90 — Fp⁸ (sha3-512 STARK at L1 sig)
cargo run ... --features "sha3-512 mldsa-44 parallel" ...

# L3 q ≤ 2^65 — Fp⁶
cargo run ... --features "sha3-384 mldsa-65 parallel" ...

# L3 q=2^90 — Fp⁸
cargo run ... --features "sha3-512 mldsa-65 parallel" ...

# L5 q ≤ 2^65 — Fp⁸
cargo run ... --features "sha3-512 mldsa-87 parallel" ...

# L5 q=2^90 — NOT POSSIBLE
```

Each build is one `cargo run` invocation; the demo auto-detects the
NIST level and calibrated r from the active feature flags.

## Production extrapolation to bw=32

At bw=32 (calibrated r ∈ {54, 79, 105}), per-sig is roughly halved
across all cells per the bw=4 → bw=32 trend in
`ml-dsa-recursive-rollup-vs-blowup.md` (~9.4× compression at L1
classical bw=32 vs 5.1× at bw=4).  Approximate bw=32 numbers:

| Level | q       | sha3      | Fp^x  | per-sig bw=32 (est.) | bundle N=4 bw=32 (est.) |
|------:|--------:|----------:|------:|---------------------:|------------------------:|
|    L1 | classical | sha3-256 | Fp⁶ |              789 KiB |                 3.24 MB |
|    L1 | q=2^65  | sha3-384  | Fp⁶ |          ~1 131 KiB |               ~4.61 MB |
|    L1 | q=2^90  | sha3-512  | Fp⁸ |          ~1 417 KiB |               ~5.74 MB |
|    L3 | q ≤ 2^65 | sha3-384 | Fp⁶ |          ~1 660 KiB |               ~6.71 MB |
|    L3 | q=2^90  | sha3-512  | Fp⁸ |          ~2 220 KiB |               ~8.94 MB |
|    L5 | q ≤ 2^65 | sha3-512 | Fp⁸ |          ~2 950 KiB |              ~11.85 MB |
