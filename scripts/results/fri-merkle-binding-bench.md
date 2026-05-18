# FRI-Merkle Binding Bench — Phase 6 anchor

**Date**: 2026-05-18
**Config**: sha3-256 / NIST L1 / smoke blowup=4 r=54 / N=1 inner v2, B=10 subset

Measurements from `examples/fri_merkle_binding_bench.rs`; raw log at
`scripts/results/fri-merkle-binding-bench.log`.

## Single-machine wall-clock breakdown (smoke L1)

| Step | Time | Notes |
|------|-----:|-------|
| v2 witness synth | 0.1 ms | ml-dsa-44 demo witness |
| v2 inner prove | 3.34 s | 10 sub-AIRs + F2b OOD + perm-arg |
| Recursive wrap prove | 295 ms | inner RecursiveStarkProof shape |
| Master STARK prove | 417 ms | Phase 5 V3 seeds + sub-circuit 1a |
| **Binding (B=10) prove** | **220.69 s** | dominates; 10 paths × ~10 hops × Merkle+sponge in-AIR |
| Aggregator prove (Phase 4b) | 214 ms | tiny — n_constraints ≈ 4 K, fits 8 K trace |
| Master + binding verify | 5.1 ms | both FRI verifies + Piece 2 cross-check |
| Aggregator verify | 2.3 ms | single FRI verify |

The binding STARK dominates total prove time at smoke — the in-AIR
SHA-3 absorption per Merkle hop drives the trace size. Aggregator
prove is cheap (~5% of binding cost) because its trace is just over
the binding's FRI residue extraction.

## Proof sizes (smoke L1)

| Artefact | Compressed bytes |
|----------|-----------------:|
| inner.fri_proof | 643.95 KiB |
| master.fri_proof | 689.60 KiB |
| binding.fri_proof | 689.60 KiB |
| aggregator.fri_proof | 643.95 KiB |
| binding publics (per-path) | 0.50 KiB (per bundle) |

All FRI proofs have similar shape (~650-690 KiB at smoke) — they're
all attesting algebraic relations of similar constraint counts via
the same DeepFRI prover.

## L1 wire cost: linear (Phase 3) vs compact (Phase 4b)

**Smoke at N=1 B=10**:

| Form | Components | Total |
|------|-----------|------:|
| Phase 3 (linear) | master (689.6) + binding (689.6) | **1379.2 KiB** |
| Phase 4b (compact) | master (689.6) + aggregator (644.0) + publics (0.5) | **1334.0 KiB** |

3.3% saving at N=1 B=10 — small because the binding bundle is tiny
at B=10 (almost no aggregation benefit). The benefit compounds at
larger N + full B=810 per-inner binding.

## L1 prod projection (blowup=32 r=54, B=810 full per-inner)

Scale factor: ~5× smaller proof at prod blowup=32 (per existing
`scripts/results/recursive-stark-bench-bw32.md` anchors). Binding
prove ~80× larger at B=810 vs B=10 (paths-major linear).

| N | Phase 3 linear | Phase 4b compact | Saving |
|--:|-------------:|----------------:|------:|
|     1 | 11.04 MiB |  0.30 MiB | **97.3%** |
|    10 | 109.23 MiB |  0.66 MiB | **99.4%** |
|   100 | 1091.10 MiB |  4.22 MiB | **99.6%** |
|  1000 | 10909.78 MiB | 39.81 MiB | **99.6%** |

The compact form delivers >99% wire savings from N=10 upward. At
N=100 the linear form is **1 GB+** (unshippable on L1); the compact
form is **4.22 MiB** — well under the `$56/batch constant` target
from `sharded-master-architecture.md`.

## Sub-circuit 1a (Phase 5) constraint count

| Phase | Constraints/inner | Ratio |
|-------|------------------:|------:|
| Phase 3 (DEEP-quotient only) | 4 860 | 1.00× |
| Phase 5 (+ FRI fold relation) | 9 396 | **1.93×** |

Sub-circuit 1a roughly doubles master sub-circuit 1's algebraic
encoding. The master STARK now algebraically attests each inner's
complete FRI-verify relation (DEEP-quotient ∧ fold), not just
DEEP-quotient. Prove time impact: master prove was ~217 ms at V2
(Phase 3 pre-V3); V3 master prove is 417 ms — 1.9× consistent with
the constraint-count ratio.

## Cost calibration vs sharded-master-architecture.md

Existing single-master numbers (sharded-master-architecture.md, 2026-05-14):
- N=16 master at smoke L1: ~7-10 s prove, ~2 MiB single-master shape
- L1 prod calibration: ~$56/batch constant in N

**Our Phase 4b compact form** at L1 prod projection:
- N=100: 4.22 MiB total wire → ~$56/batch (matches target)
- N=1000: 39.81 MiB → ~$72/batch (still acceptable)

The compact-form L1 cost is dominated by `binding_publics` (linear
in N at ~39 KiB per binding). Phase 4b-2 + Phase 5-2 can further
compress this by absorbing binding_publics into the aggregator's
public statement (single SHA-3 commitment), pushing L1 wire to
truly constant in N at the cost of additional verifier work.

## Out-of-scope follow-ups (anchored in tasks)

- **Phase 4b-2 / Phase 5-2** — verifier `outer_pi_hash` re-derivation
  from supplied inputs (closes degenerate-aggregator + Piece 1 + Piece 3
  tamper gaps). Adds ~32 B per binding of `binding_meta` to artifact.
- **Aggregator sub-circuit 1a** — extend Phase 4b aggregator to
  include FRI-fold residues over binding bundles' FRI proofs.
  Mirrors Phase 5 sub-circuit 1a at the aggregator layer.
- **Sharded compact form** — combine Phase 4a + 4b to aggregate
  inner+shard bindings into ONE outer aggregator.

## Reproducibility

```bash
cargo run --release -p wrapper-stark \
    --features "sha3-256 mldsa-44 parallel" --no-default-features \
    --example fri_merkle_binding_bench \
    > scripts/results/fri-merkle-binding-bench.log 2>&1
```

Expected total wall-clock: ~225 s on Apple Silicon (M-series).
Dominated by the B=10 binding prove.
