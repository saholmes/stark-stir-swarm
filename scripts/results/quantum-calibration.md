# Quantum-adversary calibration for the recursive STARK

Companion to `r-vs-blowup-calibration.md`.  This doc addresses the
**quantum threat model**: how `r` and the SHA-3 variant should be
chosen for a given (NIST Level, quantum query budget `q`).

## Two-axis quantum threat model

NIST PQ Categories are defined relative to AES-equivalent security
**under Grover speedup**:

| Cat | NIST Level | λ_classical | λ_quantum |
|----:|-----------:|------------:|----------:|
|   1 |         L1 |         128 |        64 |
|   3 |         L3 |         192 |        96 |
|   5 |         L5 |         256 |       128 |

The quantum adversary additionally has a quantum query budget `q`
(oracle queries to the FS hash).  Per NIST PQ, typical budgets:

```
q ≤ 2^40   (small)
q ≤ 2^65   (medium)
q ≤ 2^90   (large)
```

## The math doesn't change r — it changes the hash

Two effects move opposite directions and cancel:

1. **Per-query FRI/STIR soundness halves** under QROM analysis
   (Grover-style speedup on the FS commit phase):

   ```
   bits/query (quantum) = ¼·log₂(blowup)        [vs ½·log₂(blowup) classical]
   ```

2. **NIST quantum target halves** (Cat L = AES-L equivalent;
   AES-L breaks at 2^(L/2) Grover queries):

   ```
   λ_q = λ_classical / 2
   ```

These cancel in the soundness equation:

```
r_classical = 2·λ_c / log₂(blowup)
r_quantum   = 4·λ_q / log₂(blowup) = 4·(λ_c/2)/log₂(blowup) = 2·λ_c / log₂(blowup)
            = r_classical ✓
```

**Conclusion**: the `r` table from `r-vs-blowup-calibration.md`
remains valid in the quantum model.  Same `r ∈ {54, 79, 105}` at
blowup=32 for L1/L3/L5 regardless of threat model.

## What DOES change: the FS hash function

Brassard-Høyer-Tapp gives quantum CR on n-bit hash:

```
ε_collision ≤ q^3 / 2^n        (relaxed BHT bound, conventional)
```

For `ε ≤ 2^-λ_q`:

```
n ≥ 3·log₂(q) + λ_q
```

The user-provided table maps (Level, q) → minimum SHA-3 variant:

| Level | q ≤ 2^40 | q ≤ 2^65 | q ≤ 2^90       |
|------:|---------:|---------:|---------------:|
|    L1 | SHA3-256 | SHA3-384 | SHA3-512       |
|    L3 | SHA3-256 | SHA3-384 | SHA3-512       |
|    L5 | SHA3-384 | SHA3-512 | **NOT POSSIBLE** |

Strict-Brassard bound (`n/3 ≥ λ_q + log₂(q)`) explains the L5 q=2^90
"not possible": n ≥ 654, exceeds SHA3-512's 512-bit output.

## Composing with deep_ali's STARK ≥ sig constraint

deep_ali enforces at compile time that the STARK level (= sha3
variant) is at least the inner signature's NIST level:

| Sig (mldsa-*) | Required STARK floor |
|--------------:|---------------------:|
|      mldsa-44 |             sha3-256 |
|      mldsa-65 |             sha3-384 |
|      mldsa-87 |             sha3-512 |

The **effective SHA-3 variant** is therefore:

```
hash(L, q) = max(classical-STARK-floor(L), quantum-FS-floor(L, q))
```

| Level | q=2^40 | q=2^65 | q=2^90          |
|------:|-------:|-------:|----------------:|
|    L1 | sha3-256 (cls∨q match) | sha3-384 (q wins) | sha3-512 (q wins) |
|    L3 | **sha3-384** (cls wins) | sha3-384 (tied) | sha3-512 |
|    L5 | **sha3-512** (cls wins) | sha3-512 (tied) | NOT POSSIBLE |

The L3 q=2^40 cell: classically L3 demands sha3-384 even though
quantum BHT at q=2^40 only needs sha3-256.  The classical floor wins.

## Measured recursive STARK in quantum mode

`bench-recursive-stark.sh` now supports `BENCH_Q=40|65|90` to auto-
select the SHA-3 variant per `(level, q)`.  Apple M4, blowup=32, STIR
outer LDT, synthetic claim bench:

### L1 (calibrated r=54, λ_q=64 q-bit target)

| q          | hash     | prove (ms) | verify (ms) | proof (KiB) |
|-----------:|---------:|-----------:|------------:|------------:|
| classical  | sha3-256 |        1.6 |        0.30 |        78.9 |
| q ≤ 2^40   | sha3-256 |        1.7 |        0.28 |        78.9 |
| q ≤ 2^65   | sha3-384 |        1.7 |        0.38 |       111.9 |
| q ≤ 2^90   | sha3-512 |        2.0 |        0.57 |       144.9 |

### L3 (calibrated r=79, λ_q=96 q-bit target)

| q          | hash     | prove (ms) | verify (ms) | proof (KiB) |
|-----------:|---------:|-----------:|------------:|------------:|
| classical  | sha3-384 |        2.1 |        0.55 |       162.9 |
| q ≤ 2^40   | sha3-384 |        1.8 |        0.56 |       162.9 |
| q ≤ 2^65   | sha3-384 |        1.8 |        0.54 |       162.9 |
| q ≤ 2^90   | sha3-512 |        2.0 |        1.04 |       211.2 |

### L5 (calibrated r=105, λ_q=128 q-bit target)

| q          | hash     | prove (ms) | verify (ms) | proof (KiB) |
|-----------:|---------:|-----------:|------------:|------------:|
| classical  | sha3-512 |        2.0 |        1.05 |       280.1 |
| q ≤ 2^40   | sha3-512 |        2.1 |        1.03 |       280.1 |
| q ≤ 2^65   | sha3-512 |        2.2 |        1.04 |       280.1 |
| q ≤ 2^90   | —        | — | — | **NOT POSSIBLE** |

### Scaling with q (the cost of bigger quantum budget)

At L1, moving from q=2^40 to q=2^65 (sha3-256 → sha3-384) costs:
- +0.10 ms verify (0.28 → 0.38, +36%)
- +33 KiB proof (79 → 112, +42%)

From q=2^65 to q=2^90 (sha3-384 → sha3-512):
- +0.19 ms verify (0.38 → 0.57, +50%)
- +33 KiB proof (112 → 145, +29%)

These costs come from the FRI Merkle tree leaves growing
(sha3-256→sha3-512 doubles hash output bytes, ~doubling per-leaf
storage), plus FS challenge sampling overhead.

## Use

```bash
# Default (classical, paper-canon hashes):
BENCH_BLOWUP=32 BENCH_LDT_ONLY=stir ./scripts/bench-recursive-stark.sh

# Quantum mode at q ≤ 2^40 (small budget):
BENCH_BLOWUP=32 BENCH_Q=40 BENCH_LDT_ONLY=stir ./scripts/bench-recursive-stark.sh

# Quantum mode at q ≤ 2^65 (medium):
BENCH_BLOWUP=32 BENCH_Q=65 BENCH_LDT_ONLY=stir ./scripts/bench-recursive-stark.sh

# Quantum mode at q ≤ 2^90 (large): L5 skipped (NOT POSSIBLE).
BENCH_BLOWUP=32 BENCH_Q=90 BENCH_LDT_ONLY=stir ./scripts/bench-recursive-stark.sh
```

The harness logs the active hash per level:

```
## Quantum threat model active: q ≤ 2^65 oracle queries
## Hash selection per (level, q):
##   L1 @ q=2^65: sha3-384
##   L3 @ q=2^65: sha3-384
##   L5 @ q=2^65: sha3-512
```

## Caveats

- The relaxed BHT bound (`n ≥ 3·log₂(q) + λ_q`) is conventional;
  the strict-Brassard bound (`n/3 ≥ λ_q + log₂(q)`) is more
  conservative and produces "L5 q=2^90 NOT POSSIBLE".  The bench
  harness uses the user-provided table which matches conventional
  practice for L1/L3 and the strict bound for L5 q=2^90.
- The v2 recursion bridge is now **Ext-GENERIC** as of 2026-05-14:
  it picks up `deep_ali::binding_cells_commit::Ext` (= `SexticExt`
  at sha3-256/sha3-384, `OcticExt` at sha3-512) and the `EXT_DEGREE`
  constant is likewise cfg-selected (6 or 8).  All (level, q) cells
  that are not strictly impossible now run end-to-end through the
  full F2b OOD + recursive STARK pipeline, including L5
  (sha3-512+mldsa-87 / Fp⁸) and L1 quantum mode at q=2^90
  (sha3-512+mldsa-44 over-provisioned / Fp⁸).
- Bigger quantum budgets monotonically grow proof size and verify
  time as the hash output bytes double per upgrade.  This is the
  fundamental cost of stronger quantum-CR.
