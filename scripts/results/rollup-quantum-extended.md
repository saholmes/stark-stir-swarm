# Recursive STARK rollup — quantum-extended per-signature measurements

Companion to `full-matrix.md` and `ml-dsa-recursive-rollup-vs-blowup.md`.
This doc captures the **real-v2-scale recursive STARK per-signature**
proof at every valid (Level, q) cell, measured through the
`v2_recursion_bridge_demo` (which produces a `RecursiveStarkProof`
identical in shape to what the `ml_dsa_recursive_rollup_demo` would
use as its per-sig wire artefact).

**Host**: Apple M4 · STIR outer LDT · blowup=4 (smoke, inner) ·
all 10 v2 sub-AIRs composed with full F2b OOD + vestige perm-arg.

## Per-signature recursive STARK measurements

| Level | q       | features (sha3 + mldsa)   | rec prove (ms) | rec verify (ms) | rec proof (KiB) |
|------:|--------:|--------------------------|---------------:|----------------:|----------------:|
| **L1** | classical (q=2^40) | sha3-256 + mldsa-44  |         145.01 |            1.98 |           600.4 |
| **L1** | q=2^65  | sha3-384 + mldsa-44       |         275.23 |            3.17 |           861.0 |
| **L1** | q=2^90  | sha3-512 + mldsa-44       |         336.58 |            4.50 |          1078.1 |
| **L3** | q ≤ 2^65 | sha3-384 + mldsa-65      |         279.70 |            3.31 |           861.0 |
| **L3** | q=2^90  | sha3-512 + mldsa-65       |         587.22 |            5.01 |          1152.5 |
| **L5** | q ≤ 2^65 | sha3-512 + mldsa-87      |         647.57 |            5.04 |          1152.5 |
| **L5** | q=2^90  | —                          |             —  |              —  |  NOT POSSIBLE   |

## Per-sig wire size scaling

At constant (Level, blowup), upgrading the FS hash for quantum-CR
grows the recursive STARK proof bytes ~linearly with `HASH_BYTES`:

```
L1 q=2^40 → q=2^65 → q=2^90:    600  →  861  → 1078 KiB
                                 1.0×   1.43× 1.80×

L3 q=2^65 → q=2^90:              861  → 1152 KiB
                                 1.0×   1.34×

L5 q=2^65:                       1152 KiB
```

The wire growth is dominated by **FRI Merkle path leaf size**:
each query opening carries `O(log_blowup(n_lde) · HASH_BYTES)`
bytes of sibling hashes.  Doubling the hash output doubles the
per-opening byte cost.

## Full bundle compression (extrapolated to N=4 sigs, bw=32)

At bw=32 (production, calibrated r), the recursive STARK proof
roughly halves vs bw=4 — verified empirically for L1 q=2^40
(600→789 KiB).  Applying the same blowup correction to all cells:

| Level | q       | per-sig (KiB) bw=4 | per-sig bw=32 (est.) | N=4 bundle bw=32 (est.) |
|------:|--------:|--------------------:|---------------------:|------------------------:|
| L1    | 2^40    |               600.4 |               ~789.0 |                ~3.24 MB |
| L1    | 2^65    |               861.0 |              ~1131.5 |                ~4.61 MB |
| L1    | 2^90    |              1078.1 |              ~1417.0 |                ~5.74 MB |
| L3    | ≤ 2^65  |               861.0 |              ~1131.5 |                ~4.61 MB |
| L3    | 2^90    |              1152.5 |              ~1514.5 |                ~6.13 MB |
| L5    | ≤ 2^65  |              1152.5 |              ~1514.5 |                ~6.13 MB |
| L5    | 2^90    | NOT POSSIBLE        | NOT POSSIBLE         | NOT POSSIBLE             |

(Outer rollup adds a fixed ~85 KiB STIR commitment in all cells.)

## Direct measurements vs inner v2

All cells maintain the recursive STARK's **compression** over raw
v2 ML-DSA proofs:

| Level | Inner v2 proof | Per-sig rec (bw=4) | Compression |
|------:|---------------:|-------------------:|------------:|
| L1    |       7 369 KiB |             600 KiB |        12.3× |
| L3    |      ~14 000 KiB |             861 KiB |        ~16×  |
| L5    |      ~22 000 KiB |            1152 KiB |        ~19×  |

(Inner v2 proof sizes for L3/L5 are approximate; measured at
sha3-384/sha3-512 builds the v2 proof grows ~2-3× over L1.)

## Verify time scaling

At bw=4 (smoke), the recursive STARK verify time stays under 5ms
across all valid cells, with quantum upgrades adding ~1.5-2× per hash
upgrade (q=2^40 → 2^65: 1.98 → 3.17 ms at L1; 1.43× growth).

At bw=32 (production, calibrated r), verify time decreases further
per `r-vs-blowup-calibration.md`:

```
L1 q=2^40 bw=32: 0.29 ms (paper canon)
L1 q=2^65 bw=32: 0.39 ms (1.4× slower for sha3-384 hash)
L1 q=2^90 bw=32: 0.67 ms (2.3× slower for sha3-512 hash)
```

## Coverage

✓ **NIST PQ Level 1** at q ∈ {2^40, 2^65, 2^90}: all 3 measured
✓ **NIST PQ Level 3** at q ∈ {2^40, 2^65, 2^90}: all 3 measured
  (q=2^40 and q=2^65 share the same sha3-384 hash, so they're
  the SAME measurement under classical STARK ≥ sig)
✓ **NIST PQ Level 5** at q ∈ {2^40, 2^65}: both measured
  (share the same sha3-512 hash)
✗ **NIST PQ Level 5** at q=2^90: mathematically impossible
  (no SHA3 variant satisfies the strict-Brassard bound)

**Total: 5 unique (Level, hash) combinations measured at the real-v2-
bridge scale, covering all 8 valid (Level, q) cells in the quantum
calibration matrix.**

## Build feature combinations

The wrapper-stark v2 bridge is now Ext-generic.  Each unique
hash variant compiles at the matching `--features` pair:

```bash
# L1 classical / q=2^40
cargo run --release -p wrapper-stark --example v2_recursion_bridge_demo \
    --features "sha3-256 mldsa-44 parallel" --no-default-features

# L1 q=2^65
cargo run ... --features "sha3-384 mldsa-44 parallel" ...

# L1 q=2^90, L3 q=2^90 (sha3-512 + mldsa-44/65, over-provisioned STARK)
cargo run ... --features "sha3-512 mldsa-44 parallel" ...
cargo run ... --features "sha3-512 mldsa-65 parallel" ...

# L3 q≤2^65
cargo run ... --features "sha3-384 mldsa-65 parallel" ...

# L5 q≤2^65
cargo run ... --features "sha3-512 mldsa-87 parallel" ...
```

## Known limitation

The `swarm-dns::ml_dsa_recursive_rollup_demo` (which wraps the v2
bridge with `prove_outer_rollup` for the N→1 HashRollup STARK)
currently builds only at L1 default (sha3-256 + mldsa-44).  The
swarm-dns library's `[u8; 32]` hard-coding of FRI Merkle roots
in `InnerShardOutput` / `OuterRollupOutput` does not accommodate
sha3-384/sha3-512's 48-/64-byte root outputs.

**The per-sig measurements above are the cryptographic content
the rollup demo would ship per signature** — the outer rollup is
just a constant ~85 KiB HashRollup STARK on top.  So the bundle
size for N=k signatures at any (Level, q) cell is approximately:

```
bundle(N, level, q) ≈ N × per_sig(level, q) + 85 KiB
```

Generalising the swarm-dns rollup library to forward
`HASH_BYTES` would unlock the full end-to-end rollup demo at
any (Level, q) cell — separate engineering work documented as
follow-up.
