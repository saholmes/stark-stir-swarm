# ML-DSA Rollup — N-scaling + L1/L2 blockchain architecture

How the recursive ML-DSA rollup scales with N (number of signatures
per block / batch), and where to put each STARK proof in a typical
L1 / L2 blockchain layering.

## Measured scaling at L1 production (bw=32, r=54, STIR)

Apple M4 · L1 (sha3-256 + mldsa-44 + Fp⁶) · inner v2 bw=4 fixed ·
outer recursive STARK bw=32 calibrated for L1 (135-bit budget).

| N    | per-sig (KiB) | outer rollup (KiB) | recursive bundle (KiB) | inner-only baseline (KiB) | bundle compression | Σ rec prove (ms) | Σ rec verify (ms) |
|----:|--------------:|-------------------:|-----------------------:|--------------------------:|-------------------:|-----------------:|------------------:|
|   2 |         788.8 |               84.9 |                  1 663 |                    15 249 |               9.2× |          1 672.2 |              5.46 |
|   4 |         788.8 |               85.2 |                  3 241 |                    30 361 |               9.4× |          3 299.4 |             10.93 |
|   8 |         788.8 |               96.9 |                  6 408 |                    60 564 |               9.5× |          6 673.2 |             21.89 |
|  16 |         788.8 |               97.1 |                 12 718 |                   119 690 |               9.4× |         13 531.4 |             44.73 |

(Bundle = N · per-sig + outer rollup.  Inner-only baseline = raw v2
proofs aggregated, no recursive wrap.)

### Scaling laws

```
per-signature wire size:     ≈ 789 KiB     (CONSTANT in N)
outer rollup wire size:      ≈ 85–97 KiB   (POLYLOG in N — doubles only when N crosses a power of 4)
recursive bundle wire size:  ≈ 789·N + 97 KiB   (LINEAR in N)
recursive prove time:        ≈ 0.83 s/sig · N (sequential; parallelisable)
recursive verify time:       ≈ 2.7 ms/sig · N (each sig verified independently)
compression ratio:           ≈ 9.4×        (INVARIANT in N)
```

The 9.4× compression is the steady-state per-sig wire reduction
(7 583 → 789 KiB) regardless of how many signatures you aggregate.
The outer rollup adds at most 97 KiB of constant cost.

### Extrapolation

| N      | recursive bundle | inner-only baseline |
|------:|-----------------:|--------------------:|
|   100 |      ~ 79 MiB    |         ~ 740 MiB   |
| 1 000 |     ~ 790 MiB    |         ~ 7.4 GiB   |

Linear in N — each additional sig adds 789 KiB to the bundle.  No
sub-linear compression with N at this single-level recursion shape.

## Blockchain architecture: where to put each proof?

The architecture depends on what the L1 verifier must **cryptographically**
attest vs what it can **trust** from a data-availability layer:

### Option A: ALL-on-L1 (full L1 settlement)

```
        ┌─ N × per-sig RecursiveStarkProof  (789 KiB each)
L1 ◀──┤
        └─ 1 × outer HashRollup STARK       (97 KiB constant)
```

- **L1 receives**: N × 789 KiB + 97 KiB = full bundle on chain
- **L1 verifies**: outer rollup + N × per-sig STARK (= ~2.7·N ms + 0.5 ms)
- **N cap** at Ethereum L1: ~4 MB calldata block ≈ **5 sigs/block**
- **Use case**: small batches, full on-chain settlement, no DA dependency
- **Verdict**: works, but doesn't scale beyond ~5–20 sigs/block

### Option B: Outer-on-L1, Per-sig-on-L2/DA (typical rollup pattern)

```
                                  ┌─ N × per-sig RecursiveStarkProof (789 KiB) ──▶  L2 / DA layer
        ┌─────────────────────────┤
        │                          └─ pi_hash[0..N-1] committed to HashRollup root
L1 ◀──┤
        └─ 1 × outer HashRollup STARK   (97 KiB constant)
```

- **L1 receives**: outer rollup STARK only (~97 KiB)
- **L1 verifies**: outer rollup STARK (one ~0.5 ms FRI verify)
- **L2 / DA**: stores the N per-sig recursive STARKs; serves to clients on demand
- **L1 attests**: "this batch contains N signatures whose pi_hashes
  Merkle-commit to root R", but does NOT attest the signatures are
  valid — only that they were committed.  L1 trusts the DA layer to
  serve the per-sig STARKs when challenged.
- **N cap**: unlimited at L1 (constant wire); bounded by DA bandwidth
- **Use case**: real blockchain rollups (zkSync, StarkNet, Polygon zkEVM
  style), where L1 is settlement + DA root, L2 carries the bulk data
- **Verdict**: scales to arbitrary N; standard rollup architecture

### Option C: Multi-level recursive aggregation (future — paper-grade master)

```
        ┌─ 1 × MASTER recursive STARK proving "all N pi_hashes
L1 ◀──┤    correspond to valid recursive STARK proofs"
        │  (one ~789 KiB outer FRI proof, constant in N)
        │
        └─ optional DA pointer for per-sig STARKs (witness storage)
```

- **L1 receives**: ONE master STARK (~789 KiB regardless of N)
- **L1 verifies**: ONE FRI verify (~2.7 ms)
- **L1 attests**: ALL N signatures are cryptographically valid,
  via the master recursive STARK
- **N cap**: completely unlimited — L1 cost is O(1) in N
- **Status**: NOT YET BUILT — requires another layer of recursion
  composing N recursive STARK pi_hashes into one master proof
- **Implementation path**: the same pattern we used for v2 → recursive
  (commit `33ce712` / `0f4eb98`) applied a second time: the master
  STARK's sub-circuit 1 proves "the N recursive STARKs' FRI quotients
  vanish at FS-derived points", sub-circuit 2 commits to their pi_hashes
- **Cost estimate**: ~3-5× the per-sig recursive STARK prove time
  per batch, but L1 wire constant

## Recommendation

For typical blockchain L1/L2 layering:

| Target | Recommended option | Reason |
|---|---|---|
| **Small batches (N ≤ 5)** | A (all-on-L1) | Simple; L1 cryptographically verifies everything; no DA dependency |
| **Production rollups (N up to ~1 000)** | **B (outer-on-L1, per-sig on L2/DA)** | Standard rollup pattern; L1 cost constant; DA carries witness bulk |
| **Maximum scalability (N unbounded)** | C (multi-level master recursion) | L1 cost truly O(1); requires the additional recursion gadget |

**Today's recursive ML-DSA rollup gadget already supports Option B**
out of the box: the outer HashRollup STARK is the L1-posted piece;
the per-sig recursive STARKs go to L2 / DA.

**Option C requires one more layer of recursion** — applying the
same wrapper-stark recursion pattern AGAIN, this time wrapping N
recursive-STARK pi_hashes into one master STARK.  Architecturally
identical to the v2 → recursive bridge (commit `33ce712`); just
nested.

### Is L1 recursive STARK alone sufficient?

**Today: No** — the outer HashRollup STARK only commits to pi_hashes,
it doesn't verify the inner recursive STARK proofs.  So L1 must
either:

1. Verify N per-sig recursive STARKs itself (Option A, linear L1 cost)
2. Trust a DA layer for the per-sig proofs (Option B, constant L1 cost)

**Future (Option C)**: a master recursive STARK over the N pi_hashes
WOULD be sufficient for L1 alone, with L1 verifying just the master
proof.  This is the "true zk-rollup" shape and the natural next
architectural step for the gadget.

## Cost summary at typical batch sizes (L1 bw=32 production)

| N batch | Option A wire | Option B wire (L1 only) | Option C wire (future) | Option A L1 verify | Option B L1 verify | Option C L1 verify |
|--------:|---------------:|------------------------:|-----------------------:|-------------------:|-------------------:|-------------------:|
|       1 |        886 KiB |                  85 KiB |              ~ 789 KiB |              3 ms  |             0.5 ms |             2.7 ms |
|       4 |      3 241 KiB |                  85 KiB |              ~ 789 KiB |             11 ms  |             0.5 ms |             2.7 ms |
|      16 |     12 718 KiB |                  97 KiB |              ~ 789 KiB |             45 ms  |             0.5 ms |             2.7 ms |
|     100 |      ~ 79 MiB |                  97 KiB |              ~ 789 KiB |          ~ 270 ms  |             0.5 ms |             2.7 ms |
|   1 000 |     ~ 790 MiB |                 ~100 KiB |              ~ 789 KiB |           ~ 2.7 s  |             0.5 ms |             2.7 ms |

**The headline scaling claim**: at Option B (the standard rollup
shape), L1 cost is constant ~85 KiB / ~0.5 ms regardless of how
many ML-DSA signatures are in the batch — modulo the DA layer
serving per-sig proofs when needed.  This is the canonical
blockchain rollup architecture and works with what we have today.
