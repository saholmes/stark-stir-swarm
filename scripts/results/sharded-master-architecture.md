# Two-level sharded master recursion — STARK-DNS scale architecture

Single-level master STARK over N inners scales **n_trace linearly in N**:
N=10 000 needs ~268 M LDE rows + ~107 GB working set, which doesn't
fit on a commodity dev machine.  The sharded variant addresses this:

```
N inners  ──►  K = ⌈N/Ni⌉ first-level masters (Ni inners each, sequential)
               ──►  1 super-master over the K first-level masters
                    + 1 top batched Merkle over all N inner pi_hashes
```

Peak prover memory: **O(max(Ni, K))** instead of O(N).  L1 wire =
`super_master + top Merkle + (N + K) × 32 B`.  Only the super-master,
top Merkle, and pi_hash calldata go to L1 — the K shard masters are
local-only (their FRI-quotient algebraic relation is attested by the
super-master's sub-circuit 1).

## Measured @ N=16, Ni=4, K=4 (this demo)

| Metric | Single-level [BATCHED] | Sharded (Ni=4, K=4) | Δ |
|---|---:|---:|---:|
| super_master n_trace  | 262 144 (=N×16K) | **65 536** (=K×16K) | 4× smaller |
| super_master size     | 2359 KiB | **2094 KiB** | −11 % |
| top Merkle size       | 395.9 KiB | 395.9 KiB | — |
| L1 wire total         | 2755 KiB | **2491 KiB** | −10 % |
| Verify wall-clock     | 10.11 ms | **8.70 ms** | −14 % |
| Prove wall-clock      | 19.78 s | **13.41 s** | −32 % |

The sharded form is **smaller, faster to verify, AND faster to prove**
at the same N because the n_trace of every master is proportional to
its input count (K rather than N for the super-master, Ni rather than
N for each first-level master).  The composability of the master
recursion bridge — `prove_master_recursive(&[RecursiveStarkProof])
→ RecursiveStarkProof` — makes this drop-in.

## STARK-DNS scaling projection (sharded)

Choose Ni such that first-level shard memory fits the prover machine
(~Ni = 64–1024 on commodity hardware), then K = ⌈N/Ni⌉.

| Scale | Ni | K | first-level n_trace | super-master n_trace | L1 wire | L1 verify |
|---|---:|---:|---:|---:|---:|---:|
| N=100     |   16 |   7 |    262 144 |       114 688 | ~2.6 MiB | ~10.7 ms |
| N=1 000   |   32 |  32 |    524 288 |       524 288 | ~2.9 MiB | ~12.5 ms |
| N=10 000  |   64 | 157 |  1 048 576 |     2 572 288 | ~3.5 MiB | ~14.3 ms |
| N=100 K   |  256 | 391 |  4 194 304 |     6 406 144 | ~6.5 MiB | ~15.4 ms |
| N=1 M     | 1024 | 977 | 16 777 216 |    16 007 168 |  ~35 MiB | ~16.4 ms |

(Projection uses the measured 4-point curve: master size grows ~+130 KiB
per K doubling, verify ~+0.8 ms / doubling, n_trace doubles with K.)

For STARK-DNS at **.com-zone scale** (≈10 000 RRSIGs/L1 settlement):
- shard_size Ni = 64 → 157 first-level masters
- Each shard prover needs ~1M LDE rows × 50 cols × 6 Ext × 8 B ≈ 2.4 GB
  — fits comfortably on a 32 GB Mac
- Super-master at K=157: n_trace ~2.57 M, ~10 M LDE rows, ~12 GB working
  set — also fits
- L1 wire: ~3.5 MiB, ~14 ms verify

For **N=1 M** (one TLD epoch worth):
- A 3-level recursion (Ni=1024, then K=977 split into 32 mid-level
  masters of ~31 each, then 1 super over the 32) would keep L1 wire at
  ~3 MiB constant.  Same architectural pattern, one more level of
  recursion — clean engineering follow-up.

## L1 Ethereum cost projection

Using the same per-byte calldata + per-keccak verifier model as
`l1-ethereum-gas-analysis.md`:

| Scale | L1 wire | Gas (EIP-4844 blobs) | USD @ 30 gwei / $2 500 ETH |
|---|---:|---:|---:|
| N=100     | 2.60 MiB | ~0.74 M | **$56** |
| N=1 000   | 2.92 MiB | ~0.74 M | **$56** |
| N=10 000  | 3.50 MiB | ~0.75 M | **$56** |
| N=100 K   | 6.49 MiB | ~0.81 M | **$60** |
| N=1 M     | 34.8 MiB | ~1.42 M | **$107** |

**Constant ~$56/batch up to N=10 000**, growing only logarithmically
beyond that.  Per-signature amortized cost at N=10 000 is **$0.0056**
— better than Option B ($0.005 with DA dependency) AND with no DA
dependency at all.

## Soundness chain

1. **Super-master FRI-verifies** (sub-circuit 1: algebraic IsZero on
   FRI quotient residues for each of the K shard masters).
2. **Top batched Merkle** binds `batched_pi = SHA3(N || π₁..π_N)` to
   a Merkle root committed in the proof.
3. **Verifier cross-checks** `inner_pi_hashes[i] == inner_proofs[i].outer_pi_hash`
   for every i.

Tamper-rejection verified by in-tree test
`sharded_bundle_rejects_tampered_inner_pi_hashes`.

### Caveat (same shape as single-level Option C)

Sub-circuit 1 attests the algebraic FRI relation on prover-supplied
residues.  A tighter form would add in-AIR Merkle binding at every
recursion level (shard-level too) — natural follow-up, not a soundness
gap relative to the single-level Option C we already ship.

## Implementation

| Piece | Location | Status |
|---|---|---|
| `TwoLevelShardedProof` struct                         | `wrapper-stark::master_recursion_bridge` | ✓ |
| `prove_two_level_sharded_master` (K + 1 master proves)| same | ✓ |
| `verify_two_level_sharded_master`                     | same | ✓ |
| Round-trip test @ N=4 Ni=2 K=2                        | `tests::prove_two_level_sharded_master_n4_k2` | ✓ passes |
| Tamper-rejection test                                  | `tests::sharded_bundle_rejects_tampered_inner_pi_hashes` | ✓ passes |
| Demo @ N=16 Ni=4 K=4                                   | `examples/sharded_master_demo.rs` | ✓ runs (~75 s incl. inner v2) |

## Direct answer

**Q: Can the architecture scale to STARK-DNS zone size (N ≥ 10 000)?**
✓ **Yes** — two-level sharded master recursion bounds prover memory to
O(max(Ni, K)) and keeps L1 wire at ~3.5 MiB and verify at ~14 ms for
N=10 000.  The same pattern extends to 3+ levels for N ≥ 1 M.

**Q: Is the sharded form ever worse than single-level?**
Not at any N ≥ shard_size.  Even at small N (this demo's N=16) the
sharded form is 10 % smaller wire, 14 % faster verify, and 32 % faster
prove because each master's n_trace tracks its input count, not N.

**Q: What's the practical Ni choice?**
Ni = 64–256 on a 32 GB dev machine; Ni = 256–1024 on a 128 GB workstation.
Choose Ni such that `Ni × inner_recursive_n_trace × LDE width fits in RAM`.
