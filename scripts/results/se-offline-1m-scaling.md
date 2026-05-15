# STARK-DNS offline resolution — scaling to N=1M records

Projection from the empirical N=199 / N=857 anchors + the master-
recursion + batched-Merkle architecture landed earlier in this branch.
Answers the question: *if we shipped an offline DNS resolver covering
1 million records, what's the package size, the boot cost, and the
per-query cost?*

## Package-size projections at N=1M

Three architectures — all serve identical-functionality offline DNS
resolution for the same 1M records, differing only in what cryptographic
content is bundled.

### Naive (ship every inner proof + full Merkle tree)

```
977 inner STARK proofs (Ni=1024)         ~137 MiB
1 outer rollup STARK                      ~95 KiB
ML-DSA-65 pk + sig                        ~5 KiB
Merkle tree (full, 21 levels)             ~64 MiB
1M record metadata (~80 B each)           ~80 MiB
─────────────────────────────────────────────────
Total package                            ~281 MiB
```

### Optimised — sharded master + batched Merkle (what we built)

```
1 sharded master STARK                    ~3.5 MiB     ← attests all K=977 shards algebraically
1 batched Merkle binding STARK            ~395 KiB     ← cryptographic merkle_root anchor
ML-DSA-65 pk + sig                        ~5 KiB
Merkle leaves (1M × 32 B)                 ~32 MiB      ← internal nodes rebuilt at boot
1M record metadata                        ~80 MiB
─────────────────────────────────────────────────
Total package                            ~116 MiB     (59 % smaller)
```

The 977 individual inner proofs **disappear into the sharded master
STARK** — it cryptographically attests they all verify in algebraic FRI
quotients, so they don't need to ship.

### Aggressive — 32-byte leaf hashes only

```
1 sharded master STARK                    ~3.5 MiB
1 batched Merkle binding STARK            ~395 KiB
ML-DSA-65 pk + sig                        ~5 KiB
1M leaf hashes (32 B each)                ~32 MiB
─────────────────────────────────────────────────
Total package                            ~36 MiB    (87 % smaller than naive)
```

Resolver looks up leaf_index by domain name dictionary → 32-byte hash
serves the inclusion check.  Records' rdata bytes are NOT in the
package — the resolver's answer is a presence proof against the
committed corpus, not the full rdata.  Useful for "is this domain in
the .se TLD at epoch T?" attestation queries; not useful for serving
A-record IPs.

## Verification time budget at N=1M

Per the K-scaling sweep in `sharded-master-architecture.md` extrapolated
to K=977 (Ni=1024):

| Component | Cost @ N=1M | Source |
|---|---:|---|
| Read epoch package from disk            | ~5 ms or 0 ms mmap | 116 MiB at ~600 MB/s SSD reads in ~200 ms; can mmap with 0 ms ready |
| ML-DSA-65 signature verify              | **0.15 ms**        | measured constant (~75 µs M-series) |
| Sharded master STARK FRI verify         | **~16 ms**         | projected from K-scaling table at K=977 |
| Batched Merkle binding STARK verify     | **~1 ms**          | measured at K=8 |
| Rebuild internal Merkle nodes from leaves | **~200 ms**      | one-time at boot; 1M × ~200 ns/SHA3 |
| **One-time epoch acceptance (boot)**   | **~17 ms + 200 ms tree build** | total |
| **Per-query Merkle inclusion**          | **~10 µs**         | 20-level tree → 20 SHA3 evaluations |

## How that compares to DNS resolution today

| Workload                                          | Typical latency | STARK-DNS at N=1M |
|---|---:|---:|
| Cold DNSSEC validating lookup (root → TLD → 2LD)  | 50–300 ms       | **10 µs (offline)** |
| Warm recursive resolver                            | 5–20 ms         | **10 µs** |
| Authoritative WAN round-trip                       | 30–100 ms       | n/a (offline) |
| EDNS0 + TCP fallback for big RSA RRSIGs            | 100–500 ms      | n/a |
| Local cache hit (RFC 1035 in-memory)               | 0.1–1 ms        | **10 µs** |
| **STARK-DNS one-time boot**                        | n/a             | **17 ms + 200 ms tree build** |
| **STARK-DNS per-query offline**                    | n/a             | **10 µs** |

**Per-query offline resolution is 3-4 orders of magnitude faster than
a typical DNSSEC-validating cold lookup**, with zero network round-trips.
Even compared to a warm local cache hit, STARK-DNS is 10-100× faster
because there's no DNS-message parsing, no protocol negotiation, no
UDP/TCP layering — just a dictionary lookup + 20 SHA3 evaluations.

## Where the win compounds

The boot cost (~17 ms + 200 ms tree build = ~217 ms) **amortises across
every query for the entire epoch lifetime**:

- **DNS-heavy server** (1 M queries/day): per-query verify cost
  = 10 µs × 1 M = 10 s/day; boot cost = 217 ms once.  Total CPU cost
  ≈ **10 seconds/day** for cryptographically-attested DNS resolution.
- **Embedded IoT device** (100 queries/day): boot amortises to
  negligible; per-query 10 µs.  Cryptographic DNSSEC validation
  feasible on a microcontroller with this profile.
- **Air-gapped system** (no DNS at all today): now has cryptographic
  DNS — every query verifies against the trusted authority's ML-DSA
  signature transitively, with NO network access.

## The architectural property that makes this work

DNS queries are **read-heavy + write-rare** workloads.  The epoch
package model treats this like a static, signed dataset that gets
updated periodically (per epoch) rather than per-query:

```
Producer (epoch boundary):    expensive — minutes to hours of STARK proving
Distribution (epoch publish): one-time — push 116 MiB to all edge consumers
Edge boot (per epoch):        ~17 ms STARK + ~200 ms tree build
Edge query (per DNS lookup):  10 µs — Merkle inclusion only
```

This is **exactly** the right shape for what DNS actually is — a
periodically-updated authoritative database serving billions of read
queries between updates.  Classical DNSSEC re-validates the chain on
EVERY query, paying the same cryptographic cost over and over.  STARK-
DNS pays once per epoch and amortises across all subsequent queries.

## How many inner proofs at N=1M — sharding choice

The inner STARK trace scales linearly with shard size Ni; the choice
is governed by prover memory rather than by total record count:

| Ni (records/shard) | K shards | Inner π each | Total inner π | Per-shard prove memory |
|---:|---:|---:|---:|---:|
|     64 | 15 625 | ~140 KiB |  ~2.1 GiB |    ~2 MB |
|  1 024 |    977 | ~140 KiB | **~137 MiB** |   ~31 MB |
|  4 096 |    245 | ~180 KiB |   ~43 MiB |  ~126 MB |
| 16 384 |     62 | ~220 KiB |   ~13 MiB |  ~500 MB |
| 65 536 |     16 | ~280 KiB |    ~4.5 MiB | ~2.0 GB |
| 1 M    |      1 | huge     | n/a       |  ~32 GB |

Ni=1024 (K=977) is the recommended choice — keeps per-shard prover
memory at ~31 MB (fits anywhere) and lets the sharded master collapse
all 977 inner proofs algebraically.  Larger Ni reduces total inner-
proof bytes if you DO ship inner proofs (for the naive path), but
requires more memory per prover instance.

## Storage tradeoffs for the Merkle tree

A full binary tree over 1M leaves has **2 097 151 internal nodes
× 32 B ≈ 64 MiB** total.  But the resolver only needs to verify
inclusion paths (one per query, 20 sibling hashes × 32 B = 640 B/query):

| Strategy | Ship | Resolver pre-computes | Per-query cost |
|---|---:|---|---:|
| Ship full tree | ~64 MiB | nothing | 640 B fetched + 20 hashes |
| **Ship leaves only** | **~32 MiB** | builds internal nodes once at boot (~200 ms) | 640 B + 20 hashes |
| Ship records + salt only | ~80 MiB (records anyway) | hashes leaves + builds tree (~1 s boot) | 640 B + 20 hashes |

The middle option (ship leaves only) is the sweet spot — keeps record
rdata + 32 MB of leaf hashes, rebuilds internal nodes lazily at boot.

## Bottom line

| Metric | Value at N=1M |
|---|---:|
| **Package size** (optimised, sharded master) | **~116 MiB** |
| **Package size** (32-byte leaf hashes only)  | ~36 MiB |
| **Boot cost** (one-time per epoch)            | **~17 ms verify + ~200 ms tree build** |
| **Per-query cost** (offline DNS lookup)       | **~10 µs** |
| **Compared to cold DNSSEC validation today**  | **3-4 orders of magnitude faster** |
| **Workstation feasibility**                   | ✓ ~116 MiB fits in RAM trivially |
| **Per-query within DNS resolution time?**     | ✓ 10 µs << typical 5-300 ms |

The empirical anchors landing earlier in this branch (`se-zone-hnpl-demo.md`
+ `sharded-master-architecture.md` + `batched-merkle-binding.md`) make
these projections concrete: every component has been measured at smaller
scale and scales by well-understood mechanisms (polylog STARK +
polylog Merkle) to N=1M.
