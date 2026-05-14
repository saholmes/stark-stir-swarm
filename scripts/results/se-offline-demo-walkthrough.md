# STARK-DNS — end-to-end offline DNS resolution demonstration

Live walkthrough of the paper §IV pipeline running on **real .se DNSSEC
data**: produce a self-contained epoch package from Tranco-ranked .se
domains, ship it out-of-band, then resolve DNS queries OFFLINE from
the cryptographically-attested corpus.

## The demonstration in one paragraph

500 .se domains drawn from Tranco top-1M.  Captured 276 real DNSSEC
chain links via Hickory-DNS over UDP+TCP in 2 minutes; ran ring/p256
native pre-proof oracle on every RRSIG; STARK-proved the 199 ACCEPT-
verdict records into a HashRollup AIR (135 KiB inner π); outer-rollup-
attested into 85 KiB outer π; ML-DSA-65-signed the Def. 1 binding hash.
**Result: a single 269 KiB epoch package** that a resolver can verify
in **1.48 ms one-time** and then serve DNS queries offline at
**3.8 µs/query** for committed records, **rejecting every record
outside the corpus** including adversarial forgery attempts.

## Phase 1 (Producer) — `se_zone_demo`

```bash
SE_DOMAIN_FILE=scripts/data/se-domains-tranco.txt SE_DOMAIN_LIMIT=500 \
CAPTURE_CONCURRENCY=64 RSA_SIG_LIMIT=0 \
    cargo run --release -p swarm-dns --example se_zone_demo \
    --features "sha3-256 mldsa-44 parallel" --no-default-features
```

| Step | Operation | Result |
|---|---|---:|
| Step 1 | Concurrent Hickory-DNS capture (UDP + TCP fallback) | 276 / 500 zones returned signed records (55 %) |
| | Public anycast resolvers @ concurrency=64 | 126 s wall-clock (steady ~140 dom/s + 4 dom/s long-tail) |
| Step 2a | Native pre-proof oracle (`Verifier::verify_rrsig`) | 199 ACCEPT / **1 REJECT** / 76 SKIP |
| | (REJECT = the §III-D oracle catching a real expired RRSIG) | |
| Step 2b | Per-record STARK (HashRollup AIR S_att, 199 records) | 135.0 KiB π / 65.3 ms prove / 0.56 ms verify |
| Step 2b' | Outer rollup STARK (commits inner pi_hash → epoch root) | 84.9 KiB π / 0.9 ms prove / 0.42 ms verify |
| Step 2c | ML-DSA-65 sign (Def. 1 binding hash) | 3 309 B sig / sub-ms sign |
| **Phase 2** | **Persist self-contained epoch package to disk** | **269.4 KiB** (`target/se-epoch-package.bin`) |

**Algorithms found in this 500-zone sample**: RSASHA1, RSASHA256,
ECDSAP256SHA256, ECDSAP384SHA384, Ed25519 — five distinct algorithms
including one (RSASHA1, RFC 8624-deprecated) still in production.

## Phase 2 (Distribution)

The 269.4 KiB binary is **self-authenticating** — every byte is bound
by SHA3-256 to the ML-DSA-65 signature.  It can be shipped via ANY
channel without requiring authenticity from the channel itself:

- HTTP / HTTPS download
- IPFS content-addressed publish
- BitTorrent / DHT swarm
- Satellite broadcast (one-way, no return channel)
- Physical media (USB stick, optical disc, paper QR codes)
- Airdrop / WiFi-Direct / sneakernet

Tampering at any byte invalidates the ML-DSA signature → resolver
rejects the package before serving any queries.

## Phase 3 (Offline Resolver) — `se_offline_resolver`

```bash
cargo run --release -p swarm-dns --example se_offline_resolver \
    --features "sha3-256 mldsa-44 parallel" --no-default-features
```

### One-time epoch acceptance (NO NETWORK)

```
loaded 269.4 KiB package from disk                       0.2 ms
✓ ML-DSA-65 signature verify                             0.143 ms
✓ Outer STARK FRI verify                                 1.254 ms
─────────────────────────────────────────────────────────────────
✓ One-time epoch acceptance                              1.48 ms  ← paper Tab. II target 0.5-5 ms ✓
```

### Phase 3a — POSITIVE: queries for records IN the corpus

```
domain                   type       alg    idx   depth rdata
.                        DNSKEY    alg=8    idx=  0   d=8  rdata=a1d4219b0cd64b3a…
1177.se (health portal)  DNSKEY    alg=13   idx=  1   d=8  rdata=efa8e82dabbdbf0b…
tre.se (telco)           A         alg=14   idx=  60  d=8  rdata=48fd201947c3695c…
180.se                   DNSKEY    alg=15   idx=  96  d=8  rdata=f5891f72a5362fe7…  ← Ed25519
resilans.se              DNSKEY    alg=5    idx=  140 d=8  rdata=f567611408dfbf2e…  ← RSASHA1
─────────────────────────────────────────────────────────────────
Positive verdict: 5/5 ACCEPT  ·  avg lookup 3.8 µs / query
```

Every record present in the corpus resolves via a real Merkle inclusion
proof that re-derives the committed root.

### Phase 3b — NEGATIVE: queries for records NOT in the corpus

```
evil-attacker.se                  type=A    ✓ REJECT  ← forgery target
phishing-bank.se                  type=A    ✓ REJECT  ← forgery target
malicious.example.se              type=A    ✓ REJECT  ← forgery target
not-in-tranco.se                  type=DNSKEY  ✓ REJECT  ← non-Tranco
github.com                        type=A    ✓ REJECT  ← wrong TLD (.com)
google.com                        type=A    ✓ REJECT  ← wrong TLD (.com)
nonexistent-record-type.iis.se    type=255  ✓ REJECT  ← wrong rtype
─────────────────────────────────────────────────────────────────
Negative verdict: 7/7 REJECT  ·  coverage = committed corpus exactly
```

The resolver's answer space is **exactly** the committed records.
Every domain or record type the producer did NOT capture is correctly
refused.

### Phase 3c — ADVERSARIAL forged-inclusion-proof attack

The adversary holds the public epoch package + sees the committed
Merkle root.  They want to convince a victim that `evil.se A 6.6.6.6`
is in the corpus.  Their best attempt:

1. Synthesise a forged leaf hash for the bogus record:
   `forged_leaf = SHA3("DNS-LEAF-V1" || salt || canonical("evil.se A 6.6.6.6"))`
   `                = 949196eef5b495d02c4a6b6eb149a307…`
2. Reuse a REAL authentication path from leaf-index 0 (the adversary
   can compute it from the public tree levels):
   `path = [sibling_0, sibling_1, …, sibling_7]`  (8 siblings)
3. Publish `(forged_leaf, idx=0, path)` claiming inclusion under the
   committed root.

Resolver's check: `merkle_verify(forged_leaf, 0, path, committed_root)`:

```
forged path reconstructs to:   f75f68a848ebbdb5e145cfc14e9e4cc5…
committed Merkle root:         d4dc596be5816408c90d93405750b557…
                               (different — by SHA3-256 CR)
✓ FORGERY REJECTED
```

**Why this is unforgeable**: the committed Merkle root cryptographically
pins which leaves are in the corpus.  Any change at the leaf level
propagates upward through SHA3-256 hashes; with collision resistance
~λ=128 bits (quantum: ~85 bits per BHT), constructing a forged leaf
that hashes to the same root requires breaking SHA3-256 collision
resistance — infeasible.

### Phase 3d — TAMPER detection

```
Flip 1 byte of authority_sig: tampered.authority_sig[0] ^= 0xFF
✓ correctly rejected ("ML-DSA-65 signature verification FAILED")
```

The Def. 1 binding hash covers every component of the package via the
ML-DSA-65 signature; any mutation to π_inner, π_outer, merkle_root,
records, or the signature itself flips the verifier's verdict to
REJECT.

## Reproduce on your machine

Self-contained reproducer using the ship-on-disk Tranco list and the
persisted N=500 epoch package:

```bash
# Inspect the committed corpus (~270 KiB binary)
ls -la scripts/data/se-epoch-package-n500.bin

# Run the offline resolver against the persisted package
SE_EPOCH_PACKAGE_PATH=scripts/data/se-epoch-package-n500.bin \
    cargo run --release -p swarm-dns --example se_offline_resolver \
    --features "sha3-256 mldsa-44 parallel" --no-default-features

# Or produce a fresh package from a different .se slice
SE_DOMAIN_FILE=scripts/data/se-domains-tranco.txt SE_DOMAIN_LIMIT=500 \
CAPTURE_CONCURRENCY=64 \
    cargo run --release -p swarm-dns --example se_zone_demo \
    --features "sha3-256 mldsa-44 parallel" --no-default-features
```

## Headline numbers (this demo at N=500 captured / 199 committed)

| Metric | Measurement |
|---|---:|
| Phase 1 producer wall-clock (500 zones)            | **126 s** |
| Captured DNSSEC chain links                         | 276 |
| Records committed to STARK                          | **199** (ACCEPT-verdict only) |
| Pre-proof oracle REJECTs (expired/rotated RRSIGs)  | 1 |
| DNSSEC algorithms observed                          | 5 distinct |
| Inner shard STARK π                                 | 135.0 KiB |
| Outer rollup STARK π                                | 84.9 KiB |
| ML-DSA-65 pk + sig                                  | 5.3 KiB |
| **Total epoch package (Phase 2)**                  | **269.4 KiB** |
| Phase 3 load                                        | 0.2 ms |
| Phase 3 one-time verify (ML-DSA + outer STARK)      | **1.48 ms** |
| Phase 3 POSITIVE query avg                          | **3.8 µs / query** |
| Phase 3 NEGATIVE query reject rate                  | 7/7 = 100 % |
| Forged-inclusion-proof attempt                      | REJECTED |
| Signature-tamper attempt                            | REJECTED |

## Security guarantees (paper §V Theorems 1–4)

1. **Record Integrity** (Theorem 1): no quantum adversary can cause an
   edge to accept a DNS record that was not DNSSEC-valid at proof
   generation time — STARK soundness + SHA3 CR + ML-DSA EUF-CMA.
2. **Prover Authentication** (Theorem 2): no adversary produces a
   well-bound epoch package without the authority's ML-DSA secret key.
3. **Non-substitutability** (Theorem 3): the Merkle root R in the
   binding hash cannot be swapped for a different tree's root.
4. **Epoch Freshness** (Theorem 4): no stale epoch package can be
   substituted for a fresh one (monotone seq + binding-hash chain).

This demonstration empirically exercises all four properties on real
.se DNSSEC data: properties 1 + 3 via Phase 3a/b/c (security envelope
holds for 12 queries + 1 forgery attempt); property 2 + the EUF-CMA
side of property 1 via Phase 3d (tamper test); property 4 implicitly
via the binding-hash construction (any seq/prev tamper would break
the ML-DSA signature the same way Phase 3d demonstrates).

## True offline DNS resolution — what this enables

The 269 KiB epoch package + 1.48 ms boot + 3.8 µs/query profile is
operationally what the paper §IV-B (Phase 2 distribution) / §IV-D
(Phase 3 edge) shape was designed for:

- **Air-gapped systems** (military, industrial control, isolated
  satellite ground stations) can authenticate DNS for the committed
  corpus without any network access — even an adversary with full
  on-path control cannot inject records outside the corpus.
- **Bandwidth-constrained edge** (IoT, embedded, sensor networks)
  pre-load the package once during provisioning, then serve DNS
  forever from local memory.
- **Censorship-resistant resolvers** publish the package via any
  channel they can — HTTP, satellite, BitTorrent — and clients
  verify cryptographically without trusting the channel.
- **Forensic timestamping**: the (T, seq, prev) chain proves the
  state of DNSSEC for these zones at a specific moment in time,
  with cryptographic non-substitutability.

The architecture works **today** on real .se DNSSEC data with classical
algorithms (RSA, ECDSA, Ed25519), and is **post-quantum integrity
guaranteed** for the edge resolver: a future CRQC adversary breaking
RSA/ECDSA cannot forge any record outside the corpus, because the
Merkle root + ML-DSA-65 signature both rest on PQ-secure primitives
(SHA-3 collision resistance + Module-LWE).
