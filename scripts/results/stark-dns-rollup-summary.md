# STARK-DNS Rollup — full architectural summary

End-of-session summary tying together the calibration, scaling,
quantum-adversary, and blockchain-layering work into one
STARK-DNS-specific picture.

## What we have today (viable on L1 production)

The recursive ML-DSA STARK gadget supports the **standard rollup pattern**
(Option B from `rollup-scaling-and-l1-l2.md`) end-to-end, paper-grade,
across the full NIST PQ regime and across the full quantum-adversary
regime:

| Component | Status | Where it lives |
|---|---|---|
| Inner v2 ML-DSA verify STARK     | ✓ Production | `deep_ali::ml_dsa_verify_air_v2_orchestration` |
| Recursive STARK gadget (4 sub-circuits) | ✓ Production | `wrapper-stark::recursive_prover` |
| v2 → recursive STARK bridge      | ✓ Ext-generic (Fp⁶/Fp⁸) | `wrapper-stark::v2_recursion_bridge` |
| Outer HashRollup STARK           | ✓ HASH_BYTES-generic | `swarm-dns::prover::prove_outer_rollup` |
| ML-DSA rollup demo (end-to-end)  | ✓ Multi-level builds | `swarm-dns/examples/ml_dsa_recursive_rollup_demo.rs` |
| Calibrated r per (level, blowup) | ✓ Documented      | `scripts/results/r-vs-blowup-calibration.md` |
| Quantum-adversary calibration    | ✓ Documented      | `scripts/results/quantum-calibration.md` |
| Full (level × q × Fp^x) matrix   | ✓ Measured        | `scripts/results/quantum-matrix-full.md` |
| L1 Ethereum gas analysis         | ✓ Documented      | `scripts/results/l1-ethereum-gas-analysis.md` |

## Option B for STARK-DNS — works today

STARK-DNS aggregates DNSSEC RRSIGs across records in a zone (or
across zones in a TLD shard).  Each RRSIG → one inner v2 STARK →
one recursive STARK proof (789 KiB at L1, 3 153 KiB at L3, 5 605 KiB
at L5, bw=4 calibrated).  The outer HashRollup STARK commits to all
the per-record pi_hashes.

```
DNSSEC zone (R records) → R recursive STARKs (per-record)
                       ↘
                          → 1 outer HashRollup STARK (~85–97 KiB constant)
                       ↗
                                ┌─ posted to L1 (Ethereum)
                                └─ pi_hashes Merkle-commit to root
                                   per-record STARKs posted to L2/DA
```

**L1 cost (Option B)**: ~0.71 M gas / batch via EIP-4844 blobs
= ~$53 per batch.  Scales as $/N: at R=10 000 records/zone, **~$0.005
per record**.

## Option C for STARK-DNS — true O(1) in DNSSEC size

The natural next step.  One master STARK proves "all R per-record
recursive STARKs verify":

```
DNSSEC zone (R records) → R recursive STARKs
                            ↘
                              → 1 MASTER recursive STARK (constant ~789 KiB)
                            ↗     (proves all R recursive STARKs verify in-AIR)
                                  ↓
                              posted to L1 (Ethereum)
                              L1 cost: ONE FRI verify (~5 M gas / $375)
```

**O(1) L1 cost** regardless of zone size — whether R = 10 or R = 10 million
records.  Per-record amortized cost approaches zero at large R.

| Zone size R | Option B L1 cost | Option C L1 cost (future) |
|---:|---:|---:|
|         100 |    $53 ($0.53 / record) | ~$375 (master proof) |
|       1 000 |    $53 ($0.053 / record) | ~$375 ($0.375 / record) |
|      10 000 |    $53 ($0.0053 / record) | ~$375 ($0.0375 / record) |
|     100 000 |    $53 ($0.00053 / record) | ~$375 ($0.00375 / record) |
|   1 000 000 |    $53 ($0.000053 / record) | ~$375 ($0.000375 / record) |
|  10 000 000 |    $53 ($0.0000053 / record) | ~$375 ($0.0000375 / record) |

Notice: **Option B already amortizes to ~zero per-record** as R grows,
because the L1 cost is constant.  Option C's advantage isn't in
per-record amortized cost (both → 0) — it's in **what L1 attests**:

- **Option B**: L1 attests "the outer HashRollup commits to R pi_hashes".
  Signature cryptographic validity comes from off-chain DA + per-sig
  recursive STARK verify (on whatever consumes them).

- **Option C**: L1 attests "all R signatures are cryptographically valid",
  via the master STARK.  No DA dependency for signature validity;
  L1 alone is sufficient.

## TLD-scale projection (.com hypothetical)

`.com` ≈ 165 M domains × ~3 RRSIGs/domain ≈ 500 M signatures.

| Path | L1 cost | Wire to L1 | Wire to DA | Verifier work on consumer |
|---|---:|---:|---:|---|
| **Option B** | $53 (constant) | ~97 KiB outer | ~395 TB per-sig pile | DA serves per-sig STARK on demand; consumer verifies one at ~2.7 ms |
| **Option C** | $375 (constant) | ~789 KiB master | ~395 TB witness (optional) | Consumer verifies one master STARK at ~5 ms; signature validity guaranteed |
| **Option A** (full L1) | ~$200B (linear in R) | 395 TB to L1 | none | N/A — wholly impractical |

**Option B + DA** is the practical .com architecture today.  **Option C** is
the cleaner "L1-alone-sufficient" architecture and the natural target
for a future implementation push.

## What Option C requires

Single-level recursion: one inner v2 proof → one recursive STARK.
Implemented at `wrapper-stark::v2_recursion_bridge::prove_v2_all_subairs_composed_recursive`
(commit `0f4eb98`).

**Two-level recursion** (Option C): N recursive STARK proofs → one master
recursive STARK.  Implementation pattern:

1. Define a `RecursiveProofClaim` containing the N inner `RecursiveStarkProof`
   bundles' `outer_pi_hash`-es + a slot for proving "each one verifies".
2. Build a master-AIR with sub-circuits:
   - **sub-circuit 1** (composition): the N recursive STARKs' FRI quotient
     residues — each `c_eval(x) · Z_H(x) − Σ α · Φ(trace[x])` at queried
     positions, exactly like the inner v2 sub-AIR residue extraction.
   - **sub-circuit 2** (OOD): cross-binding of each recursive STARK's
     output pi_hash to the master STARK's public-input commitment.
   - **sub-circuit 3** (vestige): trivial.
   - **sub-circuit 4** (in-AIR Merkle): R Merkle paths binding each
     recursive STARK's FRI commits to its `outer_pi_hash`.
3. Output a single master `DeepFriProof<Ext>` of size ~789 KiB
   regardless of R.

This is **architecturally identical** to the v2 → recursive bridge —
just one level higher up the recursion ladder.  The same extraction
helpers (`extract_sub_air_residues`, `extract_v2_fri_deep_quotient_residues`,
`build_v2_v17_subair_composition`, etc.) translate one-for-one with
the recursive STARK as the inner proof shape instead of v2.

**Implementation effort**: comparable to commits `0f4eb98` +
`183af26` + `4bb14f2` (= the full sub-circuit-1-2-3-4 wiring for v2 →
recursive).  Roughly **5–8 engineer-weeks** to bring up + measure.

## Direct answer

**Q: We have a viable rollup solution for STARK-DNS using the recursive prover?**
✓ **Yes.**  Option B (outer rollup on L1, per-sig on L2/DA) is end-to-end
working today, paper-grade calibrated across all NIST PQ levels and
quantum-adversary budgets, with measured 9.4× wire compression per
signature and constant $0.71 M gas / $53 L1 cost regardless of zone size.

**Q: Option C → O(1) L1 cost regardless of DNSSEC size?**
✓ **Yes — that's the architectural target.**  One master recursive
STARK proves all R per-record recursive STARKs verify, posted to L1
at ~789 KiB / ~5 M gas regardless of R.  The implementation is
"one more layer of recursion" applied to the same wrapper-stark
gadget, well-scoped.

Both architectures (B today, C tomorrow) give L1 cost **constant
in the DNSSEC zone size** — Option B by trusting DA for per-sig
proofs, Option C by collapsing all per-sig proofs into one master
STARK.  Option B is **practical today**; Option C is the **cleaner
L1-alone-sufficient story** and the natural next implementation
push.
