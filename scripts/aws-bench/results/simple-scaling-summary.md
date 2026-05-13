# Simple-AIR Scaling Matrix — STIR/FRI Reproducibility Bench

**Host:** AWS `r8g.4xlarge` (Graviton4, 16 vCPU, 128 GiB)
**Wall time:** ~2 days
**AIRs:** Fibonacci, PoseidonChain, RegisterMachine (cairo-bench synthetic AIRs from the FRI paper)
**Trace-size sweep:** log₂(n_trace) = 11..22 (2 048..4 194 304 rows)
**NIST PQ Levels:** L1 (sha3-256, r=54), L3 (sha3-384, r=79), L5 (sha3-512, r=105)
**LDT:** STIR (full matrix) + FRI (L1 sha3-256 only, comparison reference)
**Runs:** 3 per cell, 0.3 % median CV in prove_ms ⇒ paper-trustworthy single runs
**Total measurements:** 674 rows across 242 distinct (AIR, level, hash, LDT, k) cells

---

## 1. Production-scale headline (k = 2²² ≈ 4.2 M rows, STIR)

| AIR | Level | Hash | r | Prove (s) | Verify (ms) | Proof (KiB) |
|---|---|---|---:|---:|---:|---:|
| Fibonacci | L1 | SHA3-256 | 54 | 554 | 1.64 | 231.4 |
| Fibonacci | L3 | SHA3-384 | 79 | 555 | 3.29 | 501.5 |
| Fibonacci | L5 | SHA3-512 | 105 | 587 | 6.72 | 883.9 |
| PoseidonChain | L1 | SHA3-256 | 54 | 1452 | 1.64 | 231.4 |
| PoseidonChain | L3 | SHA3-384 | 79 | 1459 | 3.30 | 501.5 |
| PoseidonChain | L5 | SHA3-512 | 105 | 1490 | 6.72 | 883.9 |
| RegisterMachine | L1 | SHA3-256 | 54 | 739 | 1.64 | 231.4 |
| RegisterMachine | L3 | SHA3-384 | 79 | 741 | 3.29 | 501.5 |
| RegisterMachine | L5 | SHA3-512 | 105 | 771 | 6.74 | 883.9 |

**Reading:** verifier work is **2–7 ms** across a 1000× range of trace sizes at all three NIST PQ levels — the polylog bound is empirically validated end-to-end.

## 2. NIST level cost is essentially flat (k = 2²², STIR)

| AIR | L1 prove (s) | L3 prove (s) | L5 prove (s) | L1→L5 prove Δ | L1 proof (KiB) | L5 proof (KiB) | L1→L5 proof Δ |
|---|---:|---:|---:|---:|---:|---:|---:|
| Fibonacci | 554 | 555 | 587 | +5.9% | 231 | 884 | +282% |
| PoseidonChain | 1452 | 1459 | 1490 | +2.6% | 231 | 884 | +282% |
| RegisterMachine | 739 | 741 | 771 | +4.4% | 231 | 884 | +282% |

**Reading:** doubling the soundness target from L1 (~128-bit) to L5 (~256-bit) costs the prover **3–6 %** at production scale.  The cost lives in the proof size (the linear-in-`r` query overhead), not the prover. This is the right shape for STARK-DNS where a resolver verifies a fresh proof on every query.

## 3. STIR vs FRI head-to-head (NIST L1, sha3-256, r=54)

| AIR | k | STIR prove (s) | FRI prove (s) | Speedup | STIR proof (KiB) | FRI proof (KiB) | Shrink |
|---|---:|---:|---:|---:|---:|---:|---:|
| Fibonacci | 2^11 | 0.27 | 0.60 | 2.23× | 135.5 | 482.4 | 3.56× |
| Fibonacci | 2^13 | 1.02 | 2.31 | 2.27× | 164.5 | 585.5 | 3.56× |
| Fibonacci | 2^15 | 4.07 | 9.33 | 2.29× | 168.1 | 670.0 | 3.99× |
| Fibonacci | 2^17 | 16.53 | 37.81 | 2.29× | 197.0 | 786.6 | 3.99× |
| Fibonacci | 2^19 | 67.33 | 152.93 | 2.27× | 200.6 | 884.6 | 4.41× |
| Fibonacci | 2^21 | 275.04 | 614.39 | 2.23× | 229.6 | 1014.7 | 4.42× |
| PoseidonChain | 2^11 | 0.64 | 0.97 | 1.52× | 135.5 | 482.4 | 3.56× |
| PoseidonChain | 2^13 | 2.51 | 3.80 | 1.51× | 164.5 | 585.5 | 3.56× |
| PoseidonChain | 2^15 | 10.32 | 15.51 | 1.50× | 168.1 | 670.0 | 3.99× |
| PoseidonChain | 2^17 | 42.49 | 63.83 | 1.50× | 197.0 | 786.6 | 3.99× |
| PoseidonChain | 2^19 | 174.48 | 260.73 | 1.49× | 200.6 | 884.6 | 4.41× |
| RegisterMachine | 2^11 | 0.32 | 0.66 | 2.05× | 135.5 | 482.4 | 3.56× |
| RegisterMachine | 2^13 | 1.25 | 2.56 | 2.05× | 164.5 | 585.5 | 3.56× |
| RegisterMachine | 2^15 | 5.11 | 10.40 | 2.03× | 168.1 | 670.0 | 3.99× |

**Reading:** STIR delivers **2.2× faster prove and 4.4× smaller proofs** than FRI on Fibonacci at k=21.  PoseidonChain (computation-heavy AIR) sees a smaller prove gap (1.5×) because the LDT is a smaller fraction of the total work; the proof-size gap holds for every AIR.  This justifies STIR as the default LDT in stark-stir-swarm.

## 4. Verifier polylog scaling (all 18 STIR cells)

- min verify_ms: **1.05 ms** at ('Fibonacci', 'L1', 'SHA3-256', 'stir', 11)
- max verify_ms across the whole matrix (STIR + FRI): **10.62 ms** at ('Fibonacci', 'L1', 'SHA3-256', 'fri', 21)
- The verifier stays under **7 ms** at every (AIR, level, hash, k=22) cell.

## 5. Reproducibility

- Median CV of prove_ms across 3 runs: **0.26 %**
- Worst-case CV: **1.33 %**
- Best-case CV: **0.00 %**

Single-run numbers are within ~1 % of the 3-run median — paper-grade stability.

---

## Figures

- `fig-prove-scaling.pdf` — log-log prove time vs trace size, 3 AIRs × 3 NIST levels
- `fig-verify-polylog.pdf` — semilog-x verify time vs trace size (polylog claim)
- `fig-proof-size.pdf` — semilog-x proof size vs trace size (AIR-independent)
- `fig-stir-vs-fri.pdf` — side-by-side STIR/FRI prove + proof-size

## Validity statement (post-v2 soundness rebuild)

The data was collected before commit `6151f2b` ("v2 NIZK soundness: close T_MEM + V17 binding gaps") but the matrix is **still authoritative on current main**.  The matrix calls `deep_ali::fri::deep_fri_prove` / `deep_fri_verify` / `deep_fri_proof_size_bytes` directly; those functions live at lines 1963 / 2199 / 2120 of `fri.rs` respectively, all outside the hunks modified by 6151f2b.  The simple AIRs (Fibonacci, PoseidonChain, RegisterMachine) do not call into `prove_one_sub_air_with_trace` or the ML-DSA v2 orchestration, which are the only call paths actually changed.

---

*Generated by `scripts/aws-bench/generate-simple-scaling-summary.py` from
`scripts/aws-bench/results/simple-scaling.csv`.*
