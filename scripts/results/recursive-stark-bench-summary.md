# Recursive ML-DSA STARK — Paper-Grade Bench Summary

**Host:** Apple M4 · **Cores:** 10 · **Rust:** rustc 1.86.0 · **Date:** 2026-05-14

Each row is one prove + verify of the **composed** recursive ML-DSA
STARK statement — sub-circuits (1) constraint composition,
(2) binding-cells OOD, and (3) permutation-argument multiset equality
— packaged into a single outer `DeepFriProof<SexticExt>`.

## Smoke profile (blowup = 4)

| Level | LDT  | Prove (ms) | Verify (ms) | Proof (KiB) |
|------:|:-----|-----------:|------------:|------------:|
| L1    | FRI  |        6.5 |        0.60 |       200.5 |
| L1    | STIR |        0.5 |        0.22 |        46.3 |
| L3    | FRI  |        1.3 |        1.08 |       394.4 |
| L3    | STIR |        0.7 |        0.36 |        93.2 |
| L5    | FRI  |        1.1 |        2.31 |       658.7 |
| L5    | STIR |        0.7 |        0.67 |       158.0 |

## Production profile (blowup = 32)

| Level | LDT  | Prove (ms) | Verify (ms) | Proof (KiB) |
|------:|:-----|-----------:|------------:|------------:|
| L1    | FRI  |        2.6 |        0.91 |       280.5 |
| L1    | STIR |        1.7 |        0.29 |        78.9 |
| L3    | FRI  |        3.2 |        1.80 |       541.0 |
| L3    | STIR |        1.8 |        0.53 |       162.9 |
| L5    | FRI  |        3.3 |        3.18 |       892.8 |
| L5    | STIR |        2.1 |        1.02 |       280.1 |

## STIR vs FRI (production blowup = 32)

| Level | Prove speedup | Verify speedup | Size shrink |
|------:|--------------:|---------------:|------------:|
| L1    |         1.53× |          3.14× |       3.55× |
| L3    |         1.78× |          3.40× |       3.32× |
| L5    |         1.57× |          3.12× |       3.19× |

## Notes

- Statement proven: ∃ witnesses such that
  `Σ α_j · Φ_j = expected` (composition)
  ∧ `Σ α_j · (f_j − g_j) = 0` (binding-cells OOD)
  ∧ `∏(γ + l_i) = ∏(γ + r_i)` (perm-arg multiset equality).
- Synthetic witnesses: 6 XOR constraints, 7 OOD binding-cell claims, 5-element
  multisets — the structural shape of an inner ML-DSA-65 verification's three
  required sub-circuits.
- All three sub-circuits LDE'd on a **shared** domain `n_trace_max × blowup`,
  summed with FS-derived outer α's into a single outer `c_eval`.
- Outer `pi_hash` binds the three per-sub-circuit `pi_hash`es + `n_trace_max`
  into the FS transcript via SHA3-256.
- Sub-circuit inner α's derived from each sub-circuit's `pi_hash` with the
  distinct seed-XOR namespaces (`0xC1..C3` composition, `0xD0..D3` OOD,
  `0xE0..E4` perm-arg) established in commits `125640e` / `8f0b17c` / `9b7d3f7`.
- All measurements at `--features parallel` with `RAYON_NUM_THREADS=10` pinned.

## Reproduce

```bash
# Smoke profile
BENCH_BLOWUP=4 ./scripts/bench-recursive-stark.sh

# Production profile
BENCH_BLOWUP=32 ./scripts/bench-recursive-stark.sh

# Single level
BENCH_BLOWUP=32 BENCH_LEVELS_ONLY=L3 ./scripts/bench-recursive-stark.sh

# STIR only
BENCH_BLOWUP=32 BENCH_LDT_ONLY=stir ./scripts/bench-recursive-stark.sh
```
