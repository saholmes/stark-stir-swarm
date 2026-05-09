# AWS c5.4xlarge benchmark suite (DEEP-ALI-STIR / DEEP-ALI-FRI)

Reproduces the empirical numbers in
`Downloads/main-22.tex` (STIR paper, Table 6) and
`Downloads/ESORICS-FIPS_Aligned_STARKs_with_Multi_Level_PQ_Security.pdf`
(FRI paper, Table 5) on the canonical reference machine: AWS
**c5.4xlarge** (Cascade Lake, AVX-512, 16 vCPU, 32 GiB RAM,
Ubuntu 22.04 LTS).

Reports prove time, verify time, proof size, and peak RSS for every
AIR instance the codebase carries:

| AIR                       | Source crate / harness                                          | Notes |
|---------------------------|------------------------------------------------------------------|-------|
| Cairo suite (4 AIRs)      | `cairo-bench/benches/cairo_air_bench.rs`                         | Fibonacci, PoseidonChain, RegisterMachine, CairoSimple — synthetic AIRs from the FRI paper, fixed-size criterion bench |
| Simple-AIR scaling        | `cairo-bench/examples/simple_air_scaling.rs` (new)               | 3 simple AIRs (Fibonacci, PoseidonChain, RegisterMachine) swept across log2(n_trace) = 11..24, matching the FRI paper's scaling methodology |
| HashRollup (DNS)          | `cairo-bench/examples/hash_rollup_scale.rs`                      | Real DNS-zone rollup trace at sizes 2¹⁶–2²² |
| Ed25519 verify            | `swarm-dns/examples/zsk_ksk_bench.rs`                            | Full v16 Ed25519 verify AIR (SHA-512, scalar reduce, 2 decompressions, 2 ladders, residual chain, cofactor mul, identity verdict) |
| RSA-2048 verify           | `deep_ali/examples/rsa2048_bench.rs` (new)                       | Stacked RSA-2048 verify AIR (modular exponentiation + final compare) |
| ML-DSA verify (L1)        | `v2_bench` test in `ml_dsa_verify_air_v2_orchestration.rs::tests` | v2 ML-DSA-44 verify AIR (Fp⁶, sha3-256), Phase 1 trace-commit |
| ML-DSA verify (L3)        | same harness, `mldsa-65` + `sha3-384`                            | Fp⁶ |
| ML-DSA verify (L5)        | same harness, `mldsa-87` + `sha3-512`                            | Fp⁸ |

## Quickstart

```bash
# On a fresh AWS c5.4xlarge instance:
git clone --recurse-submodules <repo-url> stark-stir-swarm
cd stark-stir-swarm/scripts/aws-bench
./setup.sh         # install Rust toolchain + deps; idempotent

# Smoke test (single (level, hash), no scaling sweep):
./run-all.sh       # runs every bench at default L1/SHA3-256

# Full FRI-paper-aligned matrix (recommended for paper figures):
./run-matrix.sh    # 6 (level, hash) cells × 3 simple AIRs × 14 trace
                   # sizes (k=11..24) + cryptographic AIRs at each
                   # relevant cell.  ≈ 252 simple-AIR measurements +
                   # cryptographic AIRs, triplicated.

./aggregate.sh     # collates into results/paper_table.tex
```

### The 6-cell (level, hash) matrix

Each cell corresponds to a column in paper Table~III (multi-level
parameterisation), driven by the maximum quantum adversary budget
$q_{\max}$ that the chosen SHA-3 variant supports under the QROM
binding wall:

| Level | Ext.\  | Hash      | $q_{\max}$ supported |
|-------|--------|-----------|-----------------------|
| L1    | Fp6    | SHA3-256  | $q = 2^{40}$          |
| L1    | Fp6    | SHA3-384  | $q = 2^{65}$          |
| L1    | Fp6    | SHA3-512  | $q = 2^{90}$          |
| L3    | Fp6    | SHA3-384  | $q = 2^{65}$          |
| L3    | Fp6    | SHA3-512  | $q = 2^{90}$          |
| L5    | Fp8    | SHA3-512  | $q = 2^{65}$ only — $q = 2^{90}$ violates the binding wall (Theorem 7). |

`run-matrix.sh` iterates over all 6 cells, recompiling the deep_ali
crate with the appropriate `sha3-N` + `mldsa-N` Cargo features for
each cell (mutually-exclusive feature flags).  Per-cell compile
time: ~2-4 minutes; total matrix run time on c5.4xlarge: ~3-5
hours including all measurements (depends on `BENCH_RUNS`).

Each bench is also runnable standalone:

```bash
./bench-cairo-suite.sh
./bench-ed25519.sh
./bench-rsa2048.sh
./bench-mldsa-l1.sh
./bench-mldsa-l3.sh
./bench-mldsa-l5.sh
```

## Output format

Each `bench-*.sh` writes a CSV row to `results/<air>.csv` with columns:

```
air,level,ext_field,hash,r,n_trace,blowup,prove_ms,verify_ms,proof_kib,peak_rss_mib,run_idx
```

`run-all.sh` triplicates each measurement (`run_idx` = 1, 2, 3) and
`aggregate.sh` reports the median.

## Notes on rate / query-count alignment

The default rate is **ρ₀ = 1/32** (`blowup = 32`), matching paper
Table III. Calibrated query counts:

- L1: r = 54 (Johnson regime, unconditional)
- L3: r = 79
- L5: r = 105

Smaller blowups over-provide FRI/STIR security. To re-measure the
*previous* (`blowup = 4`) FRI paper figures for like-for-like
comparison, set `BENCH_BLOWUP=4` in the environment before
`run-all.sh`.

## Reproducing FRI vs STIR comparison

By default `run-all.sh` runs the FRI mode of the deep_ali crate
(`stir = false` in `DeepFriParams`). To run STIR mode, set
`BENCH_LDT=stir` before invoking. Note: the STIR mode currently
requires Phase 2 of the soundness fix
(see `docs/v2_phase1_trace_commit_design.md`); for Phase 1 the FRI
mode is the canonical setting.

## Hardware

- AWS c5.4xlarge: 16 vCPU (Intel Xeon Platinum 8124M / 8275CL,
  Cascade Lake), 32 GiB RAM, AVX-512 native.
- Ubuntu 22.04 LTS recommended; tested with Rust 1.79+.
- All measurements use Rayon multi-threading (16 threads).
- Native SHA-3 only; no Poseidon acceleration on the security path
  (paper-canonical SHA-3-only build).

## Output → paper Table

`aggregate.sh` produces `results/paper_table.tex` — a drop-in LaTeX
fragment matching Table 6 in the STIR paper. After running, replace
the corresponding `tabular` block in `main-22.tex` with the contents
of `paper_table.tex` (or paste row-by-row).
