#!/usr/bin/env bash
# Trace-size scaling sweep for the 3 simple AIRs (Fibonacci,
# PoseidonChain, RegisterMachine) at log2(n_trace) = 11..24.
# Runs at the (level, hash) configuration determined by the
# BENCH_SHA3 / BENCH_MLDSA env vars (set by run-matrix.sh).
#
# Default: SHA3-256 + mldsa-44 (= L1, q=2^40 column).

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "simple-scaling"

cd "$REPO_ROOT"
SHA3="${BENCH_SHA3:-sha3-256}"
MLDSA="${BENCH_MLDSA:-mldsa-44}"
LEVEL_LABEL="${BENCH_LEVEL_LABEL:-L1}"
EXT_LABEL="${BENCH_EXT_LABEL:-Fp6}"
HASH_LABEL="$(echo "$SHA3" | tr '[:lower:]' '[:upper:]' | sed 's/SHA3-/SHA3-/')"

# The set of trace sizes to sweep.  Default capped at $2^{19}$ to stay
# within the c5.4xlarge $32$\,GiB ceiling: at $T = 2^{20}$+ the wider
# AIRs (PoseidonChain width 12, RegisterMachine width 8) approach the
# OOM boundary because peak memory scales as
# $T \times \mathrm{blowup} \times \max(\mathrm{width} \times 8\,B,
# \mathrm{ext\_size}, \mathrm{hash\_size})$ and crosses 30\,GiB before
# $k = 21$.  $11..19$ is $8.5$ doublings — enough for a clean
# linear-in-$T$ regression.  Override via `BENCH_K_RANGE` for higher-
# memory hosts (e.g. r5.4xlarge / r5.8xlarge).
K_RANGE="${BENCH_K_RANGE:-11 12 13 14 15 16 17 18 19}"

# r (NUM_QUERIES) is determined by the NIST PQ Level, NOT by the hash
# width.  Paper Table 5: r ∈ {54, 79, 105} for L1/L3/L5.  At L1 with
# SHA3-384 or SHA3-512 we keep r=54 — the larger hash buys binding-
# wall headroom (q=2^65 / 2^90), not per-query soundness.  Without
# this override the simple_air_scaling example would inherit
# deep_ali's compile-time `NUM_QUERIES_LEVEL`, which is hash-derived
# and therefore wrong for the off-diagonal (L1+SHA3-384/512 etc.) cells.
case "$LEVEL_LABEL" in
    L1) export BENCH_QUERIES=54  ;;
    L3) export BENCH_QUERIES=79  ;;
    L5) export BENCH_QUERIES=105 ;;
    *)  echo "[simple-scaling] WARN: unknown LEVEL_LABEL=$LEVEL_LABEL — leaving r at example default" ;;
esac

export BENCH_BLOWUP="$BLOWUP"

for AIR in Fibonacci PoseidonChain RegisterMachine; do
    LOG="$RESULTS_DIR/simple-scaling-${LEVEL_LABEL}-${SHA3}-${AIR}.run${RUN_IDX}.log"
    echo "[simple-scaling] AIR=$AIR ${LEVEL_LABEL} ${HASH_LABEL} k=$K_RANGE..."

    # shellcheck disable=SC2086
    cargo run --release -p cairo-bench --example simple_air_scaling \
        --features "deep_ali/$SHA3 deep_ali/$MLDSA deep_ali/parallel" \
        --no-default-features \
        -- --air "$AIR" $K_RANGE 2>&1 | tee "$LOG" || \
        echo "[simple-scaling] WARN: $AIR build/run failed; skipping"

    # Parse one stdout line per (k) measurement.
    awk -v run="$RUN_IDX" -v level="$LEVEL_LABEL" -v ext="$EXT_LABEL" \
        -v hash="$HASH_LABEL" -v ldt="$LDT" '
        /^simple_air_scaling / {
            for (i = 1; i <= NF; i++) {
                split($i, kv, "=")
                v[kv[1]] = kv[2]
            }
            printf "%s-2^%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,,%d,%s\n",
                v["air"], v["log2_n"], level, ext, hash, v["r"],
                v["n_trace"], v["blowup"], v["prove_ms"], v["verify_ms"],
                v["proof_kib"], run, ldt
            delete v
        }
    ' "$LOG" >> "$RESULTS_DIR/simple-scaling.csv"
done

echo "[simple-scaling] done; appended to results/simple-scaling.csv"
