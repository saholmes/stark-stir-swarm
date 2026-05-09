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

# The set of trace sizes to sweep.  Adjust BENCH_K_RANGE in the env
# (e.g. "11 12 13 14") for a smaller sweep on memory-constrained boxes.
K_RANGE="${BENCH_K_RANGE:-11 12 13 14 15 16 17 18 19 20 21 22 23 24}"

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
