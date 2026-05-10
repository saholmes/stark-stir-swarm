#!/usr/bin/env bash
# Hash-rollup STARK at trace sizes 2^16, 2^18 (was 2^16/18/20;
# 2^20 OOM-thrashes the c5.4xlarge 32 GiB ceiling because the
# hash-rollup trace is wide).  2^18 matches the paper's headline
# trace size for the simple-AIR table.  Override via
# `BENCH_HASH_ROLLUP_K` for higher-memory hosts.
# Source: cairo-bench/examples/hash_rollup_scale.rs.

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "hash-rollup"

cd "$REPO_ROOT"
LOG="$RESULTS_DIR/hash-rollup.run${RUN_IDX}.log"

K_RANGE="${BENCH_HASH_ROLLUP_K:-16 18}"
echo "[hash-rollup] running at trace sizes $K_RANGE, blowup=$BLOWUP..."
echo "[hash-rollup] RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-auto}"
# shellcheck disable=SC2086
cargo run --release -p cairo-bench --example hash_rollup_scale \
    --features "parallel sha3-256" \
    -- $K_RANGE \
    2>&1 | tee "$LOG"

# Parse output lines of form:
#   "log2_n=16 prove_ms=2660 verify_ms=3.2 proof_kib=1068 rss_mb=761"
awk -v run="$RUN_IDX" -v blowup="$BLOWUP" -v ldt="$LDT" '
    /log2_n=/ {
        for (i = 1; i <= NF; i++) {
            split($i, kv, "=")
            v[kv[1]] = kv[2]
        }
        printf "hash-rollup-2^%s,L1,Fp6,SHA3-256,54,%d,%d,%s,%s,%s,%s,%d,%s\n",
            v["log2_n"], (2 ** v["log2_n"]), blowup,
            v["prove_ms"], v["verify_ms"], v["proof_kib"], v["rss_mb"],
            run, ldt
        delete v
    }
' "$LOG" >> "$RESULTS_DIR/hash-rollup.csv"

echo "[hash-rollup] done; appended to results/hash-rollup.csv"
