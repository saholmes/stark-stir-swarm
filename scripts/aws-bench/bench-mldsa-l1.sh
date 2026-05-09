#!/usr/bin/env bash
# ML-DSA verify v2 STARK at NIST PQ Level 1 (Fp6, sha3-256, mldsa-44).
# Wrapper around the v2_bench test in deep_ali.

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "mldsa-l1"

cd "$REPO_ROOT"
LOG="$RESULTS_DIR/mldsa-l1.run${RUN_IDX}.log"
export BENCH_BLOWUP="$BLOWUP"

echo "[mldsa-l1] running v2_bench at L1 (Fp6, sha3-256, mldsa-44), blowup=$BLOWUP..."
cargo test --release -p deep_ali \
    --features "parallel sha3-256 mldsa-44" --no-default-features \
    v2_bench -- --ignored --nocapture 2>&1 | tee "$LOG"

# Parse the v2_bench CSV-friendly stdout line.
parse_v2_bench_line() {
    grep "^v2_bench " "$LOG" | tail -1
}

LINE=$(parse_v2_bench_line)
if [ -z "$LINE" ]; then
    echo "[mldsa-l1] WARN: no v2_bench line in log; CSV row skipped."
    exit 1
fi

# Extract key=value pairs.
declare -A KV
for tok in $LINE; do
    if [[ "$tok" == *=* ]]; then
        KV[${tok%%=*}]=${tok#*=}
    fi
done

csv_append "mldsa-l1" \
    "mldsa-v2-verify,L1,${KV[ext]},${KV[hash]},${KV[r]},,${KV[blowup]},${KV[prove_ms]},${KV[verify_ms]},${KV[proof_kib]},,$RUN_IDX,$LDT"

echo "[mldsa-l1] done; appended to results/mldsa-l1.csv"
