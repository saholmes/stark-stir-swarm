#!/usr/bin/env bash
# ML-DSA verify v2 STARK at NIST PQ Level 3 (Fp6, sha3-384, mldsa-65).
set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "mldsa-l3"
cd "$REPO_ROOT"
LOG="$RESULTS_DIR/mldsa-l3.run${RUN_IDX}.log"
export BENCH_BLOWUP="$BLOWUP"

echo "[mldsa-l3] running v2_bench at L3 (Fp6, sha3-384, mldsa-65), blowup=$BLOWUP..."
cargo test --release -p deep_ali \
    --features "parallel sha3-384 mldsa-65" --no-default-features \
    v2_bench -- --ignored --nocapture 2>&1 | tee "$LOG"

LINE=$(grep "^v2_bench " "$LOG" | tail -1)
if [ -z "$LINE" ]; then
    echo "[mldsa-l3] WARN: no v2_bench line in log; CSV row skipped."
    exit 1
fi

declare -A KV
for tok in $LINE; do
    if [[ "$tok" == *=* ]]; then KV[${tok%%=*}]=${tok#*=}; fi
done

csv_append "mldsa-l3" \
    "mldsa-v2-verify,L3,${KV[ext]},${KV[hash]},${KV[r]},,${KV[blowup]},${KV[prove_ms]},${KV[verify_ms]},${KV[proof_kib]},,$RUN_IDX,$LDT"

echo "[mldsa-l3] done; appended to results/mldsa-l3.csv"
