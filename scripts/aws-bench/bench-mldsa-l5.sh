#!/usr/bin/env bash
# ML-DSA verify v2 STARK at NIST PQ Level 5 (Fp8, sha3-512, mldsa-87).
set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "mldsa-l5"
cd "$REPO_ROOT"
LOG="$RESULTS_DIR/mldsa-l5.run${RUN_IDX}.log"
export BENCH_BLOWUP="$BLOWUP"

echo "[mldsa-l5] running v2_bench at L5 (Fp8, sha3-512, mldsa-87), blowup=$BLOWUP..."
cargo test --release -p deep_ali \
    --features "parallel sha3-512 mldsa-87" --no-default-features \
    v2_bench -- --ignored --nocapture 2>&1 | tee "$LOG"

LINE=$(grep "^v2_bench " "$LOG" | tail -1)
if [ -z "$LINE" ]; then
    echo "[mldsa-l5] WARN: no v2_bench line in log; CSV row skipped."
    exit 1
fi

declare -A KV
for tok in $LINE; do
    if [[ "$tok" == *=* ]]; then KV[${tok%%=*}]=${tok#*=}; fi
done

csv_append "mldsa-l5" \
    "mldsa-v2-verify,L5,${KV[ext]},${KV[hash]},${KV[r]},,${KV[blowup]},${KV[prove_ms]},${KV[verify_ms]},${KV[proof_kib]},,$RUN_IDX,$LDT"

echo "[mldsa-l5] done; appended to results/mldsa-l5.csv"
