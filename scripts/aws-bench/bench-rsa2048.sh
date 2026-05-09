#!/usr/bin/env bash
# RSA-2048 verify STARK (stacked AIR; one full RSA verify per proof).
# Uses crates/deep_ali/examples/rsa2048_bench.rs.

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "rsa2048"
cd "$REPO_ROOT"
LOG="$RESULTS_DIR/rsa2048.run${RUN_IDX}.log"
export BENCH_BLOWUP="$BLOWUP"
export BENCH_QUERIES="${BENCH_QUERIES:-54}"

echo "[rsa2048] running rsa2048_bench example, blowup=$BLOWUP, r=$BENCH_QUERIES..."
cargo run --release -p deep_ali --example rsa2048_bench \
    --features "parallel sha3-256 mldsa-44" --no-default-features \
    2>&1 | tee "$LOG"

# Parse: "rsa2048_bench n_trace=N blowup=B r=R prove_ms=X verify_ms=Y proof_kib=Z"
LINE=$(grep "^rsa2048_bench " "$LOG" | tail -1)
if [ -z "$LINE" ]; then
    echo "[rsa2048] WARN: no rsa2048_bench line in log; CSV row skipped."
    echo "[rsa2048] (Example may not have compiled — check $LOG.)"
    exit 1
fi

declare -A KV
for tok in $LINE; do
    if [[ "$tok" == *=* ]]; then KV[${tok%%=*}]=${tok#*=}; fi
done

csv_append "rsa2048" \
    "rsa2048-verify,L1,Fp6,SHA3-256,${KV[r]},${KV[n_trace]},${KV[blowup]},${KV[prove_ms]},${KV[verify_ms]},${KV[proof_kib]},,$RUN_IDX,$LDT"

echo "[rsa2048] done; appended to results/rsa2048.csv"
