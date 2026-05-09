#!/usr/bin/env bash
# 6-cell (level, hash) matrix runner.  Reproduces the FRI paper's
# benchmark methodology: each of the 3 simple AIRs swept across
# log2(n_trace) = 11..24 at every (level, hash) pair valid for the
# corresponding NIST PQ binding-wall column:
#
#   L1: SHA3-256 (q=2^40), SHA3-384 (q=2^65), SHA3-512 (q=2^90)
#   L3: SHA3-384 (q=2^65), SHA3-512 (q=2^90)
#   L5: SHA3-512 (q=2^65 only; q=2^90 violates the binding wall)
#
# Total: 6 (level, hash) configurations × 3 simple AIRs × 14 trace
# sizes = 252 measurements per run, triplicated by BENCH_RUNS.
#
# The cryptographic AIRs (Ed25519, RSA-2048, ML-DSA-{L1,L3,L5}) are
# at their natural fixed trace sizes and run once per relevant
# (level, hash) cell.

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"

mkdir -p results

# ─── 6-cell matrix ───────────────────────────────────────────────
# Each row: LEVEL_LABEL EXT_LABEL SHA3 MLDSA q_max_label
MATRIX=(
    "L1 Fp6 sha3-256 mldsa-44 q=2^40"
    "L1 Fp6 sha3-384 mldsa-44 q=2^65"
    "L1 Fp6 sha3-512 mldsa-44 q=2^90"
    "L3 Fp6 sha3-384 mldsa-65 q=2^65"
    "L3 Fp6 sha3-512 mldsa-65 q=2^90"
    "L5 Fp8 sha3-512 mldsa-87 q=2^65"
)

RUNS="${BENCH_RUNS:-3}"

{
    echo "## Matrix run started: $(date -Iseconds)"
    echo "## Host: $(hostname)"
    echo "## Cells: ${#MATRIX[@]}"
    echo "## Runs per cell: $RUNS"
    echo "## Cells:"
    printf "##   %s\n" "${MATRIX[@]}"
} > results/matrix-meta.txt
cat results/matrix-meta.txt

for cell in "${MATRIX[@]}"; do
    set -- $cell
    LEVEL=$1; EXT=$2; SHA3=$3; MLDSA=$4; QMAX=$5

    export BENCH_LEVEL_LABEL="$LEVEL"
    export BENCH_EXT_LABEL="$EXT"
    export BENCH_SHA3="$SHA3"
    export BENCH_MLDSA="$MLDSA"

    echo
    echo "════════════════════════════════════════════════════════════"
    echo "Cell: $LEVEL × $EXT × $SHA3 × $MLDSA (binding $QMAX)"
    echo "════════════════════════════════════════════════════════════"

    for run in $(seq 1 "$RUNS"); do
        export BENCH_RUN_IDX="$run"
        echo "--- Run $run / $RUNS ---"

        # Simple AIRs (3) × 14 trace sizes
        "$SCRIPT_DIR/bench-simple-scaling.sh" \
            || echo "[warn] simple-scaling failed: $LEVEL/$SHA3 run $run"

        # Cryptographic AIRs at this (level, hash) cell — only run
        # the ones whose level matches.
        case "$LEVEL" in
            L1)
                "$SCRIPT_DIR/bench-mldsa-l1.sh" \
                    || echo "[warn] mldsa-l1 failed: $SHA3 run $run"
                # Ed25519 / RSA-2048 are L1 by construction; run once
                # in the SHA3-256 cell to avoid 3× duplication.
                if [ "$SHA3" = "sha3-256" ]; then
                    "$SCRIPT_DIR/bench-ed25519.sh" \
                        || echo "[warn] ed25519 failed: run $run"
                    "$SCRIPT_DIR/bench-rsa2048.sh" \
                        || echo "[warn] rsa2048 failed: run $run"
                    "$SCRIPT_DIR/bench-hash-rollup.sh" \
                        || echo "[warn] hash-rollup failed: run $run"
                fi
                ;;
            L3)
                "$SCRIPT_DIR/bench-mldsa-l3.sh" \
                    || echo "[warn] mldsa-l3 failed: $SHA3 run $run"
                ;;
            L5)
                "$SCRIPT_DIR/bench-mldsa-l5.sh" \
                    || echo "[warn] mldsa-l5 failed: $SHA3 run $run"
                ;;
        esac
    done
done

echo
echo "=== Aggregating across all matrix cells ==="
"$SCRIPT_DIR/aggregate.sh"

echo
echo "=== Matrix run done ==="
echo "Per-cell logs:    results/simple-scaling-*.log, results/mldsa-l*.log, ..."
echo "Per-AIR CSVs:     results/*.csv"
echo "Median summary:   results/summary_median.csv"
echo "Paper Table 6:    results/paper_table.tex"
