#!/usr/bin/env bash
# Master bench runner: runs every AIR's bench script 3 times each,
# producing CSVs under results/.  Then aggregates into summary.csv
# and paper_table.tex.

set -euo pipefail

cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
mkdir -p results

# ─── Header info ─────────────────────────────────────────────────
{
    echo "## AWS bench run started: $(date -Iseconds)"
    echo "## Host: $(hostname)"
    echo "## CPU: $(grep -m1 'model name' /proc/cpuinfo 2>/dev/null | sed 's/.*: //' || sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown)"
    echo "## Cores: $(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo unknown)"
    echo "## Mem: $(free -h 2>/dev/null | awk '/^Mem/ {print $2}' || echo unknown)"
    echo "## Rust: $(rustc --version)"
    echo "## Git: $(git -C .. rev-parse --short HEAD 2>/dev/null || echo unknown)"
} > results/run-meta.txt
cat results/run-meta.txt

# ─── Run each bench 3 times ──────────────────────────────────────
RUNS="${BENCH_RUNS:-3}"
echo
echo "=== Running each bench ${RUNS}× ==="

for run in $(seq 1 "$RUNS"); do
    export BENCH_RUN_IDX="$run"
    echo
    echo "--- Run $run / $RUNS ---"

    "$SCRIPT_DIR/bench-cairo-suite.sh" || echo "[warn] cairo-suite failed on run $run"
    "$SCRIPT_DIR/bench-hash-rollup.sh" || echo "[warn] hash-rollup failed on run $run"
    "$SCRIPT_DIR/bench-ed25519.sh"     || echo "[warn] ed25519 failed on run $run"
    "$SCRIPT_DIR/bench-rsa2048.sh"     || echo "[warn] rsa2048 failed on run $run"
    "$SCRIPT_DIR/bench-mldsa-l1.sh"    || echo "[warn] mldsa-l1 failed on run $run"
    "$SCRIPT_DIR/bench-mldsa-l3.sh"    || echo "[warn] mldsa-l3 failed on run $run"
    "$SCRIPT_DIR/bench-mldsa-l5.sh"    || echo "[warn] mldsa-l5 failed on run $run"
done

# ─── Aggregate ───────────────────────────────────────────────────
echo
echo "=== Aggregating results ==="
"$SCRIPT_DIR/aggregate.sh"

echo
echo "=== Done ==="
echo "Per-AIR CSVs: results/*.csv"
echo "Summary:     results/summary.csv"
echo "Paper table: results/paper_table.tex"
