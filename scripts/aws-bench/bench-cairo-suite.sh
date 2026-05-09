#!/usr/bin/env bash
# Re-run the original FRI-paper Cairo AIR suite (Fibonacci, PoseidonChain,
# RegisterMachine, CairoSimple) under the canonical paper-aligned
# parameters (blowup=32, r=54).  Source: cairo-bench/benches/cairo_air_bench.rs.
# Criterion-driven; produces a JSON-friendly CSV summary.

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "cairo-suite"

cd "$REPO_ROOT"
echo "[cairo-suite] running criterion bench at blowup=$BLOWUP, run $RUN_IDX..."
echo "[cairo-suite] RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-auto}"

# Criterion outputs to target/criterion/.../report.html and prints summary.
# Explicit feature pin (cairo-bench's default already includes
# parallel + sha3-256, but pin for reproducibility).
LOG="$RESULTS_DIR/cairo-suite.run${RUN_IDX}.log"
cargo bench --release -p cairo-bench --bench cairo_air_bench \
    --features "parallel sha3-256" -- \
    --output-format bencher 2>&1 | tee "$LOG"

# Parse 'test cairo_air/<name>/<size> ... bench: <prove_ns> ns/iter' lines.
# Convert to ms and emit one row per (AIR, trace_size).
awk -v run="$RUN_IDX" -v blowup="$BLOWUP" -v ldt="$LDT" '
    /^test cairo_air/ {
        # name pattern: cairo_air/<air_name>/<trace_size>
        split($2, parts, "/")
        air = parts[2]; size = parts[3]
        # time: "bench: <ns> ns/iter (...)" — field 4 in bencher format
        ns = $4 + 0
        prove_ms = ns / 1e6
        printf "cairo-%s,L1,Fp6,SHA3-256,54,%s,%d,%.2f,,,,%d,%s\n",
               air, size, blowup, prove_ms, run, ldt
    }
' "$LOG" >> "$RESULTS_DIR/cairo-suite.csv"

echo "[cairo-suite] done; appended to results/cairo-suite.csv"
