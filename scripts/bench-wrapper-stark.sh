#!/usr/bin/env bash
# bench-wrapper-stark.sh — measure wrapper-stark SHA-3 STARK at L1/L3/L5.
#
# Runs `bench_wrapper_sha3_stark` for each (variant, blowup) combination
# and aggregates the output into scripts/results/wrapper-stark-bench.csv
# + .md.
#
# Each cell rebuilds wrapper-stark with the matching (sha3-*, mldsa-*)
# feature pair so the bench code picks up the right Sha3Variant at
# compile time.
#
# Usage:
#   ./scripts/bench-wrapper-stark.sh                # full sweep
#   BENCH_BLOWUP=4 ./scripts/bench-wrapper-stark.sh # smoke
#   BENCH_LEVELS_ONLY=L1 ./scripts/bench-wrapper-stark.sh  # one level

set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

RESULTS_DIR="$REPO_ROOT/scripts/results"
mkdir -p "$RESULTS_DIR"

BLOWUP="${BENCH_BLOWUP:-4}"
LEVELS_FILTER="${BENCH_LEVELS_ONLY:-L1 L3 L5}"
LDT_FILTER="${BENCH_LDT_ONLY:-fri stir}"

CSV="$RESULTS_DIR/wrapper-stark-bench.csv"
echo "variant,nist_level,blowup,r,ldt,prove_ms,verify_ms,proof_kib,n_trace" > "$CSV"

# Pin Rayon for reproducibility.
NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-$NPROC}"

run_cell() {
    local level="$1"    # L1, L3, L5
    local sha3="$2"     # sha3-256, sha3-384, sha3-512
    local mldsa="$3"    # mldsa-44, mldsa-65, mldsa-87
    local r="$4"        # 54, 79, 105
    local ldt="$5"      # fri, stir

    local stir_env=""
    if [ "$ldt" = "stir" ]; then stir_env="BENCH_STIR=1"; fi

    local log="$RESULTS_DIR/wrapper-stark-${level}-${sha3}-${ldt}-bw${BLOWUP}.log"
    echo "━━━ wrapper-stark ${level} ${sha3} r=${r} ldt=${ldt} blowup=${BLOWUP} ━━━"

    BENCH_BLOWUP=$BLOWUP BENCH_R=$r $stir_env \
        cargo test --release -p wrapper-stark \
        --features "$sha3 $mldsa parallel" --no-default-features \
        --lib bench_wrapper_sha3_stark -- --ignored --nocapture 2>&1 | tee "$log" >/dev/null

    local csv_line
    csv_line=$(grep "^wrapper_sha3 " "$log" | tail -1)
    if [ -z "$csv_line" ]; then
        echo "  → bench did not emit a measurement; check $log"
        return
    fi

    local prove_ms verify_ms proof_kib n_trace
    prove_ms=$(echo "$csv_line" | grep -oE "prove_ms=[0-9.]+" | cut -d= -f2)
    verify_ms=$(echo "$csv_line" | grep -oE "verify_ms=[0-9.]+" | cut -d= -f2)
    proof_kib=$(echo "$csv_line" | grep -oE "proof_kib=[0-9.]+" | cut -d= -f2)
    n_trace=$(echo "$csv_line" | grep -oE "n_trace=[0-9]+" | cut -d= -f2)

    echo "  → prove=${prove_ms}ms verify=${verify_ms}ms proof=${proof_kib}KiB n_trace=${n_trace}"
    echo "${sha3},${level},${BLOWUP},${r},${ldt},${prove_ms},${verify_ms},${proof_kib},${n_trace}" >> "$CSV"
}

echo "## Bench started: $(date -Iseconds)"
echo "## Host: $(hostname)"
echo "## CPU: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || \
           grep -m1 'model name' /proc/cpuinfo 2>/dev/null | sed 's/.*: //' || echo unknown)"
echo "## Cores: $NPROC"
echo "## Rayon: $RAYON_NUM_THREADS"
echo "## Blowup: $BLOWUP"
echo "## Rust: $(rustc --version)"
echo "## Git HEAD: $(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
echo

# Run cells.
if [[ " $LEVELS_FILTER " == *" L1 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_cell L1 sha3-256 mldsa-44  54 "$ldt"
    done
fi
if [[ " $LEVELS_FILTER " == *" L3 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_cell L3 sha3-384 mldsa-65  79 "$ldt"
    done
fi
if [[ " $LEVELS_FILTER " == *" L5 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_cell L5 sha3-512 mldsa-87 105 "$ldt"
    done
fi

# Emit Markdown summary.
MD="$RESULTS_DIR/wrapper-stark-bench.md"
{
    echo "# Wrapper-STARK SHA-3 Bench"
    echo
    echo "**Host:** \`$(hostname)\` · **Cores:** \`$NPROC\` · **Blowup:** \`$BLOWUP\` · **Git:** \`$(git rev-parse --short HEAD 2>/dev/null || echo unknown)\`"
    echo
    echo "Each row is one prove + verify of SHA-3(message=\"abc\") under the wrapper-stark row-uniform AIR, evaluated through deep_ali's deep_fri_prove."
    echo
    echo "| Variant | NIST L | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |"
    echo "|---|---|---:|---:|---|---:|---:|---:|---:|"
    awk -F, 'NR>1 {printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6,$7,$8,$9}' "$CSV"
    echo
    echo "## Notes"
    echo "- Row-uniform encoding per paper §3 + §5: 7 557-column schema (L1), 16 000 selected sub-step constraints per round + 5 957 always-active (booleanity + state threading)."
    echo "- pi_hash binds (variant, message) into the FS transcript; verifier rejects on FS divergence (validated by tamper test)."
    echo "- All measurements at \`--features parallel\` with RAYON_NUM_THREADS=\`$NPROC\` pinned."
} > "$MD"

echo
echo "═══════════════════════════════════════════════════════════"
echo "Done.  Results:"
echo "  Markdown:  $MD"
echo "  CSV:       $CSV"
echo "═══════════════════════════════════════════════════════════"
