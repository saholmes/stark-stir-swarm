#!/usr/bin/env bash
# bench-recursive-stark.sh — measure the composed recursive ML-DSA STARK
# (3 sub-circuits → 1 outer FRI proof) across L1/L3/L5 × FRI/STIR.
#
# Each cell rebuilds wrapper-stark with the matching (sha3-*, mldsa-*)
# feature pair, then invokes the `bench_recursive_stark` test from
# recursive_prover.rs.  Output is aggregated into
# scripts/results/recursive-stark-bench.{csv,md}.
#
# Usage:
#   ./scripts/bench-recursive-stark.sh                         # full sweep
#   BENCH_BLOWUP=4 ./scripts/bench-recursive-stark.sh          # smoke profile
#   BENCH_LEVELS_ONLY=L1 ./scripts/bench-recursive-stark.sh    # one level
#   BENCH_LDT_ONLY=stir ./scripts/bench-recursive-stark.sh     # STIR only

set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

RESULTS_DIR="$REPO_ROOT/scripts/results"
mkdir -p "$RESULTS_DIR"

BLOWUP="${BENCH_BLOWUP:-4}"
LEVELS_FILTER="${BENCH_LEVELS_ONLY:-L1 L3 L5}"
LDT_FILTER="${BENCH_LDT_ONLY:-fri stir}"

CSV="$RESULTS_DIR/recursive-stark-bench-bw${BLOWUP}.csv"
echo "variant,nist_level,blowup,r,ldt,prove_ms,verify_ms,proof_kib,n_trace,n_constraints,n_ood,n_perm" > "$CSV"

NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-$NPROC}"

## Calibrated `r` per (blowup, level) from
## scripts/results/r-vs-blowup-calibration.md:
##   r = ⌈total_bit_target / (½ · log₂(blowup))⌉
##   where total_bit_target ∈ {135, 197.5, 262.5} for L1/L3/L5.
##
## BENCH_R overrides this if set explicitly.
calibrated_r() {
    local level="$1"
    local blowup="$2"
    case "$level $blowup" in
        "L1 4")  echo 135 ;;
        "L1 8")  echo  90 ;;
        "L1 16") echo  68 ;;
        "L1 32") echo  54 ;;
        "L3 4")  echo 198 ;;
        "L3 8")  echo 132 ;;
        "L3 16") echo  99 ;;
        "L3 32") echo  79 ;;
        "L5 4")  echo 263 ;;
        "L5 8")  echo 175 ;;
        "L5 16") echo 132 ;;
        "L5 32") echo 105 ;;
        *) echo "?" ;;
    esac
}

run_cell() {
    local level="$1"    # L1, L3, L5
    local sha3="$2"     # sha3-256, sha3-384, sha3-512
    local mldsa="$3"    # mldsa-44, mldsa-65, mldsa-87
    local r="$4"        # 54, 79, 105
    local ldt="$5"      # fri, stir

    local log="$RESULTS_DIR/recursive-stark-${level}-${sha3}-${ldt}-bw${BLOWUP}.log"
    echo "━━━ recursive-stark ${level} ${sha3} r=${r} ldt=${ldt} blowup=${BLOWUP} ━━━"

    if [ "$ldt" = "stir" ]; then
        BENCH_BLOWUP=$BLOWUP BENCH_R=$r BENCH_STIR=1 \
            cargo test --release -p wrapper-stark \
            --features "$sha3 $mldsa parallel" --no-default-features \
            --lib recursive_prover::tests::bench_recursive_stark \
            -- --ignored --nocapture 2>&1 | tee "$log" >/dev/null
    else
        BENCH_BLOWUP=$BLOWUP BENCH_R=$r \
            cargo test --release -p wrapper-stark \
            --features "$sha3 $mldsa parallel" --no-default-features \
            --lib recursive_prover::tests::bench_recursive_stark \
            -- --ignored --nocapture 2>&1 | tee "$log" >/dev/null
    fi

    local line
    line=$(grep "^recursive_stark " "$log" | tail -1)
    if [ -z "$line" ]; then
        echo "  → bench did not emit a measurement; check $log"
        return
    fi

    local prove_ms verify_ms proof_kib n_trace n_constraints n_ood n_perm
    prove_ms=$(echo "$line" | grep -oE "prove_ms=[0-9.]+" | cut -d= -f2)
    verify_ms=$(echo "$line" | grep -oE "verify_ms=[0-9.]+" | cut -d= -f2)
    proof_kib=$(echo "$line" | grep -oE "proof_kib=[0-9.]+" | cut -d= -f2)
    n_trace=$(echo "$line" | grep -oE "n_trace=[0-9]+" | cut -d= -f2)
    n_constraints=$(echo "$line" | grep -oE "n_constraints=[0-9]+" | cut -d= -f2)
    n_ood=$(echo "$line" | grep -oE "n_ood=[0-9]+" | cut -d= -f2)
    n_perm=$(echo "$line" | grep -oE "n_perm=[0-9]+" | cut -d= -f2)

    echo "  → prove=${prove_ms}ms verify=${verify_ms}ms proof=${proof_kib}KiB n_trace=${n_trace}"
    echo "${sha3},${level},${BLOWUP},${r},${ldt},${prove_ms},${verify_ms},${proof_kib},${n_trace},${n_constraints},${n_ood},${n_perm}" >> "$CSV"
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

## Per-level r is now auto-derived from blowup via `calibrated_r` to
## maintain consistent NIST PQ bit-budget across blowups (see
## scripts/results/r-vs-blowup-calibration.md).  BENCH_R env var
## still overrides if set explicitly.

l1_r="${BENCH_R:-$(calibrated_r L1 "$BLOWUP")}"
l3_r="${BENCH_R:-$(calibrated_r L3 "$BLOWUP")}"
l5_r="${BENCH_R:-$(calibrated_r L5 "$BLOWUP")}"

echo "## Calibrated r per level @ blowup=${BLOWUP}: L1=${l1_r}  L3=${l3_r}  L5=${l5_r}"
echo

if [[ " $LEVELS_FILTER " == *" L1 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_cell L1 sha3-256 mldsa-44  "$l1_r" "$ldt"
    done
fi
if [[ " $LEVELS_FILTER " == *" L3 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_cell L3 sha3-384 mldsa-65  "$l3_r" "$ldt"
    done
fi
if [[ " $LEVELS_FILTER " == *" L5 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_cell L5 sha3-512 mldsa-87 "$l5_r" "$ldt"
    done
fi

# Markdown summary.
MD="$RESULTS_DIR/recursive-stark-bench-bw${BLOWUP}.md"
{
    echo "# Recursive ML-DSA STARK Bench"
    echo
    echo "**Host:** \`$(hostname)\` · **Cores:** \`$NPROC\` · **Blowup:** \`$BLOWUP\` · **Git:** \`$(git rev-parse --short HEAD 2>/dev/null || echo unknown)\`"
    echo
    echo "Each row is one prove + verify of the **composed** recursive STARK statement (constraint composition ∧ binding-cells OOD ∧ perm-arg multiset equality), produced as a single outer DeepFriProof<SexticExt>."
    echo
    echo "| Variant | NIST L | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace | n_constraints | n_ood | n_perm |"
    echo "|---|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|"
    awk -F, 'NR>1 {printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12}' "$CSV"
    echo
    echo "## Notes"
    echo "- Statement proven: \"I know witnesses such that Σ α·Φ = expected (composition) ∧ Σ α·(f − g) = 0 (binding-cells OOD) ∧ ∏(γ + l) = ∏(γ + r) (perm-arg)\"."
    echo "- All three sub-circuits LDE'd on a shared domain of n_trace_max × blowup, summed with FS-derived outer α's into a single outer c_eval."
    echo "- Synthesised witnesses: 6 XOR constraints + 7 OOD binding-cells claims + 5-element multisets — these are the structural shapes of an inner ML-DSA-65 verification's three required sub-circuits."
    echo "- All measurements at \`--features parallel\` with RAYON_NUM_THREADS=\`$NPROC\` pinned."
} > "$MD"

echo
echo "═══════════════════════════════════════════════════════════"
echo "Done.  Results:"
echo "  Markdown:  $MD"
echo "  CSV:       $CSV"
echo "═══════════════════════════════════════════════════════════"
