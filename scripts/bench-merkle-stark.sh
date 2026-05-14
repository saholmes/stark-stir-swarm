#!/usr/bin/env bash
# bench-merkle-stark.sh — measure wrapper-stark Merkle path STARK at
# multiple depths (log2 leaves = 1..5) under FRI and STIR.
#
# Usage:
#   ./scripts/bench-merkle-stark.sh                    # default sweep
#   BENCH_MERKLE_DEPTHS="2 4" ./scripts/bench-merkle-stark.sh
#   BENCH_LDT_ONLY=stir ./scripts/bench-merkle-stark.sh

set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

RESULTS_DIR="$REPO_ROOT/scripts/results"
mkdir -p "$RESULTS_DIR"

DEPTHS="${BENCH_MERKLE_DEPTHS:-2 3 4}"
LDT_FILTER="${BENCH_LDT_ONLY:-fri stir}"
BLOWUP="${BENCH_BLOWUP:-4}"
# NIST levels: BENCH_MERKLE_LEVELS="L1 L3 L5" — each rebuilds with the
# matching (sha3-*, mldsa-*) feature pair.
LEVELS_FILTER="${BENCH_MERKLE_LEVELS:-L1}"

NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-$NPROC}"

CSV="$RESULTS_DIR/merkle-stark-bench.csv"
echo "level,sha3,depth_log2,n_leaves,blowup,r,ldt,prove_ms,verify_ms,proof_kib,n_trace" > "$CSV"

echo "## Bench started: $(date -Iseconds)"
echo "## Host: $(hostname)"
echo "## CPU: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || \
           grep -m1 'model name' /proc/cpuinfo 2>/dev/null | sed 's/.*: //' || echo unknown)"
echo "## Cores: $NPROC"
echo "## Blowup: $BLOWUP"
echo

for level in $LEVELS_FILTER; do
    case "$level" in
        L1) sha3=sha3-256; mldsa=mldsa-44; r=54  ;;
        L3) sha3=sha3-384; mldsa=mldsa-65; r=79  ;;
        L5) sha3=sha3-512; mldsa=mldsa-87; r=105 ;;
        *) echo "[skip] unknown level: $level"; continue ;;
    esac
    # Allow BENCH_R env var to override the level default.
    r_actual="${BENCH_R:-$r}"

    for depth in $DEPTHS; do
        n_leaves=$((1 << depth))
        for ldt in $LDT_FILTER; do
            echo "━━━ Merkle ${level} ${sha3} depth=$depth (n=$n_leaves) ldt=$ldt blowup=$BLOWUP r=$r_actual ━━━"
            log="$RESULTS_DIR/merkle-stark-${level}-${sha3}-d${depth}-${ldt}-bw${BLOWUP}.log"
            if [ "$ldt" = "stir" ]; then
                BENCH_MERKLE_DEPTH=$depth BENCH_BLOWUP=$BLOWUP BENCH_R=$r_actual BENCH_STIR=1 \
                    cargo test --release -p wrapper-stark \
                    --features "$sha3 $mldsa parallel" --no-default-features \
                    --lib bench_merkle_path_stark -- --ignored --nocapture 2>&1 \
                    | tee "$log" >/dev/null
            else
                BENCH_MERKLE_DEPTH=$depth BENCH_BLOWUP=$BLOWUP BENCH_R=$r_actual \
                    cargo test --release -p wrapper-stark \
                    --features "$sha3 $mldsa parallel" --no-default-features \
                    --lib bench_merkle_path_stark -- --ignored --nocapture 2>&1 \
                    | tee "$log" >/dev/null
            fi
            line=$(grep "^merkle_stark " "$log" | tail -1)
            if [ -z "$line" ]; then
                echo "  → bench did not emit a line; see $log"
                continue
            fi
            prove_ms=$(echo "$line" | grep -oE "prove_ms=[0-9.]+" | cut -d= -f2)
            verify_ms=$(echo "$line" | grep -oE "verify_ms=[0-9.]+" | cut -d= -f2)
            proof_kib=$(echo "$line" | grep -oE "proof_kib=[0-9.]+" | cut -d= -f2)
            n_trace=$(echo "$line" | grep -oE "n_trace=[0-9]+" | cut -d= -f2)
            echo "  → prove=${prove_ms}ms verify=${verify_ms}ms proof=${proof_kib}KiB n_trace=${n_trace}"
            echo "${level},${sha3},${depth},${n_leaves},${BLOWUP},${r_actual},${ldt},${prove_ms},${verify_ms},${proof_kib},${n_trace}" >> "$CSV"
        done
    done
done

# Emit Markdown summary.
MD="$RESULTS_DIR/merkle-stark-bench.md"
{
    echo "# Wrapper-STARK Merkle Path Bench"
    echo
    echo "**Host:** \`$(hostname)\` · **Cores:** \`$NPROC\` · **Blowup:** \`$BLOWUP\` · **Levels:** \`$LEVELS_FILTER\`"
    echo
    echo "Each row is one prove + verify of a Merkle authentication path STARK at the given depth, evaluated through deep_ali's deep_fri_prove."
    echo
    echo "| Level | Hash | Depth | Leaves | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |"
    echo "|---|---|---:|---:|---:|---:|---|---:|---:|---:|---:|"
    awk -F, 'NR>1 {printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11}' "$CSV"
    echo
    echo "## Notes"
    echo "- Statement proven: \"I know a leaf + authentication path such that the Merkle chain hashes to the public root.\""
    echo "- Trace: \`d × 98\` rows (1 merkle hop + 97 sponge_air sub-rows per hop), padded to next power of 2."
    echo "- Constraints: selection (2N per hop) + sponge sub-AIR (~22k per absorb) + cross-row bindings (~2N per hop) + root boundary."
    echo "- All measurements at \`--features parallel\` with RAYON_NUM_THREADS=\`$NPROC\` pinned."
} > "$MD"

echo
echo "═══════════════════════════════════════════════════════════"
echo "Done.  Results:"
echo "  Markdown:  $MD"
echo "  CSV:       $CSV"
echo "═══════════════════════════════════════════════════════════"
