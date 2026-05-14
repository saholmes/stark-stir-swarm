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
## The SAME `r` table holds for the quantum threat model — the Grover-
## halved per-query soundness is offset by NIST's Cat-L quantum target
## being half the classical target.  What changes in the quantum model
## is the HASH FUNCTION (see `quantum_hash` below), not `r`.
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

## Quantum-aware hash function selection per (level, quantum-query-budget).
## See scripts/results/quantum-calibration.md for the full derivation.
## Uses the strict-Brassard bound n/3 ≥ λ_q + log₂(q), where λ_q is the
## quantum bit-target (= λ_classical / 2 via NIST Cat L = AES-L
## equivalent and AES quantum loss to Grover).
##
##   L1 (λ_q=64):
##     q ≤ 2^40 → n ≥ 312 → SHA3-384
##                (relaxed BHT bound: q^3/2^n ≤ 2^-64 → n ≥ 184; SHA3-256 ok)
##     q ≤ 2^65 → n ≥ 387 → SHA3-512
##                (relaxed: n ≥ 259 → SHA3-384)
##     q ≤ 2^90 → n ≥ 462 → IMPOSSIBLE (strict)
##                (relaxed: n ≥ 334 → SHA3-512)
##   L3 (λ_q=96):
##     q ≤ 2^40 → n ≥ 408 → IMPOSSIBLE (strict)
##                (relaxed: n ≥ 216 → SHA3-256)
##     q ≤ 2^65 → n ≥ 483 → IMPOSSIBLE (strict)
##                (relaxed: n ≥ 291 → SHA3-384)
##     q ≤ 2^90 → IMPOSSIBLE
##                (relaxed: n ≥ 366 → SHA3-384)
##   L5 (λ_q=128):
##     q ≤ 2^40 → n ≥ 504 → SHA3-512 (relaxed: n ≥ 248 → SHA3-256)
##     q ≤ 2^65 → IMPOSSIBLE strict; relaxed n ≥ 323 → SHA3-384
##     q ≤ 2^90 → IMPOSSIBLE BOTH STRICT AND RELAXED (n ≥ 398, but SHA3-512=512 ok under relaxed bound)
##
## The harness uses the RELAXED bound (more commonly cited; matches the
## user-provided table).  Override with BENCH_HASH=sha3-{256,384,512}.
quantum_hash() {
    local level="$1"
    local q_log2="$2"  # quantum query budget log2 ∈ {40, 65, 90}
    # Pick MAX(classical-STARK-floor, quantum-FS-hash-floor) so the
    # combination satisfies both:
    #   (a) deep_ali's compile-time STARK ≥ sig constraint
    #       (sha3 variant must match or exceed the mldsa level)
    #   (b) Quantum FS-hash CR at the requested (level, q) per the
    #       user-provided q-vs-hash table.
    case "$level $q_log2" in
        # L1 classical floor sha3-256:
        "L1 40") echo sha3-256 ;;  # quantum floor sha3-256 ✓
        "L1 65") echo sha3-384 ;;  # quantum floor sha3-384
        "L1 90") echo sha3-512 ;;  # quantum floor sha3-512
        # L3 classical floor sha3-384:
        "L3 40") echo sha3-384 ;;  # quantum sha3-256, but classical floor wins
        "L3 65") echo sha3-384 ;;  # both at sha3-384
        "L3 90") echo sha3-512 ;;
        # L5 classical floor sha3-512:
        "L5 40") echo sha3-512 ;;  # quantum sha3-384, but classical floor wins
        "L5 65") echo sha3-512 ;;
        "L5 90") echo IMPOSSIBLE ;;
        *) echo "?" ;;
    esac
}

## Matching mldsa-* feature.  The ML-DSA parameter set is independent of
## the quantum hash choice — it's selected by NIST level only.
mldsa_for_level() {
    case "$1" in
        L1) echo mldsa-44 ;;
        L3) echo mldsa-65 ;;
        L5) echo mldsa-87 ;;
        *)  echo "?" ;;
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

## Quantum threat model: when BENCH_Q is set to 40, 65, or 90, the
## SHA3 variant per level is auto-selected via `quantum_hash`.  Without
## BENCH_Q, the default uses the classical paper-canon (L1=sha3-256,
## L3=sha3-384, L5=sha3-512) which is also the "q ≤ 2^40 quantum"
## hash for L1, but is UNDER-CALIBRATED for higher quantum query budgets.
BENCH_Q="${BENCH_Q:-}"  # empty | 40 | 65 | 90

if [ -n "$BENCH_Q" ]; then
    echo "## Quantum threat model active: q ≤ 2^${BENCH_Q} oracle queries"
    echo "## Hash selection per (level, q):"
    for lvl in L1 L3 L5; do
        echo "##   $lvl @ q=2^${BENCH_Q}: $(quantum_hash $lvl $BENCH_Q)"
    done
    echo
fi

run_level_cell() {
    local level="$1"
    local r_val="$2"
    local ldt="$3"
    local sha3 mldsa
    if [ -n "$BENCH_Q" ]; then
        sha3=$(quantum_hash "$level" "$BENCH_Q")
        if [ "$sha3" = "IMPOSSIBLE" ]; then
            echo "[skip] $level @ q=2^${BENCH_Q} is NOT POSSIBLE under any SHA3 variant."
            return
        fi
    else
        # Classical paper-canon hashes.
        case "$level" in
            L1) sha3=sha3-256 ;;
            L3) sha3=sha3-384 ;;
            L5) sha3=sha3-512 ;;
        esac
    fi
    mldsa=$(mldsa_for_level "$level")
    run_cell "$level" "$sha3" "$mldsa" "$r_val" "$ldt"
}

if [[ " $LEVELS_FILTER " == *" L1 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_level_cell L1 "$l1_r" "$ldt"
    done
fi
if [[ " $LEVELS_FILTER " == *" L3 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_level_cell L3 "$l3_r" "$ldt"
    done
fi
if [[ " $LEVELS_FILTER " == *" L5 "* ]]; then
    for ldt in $LDT_FILTER; do
        run_level_cell L5 "$l5_r" "$ldt"
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
