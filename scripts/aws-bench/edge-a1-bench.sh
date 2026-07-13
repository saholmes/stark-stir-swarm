#!/usr/bin/env bash
# edge-a1-bench.sh — CONSTRAINED-EDGE decider/fold/epoch benchmark for STARK-DNS
# on AWS a1.medium (Graviton1 = Cortex-A72, the Raspberry Pi 4's core).
#
# Produces the camera-ready constrained-edge numbers: the once-per-epoch
# statement-validity DECIDER verify time, the hierarchical FOLD verify vs
# leaves, the epoch-Pi L1/L3/L5 verify, and — the reviewer's key question —
# the peak resident-set size, to confirm a 2 GiB edge can verify at all.
#
# Method:
#   * pin to a single vCPU (taskset) — the edge verifier is single-threaded,
#   * run the compiled test binary directly under GNU `/usr/bin/time -v` so the
#     reported peak RSS is the PROVER-plus-VERIFY footprint of the test, not
#     cargo/rustc (as in scripts/bench-rss.sh),
#   * the tests also print their own internal timings/RSS (getrusage) — we keep
#     both the external (time -v) and internal numbers.
#
# NOTE ON PROVE-vs-VERIFY: the decider test proves AND verifies in one process
# to produce the proof it then verifies.  The EDGE cost is the printed VERIFY
# ms; proving is publisher-side and only run here to generate the object.  The
# peak RSS is therefore an UPPER BOUND on the verifier footprint (prove
# dominates); the edge alone holds only the proof + constraint system.
#
# Usage (after edge-a1-setup.sh):
#   ./scripts/aws-bench/edge-a1-bench.sh
#   PIN_CORE=0 DECIDER_NS="512 2048" ./scripts/aws-bench/edge-a1-bench.sh
#
# On a 2 GiB a1.medium, N=8192 (~1.2 GiB) works only with the swap that
# edge-a1-setup.sh adds; the default sweep is capped accordingly.
set -uo pipefail

cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
REPO_ROOT="$(cd ../.. && pwd)"
CRATE_DIR="$REPO_ROOT/crates/binius-substrate"
STAMP="$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || echo run)"
RES="$SCRIPT_DIR/results/edge-a1-$STAMP"
PIN_CORE="${PIN_CORE:-0}"
mkdir -p "$RES"

# shellcheck disable=SC1090
[ -f "$HOME/.cargo/env" ] && source "$HOME/.cargo/env"

echo "=== STARK-DNS constrained-edge bench ==="
echo "host: $(uname -m), $(nproc) cores, ram $(free -m 2>/dev/null | awk '/Mem:/{print $2" MiB"}')"
echo "pin:  core $PIN_CORE   results: $RES"
uname -a > "$RES/host.txt"; (lscpu 2>/dev/null || sysctl -n machdep.cpu.brand_string 2>/dev/null) >> "$RES/host.txt" || true

command -v taskset >/dev/null 2>&1 || { echo "taskset missing (install util-linux)"; PIN=""; }
PIN="${PIN-taskset -c $PIN_CORE}"
# Prefer GNU time (supports -v). On Linux /usr/bin/time is GNU; on macOS it is BSD
# (no -v), so prefer `gtime` there. If only BSD time is found, skip external RSS.
TIME_BIN="$(command -v gtime || true)"
if [ -z "$TIME_BIN" ] && /usr/bin/time -v true >/dev/null 2>&1; then
  TIME_BIN="/usr/bin/time"
fi
[ -n "$TIME_BIN" ] || echo "WARNING: GNU time (-v) not found — external peak RSS unavailable (tests still print their own internal RSS)."

# ─── locate the compiled test binary (built by edge-a1-setup.sh) ─────────
echo "[bench] locating test binary..."
cd "$CRATE_DIR"
TESTBIN="$(CARGO_BUILD_JOBS=1 cargo test --release --lib --no-run --message-format=json 2>/dev/null \
  | grep -o '"executable":"[^"]*binius_substrate-[^"]*"' | head -1 | sed 's/.*"executable":"//; s/"$//')"
if [ -z "${TESTBIN:-}" ] || [ ! -x "$TESTBIN" ]; then
  TESTBIN="$(find "$REPO_ROOT/target/release/deps" "$CRATE_DIR/target/release/deps" -maxdepth 1 -type f -name 'binius_substrate-*' ! -name '*.d' -perm -u+x 2>/dev/null | sort | tail -1)"
fi
[ -x "${TESTBIN:-}" ] || { echo "ERROR: test binary not found — run edge-a1-setup.sh first."; exit 1; }
echo "[bench] test binary: $TESTBIN"

CSV="$RES/summary.csv"
echo "bench,external_peak_rss_mib,status,out_file" > "$CSV"

STEP=0
NSTEPS=4
RUN_T0=$SECONDS
echo "[progress] starting $NSTEPS benchmarks at $(date -u +%H:%M:%SZ) ..."

run_one() {
  local test="$1" tag="$2"
  local out="$RES/$tag.out" tim="$RES/$tag.time"
  STEP=$((STEP + 1))
  local t0=$SECONDS
  echo ""
  echo "─── [$STEP/$NSTEPS] $tag  ($test) — started $(date -u +%H:%M:%SZ) ───"
  if [ -n "$TIME_BIN" ]; then
    # shellcheck disable=SC2086
    $PIN "$TIME_BIN" -v "$TESTBIN" "$test" --include-ignored --nocapture >"$out" 2>"$tim" || true
    local kb; kb="$(grep -i 'Maximum resident set size' "$tim" | awk '{print $NF}')"
    local mib=$(( ${kb:-0} / 1024 ))
  else
    # shellcheck disable=SC2086
    $PIN "$TESTBIN" "$test" --include-ignored --nocapture >"$out" 2>&1 || true
    local mib=0
  fi
  local status="ok"; grep -q "test result: ok" "$out" || status="FAILED/na"
  # echo the tests' own printed tables (verify ms lives here)
  grep -E '^\||VERIFY|verify |leaves ×|GATE epoch|prove |peak RSS' "$out" | sed 's/^/    /' || true
  echo "[$STEP/$NSTEPS] ✓ $tag DONE in $((SECONDS - t0))s — external peak RSS ${mib} MiB, status: $status"
  echo "$tag,$mib,$status,$out" >> "$CSV"
}

# ─── the edge-relevant benchmarks ───────────────────────────────────────
# Full decider (statement validity): VERIFY ms + peak RSS — the 2 GiB question.
run_one decider_verify_width_term           "decider"
# Hierarchical fold: VERIFY vs leaves (polylog).
run_one hierarchical_fold_verify_scaling    "fold-hierarchical"
# Epoch-Pi L1/L3/L5 verify (the laddered aggregation proof).
run_one epoch_pi_challenger_ladders         "epoch-pi-ladder"
# Committed opening, leaves-independent.
run_one interleaved_decider_verify_vs_leaves "opening-leaves-indep"

# ─── summary ────────────────────────────────────────────────────────────
{
  echo "# STARK-DNS constrained-edge (a1.medium / Cortex-A72) results"
  echo ""
  echo "- host: \`$(uname -m)\`, $(nproc) core(s); pinned to core $PIN_CORE"
  echo "- date: $STAMP"
  echo "- \`decider\` VERIFY ms is the once-per-epoch edge cost; peak RSS confirms the 2 GiB fit."
  echo ""
  echo '```'
  cat "$CSV"
  echo '```'
  echo ""
  echo "The decider VERIFY time (Cortex-A72) is in \`decider.out\` (columns: N | PROVE | VERIFY | prove-peak-RSS | proof)."
  echo "For the paper: add a row to tab:verify-costs with Node=a1/A72, and replace the extrapolation paragraph."
} > "$RES/SUMMARY.md"

TOTAL=$((SECONDS - RUN_T0))
echo ""
echo "════════════════════════════════════════════════════════════"
echo "  ✅ RUN FINISHED — $NSTEPS/$NSTEPS benchmarks complete"
echo "     total wall time: ${TOTAL}s ($((TOTAL/60))m $((TOTAL%60))s)   at $(date -u +%H:%M:%SZ)"
echo "════════════════════════════════════════════════════════════"
echo "Summary:  $RES/SUMMARY.md"
echo "CSV:      $CSV"
echo "Raw:      $RES/*.out  (+ *.time for external peak RSS)"
# machine-detectable completion marker for `grep`/automation on the nohup log:
echo "EDGE_A1_BENCH_COMPLETE status=done steps=$NSTEPS seconds=$TOTAL results=$RES"
