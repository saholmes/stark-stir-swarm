#!/usr/bin/env bash
# bench-rss.sh — peak-RSS baseline harness for the low-mem/IoT streaming
# investigation (branch feature/low-mem-streaming-prover).
#
# Measures PEAK resident-set size of each in-tree signature/DNS prover so
# the "fit a shard in 1 GB" target is anchored to measured numbers.
#
# Method: build the example in release, then run the BUILT BINARY directly
# under `/usr/bin/time -l` (macOS).  We must NOT wrap `cargo run` — on macOS
# `time -l` reports the max RSS of the direct child only, so cargo/rustc
# would mask the prover's footprint.
#
# Output:
#   scripts/results/rss_baseline.csv
#   scripts/results/rss_baseline.md
#   scripts/results/rss-<tag>-b<blowup>.err   (per-run time -l + stderr)
#
# Usage:
#   ./scripts/bench-rss.sh                 # default blowup=4, stir
#   BENCH_BLOWUP=32 ./scripts/bench-rss.sh # production blowup
#   RSS_WORKLOADS="rsa2048 mldsa44" ./scripts/bench-rss.sh
set -uo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
RESULTS_DIR="$REPO_ROOT/scripts/results"
mkdir -p "$RESULTS_DIR"

BLOWUP="${BENCH_BLOWUP:-4}"
LDT="${BENCH_LDT:-stir}"
NPROC="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 1)"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-$NPROC}"
export BENCH_BLOWUP="$BLOWUP"
export BENCH_LDT="$LDT"

# Which workloads to run (in-tree, real full-prove examples only).
WORKLOADS="${RSS_WORKLOADS:-rsa2048 mldsa44 mldsa65 mldsa87}"

CSV="$RESULTS_DIR/rss_baseline.csv"
MD="$RESULTS_DIR/rss_baseline.md"
echo "scheme,nist_level,features,blowup,ldt,peak_rss_mib,prove_ms,proof_kib,trace_dims,note" > "$CSV"

# tag -> "example|features|nist_level"
cell_for() {
  case "$1" in
    # plain (likely non-bound) prover — kept for reference/comparison
    rsa2048)     echo "rsa2048_bench|parallel sha3-256 mldsa-44|L1" ;;
    # SOUND witness-binding provers ported from STARK-DNS (the real targets).
    # deep_ali requires exactly one mldsa-N feature to compile; mldsa-44
    # selects the L1 sha3-256 params for the classical-sig benches.
    rsa_bound)     echo "rsa2048_exp_bound_bench|parallel sha3-256 mldsa-44|L1" ;;
    ecdsa_bound)   echo "ecdsa_verify_multirow_bound_bench|parallel sha3-256 mldsa-44|L1" ;;
    ed25519_bound) echo "ed25519_verify_bound_bench|parallel sha3-256 mldsa-44|L1" ;;
    mldsa44) echo "mldsa_v2_bench|parallel sha3-256 mldsa-44|L1" ;;
    mldsa65) echo "mldsa_v2_bench|parallel sha3-384 mldsa-65|L3" ;;
    mldsa87) echo "mldsa_v2_bench|parallel sha3-512 mldsa-87|L5" ;;
    *) echo "" ;;
  esac
}

parse_rss_mib() {  # bytes on macOS -> MiB
  local err="$1" bytes
  bytes=$(grep -iE "maximum resident set size" "$err" | grep -oE "[0-9]+" | head -1)
  [ -n "$bytes" ] && awk "BEGIN{printf \"%.1f\", $bytes/1048576}" || echo "NA"
}

run_one() {
  local tag="$1" cell example features nist_level bin err out
  cell="$(cell_for "$tag")"
  if [ -z "$cell" ]; then echo "  [skip] unknown workload $tag"; return; fi
  IFS='|' read -r example features nist_level <<<"$cell"
  bin="$REPO_ROOT/target/release/examples/$example"
  err="$RESULTS_DIR/rss-${tag}-b${BLOWUP}.err"
  out="$RESULTS_DIR/rss-${tag}-b${BLOWUP}.out"

  echo "━━━ $tag  ($nist_level, blowup=$BLOWUP, ldt=$LDT) ━━━"
  echo "  building: cargo build --release -p deep_ali --example $example --features \"$features\" --no-default-features"
  if ! cargo build --release -p deep_ali --example "$example" \
        --features "$features" --no-default-features >"$err.build" 2>&1; then
    echo "  [BUILD FAILED] see $err.build"
    echo "$tag,$nist_level,\"$features\",$BLOWUP,$LDT,NA,NA,NA,NA,build-failed" >> "$CSV"
    return
  fi
  echo "  running under /usr/bin/time -l ..."
  /usr/bin/time -l "$bin" >"$out" 2>"$err" || true

  local rss prove_ms proof_kib dims
  rss="$(parse_rss_mib "$err")"
  prove_ms=$(grep -oE "prove_ms=[0-9.]+" "$out" | tail -1 | cut -d= -f2 || echo NA)
  proof_kib=$(grep -oE "proof_kib=[0-9.]+" "$out" | tail -1 | cut -d= -f2 || echo NA)
  dims=$(grep -iE "trace cols|rows:|constraints" "$err" | tail -1 | tr ',' ';' | tr -s ' ' || echo NA)
  [ -z "$prove_ms" ] && prove_ms=NA
  [ -z "$proof_kib" ] && proof_kib=NA

  echo "  peak_rss=${rss} MiB  prove_ms=${prove_ms}  proof_kib=${proof_kib}"
  echo "$tag,$nist_level,\"$features\",$BLOWUP,$LDT,$rss,$prove_ms,$proof_kib,\"$dims\"," >> "$CSV"
}

for w in $WORKLOADS; do run_one "$w"; done

# ── Markdown table (in-tree + honest not-in-tree rows) ───────────────
{
  echo "# Peak-RSS baseline — blowup=$BLOWUP, ldt=$LDT ($(uname -m), ${NPROC} threads)"
  echo
  echo "| Scheme | NIST | Peak RSS (MiB) | Prove (ms) | Proof (KiB) | Note |"
  echo "|---|---|--:|--:|--:|---|"
  tail -n +2 "$CSV" | while IFS=, read -r scheme lvl feats bw ldt rss prove proof dims note; do
    echo "| $scheme | $lvl | $rss | $prove | $proof | $note |"
  done
  echo "| Ed25519 | L1 | — | — | — | full per-sig harness NOT in tree (see memory project_crossalg_bench) |"
  echo "| ECDSA-P256 | L1 | — | — | — | AIR in sibling repo, NOT in tree (see memory project_ecdsa_status) |"
} > "$MD"

echo ""
echo "Wrote $CSV and $MD"
cat "$MD"
