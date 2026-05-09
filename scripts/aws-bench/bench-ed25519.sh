#!/usr/bin/env bash
# Ed25519 verify AIR (full v16: SHA-512 + scalar reduce + 2 decompressions
# + 2 ladders + residual chain + cofactor mul + identity verdict).
# Source: swarm-dns/examples/zsk_ksk_bench.rs.

set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
# shellcheck source=./_lib.sh
source "$SCRIPT_DIR/_lib.sh"

csv_init "ed25519"

cd "$REPO_ROOT"
LOG="$RESULTS_DIR/ed25519.run${RUN_IDX}.log"

echo "[ed25519] running zsk_ksk_bench (full STARK pass)..."
echo "[ed25519] RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-auto}"
# swarm-dns default features include parallel + sha3-256, but we
# pass them explicitly for reproducibility.
cargo run --release -p swarm-dns --example zsk_ksk_bench \
    --features "parallel sha3-256" 2>&1 | tee "$LOG"

# Parse lines of the form:
#   "STARK prove: <X>s"  /  "STARK verify: <Y>ms"
#   "Proof size: <Z> KiB"
prove_s=$(grep -i "STARK prove" "$LOG" | tail -1 | awk '{for(i=1;i<=NF;i++) if($i ~ /s$/) {gsub(/s/,"",$i); print $i; exit}}')
verify_ms=$(grep -i "STARK verify" "$LOG" | tail -1 | awk '{for(i=1;i<=NF;i++) if($i ~ /ms$/) {gsub(/ms/,"",$i); print $i; exit}}')
proof_kib=$(grep -i "Proof size" "$LOG" | tail -1 | awk '{for(i=1;i<=NF;i++) if($i ~ /KiB|KB/) {gsub(/KiB|KB/,"",$i); print $i; exit}}')

prove_ms=$(awk -v s="${prove_s:-0}" 'BEGIN { printf "%.0f", s * 1000 }')

csv_append "ed25519" \
  "ed25519-verify-v16,L1,Fp6,SHA3-256,54,8192,$BLOWUP,${prove_ms:-0},${verify_ms:-0},${proof_kib:-0},0,$RUN_IDX,$LDT"

echo "[ed25519] done; appended to results/ed25519.csv"
