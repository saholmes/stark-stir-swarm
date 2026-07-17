#!/usr/bin/env bash
# Raspberry Pi fleet-proving benchmark for DNS-STARK / S1d ML-DSA-44 verify.
#
# Measures each fleet strand's UNIT per-shard prove cost + RSS on THIS Pi's core, then
# reports the end-to-end model for one ML-DSA-44 verify: shard counts, total shard-work,
# per-signature latency, and throughput (sigs/hr) as the fleet (number of Pis) grows.
#
# Run ON a Raspberry Pi (64-bit Pi OS / aarch64). Same test runs on any aarch64 host.
#   SHARD_COEFFS=32 ./pi-fleet-bench.sh          # default shard size
#   PIN_CORE=0 SHARD_COEFFS=16 ./pi-fleet-bench.sh
set -uo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
REPO_ROOT="$(cd ../.. && pwd)"
CRATE_DIR="$REPO_ROOT/crates/binius-substrate"
STAMP="$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || echo run)"
RES="$SCRIPT_DIR/results/pi-$STAMP"
SHARD_COEFFS="${SHARD_COEFFS:-32}"
mkdir -p "$RES"

echo "== host ==" | tee "$RES/host.txt"
{
  uname -a
  echo "arch: $(uname -m)"
  echo "cores: $(nproc 2>/dev/null || echo '?')"
  free -m 2>/dev/null | awk '/Mem:/{print "ram: "$2" MiB"}'
  grep -m1 -i "model" /proc/cpuinfo 2>/dev/null || sysctl -n machdep.cpu.brand_string 2>/dev/null
  grep -m1 "Revision" /proc/cpuinfo 2>/dev/null
} | tee -a "$RES/host.txt"

# Optional single-core pin (a Pi's proving is single-threaded per shard unless --features parallel).
PIN=""
if command -v taskset >/dev/null 2>&1 && [ -n "${PIN_CORE:-}" ]; then
  PIN="taskset -c $PIN_CORE"
  echo "pinned to core $PIN_CORE"
fi

echo "== building test binary (release, parallel) ==" | tee -a "$RES/host.txt"
cd "$CRATE_DIR"
cargo test --release --lib --features parallel --no-run 2>&1 | tail -2 | tee -a "$RES/host.txt"

echo "== fleet throughput model (SHARD_COEFFS=$SHARD_COEFFS) =="
SHARD_COEFFS="$SHARD_COEFFS" $PIN cargo test --release --lib --features parallel \
  fleet_throughput_model -- --ignored --test-threads=1 --nocapture 2>&1 \
  | tee "$RES/throughput.txt" \
  | grep -E "arch=|strand |per-signature|fleet size|^\| |unit costs"

echo
echo "results saved to: $RES"
echo "  host.txt        — Pi model, cores, RAM"
echo "  throughput.txt  — per-strand unit costs + fleet throughput/latency table"
