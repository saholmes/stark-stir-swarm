#!/usr/bin/env bash
# One-step Mac -> Raspberry Pi: cross-build the fleet benchmark, deploy the binary, run it on the
# Pi, and collect results back on the Mac.  No Rust toolchain on the Pi — just the ~15 MB binary.
#
#   PI_HOST=pi@raspberrypi.local ./deploy.sh
#   ./deploy.sh pi@192.168.1.50
#   SKIP_BUILD=1 ./deploy.sh pi@raspberrypi.local        # reuse existing deploy/pi-bench
#   SHARD_COEFFS=16 TARGET=aarch64-unknown-linux-musl ./deploy.sh pi@raspberrypi.local
set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
PI_HOST="${1:-${PI_HOST:-}}"
[ -n "$PI_HOST" ] || { echo "usage: PI_HOST=pi@raspberrypi.local ./deploy.sh   (or: ./deploy.sh pi@host)"; exit 1; }
REMOTE_DIR="${REMOTE_DIR:-dns-stark-bench}"
SHARD_COEFFS="${SHARD_COEFFS:-16}"
STAMP="$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || echo run)"
RES="$SCRIPT_DIR/results/deploy-$STAMP"
BIN="$SCRIPT_DIR/deploy/pi-bench"
mkdir -p "$RES"

# 1. cross-build on the Mac (unless SKIP_BUILD=1 and a binary already exists).
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo "== [1/4] cross-building on $(uname -m) for the Pi =="
  ./cross-build.sh
fi
[ -f "$BIN" ] || { echo "no binary at $BIN — run ./cross-build.sh (or unset SKIP_BUILD)"; exit 1; }

# 2. deploy the binary.
echo "== [2/4] deploying to $PI_HOST:$REMOTE_DIR =="
ssh "$PI_HOST" "mkdir -p $REMOTE_DIR"
scp "$BIN" "$PI_HOST:$REMOTE_DIR/pi-bench"
ssh "$PI_HOST" "chmod +x $REMOTE_DIR/pi-bench"

# 3. Pi host info.
echo "== [3/4] Pi host info =="
ssh "$PI_HOST" 'uname -a; nproc | sed "s/^/cores: /"; grep -m1 MemTotal /proc/meminfo; grep -m1 -i "model" /proc/cpuinfo' \
  | tee "$RES/host.txt"

# 4. run the benchmarks on the Pi, collect results on the Mac.
echo "== [4/4] running on the Pi (SHARD_COEFFS=$SHARD_COEFFS) =="
echo "  -- STEP 1: single-device RSS pipeline --"
ssh "$PI_HOST" "cd $REMOTE_DIR && SHARD_COEFFS=$SHARD_COEFFS ./pi-bench single_device_rss_pipeline --ignored --nocapture --test-threads=1" \
  | tee "$RES/rss-pipeline.txt" | grep -E "arch=|baseline|after |PEAK RSS|plateaus|headroom|combiner ="
echo "  -- STEP 2: fleet throughput model --"
ssh "$PI_HOST" "cd $REMOTE_DIR && SHARD_COEFFS=$SHARD_COEFFS ./pi-bench fleet_throughput_model --ignored --nocapture --test-threads=1" \
  | tee "$RES/throughput.txt" | grep -E "arch=|strand |per-signature|fleet size|^\| "

echo
echo "done — results on the Mac in: $RES"
echo "  host.txt        — Pi model / cores / RAM"
echo "  rss-pipeline.txt — peak RSS plateau (the one-Pi RSS-pipeline result)"
echo "  throughput.txt  — per-strand costs + fleet throughput/latency"
