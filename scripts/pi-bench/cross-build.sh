#!/usr/bin/env bash
# Cross-compile the DNS-STARK Pi fleet benchmark ON macOS (Apple Silicon / Mac mini) FOR a
# Raspberry Pi (aarch64 Linux).  The crate is PURE RUST (no C build deps) and `peak_rss_bytes`
# already normalises Linux's kilobyte ru_maxrss, so this is a clean cross-compile — the only
# tool needed is a cross-linker, provided by `zig` via `cargo-zigbuild`.
#
# The crate's lib builds only under `cargo test` (mldsa_verify pulls the cfg(test) `reference`
# oracle), so we cross-compile the TEST binary — it is a standalone executable that carries the
# `single_device_rss_pipeline` and `fleet_throughput_model` `#[ignore]` benchmarks.
#
# One-time setup on the Mac:
#   brew install zig
#   cargo install cargo-zigbuild
#
# Usage:
#   ./cross-build.sh                       # default: glibc target for Pi OS Bullseye (2.31)
#   TARGET=aarch64-unknown-linux-gnu.2.36 ./cross-build.sh   # Pi OS Bookworm glibc
#   TARGET=aarch64-unknown-linux-musl ./cross-build.sh       # STATIC binary (runs on any Pi OS)
set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
CRATE_DIR="$(cd ../../crates/binius-substrate && pwd)"
TARGET="${TARGET:-aarch64-unknown-linux-gnu.2.31}"
BARE_TARGET="${TARGET%%.*}"          # strip any .glibc-version suffix for rustup
OUT="$SCRIPT_DIR/deploy"; mkdir -p "$OUT"

command -v zig            >/dev/null 2>&1 || { echo "missing zig — run:  brew install zig"; exit 1; }
command -v cargo-zigbuild >/dev/null 2>&1 || { echo "missing cargo-zigbuild — run:  cargo install cargo-zigbuild"; exit 1; }
echo "== ensuring rust target $BARE_TARGET =="
rustup target add "$BARE_TARGET" >/dev/null 2>&1 || true

echo "== cross-compiling the test binary for $TARGET (this is the deployable benchmark) =="
cd "$CRATE_DIR"
BIN="$(cargo zigbuild test --release --lib --features parallel --no-run \
        --target "$TARGET" --message-format=json 2>/dev/null \
      | grep -o '"executable":"[^"]*binius_substrate-[^"]*"' | head -1 \
      | sed 's/.*"executable":"//; s/"$//')"
[ -n "${BIN:-}" ] && [ -f "$BIN" ] || { echo "ERROR: cross build produced no test binary"; exit 1; }

cp "$BIN" "$OUT/pi-bench"
chmod +x "$OUT/pi-bench"
echo "cross-built: $OUT/pi-bench"
file "$OUT/pi-bench" 2>/dev/null | sed 's/^/  /'
ls -lh "$OUT/pi-bench" | awk '{print "  size: "$5}'

cat <<EOF

deploy + run on the Pi (aarch64 64-bit Pi OS):
  scp $OUT/pi-bench pi@raspberrypi:~/
  # STEP 1 — the one-Pi RSS pipeline (peak RSS ~ one strand):
  ssh pi@raspberrypi 'SHARD_COEFFS=16 ./pi-bench single_device_rss_pipeline --ignored --nocapture --test-threads=1'
  # STEP 2 — the throughput/wall model (sizes the fleet):
  ssh pi@raspberrypi 'SHARD_COEFFS=32 ./pi-bench fleet_throughput_model  --ignored --nocapture --test-threads=1'

No Rust toolchain needed on the Pi — just the ~20 MB binary (musl target = fully static; glibc
target requires the Pi OS glibc ≥ the version in TARGET).
EOF
