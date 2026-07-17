#!/usr/bin/env bash
# Cross-compile the DNS-STARK Pi fleet benchmark ON macOS (Apple Silicon / Mac mini) FOR a
# Raspberry Pi (aarch64 Linux).  The crate is Rust with ONE transitive C dep (`stackalloc`), so
# the only tool needed is `zig` as the cross compiler+linker.
#
# The crate's lib builds only under `cargo test` (mldsa_verify pulls the cfg(test) `reference`
# oracle), so we cross-compile the TEST binary — a standalone executable that carries the
# `single_device_rss_pipeline` and `fleet_throughput_model` `#[ignore]` benchmarks.
#
# cargo-zigbuild has NO `test` subcommand, so we drive `cargo test --no-run` directly and point
# CC / AR / linker at a small `zig cc` shim (generated below).  The shim:
#   * drops cc-rs's rust-triple `--target=aarch64-unknown-linux-musl` (zig can't parse it) and
#     forces zig's own `-target aarch64-linux-musl` — so C deps compile as ELF, not Mach-O;
#   * at link time drops rust's self-contained crt objects + `-nostartfiles` so ONLY zig supplies
#     the musl/glibc startup files (otherwise `_start` is defined twice → duplicate-symbol error).
#
# One-time setup on the Mac:
#   brew install zig            # provides `zig cc` (cross compiler + linker) and `zig ar`
#   (python3 is already present on macOS)
#
# Usage:
#   ./cross-build.sh                                         # default: STATIC musl (any Pi OS)
#   TARGET=aarch64-unknown-linux-gnu.2.31 ./cross-build.sh   # Pi OS Bullseye glibc
#   TARGET=aarch64-unknown-linux-gnu.2.36 ./cross-build.sh   # Pi OS Bookworm glibc
set -euo pipefail
cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
CRATE_DIR="$(cd ../../crates/binius-substrate && pwd)"
TARGET="${TARGET:-aarch64-unknown-linux-musl}"   # static by default → runs on any 64-bit Pi OS
BARE_TARGET="${TARGET%%.*}"                       # strip any .glibc-version suffix for rustup
GLIBC_SUFFIX="${TARGET#"$BARE_TARGET"}"           # e.g. ".2.31" (empty for musl)
OUT="$SCRIPT_DIR/deploy"; mkdir -p "$OUT"

# rust triple -> zig target (zig understands a trailing glibc version, e.g. aarch64-linux-gnu.2.31)
case "$BARE_TARGET" in
  aarch64-unknown-linux-musl) ZIG_TARGET="aarch64-linux-musl" ;;
  aarch64-unknown-linux-gnu)  ZIG_TARGET="aarch64-linux-gnu"  ;;
  *) echo "unsupported TARGET '$TARGET' (use aarch64-unknown-linux-{musl,gnu})"; exit 1 ;;
esac
ZIG_TARGET="$ZIG_TARGET$GLIBC_SUFFIX"

command -v zig     >/dev/null 2>&1 || { echo "missing zig — run:  brew install zig"; exit 1; }
command -v python3 >/dev/null 2>&1 || { echo "missing python3"; exit 1; }
echo "== ensuring rust target $BARE_TARGET =="
rustup target add "$BARE_TARGET" >/dev/null 2>&1 || true

# --- generate the target-aware zig cc / zig ar shims -------------------------------------------
WRAP="$OUT/.zig-shim"; mkdir -p "$WRAP"
cat > "$WRAP/zigcc.py" <<PY
#!/usr/bin/env python3
# zig cc shim for cross-compiling+linking to $ZIG_TARGET from macOS (robust to spaces in paths).
import sys, os
CRT = {'crt1.o','crti.o','crtn.o','crtbegin.o','crtend.o',
       'crtbeginS.o','crtendS.o','Scrt1.o','rcrt1.o'}
args = []
for a in sys.argv[1:]:
    if a.startswith('--target='):     # cc-rs adds the rust triple; zig can't parse it
        continue
    if a == '-nostartfiles':          # let zig own the crt so _start is defined exactly once
        continue
    if os.path.basename(a) in CRT:     # drop rust's self-contained crt objects
        continue
    args.append(a)
os.execvp('zig', ['zig', 'cc', '-target', '$ZIG_TARGET'] + args)
PY
cat > "$WRAP/zigar.py" <<'PY'
#!/usr/bin/env python3
import sys, os
os.execvp('zig', ['zig', 'ar'] + sys.argv[1:])
PY
chmod +x "$WRAP/zigcc.py" "$WRAP/zigar.py"

# --- cross-compile the test binary -------------------------------------------------------------
UNDERSCORE="${BARE_TARGET//-/_}"                       # aarch64_unknown_linux_musl (CC/AR vars)
UPPER="$(printf '%s' "$BARE_TARGET" | tr 'a-z-' 'A-Z_')" # AARCH64_UNKNOWN_LINUX_MUSL (CARGO var)
echo "== cross-compiling the test binary for $TARGET (zig target: $ZIG_TARGET) =="
cd "$CRATE_DIR"
JSON="$(mktemp)"
env \
  "CARGO_TARGET_${UPPER}_LINKER=$WRAP/zigcc.py" \
  "CC_${UNDERSCORE}=$WRAP/zigcc.py" \
  "CXX_${UNDERSCORE}=$WRAP/zigcc.py" \
  "AR_${UNDERSCORE}=$WRAP/zigar.py" \
  cargo test --release --lib --features parallel --no-run \
    --target "$BARE_TARGET" --message-format=json > "$JSON" 2>"$JSON.err" || {
      echo "ERROR: cross build failed — last errors:"; tail -20 "$JSON.err"; exit 1; }

BIN="$(grep -o '"executable":"[^"]*binius_substrate-[^"]*"' "$JSON" | head -1 \
       | sed 's/.*"executable":"//; s/"$//')"
rm -f "$JSON" "$JSON.err"
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

No Rust toolchain needed on the Pi — just the ~15 MB binary.  The default musl target is fully
static (no glibc-version matching); a glibc TARGET requires the Pi OS glibc >= the pinned version.
EOF
