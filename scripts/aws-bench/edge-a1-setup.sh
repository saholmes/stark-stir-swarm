#!/usr/bin/env bash
# edge-a1-setup.sh — one-shot environment setup for the CONSTRAINED-EDGE
# decider/fold benchmark on an AWS a1.medium (Graviton1 = Cortex-A72, the
# Raspberry Pi 4's core), 1 vCPU / 2 GiB RAM.
#
# What it does (idempotent, safe to re-run):
#   1. installs build deps (Ubuntu apt OR Amazon Linux dnf) incl. GNU time,
#   2. adds a swapfile (a 2 GiB box cannot build this workspace, and the
#      N=8192 decider peaks ~1.2 GiB — swap gives headroom without OOM),
#   3. installs a Rust toolchain,
#   4. builds the test binary single-threaded (CARGO_BUILD_JOBS=1) so the
#      compile itself does not OOM on 2 GiB.
#
# Usage (on the a1.medium):
#   ./scripts/aws-bench/edge-a1-setup.sh
#   SWAP_GIB=8 ./scripts/aws-bench/edge-a1-setup.sh    # bigger swap
#
# Then run:  ./scripts/aws-bench/edge-a1-bench.sh
set -euo pipefail

cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
REPO_ROOT="$(cd ../.. && pwd)"
SWAP_GIB="${SWAP_GIB:-6}"

SETUP_T0=$SECONDS
echo "=== STARK-DNS constrained-edge (a1.medium / Cortex-A72) setup ==="
echo "[progress] setup started at $(date -u +%H:%M:%SZ)"
echo "arch=$(uname -m)  cores=$(nproc)  ram=$(free -h 2>/dev/null | awk '/Mem:/{print $2}')"
if [[ "$(uname -m)" != "aarch64" && "$(uname -m)" != "arm64" ]]; then
  echo "WARNING: not an ARM host — this benchmark is meaningful only on Cortex-A72 (a1.*/Pi 4)."
fi

# ─── 1. System packages ─────────────────────────────────────────────────
echo "[setup] installing build dependencies..."
if command -v apt-get >/dev/null 2>&1; then
  sudo apt-get update -qq
  sudo apt-get install -y -qq build-essential clang lld pkg-config libssl-dev git curl ca-certificates time util-linux
elif command -v dnf >/dev/null 2>&1; then
  # Amazon Linux 2023 ships `curl-minimal`; installing full `curl` conflicts with it, and
  # we do NOT need it (curl-minimal already provides the `curl` binary rustup uses). Omit
  # curl; --allowerasing resolves any other minimal-vs-full package conflicts (e.g. gnutls).
  sudo dnf -y -q groupinstall "Development Tools" || sudo dnf -y -q group install "Development Tools" || true
  sudo dnf -y -q --allowerasing install clang lld pkgconfig openssl-devel git time util-linux
else
  echo "[setup] unknown package manager; install: gcc/clang, pkg-config, openssl-dev, git, GNU time, util-linux(taskset)"
fi

# ─── 2. Swap (critical on 2 GiB) ────────────────────────────────────────
if ! swapon --show 2>/dev/null | grep -q '/'; then
  echo "[setup] adding ${SWAP_GIB} GiB swapfile (2 GiB RAM cannot build/prove without it)..."
  sudo fallocate -l "${SWAP_GIB}G" /swapfile 2>/dev/null || sudo dd if=/dev/zero of=/swapfile bs=1M count=$((SWAP_GIB*1024))
  sudo chmod 600 /swapfile
  sudo mkswap /swapfile >/dev/null
  sudo swapon /swapfile
  echo "[setup] swap active: $(swapon --show | tail -n +2)"
else
  echo "[setup] swap already present: $(swapon --show | tail -n +2)"
fi

# ─── 3. Rust toolchain ──────────────────────────────────────────────────
if ! command -v cargo >/dev/null 2>&1; then
  echo "[setup] installing rustup + stable toolchain..."
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
fi
# shellcheck disable=SC1090
source "$HOME/.cargo/env"
echo "[setup] $(rustc --version)  $(cargo --version)"

# ─── 4. Build the test binary (single-threaded so the compile fits 2 GiB) ─
echo "[setup] building test binary (CARGO_BUILD_JOBS=1; this is SLOW on Cortex-A72 — expect 30-90 min)..."
cd "$REPO_ROOT/crates/binius-substrate"
CARGO_BUILD_JOBS=1 CARGO_PROFILE_RELEASE_DEBUG=0 \
  cargo test --release --lib --no-run 2>&1 | tail -5

SETUP_TOTAL=$((SECONDS - SETUP_T0))
echo ""
echo "════════════════════════════════════════════════════════════"
echo "  ✅ SETUP COMPLETE in ${SETUP_TOTAL}s ($((SETUP_TOTAL/60))m $((SETUP_TOTAL%60))s)  at $(date -u +%H:%M:%SZ)"
echo "════════════════════════════════════════════════════════════"
echo "Next:  cd $REPO_ROOT && ./scripts/aws-bench/edge-a1-bench.sh"
# machine-detectable marker for the nohup log:
echo "EDGE_A1_SETUP_COMPLETE status=done seconds=$SETUP_TOTAL"
