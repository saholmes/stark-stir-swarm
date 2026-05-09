#!/usr/bin/env bash
# Idempotent AWS c5.4xlarge environment setup.
# Installs: rustup toolchain (stable + 1.79 minimum), build-essential,
# clang, perf (for RSS reporting), git LFS (some submodules use it).
#
# Safe to re-run.  Exits non-zero on any failure.

set -euo pipefail

cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"
REPO_ROOT="$(cd ../.. && pwd)"

echo "=== AWS bench setup ==="
echo "Repo root: $REPO_ROOT"
echo "Script dir: $SCRIPT_DIR"

# ─── 1. System packages ──────────────────────────────────────────
if [[ "$(uname)" == "Linux" ]]; then
    if [ -f /etc/os-release ] && grep -qi "ubuntu\|debian" /etc/os-release; then
        echo "[setup] Installing apt packages..."
        sudo apt-get update -qq
        sudo apt-get install -y -qq \
            build-essential clang lld pkg-config libssl-dev \
            git git-lfs curl ca-certificates \
            linux-tools-common linux-tools-generic \
            time
    else
        echo "[setup] Non-apt Linux detected; install build-essential / clang / git-lfs manually."
    fi
elif [[ "$(uname)" == "Darwin" ]]; then
    echo "[setup] macOS detected; assuming Xcode CLT installed."
    if ! command -v brew &> /dev/null; then
        echo "[setup] Homebrew not found; install from https://brew.sh first."
        exit 1
    fi
    brew install -q git-lfs gnu-time || true
fi

# ─── 2. Rust toolchain ───────────────────────────────────────────
if ! command -v rustup &> /dev/null; then
    echo "[setup] Installing rustup..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
    # shellcheck source=/dev/null
    source "$HOME/.cargo/env"
fi

# Ensure stable + 1.79 (workspace MSRV)
rustup install stable
rustup default stable
rustc --version

# ─── 3. Pre-build (optimised release, parallel feature) ─────────
cd "$REPO_ROOT"
echo "[setup] Pre-building deep_ali (release, parallel, sha3-256)..."
cargo build --release -p deep_ali \
    --features "parallel sha3-256 mldsa-44" --no-default-features

echo "[setup] Pre-building cairo-bench..."
cargo build --release -p cairo-bench

echo "[setup] Pre-building swarm-dns..."
cargo build --release -p swarm-dns

# ─── 4. Bench results dir ────────────────────────────────────────
mkdir -p "$SCRIPT_DIR/results"
echo "[setup] Results will be written to: $SCRIPT_DIR/results/"

echo "=== Setup complete ==="
echo "Next: ./run-all.sh"
