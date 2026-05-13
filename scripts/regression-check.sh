#!/usr/bin/env bash
# regression-check.sh — tripwire that catches regressions in production
# paths during recursive-STARK wrapper development.
#
# Run on every wrapper-stark commit BEFORE merging back to main.
# Exits non-zero on any production-path regression.
#
# Usage:
#   ./scripts/regression-check.sh                # all checks
#   REGCHECK_FAST=1 ./scripts/regression-check.sh  # skip the slow bench cell

set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

# Colors for pass/fail.
GREEN='\033[0;32m'
RED='\033[0;31m'
BOLD='\033[1m'
NC='\033[0m'

declare -i PASS=0 FAIL=0
SECTION=""

section() {
    SECTION="$1"
    printf "\n${BOLD}━━━ %s ━━━${NC}\n" "$SECTION"
}

ok() {
    PASS+=1
    printf "  ${GREEN}✓${NC} %s\n" "$1"
}

fail() {
    FAIL+=1
    printf "  ${RED}✗${NC} %s\n" "$1"
}

# ─── 1. Build sanity ─────────────────────────────────────────────────
section "1. Build sanity (workspace builds clean)"
if cargo check --workspace --all-targets 2>&1 | tee /tmp/regcheck-build.log | tail -5; then
    if grep -q "^error" /tmp/regcheck-build.log; then
        fail "cargo check reported errors"
    else
        ok "workspace builds without errors"
    fi
else
    fail "cargo check exited non-zero"
fi

# ─── 2. Production-path test suites ──────────────────────────────────
section "2. deep_ali test suite (539 non-ignored tests must pass)"
if cargo test --release -p deep_ali --features "parallel sha3-256 mldsa-44" --no-default-features \
    --lib --tests --quiet 2>&1 | tee /tmp/regcheck-deep_ali.log | tail -10; then
    if grep -qE "test result: ok\. [0-9]+ passed" /tmp/regcheck-deep_ali.log; then
        ok "deep_ali tests pass"
    else
        fail "deep_ali tests did not report all-pass"
    fi
else
    fail "deep_ali test suite exited non-zero"
fi

# ─── 3. v2 soundness gates (8 ignored tests, all must still reject ──
#       tampered inputs and accept honest inputs)
section "3. v2 NIZK soundness gates (8 v2_* ignored tests)"
V2_TESTS="v2_real_round_trip v2_l0_regression_rejects_tampered_w_approx \
          v2_l1_gap_intt_canonical_coeff_tampered v2_l4_gap_lies_about_w1bytes \
          v2_l5_regression_v17_rejects_tampered_eq_region v2_session6_ood_l2a_poc"
for t in $V2_TESTS; do
    if cargo test --release -p deep_ali --features "parallel sha3-384 mldsa-65" --no-default-features \
        "$t" -- --ignored --nocapture --test-threads=1 2>&1 | tee /tmp/regcheck-${t}.log | tail -3 \
        | grep -qE "test result: ok\. 1 passed"; then
        ok "$t"
    else
        fail "$t"
    fi
done

# ─── 4. Signature bench smoke (blowup=4, STIR only, ~30s) ────────────
if [ "${REGCHECK_FAST:-0}" != "1" ]; then
    section "4. Signature bench smoke (RSA-2048 + ML-DSA at L3, blowup=4 STIR)"
    BENCH_LDT_ONLY=stir BENCH_BLOWUP=4 bash scripts/bench-all-signatures.sh \
        > /tmp/regcheck-bench.log 2>&1 || true
    if grep -qE "RSA-2048.*prove=[0-9]+ms.*proof=[0-9.]+KiB" /tmp/regcheck-bench.log; then
        ok "RSA-2048 STIR blowup=4 produces a valid proof"
    else
        fail "RSA-2048 bench smoke failed — see /tmp/regcheck-bench.log"
    fi
    if grep -qE "ML-DSA-65.*prove=[0-9]+ms.*proof=[0-9.]+KiB" /tmp/regcheck-bench.log; then
        ok "ML-DSA-65 v2 STIR blowup=4 produces a valid proof"
    else
        fail "ML-DSA-65 v2 bench smoke failed — see /tmp/regcheck-bench.log"
    fi
fi

# ─── 5. Matrix spot-check (Fibonacci L1 SHA3-256 k=14, ~5s) ──────────
section "5. Simple-AIR matrix spot-check (Fibonacci L1 k=14)"
if BENCH_QUERIES=54 BENCH_BLOWUP=32 cargo run --release -p cairo-bench --example simple_air_scaling \
    --features "deep_ali/sha3-256 deep_ali/mldsa-44 deep_ali/parallel" \
    --no-default-features \
    -- --air Fibonacci 14 2>&1 | tee /tmp/regcheck-matrix.log | tail -3 \
    | grep -qE "simple_air_scaling.*prove_ms=[0-9.]+.*proof_kib=[0-9.]+"; then
    ok "matrix Fibonacci L1 k=14 cell still produces valid measurement"
else
    fail "matrix Fibonacci L1 k=14 spot-check failed — see /tmp/regcheck-matrix.log"
fi

# ─── 6. Summary ──────────────────────────────────────────────────────
section "Regression check summary"
TOTAL=$((PASS + FAIL))
printf "  Passed: ${GREEN}%d${NC} / %d\n" "$PASS" "$TOTAL"
if [ "$FAIL" -gt 0 ]; then
    printf "  Failed: ${RED}%d${NC} / %d\n" "$FAIL" "$TOTAL"
    printf "\n${RED}${BOLD}REGRESSION DETECTED${NC} — wrapper-stark work introduced a regression\n"
    printf "in a production path.  Inspect logs in /tmp/regcheck-*.log before\n"
    printf "merging to main.\n"
    exit 1
fi

printf "\n${GREEN}${BOLD}ALL PRODUCTION PATHS GREEN${NC} — safe to commit wrapper-stark changes.\n"
exit 0
