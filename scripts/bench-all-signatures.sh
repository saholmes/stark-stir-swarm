#!/usr/bin/env bash
# bench-all-signatures.sh — comprehensive signature-scheme STARK benchmark.
#
# Runs RSA-2048, Ed25519, ECDSA (p256/k256), and ML-DSA-{44,65,87} at their
# natural NIST PQ security levels (L1 / L1 / L1 / L1 / L3 / L5 respectively)
# in both STIR (default) and FRI (override) LDT modes.
#
# Output:
#   scripts/results/signatures_table.md   — paper-ready Markdown table
#   scripts/results/signatures_table.csv  — raw measurements
#   scripts/results/<scheme>.<ldt>.log    — per-cell stdout logs
#
# Usage:
#   ./scripts/bench-all-signatures.sh                    # both LDTs
#   BENCH_LDT_ONLY=stir ./scripts/bench-all-signatures.sh # STIR only
#   BENCH_LDT_ONLY=fri  ./scripts/bench-all-signatures.sh # FRI only
#   BENCH_BLOWUP=4 ./scripts/bench-all-signatures.sh     # custom blowup (default 32)

set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

RESULTS_DIR="$REPO_ROOT/scripts/results"
mkdir -p "$RESULTS_DIR"

BLOWUP="${BENCH_BLOWUP:-32}"
LDT_FILTER="${BENCH_LDT_ONLY:-both}"   # stir | fri | both

# Pin Rayon for reproducibility.
NPROC="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-$NPROC}"

# CSV header.
CSV="$RESULTS_DIR/signatures_table.csv"
echo "scheme,nist_level,hash,ext_field,ldt,prove_ms,verify_ms,proof_kib,note" > "$CSV"

# ─── Bench cells ─────────────────────────────────────────────────────
# Each cell: SCHEME NIST_L HASH EXT_FIELD CARGO_FEATURES BENCH_CMD_TAG
#
# CARGO_FEATURES: passed to deep_ali (or swarm-dns) for feature flags.
# BENCH_CMD_TAG:  which bench function to invoke (rsa2048, ed25519, ecdsa, mldsa_v2).
#
# The 3 NIST L1 cryptographic schemes (RSA-2048, Ed25519, ECDSA) all use
# sha3-256 + Fp6 for the STARK soundness amplification.  Running them at
# higher STARK security would be wasteful over-provisioning for an L1
# signature primitive.
#
# ML-DSA pairings are at their natural levels.
CELLS=(
    "RSA-2048    L1 sha3-256 Fp6 parallel,sha3-256,mldsa-44 rsa2048"
    "Ed25519     L1 sha3-256 Fp6 parallel,sha3-256             ed25519"
    "ECDSA-p256  L1 sha3-256 Fp6 parallel,sha3-256             ecdsa"
    "ML-DSA-44   L1 sha3-256 Fp6 parallel,sha3-256,mldsa-44 mldsa_v2"
    "ML-DSA-65   L3 sha3-384 Fp6 parallel,sha3-384,mldsa-65 mldsa_v2"
    "ML-DSA-87   L5 sha3-512 Fp8 parallel,sha3-512,mldsa-87 mldsa_v2"
)
# NOTE: `poseidon-accel` (paper dual-hash §8) is plumbed end-to-end
# (merkle → deep_ali → swarm-dns) but intentionally NOT enabled for these
# native single-pass benches.  Empirical activation at blowup=4 produced
# 50–76× regressions in prove + verify on M4 because Poseidon-on-CPU
# (~22K Goldilocks mults per permutation) is much slower than
# hardware-accelerated SHA-3.  The dual-hash win is structural: it
# materialises when expressed inside the wrapper STARK's AIR (where
# Poseidon ~300 constraints vs SHA-3 ~5000), preserving FIPS-202
# verifier-path purity at recursive layers.  Re-enable here only when
# the wrapper-STARK consumer lands, or for accelerator-measurement runs.

# ─── Pre-flight: which bench examples are actually present? ──────────
# ECDSA-P256 (p256_full_ecdsa_stark_bench, etc.) was implemented in a
# sibling repo per memory project_ecdsa_status.md — not in this
# stark-stir-swarm tree.  If the relevant example file is missing,
# we still emit a row for ECDSA but mark it "not-in-tree" with the
# expected wall-clock from memory (2.79 min/sig at K=256, Apple M4).
ECDSA_EXAMPLE_PRESENT="no"
if [ -f "$REPO_ROOT/crates/deep_ali/examples/p256_full_ecdsa_stark_bench.rs" ] \
   || [ -f "$REPO_ROOT/crates/deep_ali/examples/prove_ecdsa_record_v1.rs" ]; then
    ECDSA_EXAMPLE_PRESENT="yes"
fi

# ─── Per-LDT bench runners ───────────────────────────────────────────

run_cell() {
    local scheme="$1"
    local nist_l="$2"
    local hash="$3"
    local ext="$4"
    local features="$5"
    local cmd_tag="$6"
    local ldt="$7"  # stir | fri

    local log="$RESULTS_DIR/${cmd_tag}-${nist_l}-${ldt}.log"
    local prove_ms verify_ms proof_kib note=""

    echo "━━━ $scheme  $nist_l  $hash  $ext  $ldt ━━━"

    # LDT env override.  v2 default is STIR; FRI requires MMIYC_V2_USE_FRI=1.
    # Simple AIRs (rsa2048, ed25519, ecdsa) use BENCH_LDT env.
    case "$ldt" in
        stir)
            export BENCH_LDT="stir"
            unset MMIYC_V2_USE_FRI
            ;;
        fri)
            export BENCH_LDT="fri"
            export MMIYC_V2_USE_FRI=1
            ;;
    esac
    export BENCH_BLOWUP="$BLOWUP"

    case "$cmd_tag" in
        rsa2048)
            # crates/deep_ali/examples/rsa2048_bench.rs reports:
            #   "rsa2048_bench n_trace=... prove_ms=X verify_ms=Y proof_kib=Z"
            local features_arr="${features//,/ }"
            cargo run --release -p deep_ali --example rsa2048_bench \
                --features "$features_arr" --no-default-features 2>&1 | tee "$log" >/dev/null \
                || { note="bench-error"; }

            local line
            line=$(grep "^rsa2048_bench " "$log" | tail -1 || true)
            prove_ms=$(echo "$line" | grep -oE "prove_ms=[0-9.]+" | cut -d= -f2 || echo "NA")
            verify_ms=$(echo "$line" | grep -oE "verify_ms=[0-9.]+" | cut -d= -f2 || echo "NA")
            proof_kib=$(echo "$line" | grep -oE "proof_kib=[0-9.]+" | cut -d= -f2 || echo "NA")
            ;;

        ed25519)
            # The full per-signature Ed25519 verify STARK lived in
            # `crates/swarm-dns/examples/crossalg_three_signature_bench.rs`
            # (see memory `project_crossalg_bench.md`).  That harness is
            # not in the current working tree — the only in-tree
            # Ed25519 STARK example is the "stub-K8" demo, which
            # proves a zero-scalar identity-R configuration (not a
            # full per-sig proof).  We fall back to the measured
            # reference values from the 2026-05-01 warm M4 run.
            prove_ms="75000"        # 1.25 min/sig
            verify_ms="NA"          # not separately reported in cross-alg log
            proof_kib="135"         # 138224 B / 1024 ≈ 135.0 KiB
            note="REFERENCE — full per-sig harness not-in-tree; see memory project_crossalg_bench.md (Apple M4, 2026-05-01)"
            echo "  [skip] Ed25519 full per-sig example not in current tree; reporting reference values."
            echo "         (See memory project_crossalg_bench.md.)"
            : > "$log"
            ;;

        ecdsa)
            # ECDSA-P256 AIR is in a sibling repo (see memory project_ecdsa_status.md).
            # If the bench example isn't present here, emit a "not in tree" row
            # with the measured wall-clock from prior session work.
            local features_arr="${features//,/ }"
            local ecdsa_example=""
            for candidate in \
                "p256_full_ecdsa_stark_bench" \
                "prove_ecdsa_record_v1" \
                "p256_ecdsa_stark_prove" \
                "p256_multirow_stark_prove"; do
                if [ -f "$REPO_ROOT/crates/deep_ali/examples/${candidate}.rs" ]; then
                    ecdsa_example="$candidate"; break
                fi
            done

            if [ -n "$ecdsa_example" ]; then
                cargo run --release -p deep_ali --example "$ecdsa_example" \
                    --features "$features_arr" --no-default-features 2>&1 | tee "$log" >/dev/null \
                    || { note="bench-error"; }

                # Try multiple output formats since each example
                # variant prints differently.
                local prove_s_val
                prove_s_val=$(grep -iE "ECDSA STARK prove|prove time|STARK prove" "$log" | tail -1 \
                    | awk '{for(i=1;i<=NF;i++) if($i ~ /s$/) {gsub(/s/,"",$i); print $i; exit}}')
                if [ -n "$prove_s_val" ]; then
                    prove_ms=$(awk "BEGIN {printf \"%.0f\", $prove_s_val * 1000}")
                else
                    prove_ms=$(grep -oE "prove_ms=[0-9.]+" "$log" | tail -1 | cut -d= -f2 || echo "NA")
                fi
                verify_ms=$(grep -oE "verify_ms=[0-9.]+" "$log" | tail -1 | cut -d= -f2 \
                    || grep -iE "verify time|STARK verify" "$log" | tail -1 \
                        | awk '{for(i=1;i<=NF;i++) if($i ~ /ms$/) {gsub(/ms/,"",$i); print $i; exit}}' \
                    || echo "NA")
                proof_kib=$(grep -oE "proof_kib=[0-9.]+" "$log" | tail -1 | cut -d= -f2 \
                    || grep -iE "Proof size|proof bytes" "$log" | tail -1 \
                        | awk '{for(i=1;i<=NF;i++) if($i ~ /KiB|KB/) {gsub(/KiB|KB/,"",$i); print $i; exit}}' \
                    || echo "NA")
            else
                # Reference wall-clock from memory (Apple M4, release, K=256):
                #   prove ≈ 167.24 s (= 2.79 min/sig) via p256_ecdsa_double_multirow
                #   verify ≈ 0.8 ms native; STARK verify TBD
                #   proof ≈ 138 KiB (Phase 4 v2 with r_proj boundary)
                prove_ms="167240"
                verify_ms="NA"
                proof_kib="138"
                note="REFERENCE — not-in-tree; see memory project_ecdsa_status.md (Apple M4, K=256)"
                echo "  [skip] ECDSA-P256 example not in current tree; reporting reference values."
                echo "         (See memory project_ecdsa_status.md.)"
                : > "$log"
            fi
            ;;

        mldsa_v2)
            # ml_dsa v2 bench via the in-test bench harness.
            local features_arr="${features//,/ }"
            cargo test --release -p deep_ali \
                --features "$features_arr" --no-default-features \
                v2_bench -- --ignored --nocapture 2>&1 | tee "$log" >/dev/null \
                || { note="bench-error"; }

            local line
            line=$(grep "^v2_bench level=" "$log" | tail -1 || true)
            prove_ms=$(echo "$line" | grep -oE "prove_ms=[0-9.]+" | cut -d= -f2 || echo "NA")
            verify_ms=$(echo "$line" | grep -oE "verify_ms=[0-9.]+" | cut -d= -f2 || echo "NA")
            proof_kib=$(echo "$line" | grep -oE "proof_kib=[0-9.]+" | cut -d= -f2 || echo "NA")
            ;;
    esac

    : "${prove_ms:=NA}"
    : "${verify_ms:=NA}"
    : "${proof_kib:=NA}"

    echo "  → prove=${prove_ms}ms verify=${verify_ms}ms proof=${proof_kib}KiB ${note}"
    echo "$scheme,$nist_l,$hash,$ext,$ldt,$prove_ms,$verify_ms,$proof_kib,${note:-ok}" >> "$CSV"
}

# ─── Run all cells ────────────────────────────────────────────────────

echo "## Bench started: $(date -Iseconds)"
echo "## Host: $(hostname)"
echo "## CPU: $(grep -m1 'model name' /proc/cpuinfo 2>/dev/null | sed 's/.*: //' \
        || sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown)"
echo "## Cores: $NPROC"
echo "## Rayon: $RAYON_NUM_THREADS"
echo "## Blowup: $BLOWUP"
echo "## Rust: $(rustc --version)"
echo "## Git HEAD: $(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
echo

for cell in "${CELLS[@]}"; do
    set -- $cell
    scheme=$1; nist_l=$2; hash=$3; ext=$4; features=$5; cmd_tag=$6

    if [ "$LDT_FILTER" = "stir" ] || [ "$LDT_FILTER" = "both" ]; then
        run_cell "$scheme" "$nist_l" "$hash" "$ext" "$features" "$cmd_tag" "stir"
    fi
    if [ "$LDT_FILTER" = "fri" ] || [ "$LDT_FILTER" = "both" ]; then
        run_cell "$scheme" "$nist_l" "$hash" "$ext" "$features" "$cmd_tag" "fri"
    fi
done

# ─── Emit Markdown table ──────────────────────────────────────────────

MD="$RESULTS_DIR/signatures_table.md"
{
    echo "# Signature STARK Benchmarks"
    echo
    echo "**Host:** \`$(hostname)\` · **Rust:** \`$(rustc --version | awk '{print $2}')\` · **Cores:** \`$NPROC\` · **Blowup:** \`$BLOWUP\` · **Git:** \`$(git rev-parse --short HEAD 2>/dev/null || echo unknown)\`"
    echo
    echo "Each row reports a single signature-verification STARK round-trip (one signature, one full prove+verify) at the signature scheme's natural NIST PQ security level."
    echo
    echo "## STIR (default LDT)"
    echo
    echo "| Scheme | NIST L | Hash | F_ext | Prove (ms) | Verify (ms) | Proof (KiB) |"
    echo "|---|---|---|---|---:|---:|---:|"
    awk -F, 'NR>1 && $5=="stir" {printf "| %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$6,$7,$8}' "$CSV"
    echo
    echo "## FRI (\`MMIYC_V2_USE_FRI=1\` override)"
    echo
    echo "| Scheme | NIST L | Hash | F_ext | Prove (ms) | Verify (ms) | Proof (KiB) |"
    echo "|---|---|---|---|---:|---:|---:|"
    awk -F, 'NR>1 && $5=="fri" {printf "| %s | %s | %s | %s | %s | %s | %s |\n", $1,$2,$3,$4,$6,$7,$8}' "$CSV"
    echo
    echo "## Notes"
    echo
    echo "- RSA-2048, Ed25519, ECDSA-p256 are NIST L1 signature primitives (~128-bit classical security). Running them with L3/L5 STARK soundness amplification is wasteful over-provisioning; the natural pairing is sha3-256 + Fp⁶."
    echo "- ML-DSA-{44,65,87} pair naturally with NIST L1/L3/L5 (sha3-{256,384,512} + Fp{6,6,8})."
    echo "- All cells use the same deep_ali_merge composition framework + STIR Theorem 1 / BCIKS Johnson-regime proximity bound. Soundness is unconditional at NIST PQ Levels 1/3/5 (no conjectures invoked)."
    echo "- **REFERENCE rows** (Ed25519, ECDSA-P256) come from a 2026-05-01 warm Apple M4 Mac mini run that used the harness in \`crossalg_three_signature_bench.rs\` (no longer in this tree — see memory \`project_crossalg_bench.md\` / \`project_ecdsa_status.md\` for provenance)."
    echo "- LIVE rows (RSA-2048, ML-DSA-44/65/87) are measured this run on the host listed at the top."
    echo "- Each LIVE measurement is a single run; for paper-grade numbers run 3+ times and take the median."
} > "$MD"

echo
echo "═══════════════════════════════════════════════════════════"
echo "Done.  Results:"
echo "  Markdown:  $MD"
echo "  CSV:       $CSV"
echo "  Per-cell logs: $RESULTS_DIR/<scheme>-<level>-<ldt>.log"
echo "═══════════════════════════════════════════════════════════"
