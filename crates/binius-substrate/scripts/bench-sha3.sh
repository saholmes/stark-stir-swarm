#!/usr/bin/env bash
#
# bench-sha3.sh — prove-time + peak-RSS scaling sweep for the M2a in-circuit
# SHA3-256 gadget on Binius, at blowup=4 (log_inv_rate=2), security_bits=100.
#
# ============================ HONEST COMPARISON FRAMING =====================
# Goldilocks baseline (the paper): 221 s of PROVE time to bind a B=10 subset of
# 810 in-AIR SHA-3 Merkle-path openings (smoke L1, blowup=4, on an M4).
#
# The Binius unit measured HERE: prove time for N in-circuit SHA3-256 single-
# block Keccak-f[1600] permutations (each ≈ one Keccak-256 node hash). A B=10
# Merkle-path binding is ~10 × (path-depth) such node hashes.
#
# THIS IS AN INDICATIVE CROSS-SYSTEM DATAPOINT, NOT AN APPLES-TO-APPLES NUMBER:
#   * different fields (Goldilocks p≈2^64 vs Binius binary-tower / B128),
#   * different proof systems (FRI-STARK AIR vs Binius M3 + FRI),
#   * the 221 s includes Merkle-PATH STRUCTURE + binding, not raw hashing alone.
# So we report the PER-HASH ms and PEAK RSS on Binius and let the reader scale
# it. We deliberately do NOT print a single triumphant "Nx faster".
# ============================================================================
#
# Peak RSS: on macOS `/usr/bin/time -l` reports "maximum resident set size" in
# BYTES (Linux reports KB — this script assumes macOS / bytes). We run the built
# release binary DIRECTLY under `/usr/bin/time -l` (never `cargo run`, which would
# mask the prover's RSS with cargo's own).
#
# Usage:  scripts/bench-sha3.sh              # default sweep
#         N_SWEEP="8 64 256 1024" scripts/bench-sha3.sh   # custom sweep
#
# Machine notes: developed/measured on an Apple M4 (10 cores). Binius proving is
# rayon-parallel; RAYON_NUM_THREADS is echoed in the header for the record.

set -euo pipefail

# Resolve the crate dir (this script lives in <crate>/scripts/).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${CRATE_DIR}"

BIN="${CRATE_DIR}/target/release/bench_sha3"
LOG_INV_RATE="${LOG_INV_RATE:-2}"            # blowup = 2^LOG_INV_RATE = 4
N_SWEEP="${N_SWEEP:-8 64 256 1024 4096}"     # add 16384 once the small ones prove fast

echo "# binius-substrate — in-circuit SHA3-256 prove/verify scaling (blowup=$((1 << LOG_INV_RATE)), security_bits=100)"
echo "#"
echo "# machine: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown), $(sysctl -n hw.ncpu 2>/dev/null || echo '?') cores"
echo "# RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-<unset: rayon uses all cores>}"
echo "# sweep: N in { ${N_SWEEP} }"
echo "#"

# Build the binary release (once).
echo "# building bench_sha3 (release)…" 1>&2
cargo build --release --bin bench_sha3 1>&2

if [[ ! -x "${BIN}" ]]; then
	echo "ERROR: built binary not found at ${BIN}" 1>&2
	exit 1
fi

# Markdown table header.
echo "| N | prove_ms | ms/hash | verify_ms | proof_bytes | peak_RSS_MiB |"
echo "|---:|---:|---:|---:|---:|---:|"

for N in ${N_SWEEP}; do
	# `/usr/bin/time -l` writes its report to STDERR, the program's RESULT line to
	# STDOUT. Capture them into separate temp files.
	OUT="$(mktemp)"
	ERR="$(mktemp)"
	/usr/bin/time -l "${BIN}" "${N}" "${LOG_INV_RATE}" >"${OUT}" 2>"${ERR}"

	RESULT_LINE="$(grep '^RESULT ' "${OUT}" || true)"
	if [[ -z "${RESULT_LINE}" ]]; then
		echo "ERROR: no RESULT line for N=${N}; stderr was:" 1>&2
		cat "${ERR}" 1>&2
		rm -f "${OUT}" "${ERR}"
		exit 1
	fi

	# Parse key=value fields from the RESULT line.
	get() { echo "${RESULT_LINE}" | tr ' ' '\n' | grep "^$1=" | cut -d= -f2; }
	PROVE_MS="$(get prove_ms)"
	VERIFY_MS="$(get verify_ms)"
	PROOF_BYTES="$(get proof_bytes)"
	MS_PER_HASH="$(get ms_per_hash)"

	# macOS: "maximum resident set size" is in BYTES → MiB.
	RSS_BYTES="$(grep 'maximum resident set size' "${ERR}" | awk '{print $1}')"
	RSS_MIB="$(awk -v b="${RSS_BYTES:-0}" 'BEGIN{ printf "%.1f", b/1048576 }')"

	echo "| ${N} | ${PROVE_MS} | ${MS_PER_HASH} | ${VERIFY_MS} | ${PROOF_BYTES} | ${RSS_MIB} |"

	rm -f "${OUT}" "${ERR}"
done

echo "#"
echo "# Reminder: per-hash ms above is Binius in-circuit SHA3-256 prover cost."
echo "# The Goldilocks baseline is 221 s to bind a B=10 subset of 810 in-AIR"
echo "# SHA-3 Merkle-path openings (smoke L1, blowup=4). Different fields / proof"
echo "# systems — scale the per-hash number yourself; this is indicative, not"
echo "# apples-to-apples."
