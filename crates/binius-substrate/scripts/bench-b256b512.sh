#!/usr/bin/env bash
#
# bench-b256b512.sh — PART 1 RSS baseline. Prove-time + peak-RSS scaling sweep for
# raw Keccak-f[1600] permutations over the NIST tower fields:
#   * B256TowerFamily at security_bits=128  (NIST L1)
#   * B512TowerFamily at security_bits=256  (NIST L5)
# under the FIPS SHA-256 Merkle commitment + SHA-256 Fiat-Shamir transcript,
# blowup=2 (log_inv_rate=1) — the exact wiring the b256_keccak / b512_keccak gates
# already verify.
#
# GOAL: establish the concrete "<1 GB per proof?" datapoint. A single Binius proof
# is one process; the S-strand architecture keeps each strand's process under the
# ~1 GB IoT budget by proving each strand SEPARATELY. The peak RSS numbers below
# tell us the per-level strand granularity G (how many Keccak-f perms fit under
# 1 GB) that the signature-AIR port must respect.
#
# Peak RSS: on macOS `/usr/bin/time -l` reports "maximum resident set size" in
# BYTES (Linux reports KB — this script assumes macOS / bytes). We run the built
# release binary DIRECTLY under `/usr/bin/time -l` (never `cargo run`, which would
# mask the prover's RSS with cargo's own).
#
# Usage:  scripts/bench-b256b512.sh
#         B256_SWEEP="8 64 256 1024" B512_SWEEP="8 64" scripts/bench-b256b512.sh
#
# Machine notes: Binius proving is rayon-parallel; RAYON_NUM_THREADS is echoed in
# the header for the record.

set -euo pipefail

# Resolve the crate dir (this script lives in <crate>/scripts/).
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${CRATE_DIR}"

BIN="${CRATE_DIR}/target/release/bench_b256b512"

# b256 is ~16x lighter per row than b512, so sweep it further.
B256_SWEEP="${B256_SWEEP:-8 64 256}"
B512_SWEEP="${B512_SWEEP:-8 64}"
B256_SEC="${B256_SEC:-128}"   # NIST L1
B512_SEC="${B512_SEC:-256}"   # NIST L5

echo "# binius-substrate — PART 1 RSS baseline: raw Keccak-f[1600] over NIST tower fields"
echo "# B256 @ sec=${B256_SEC} (NIST L1), B512 @ sec=${B512_SEC} (NIST L5), blowup=2 (log_inv_rate=1)"
echo "#"
echo "# machine: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown), $(sysctl -n hw.ncpu 2>/dev/null || echo '?') cores"
echo "# RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-<unset: rayon uses all cores>}"
echo "# b256 sweep: N in { ${B256_SWEEP} }; b512 sweep: N in { ${B512_SWEEP} }"
echo "#"

# Build the binary release (once).
echo "# building bench_b256b512 (release)…" 1>&2
cargo build --release --bin bench_b256b512 1>&2

if [[ ! -x "${BIN}" ]]; then
	echo "ERROR: built binary not found at ${BIN}" 1>&2
	exit 1
fi

# Markdown table header.
echo "| field | N | sec | prove_ms | verify_ms | proof_bytes | peak_RSS_MiB |"
echo "|:---|---:|---:|---:|---:|---:|---:|"

run_one() {
	local FIELD="$1" N="$2" SEC="$3"
	local OUT ERR
	OUT="$(mktemp)"
	ERR="$(mktemp)"

	# `/usr/bin/time -l` writes its report to STDERR, the program's RESULT line to
	# STDOUT. Capture them into separate temp files.
	/usr/bin/time -l "${BIN}" "${FIELD}" "${N}" "${SEC}" >"${OUT}" 2>"${ERR}"

	local RESULT_LINE
	RESULT_LINE="$(grep '^RESULT ' "${OUT}" || true)"
	if [[ -z "${RESULT_LINE}" ]]; then
		echo "ERROR: no RESULT line for field=${FIELD} N=${N}; stderr was:" 1>&2
		cat "${ERR}" 1>&2
		rm -f "${OUT}" "${ERR}"
		exit 1
	fi

	local get
	get() { echo "${RESULT_LINE}" | tr ' ' '\n' | grep "^$1=" | cut -d= -f2; }
	local ACTUAL_N PROVE_MS VERIFY_MS PROOF_BYTES
	ACTUAL_N="$(get N)"
	PROVE_MS="$(get prove_ms)"
	VERIFY_MS="$(get verify_ms)"
	PROOF_BYTES="$(get proof_bytes)"

	# macOS: "maximum resident set size" is in BYTES → MiB.
	local RSS_BYTES RSS_MIB
	RSS_BYTES="$(grep 'maximum resident set size' "${ERR}" | awk '{print $1}')"
	RSS_MIB="$(awk -v b="${RSS_BYTES:-0}" 'BEGIN{ printf "%.1f", b/1048576 }')"

	echo "| ${FIELD} | ${ACTUAL_N} | ${SEC} | ${PROVE_MS} | ${VERIFY_MS} | ${PROOF_BYTES} | ${RSS_MIB} |"

	rm -f "${OUT}" "${ERR}"
}

for N in ${B256_SWEEP}; do
	run_one b256 "${N}" "${B256_SEC}"
done
for N in ${B512_SWEEP}; do
	run_one b512 "${N}" "${B512_SEC}"
done

echo "#"
echo "# Reminder: peak_RSS_MiB is the whole-process peak resident set of ONE proof."
echo "# The <1 GB (1024 MiB) line is the per-strand IoT budget: the largest N whose"
echo "# row stays under it sets the strand granularity G for that NIST level."
