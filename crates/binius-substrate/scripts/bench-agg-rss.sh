#!/usr/bin/env bash
#
# bench-agg-rss.sh — PART 2 Tier-A AGGREGATION RSS. Peak-RSS scaling sweep for the
# LEVEL-1 aggregation tier under the strand/swarm model with small STITCHABLE
# proof circuits, over B256 at NIST L1 (security_bits=128, blowup=2).
#
# The Tier-A shape (prove-R-1b/1c, prove-D-epoch): a zone of N records is proven as
# N SEPARATE bounded strand proofs (`prove_verify_sha3_b256`), the coordinator
# folds their 32-byte roots NATIVELY into R* (`merkle_root_sha3`), and one
# in-circuit master join binds a root into the tree (`prove_verify_join_b256`). The
# strands prove one-at-a-time, so the process holds only one witness at any moment.
#
# CLAIM UNDER TEST: peak RSS == the largest SINGLE stitchable proof and is
# INDEPENDENT of the zone size N. The peak_RSS_MiB column should stay FLAT across
# the sweep while leaf_total_ms grows ~linearly in N — the swarm/edge payoff: an
# edge aggregator folds an arbitrarily large zone under ONE strand's memory budget.
#
# HOW IT RUNS (crate build path): this detached crate only builds under
# `cargo test --lib` (several non-test modules import dev-dep-backed native
# references at module scope), so the RSS row is the `#[ignore]`d `agg_rss_row`
# test. We build the lib TEST binary ONCE, then run it DIRECTLY under
# `/usr/bin/time -l` once per N (never `cargo test`, whose own RSS would mask the
# prover's), passing the zone size via the AGG_N env var.
#
# Peak RSS: on macOS `/usr/bin/time -l` reports "maximum resident set size" in
# BYTES. The test-harness overhead is small and CONSTANT across N, so it does not
# affect the flatness of the column.
#
# Usage:  scripts/bench-agg-rss.sh
#         AGG_SWEEP="2 8 32 128 512" scripts/bench-agg-rss.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${CRATE_DIR}"

AGG_SWEEP="${AGG_SWEEP:-2 8 32 128}"
AGG_SEC="${AGG_SEC:-128}"   # NIST L1
TEST_PATH="bench::tests::agg_rss_row"

echo "# binius-substrate — PART 2 Tier-A aggregation RSS: N-record zone over B256"
echo "# strand/swarm model (N bounded strands + native fold + 1 master join)"
echo "# sec=${AGG_SEC} (NIST L1), blowup=2 (log_inv_rate=1)"
echo "#"
echo "# machine: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown), $(sysctl -n hw.ncpu 2>/dev/null || echo '?') cores"
echo "# RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-<unset: rayon uses all cores>}"
echo "# sweep: N in { ${AGG_SWEEP} }"
echo "#"

# Build the lib TEST binary once and capture its path from cargo's JSON output.
echo "# building lib test binary (release)…" 1>&2
BIN="$(cargo test --release --lib --no-run --message-format=json 2>/dev/null \
	| /usr/bin/python3 -c '
import sys, json
for line in sys.stdin:
    try:
        m = json.loads(line)
    except ValueError:
        continue
    t = m.get("target", {})
    if m.get("reason") == "compiler-artifact" \
       and t.get("test") \
       and "lib" in t.get("kind", []) \
       and m.get("executable"):
        print(m["executable"])
' | tail -n1)"

if [[ -z "${BIN}" || ! -x "${BIN}" ]]; then
	echo "ERROR: could not locate the built lib test binary" 1>&2
	exit 1
fi
echo "# test binary: ${BIN}" 1>&2

# Markdown table header. peak_RSS_MiB is the whole-process high-water mark.
echo "| N (records) | sec | leaf_max_ms | leaf_total_ms | master_ms | leaf_bytes | master_bytes | artifact_bytes | peak_RSS_MiB |"
echo "|---:|---:|---:|---:|---:|---:|---:|---:|---:|"

run_one() {
	local N="$1" SEC="$2"
	local OUT ERR
	OUT="$(mktemp)"
	ERR="$(mktemp)"

	# Run the single ignored row test directly under /usr/bin/time -l. --nocapture
	# lets the RESULT line reach stdout; --test-threads=1 keeps it isolated.
	AGG_N="${N}" AGG_SEC="${SEC}" /usr/bin/time -l "${BIN}" \
		--exact "${TEST_PATH}" --ignored --nocapture --test-threads=1 \
		>"${OUT}" 2>"${ERR}"

	# With --nocapture the harness prints "test NAME ... " (no newline) immediately
	# before the test's own "RESULT …", so the RESULT text is not at line start;
	# match it anywhere and slice from "RESULT" onward.
	local RESULT_LINE
	RESULT_LINE="$(grep -o 'RESULT tier=A.*' "${OUT}" | head -n1 || true)"
	if [[ -z "${RESULT_LINE}" ]]; then
		echo "ERROR: no RESULT line for N=${N}; stderr was:" 1>&2
		cat "${ERR}" 1>&2
		rm -f "${OUT}" "${ERR}"
		exit 1
	fi

	local get
	get() { echo "${RESULT_LINE}" | tr ' ' '\n' | grep "^$1=" | cut -d= -f2; }
	local ACTUAL_N LEAF_MAX LEAF_TOTAL MASTER LEAF_B MASTER_B ART_B
	ACTUAL_N="$(get N)"
	LEAF_MAX="$(get leaf_max_prove_ms)"
	LEAF_TOTAL="$(get leaf_total_prove_ms)"
	MASTER="$(get master_prove_ms)"
	LEAF_B="$(get leaf_proof_bytes)"
	MASTER_B="$(get master_proof_bytes)"
	ART_B="$(get agg_artifact_bytes)"

	# macOS: "maximum resident set size" is in BYTES → MiB.
	local RSS_BYTES RSS_MIB
	RSS_BYTES="$(grep 'maximum resident set size' "${ERR}" | awk '{print $1}')"
	RSS_MIB="$(awk -v b="${RSS_BYTES:-0}" 'BEGIN{ printf "%.1f", b/1048576 }')"

	echo "| ${ACTUAL_N} | ${SEC} | ${LEAF_MAX} | ${LEAF_TOTAL} | ${MASTER} | ${LEAF_B} | ${MASTER_B} | ${ART_B} | ${RSS_MIB} |"

	rm -f "${OUT}" "${ERR}"
}

for N in ${AGG_SWEEP}; do
	run_one "${N}" "${AGG_SEC}"
done

echo "#"
echo "# Reading the table: leaf_total_ms grows ~linearly in N (each record is one"
echo "# strand), but peak_RSS_MiB stays FLAT — the process never holds two witnesses"
echo "# at once. That flat column IS the Level-1 aggregation RSS: an edge/IoT"
echo "# aggregator folds a zone of any N under ONE strand's memory budget."
