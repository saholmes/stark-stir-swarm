#!/usr/bin/env bash
#
# bench-circuit-rss.sh — PART 3 PER-CIRCUIT prove-RSS. Peak resident-set of each
# ATOMIC stitchable circuit the streaming/"sliver" prover schedules to verify a
# signature, over B256 at NIST L1. A full signature verify decomposes into a known
# LIST of these circuits (see the per-scheme circuit inventory); the sliver prover
# proves them ONE AT A TIME, so the peak prover RSS of the whole signature == the
# MAX over its circuit types. This sweep measures that per-circuit budget.
#
# The dominant circuit is the non-native modular multiply ModMul<W>; its RSS scales
# ~(W/512)^2, so the widest ModMul a scheme uses sets that scheme's peak RSS:
#   Ed25519  -> ModMul(512,255)     P-256    -> ModMul(1024,256)
#   RSA-496  -> ModMul(1024,496)    RSA-1024 -> ModMul(2048,1024)
#   RSA-2048 -> ModMul(8192,2048)   ML-DSA q -> ModMul(64,23)
# plus Keccak-f[1600] (SHA3/SHAKE block, ML-DSA + DNS commitments) and the Tier-A
# aggregation Join node.
#
# HOW IT RUNS: this detached crate only builds under `cargo test --lib`, so each
# circuit row is the `#[ignore]`d `circuit_rss_row` test parameterized by env vars
# (CKT, MM_W, MM_N). We build the lib TEST binary ONCE, then run it DIRECTLY under
# `/usr/bin/time -l` once per circuit (never `cargo test`, whose RSS would mask the
# prover's). On macOS `/usr/bin/time -l` reports "maximum resident set size" in
# BYTES.
#
# Usage:  scripts/bench-circuit-rss.sh
#         CKT_SWEEP="keccak join modmul:1024:496 modmul:8192:2048" scripts/bench-circuit-rss.sh
#   spec forms:  keccak | join | modmul:<W>:<n>

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${CRATE_DIR}"

# Default sweep: the atomic building blocks + one ModMul per scheme width.
# Widths respect the ModMul assert 2*n+1 <= W: RSA-1024 (n=1024) needs W=4096,
# RSA-2048 (n=2048) needs W=8192. Scheme rows: Ed25519 (512,255), P-256 (1024,256),
# RSA-496 (1024,496), RSA-1024 (4096,1024), RSA-2048 (8192,2048), ML-DSA q (64,23).
CKT_SWEEP="${CKT_SWEEP:-keccak join modmul:64:23 modmul:512:255 modmul:1024:256 modmul:1024:496 modmul:2048:1023 modmul:4096:1024 modmul:4096:2047 modmul:8192:2048}"
TEST_PATH="bench::tests::circuit_rss_row"

echo "# binius-substrate — PART 3 per-circuit prove-RSS over B256 @ NIST L1 (sec=128, blowup=2)"
echo "# the atomic stitchable circuits the sliver prover schedules per signature verify"
echo "#"
echo "# machine: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown), $(sysctl -n hw.ncpu 2>/dev/null || echo '?') cores"
echo "# RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-<unset: rayon uses all cores>}"
echo "# sweep: ${CKT_SWEEP}"
echo "#"

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

echo "| circuit | W | n | prove_ms | proof_bytes | peak_RSS_MiB |"
echo "|:---|---:|---:|---:|---:|---:|"

# run_one dispatches two spec kinds:
#   modmul:<W>:<n> | keccak | join   -> the parameterized circuit_rss_row runner
#   gate=<test::path>                -> an EXISTING #[test] strand gate, run as-is
#                                       (the real per-strand sliver unit: a scalar-mul
#                                       round bundles several ModMuls+glue in ONE CS).
run_one() {
	local SPEC="$1"

	if [[ "${SPEC}" == gate=* ]]; then
		local GPATH GLABEL OUT ERR
		GPATH="${SPEC#gate=}"
		GLABEL="${GPATH##*::}"
		OUT="$(mktemp)"; ERR="$(mktemp)"
		# These gates are ordinary #[test]s (not #[ignore]d): run directly. They
		# print a "GATE …" line, not RESULT; we take peak RSS + wall time.
		/usr/bin/time -l "${BIN}" --exact "${GPATH}" --nocapture --test-threads=1 \
			>"${OUT}" 2>"${ERR}" || { echo "ERROR: gate ${GPATH} failed:" 1>&2; cat "${ERR}" 1>&2; rm -f "${OUT}" "${ERR}"; exit 1; }
		local REAL_S PMS RSS_BYTES RSS_MIB
		REAL_S="$(grep -Eo '^[[:space:]]*[0-9.]+ real' "${ERR}" | awk '{print $1}')"
		PMS="$(awk -v s="${REAL_S:-0}" 'BEGIN{ printf "%.0f", s*1000 }')"
		RSS_BYTES="$(grep 'maximum resident set size' "${ERR}" | awk '{print $1}')"
		RSS_MIB="$(awk -v b="${RSS_BYTES:-0}" 'BEGIN{ printf "%.1f", b/1048576 }')"
		echo "| ${GLABEL} (gate) | - | - | ${PMS} | - | ${RSS_MIB} |"
		rm -f "${OUT}" "${ERR}"
		return
	fi

	local CKT MM_W MM_N
	case "${SPEC}" in
		modmul:*:*)
			CKT="modmul"
			MM_W="$(echo "${SPEC}" | cut -d: -f2)"
			MM_N="$(echo "${SPEC}" | cut -d: -f3)"
			;;
		keccak) CKT="keccak"; MM_W=1600; MM_N=1 ;;
		join)   CKT="join";   MM_W=256;  MM_N=1 ;;
		*) echo "ERROR: bad spec '${SPEC}'" 1>&2; exit 1 ;;
	esac

	local OUT ERR
	OUT="$(mktemp)"; ERR="$(mktemp)"

	CKT="${CKT}" MM_W="${MM_W}" MM_N="${MM_N}" /usr/bin/time -l "${BIN}" \
		--exact "${TEST_PATH}" --ignored --nocapture --test-threads=1 \
		>"${OUT}" 2>"${ERR}" || true

	# With --nocapture the "RESULT …" text follows "test NAME ... " on one line.
	# A single circuit that panics/OOMs must NOT abort the whole sweep — record it
	# (peak RSS at the point of failure, if any) and move on.
	local RESULT_LINE
	RESULT_LINE="$(grep -o 'RESULT circuit=.*' "${OUT}" | head -n1 || true)"
	if [[ -z "${RESULT_LINE}" ]]; then
		local FRSS_B FRSS_M
		FRSS_B="$(grep 'maximum resident set size' "${ERR}" | awk '{print $1}')"
		FRSS_M="$(awk -v b="${FRSS_B:-0}" 'BEGIN{ printf "%.1f", b/1048576 }')"
		echo "| ${CKT}(${MM_W},${MM_N}) FAILED | ${MM_W} | ${MM_N} | - | - | ${FRSS_M} |"
		echo "# NOTE: ${SPEC} produced no RESULT (panic/OOM). stderr tail:" 1>&2
		tail -n3 "${ERR}" 1>&2
		rm -f "${OUT}" "${ERR}"; return
	fi

	local get
	get() { echo "${RESULT_LINE}" | tr ' ' '\n' | grep "^$1=" | cut -d= -f2; }
	local CNAME CW CN PMS PB
	CNAME="$(get circuit)"; CW="$(get W)"; CN="$(get n)"
	PMS="$(get prove_ms)"; PB="$(get proof_bytes)"

	local RSS_BYTES RSS_MIB
	RSS_BYTES="$(grep 'maximum resident set size' "${ERR}" | awk '{print $1}')"
	RSS_MIB="$(awk -v b="${RSS_BYTES:-0}" 'BEGIN{ printf "%.1f", b/1048576 }')"

	echo "| ${CNAME} | ${CW} | ${CN} | ${PMS} | ${PB} | ${RSS_MIB} |"
	rm -f "${OUT}" "${ERR}"
}

for SPEC in ${CKT_SWEEP}; do
	run_one "${SPEC}"
done

echo "#"
echo "# Reading the table: for each signature scheme, peak PROVER RSS == the max"
echo "# peak_RSS_MiB over the circuit types in its inventory (the widest ModMul it"
echo "# uses, or Keccak-f for ML-DSA). The full verify is a SCHEDULE of these"
echo "# circuits proven one-at-a-time; the sliver prover fits a memory budget B iff"
echo "# every circuit-type row is <= B."
