#!/usr/bin/env bash
#
# calibrate.sh — validate the sliver simulator's scheduler against REAL parallel runs,
# and quantify the Mac's shared-core contention.
#
# Runs N real single-core strand proofs (RAYON_NUM_THREADS=1, so one Mac core = one
# simulated "processor") across P parallel slots, measures the makespan, and compares it
# to sim.py's ideal no-contention prediction (ceil(N/P) x strand_time).
#
# The RATIO real/ideal is the contention factor. On separate machines (the deployment
# target) there is NO shared-memory contention, so the ideal model is what the fleet
# actually gets; the Mac run (shared cores/memory) only validates the SCHEDULER logic and
# bounds how far a single Mac can cross-check before the independence argument takes over
# (i.e. up to ~#cores). Contention that appears past a couple of cores is a Mac artifact,
# NOT part of the distributed extrapolation.
#
# Usage:  scripts/calibrate.sh
#         N=16 PLIST="1 2 4 8" STRAND_LP=64 scripts/calibrate.sh

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${CRATE_DIR}"

N="${N:-12}"                 # number of strand proofs
PLIST="${PLIST:-1 2 4 8}"    # parallel slot counts to test (keep <= #cores)
LP="${STRAND_LP:-64}"        # limbproduct size (64 is the cheapest RSA limb strand)
TESTPATH="bench::tests::circuit_rss_row"

now_ms() { python3 -c 'import time;print(time.time()*1000)'; }
ncores="$(sysctl -n hw.ncpu 2>/dev/null || echo '?')"

echo "# calibrate.sh — scheduler validation + Mac contention factor"
echo "# machine: $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown), ${ncores} cores"
echo "# strand: limbproduct_${LP} (single-core, RAYON_NUM_THREADS=1); N=${N}; P in { ${PLIST} }"
echo "# building lib test binary…" 1>&2
BIN="$(cargo test --release --lib --no-run --message-format=json 2>/dev/null \
  | /usr/bin/python3 -c '
import sys,json
for l in sys.stdin:
    try: m=json.loads(l)
    except ValueError: continue
    t=m.get("target",{})
    if m.get("reason")=="compiler-artifact" and t.get("test") and "lib" in t.get("kind",[]) and m.get("executable"):
        print(m["executable"])' | tail -n1)"
[[ -x "${BIN}" ]] || { echo "ERROR: no lib test binary" 1>&2; exit 1; }

runone() {
  env RAYON_NUM_THREADS=1 CKT=limbproduct LP_L="${LP}" "${BIN}" \
    --exact "${TESTPATH}" --ignored --nocapture --test-threads=1 >/dev/null 2>&1
}
export -f runone
export BIN TESTPATH LP

# --- isolated single-core strand time (the sim's per-strand cost) ---
echo "# measuring isolated single-core strand time…" 1>&2
t0="$(now_ms)"; runone; t1="$(now_ms)"
TS="$(python3 -c "print(f'{${t1}-${t0}:.0f}')")"
echo "# single-core strand time = ${TS} ms"
echo
echo "| P (slots) | real makespan | ideal (sim) | contention | sim ok? |"
echo "|---:|---:|---:|---:|:---:|"

for P in ${PLIST}; do
  s0="$(now_ms)"
  seq "${N}" | xargs -P "${P}" -I{} bash -c 'runone' || true
  s1="$(now_ms)"
  # ideal (no-contention) makespan = ceil(N/P) * TS
  REAL="$(python3 -c "print(f'{${s1}-${s0}:.0f}')")"
  IDEAL="$(python3 -c "import math;print(f'{math.ceil(${N}/${P})*${TS}:.0f}')")"
  RATIO="$(python3 -c "import math;print(f'{(${s1}-${s0})/(math.ceil(${N}/${P})*${TS}):.2f}')")"
  # cross-check: sim.py flat:N reproduces the same ideal makespan
  SIM="$(python3 "${SCRIPT_DIR}/sim.py" --workload "flat:${N}" --strand-cost-ms "${TS}" --p "${P}" 2>/dev/null \
        | grep -E "^\|[[:space:]]*${P}[[:space:]]*\|" | head -n1 | awk -F'|' '{gsub(/ /,"",$3);print $3}')"
  SIMOK="$(python3 -c "import re;v='${SIM}';m=re.match(r'([0-9.]+)(ms|s|min|h)',v);
u={'ms':1,'s':1000,'min':60000,'h':3600000};ms=float(m.group(1))*u[m.group(2)] if m else -1;
print('yes' if m and abs(ms-${IDEAL})<0.03*${IDEAL}+100 else '?')" 2>/dev/null || echo '?')"
  echo "| ${P} | ${REAL} ms | ${IDEAL} ms | ${RATIO}× | ${SIMOK} |"
done

echo
echo "# contention ≈ 1.0 ⇒ scheduler + per-strand cost are accurate; a fleet of SEPARATE"
echo "# machines has no shared-memory contention, so the ideal (sim) makespan is what it"
echo "# gets. contention > 1 past a couple of slots = the Mac saturating shared memory"
echo "# bandwidth — a single-machine artifact, excluded from the distributed extrapolation."
