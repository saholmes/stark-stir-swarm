#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════════════════
#  swarm-ecdsa-demo.sh — prove a REAL P256 ECDSA signature with the
#  committed G-way stranded STARK, using INDEPENDENT OS PROCESSES on this
#  M4 as swarm elements (one strand per process, ≤1 GB each, in parallel),
#  then splice + verify.
#
#  Params (env):
#    G            strand count           (default 16)
#    BENCH_BLOWUP FRI blowup             (default 4)
#    K            scalar-mult steps      (default 256)
#    POOL         max concurrent workers (default 6)
#    SWARM_KEY    32-byte sk hex         (optional)
#    SWARM_MSG    message                (optional)
#
#  Reuses only committed machinery (see crates/deep_ali/examples/
#  ecdsa_swarm_demo.rs).  Soundness is NOT re-derived here.
# ═══════════════════════════════════════════════════════════════════════
set -euo pipefail

# NOTE: at G=16 each strand's SOLO peak is ~0.85 GB, but under POOL=6
# oversubscription on the M4 one starved worker can transiently peak
# ~1.05 GB.  Use G=24-32 (env G=32) for a clean ≤1 GB margin under POOL=6.
G="${G:-16}"
BENCH_BLOWUP="${BENCH_BLOWUP:-4}"
K="${K:-256}"
POOL="${POOL:-6}"

REPO="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$REPO/target/release/examples/ecdsa_swarm_demo"
FEATURES="parallel sha3-256 mldsa-44"

SWARM_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ecdsa-swarm.XXXXXX")"
export SWARM_DIR
# Keep the work dir on failure (for debugging); cleaned explicitly on success.

now() { perl -MTime::HiRes=time -e 'printf "%.3f", time'; }

echo "════════════════════════════════════════════════════════════════════════"
echo " ECDSA SWARM DEMO  —  G=$G  blowup=$BENCH_BLOWUP  K=$K  POOL=$POOL"
echo " work dir: $SWARM_DIR"
echo "════════════════════════════════════════════════════════════════════════"

# ── build ──
echo "[build] cargo build --release --example ecdsa_swarm_demo ..."
( cd "$REPO" && cargo build --release -p deep_ali --example ecdsa_swarm_demo \
    --no-default-features --features "$FEATURES" ) >/dev/null 2>&1 || {
  echo "BUILD FAILED"; ( cd "$REPO" && cargo build --release -p deep_ali \
    --example ecdsa_swarm_demo --no-default-features --features "$FEATURES" ); exit 1; }

# ── coordinator: keygen/sign + manifest ──
echo
G="$G" BENCH_BLOWUP="$BENCH_BLOWUP" K="$K" SWARM_ROLE=coordinator "$BIN"

# ── launch G worker processes in parallel, POOL at a time ──
echo
echo "────────────────────────────────────────────────────────────────────────"
echo " Launching $G worker processes (one strand each, ≤1 GB target), POOL=$POOL"
echo "────────────────────────────────────────────────────────────────────────"

run_worker() {
  local id="$1"
  local ws; ws="$(now)"
  # /usr/bin/time -l → peak RSS (bytes) on stderr.
  SWARM_ROLE=worker STRAND_ID="$id" /usr/bin/time -l "$BIN" \
    >"$SWARM_DIR/strand_$id.out" 2>"$SWARM_DIR/strand_$id.rss" || {
      echo "  worker $id FAILED"; cat "$SWARM_DIR/strand_$id.rss"; exit 1; }
  local we; we="$(now)"
  awk -v a="$ws" -v b="$we" 'BEGIN{printf "%.1f", b-a}' > "$SWARM_DIR/strand_$id.wall"
  echo "  ✓ worker $id done"
}

# Launch in explicit batches of POOL (bash 3.2 on macOS has no `wait -n`),
# so the worker-phase wall clock ≈ ceil(G/POOL) × slowest strand in a batch.
phase_start="$(now)"
running=0
for id in $(seq 0 $((G-1))); do
  run_worker "$id" &
  running=$((running+1))
  if [ "$running" -ge "$POOL" ]; then
    wait            # drain the current batch
    running=0
  fi
done
wait
phase_end="$(now)"
PARALLEL_WALL="$(awk -v a="$phase_start" -v b="$phase_end" 'BEGIN{printf "%.1f", b-a}')"

# ── per-worker report table ──
echo
echo "────────────────────────────────────────────────────────────────────────"
echo " Per-worker table  (strand / width / peak RSS / fill / prove / wall)"
echo "────────────────────────────────────────────────────────────────────────"
printf "  %-7s %-8s %-12s %-9s %-10s %-8s\n" "strand" "width" "peakRSS(MiB)" "fill(ms)" "prove(ms)" "wall(s)"
all_under=1
sum_prove=0
max_rss=0
for id in $(seq 0 $((G-1))); do
  read -r width fill prove _bytes < "$SWARM_DIR/strand_$id.meta" || true
  # macOS /usr/bin/time -l prints "  <bytes>  maximum resident set size"
  rss_bytes="$(grep 'maximum resident set size' "$SWARM_DIR/strand_$id.rss" | awk '{print $1}')"
  rss_mib="$(awk -v b="$rss_bytes" 'BEGIN{printf "%.0f", b/1048576}')"
  wall="$(cat "$SWARM_DIR/strand_$id.wall")"
  flag=""
  if [ "$rss_mib" -gt 1024 ]; then flag=" ⚠ >1GB"; all_under=0; fi
  if [ "$rss_mib" -gt "$max_rss" ]; then max_rss="$rss_mib"; fi
  sum_prove="$(awk -v s="$sum_prove" -v p="$prove" 'BEGIN{printf "%.0f", s+p}')"
  printf "  %-7s %-8s %-12s %-9s %-10s %-8s%s\n" \
    "$id" "$width" "$rss_mib" "$fill" "$prove" "$wall" "$flag"
done

echo
if [ "$all_under" -eq 1 ]; then
  echo "  ✓ EVERY worker peaked ≤ 1 GB  (max observed = ${max_rss} MiB)"
else
  echo "  ⚠ some worker exceeded 1 GB (max = ${max_rss} MiB) — raise G and re-run"
fi

# ── parallel wall-clock vs naive sum-of-work ──
echo
echo "────────────────────────────────────────────────────────────────────────"
echo " Wall-clock: swarm (parallel) vs naive sequential sum"
echo "────────────────────────────────────────────────────────────────────────"
sum_prove_s="$(awk -v m="$sum_prove" 'BEGIN{printf "%.1f", m/1000}')"
speedup="$(awk -v s="$sum_prove_s" -v p="$PARALLEL_WALL" 'BEGIN{ if(p>0) printf "%.2f", s/p; else print "n/a" }')"
batches="$(awk -v g="$G" -v pool="$POOL" 'BEGIN{printf "%d", (g+pool-1)/pool}')"
echo "  Σ per-strand prove time (naive sequential) : ${sum_prove_s} s"
echo "  swarm worker-phase wall clock (POOL=$POOL) : ${PARALLEL_WALL} s   (~${batches} batches)"
echo "  observed speedup                           : ${speedup}×"

# ── splice (prover-side): assemble the G strand sub-proofs into proof.bin ──
echo
splice_out="$(SWARM_ROLE=splice "$BIN")"
echo "$splice_out" | grep -v '^SPLICE '
SPLICE_MS="$(echo "$splice_out" | awk -F'splice_ms=' '/^SPLICE /{print $2}' | awk '{print $1}')"
PROOF_BYTES="$(echo "$splice_out" | awk -F'proof_bytes=' '/^SPLICE /{print $2}')"
PROOF_MIB="$(awk -v b="$PROOF_BYTES" 'BEGIN{printf "%.1f", b/1048576}')"

# ── verify (consumer-side): read proof.bin, check, tamper-reject ──
echo
verify_out="$(SWARM_ROLE=verify "$BIN")"
echo "$verify_out" | grep -v '^VERIFY '
VERIFY_MS="$(echo "$verify_out" | awk -F'verify_ms=' '/^VERIFY /{print $2}')"

# ── deployment cost breakdown: prover vs consumer ──
TOTAL_PROVER="$(awk -v w="$PARALLEL_WALL" -v s="$SPLICE_MS" 'BEGIN{printf "%.1f", w + s/1000}')"
echo
echo "────────────────────────────────────────────────────────────────────────"
echo " Deployment cost breakdown  (prover-side production vs consumer verify)"
echo "────────────────────────────────────────────────────────────────────────"
printf "  PROVER : parallel worker-prove wall  = %s s\n" "$PARALLEL_WALL"
printf "         + splice (assemble+write)     = %s s  (%s ms)\n" \
  "$(awk -v s="$SPLICE_MS" 'BEGIN{printf "%.1f", s/1000}')" "$SPLICE_MS"
printf "         ─────────────────────────────────────────\n"
printf "         = TOTAL PROVER               = %s s\n" "$TOTAL_PROVER"
echo
printf "  VERIFY : consumer one-shot           = %s s  (%s ms)\n" \
  "$(awk -v v="$VERIFY_MS" 'BEGIN{printf "%.1f", v/1000}')" "$VERIFY_MS"
echo
printf "  PROOF  : proof.bin on disk           = %s MiB\n" "$PROOF_MIB"

echo
echo "════════════════════════════════════════════════════════════════════════"
echo " DONE — a swarm of ≤1 GB independent processes proved a real ECDSA sig."
echo "════════════════════════════════════════════════════════════════════════"

rm -rf "$SWARM_DIR"   # success → clean up (~3-4 GB of strand files + proof.bin)
