# Common helpers for bench-*.sh scripts.  Source from each script.
# Provides:
#   - csv_init <name> : initialise results/<name>.csv with header
#   - csv_append <name> <row> : append a CSV row
#   - time_cmd <out_var> <cmd...> : run cmd, capture wall-ms into $out_var
#   - peak_rss_mib <out_var> <cmd...> : run cmd, capture peak RSS in MiB

set -euo pipefail

SCRIPT_DIR="${SCRIPT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
RESULTS_DIR="$SCRIPT_DIR/results"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
RUN_IDX="${BENCH_RUN_IDX:-1}"
BLOWUP="${BENCH_BLOWUP:-32}"
LDT="${BENCH_LDT:-fri}"

mkdir -p "$RESULTS_DIR"

CSV_HEADER="air,level,ext_field,hash,r,n_trace,blowup,prove_ms,verify_ms,proof_kib,peak_rss_mib,run_idx,ldt"

csv_init() {
    local f="$RESULTS_DIR/$1.csv"
    if [ ! -f "$f" ]; then
        echo "$CSV_HEADER" > "$f"
    fi
}

csv_append() {
    local f="$RESULTS_DIR/$1.csv"
    shift
    echo "$@" >> "$f"
}

time_ms() {
    # Run a command; print wall-clock ms to stdout.
    # Usage: time_ms cmd args...
    local start
    start=$(date +%s%N)
    "$@" >&2
    local end
    end=$(date +%s%N)
    echo $(( (end - start) / 1000000 ))
}

peak_rss_mib() {
    # Run a command under /usr/bin/time -v; print peak RSS in MiB.
    # Usage: peak_rss_mib outfile cmd args...
    local outfile="$1"
    shift
    if command -v /usr/bin/time &> /dev/null; then
        /usr/bin/time -v "$@" 2>"$outfile" >&2 || true
        # parse "Maximum resident set size (kbytes): X"
        local kb
        kb=$(grep -i "Maximum resident set size" "$outfile" | awk '{print $NF}')
        if [ -n "$kb" ]; then
            echo $(( kb / 1024 ))
        else
            echo "0"
        fi
    elif command -v gtime &> /dev/null; then
        gtime -v "$@" 2>"$outfile" >&2 || true
        local kb
        kb=$(grep -i "Maximum resident set size" "$outfile" | awk '{print $NF}')
        echo $(( ${kb:-0} / 1024 ))
    else
        "$@" >&2
        echo "0"
    fi
}
