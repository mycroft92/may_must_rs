#!/usr/bin/env sh
# run.sh — compile and check SV-COMP benchmark files with Smash-plus-ultra.
#
# Usage
# -----
#   ./run.sh --benchmarks /path/to/sv-benchmarks [options]
#
# Required
#   --benchmarks DIR   Root of the sv-benchmarks repository clone.
#
# Options
#   --categories FILE  Category list (default: categories.txt next to this script).
#   --out-dir DIR      Directory for converted sources and bitcode (default: ./out).
#   --limit N          Stop after N files per category (default: unlimited).
#   --checker PATH     Path to the checker binary (default: auto-detect via cargo).
#   --checker-flags F  Extra flags passed to the checker (default: --no-dot).
#   --csv FILE         Append results to this CSV file (default: results.csv).
#   --jobs N           Parallel jobs (default: 1; >1 requires GNU parallel).
#
# Output
# ------
# For each benchmark file the script prints one line:
#   <verdict>  <file>
# where verdict is SAFE, UNSAFE, UNKNOWN, ERROR (compile/checker failure),
# or SKIP (unsupported property).
#
# A CSV summary is also written to --csv (appended, not overwritten):
#   file,category,expected,verdict,time_s
#
# Set-up
# ------
#   git clone git@gitlab.com:sosy-lab/benchmarking/sv-benchmarks.git
#   cd /path/to/smash-plus-ultra
#   cargo build --release
#   ./benchmarks/sv-comp/run.sh --benchmarks /path/to/sv-benchmarks
set -eu

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
CATEGORIES_FILE="$SCRIPT_DIR/categories.txt"
OUT_DIR="$SCRIPT_DIR/out"
LIMIT=0          # 0 = unlimited
CHECKER=""
CHECKER_FLAGS="--no-dot"
CSV_FILE="$SCRIPT_DIR/results.csv"
JOBS=1
BENCHMARKS_DIR=""

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [ $# -gt 0 ]; do
    case "$1" in
        --benchmarks)   BENCHMARKS_DIR="$2"; shift 2 ;;
        --categories)   CATEGORIES_FILE="$2"; shift 2 ;;
        --out-dir)      OUT_DIR="$2"; shift 2 ;;
        --limit)        LIMIT="$2"; shift 2 ;;
        --checker)      CHECKER="$2"; shift 2 ;;
        --checker-flags) CHECKER_FLAGS="$2"; shift 2 ;;
        --csv)          CSV_FILE="$2"; shift 2 ;;
        --jobs)         JOBS="$2"; shift 2 ;;
        -h|--help)
            sed -n '2,/^set -eu/p' "$0" | grep '^#' | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) printf 'Unknown option: %s\n' "$1" >&2; exit 1 ;;
    esac
done

if [ -z "$BENCHMARKS_DIR" ]; then
    printf 'error: --benchmarks is required\n' >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Locate tools
# ---------------------------------------------------------------------------
if [ -z "$CHECKER" ]; then
    RELEASE_BIN="$REPO_ROOT/target/release/main"
    DEBUG_BIN="$REPO_ROOT/target/debug/main"
    if [ -x "$RELEASE_BIN" ]; then
        CHECKER="$RELEASE_BIN"
    elif [ -x "$DEBUG_BIN" ]; then
        CHECKER="$DEBUG_BIN"
    else
        printf 'Building checker (release)...\n'
        cargo build --release --manifest-path "$REPO_ROOT/Cargo.toml"
        CHECKER="$RELEASE_BIN"
    fi
fi

CLANG="${CLANG:-clang}"
PYTHON3="${PYTHON3:-python3}"
CONVERT="$SCRIPT_DIR/convert.py"

mkdir -p "$OUT_DIR"

# Write CSV header if the file does not exist yet.
if [ ! -f "$CSV_FILE" ]; then
    printf 'file,category,expected,verdict,time_s\n' > "$CSV_FILE"
fi

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Read expected verdict from a .yml task file.
# Returns "true" (safe), "false" (unsafe), or "unknown".
expected_verdict() {
    yml="$1"
    if [ ! -f "$yml" ]; then
        printf 'unknown'
        return
    fi
    # Look for: expected_verdict: true/false under unreach-call property.
    verdict=$(grep -A3 'unreach-call' "$yml" 2>/dev/null \
              | grep 'expected_verdict' \
              | sed 's/.*expected_verdict:\s*//' \
              | tr -d '[:space:]' \
              | head -1)
    case "$verdict" in
        true)  printf 'safe' ;;
        false) printf 'unsafe' ;;
        *)     printf 'unknown' ;;
    esac
}

# Check one file; print result line and append to CSV.
check_one() {
    src="$1"         # original .c path inside sv-benchmarks
    category="$2"   # e.g. c/ReachSafety-Loops

    stem=$(basename "$src" .c)
    safe_cat=$(printf '%s' "$category" | tr '/' '_')
    conv="$OUT_DIR/${safe_cat}_${stem}.c"
    bc="$OUT_DIR/${safe_cat}_${stem}.bc"

    # Find corresponding .yml for expected verdict.
    yml=$(dirname "$src")/"${stem}.yml"
    expected=$(expected_verdict "$yml")

    # Convert source.
    if ! "$PYTHON3" "$CONVERT" "$src" "$conv" 2>/dev/null; then
        printf 'ERROR (convert)  %s\n' "$src"
        printf '%s,%s,%s,ERROR_CONVERT,0\n' "$stem" "$category" "$expected" >> "$CSV_FILE"
        return
    fi

    # Compile to bitcode.
    if ! "$CLANG" -O0 -g -fno-inline -c -emit-llvm \
            "-I$SCRIPT_DIR" "$conv" -o "$bc" 2>/dev/null; then
        printf 'ERROR (compile)  %s\n' "$src"
        printf '%s,%s,%s,ERROR_COMPILE,0\n' "$stem" "$category" "$expected" >> "$CSV_FILE"
        return
    fi

    # Run the checker; capture verdict from stdout.
    start=$(date +%s%3N 2>/dev/null || date +%s)
    checker_out=$("$CHECKER" $CHECKER_FLAGS "$bc" 2>/dev/null || true)
    end=$(date +%s%3N 2>/dev/null || date +%s)
    elapsed=$(( end - start ))
    # Convert ms to seconds with one decimal if %3N is supported; else seconds.
    if [ ${#elapsed} -gt 3 ]; then
        time_s=$(printf '%d.%d' $(( elapsed / 1000 )) $(( (elapsed % 1000) / 100 )))
    else
        time_s="${elapsed}.0"
    fi

    # Extract "module verdict: SAFE/UNSAFE/UNKNOWN" from checker output.
    verdict=$(printf '%s' "$checker_out" \
              | grep -i 'module verdict:' \
              | sed 's/.*module verdict:[[:space:]]*//' \
              | tr '[:lower:]' '[:upper:]' \
              | tr -d '[:space:]' \
              | head -1)
    [ -z "$verdict" ] && verdict="UNKNOWN"

    printf '%-8s  %s\n' "$verdict" "$src"
    printf '%s,%s,%s,%s,%s\n' "$stem" "$category" "$expected" "$verdict" "$time_s" >> "$CSV_FILE"
}

# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------
total=0
safe=0
unsafe=0
unknown=0
errors=0

while IFS= read -r category; do
    # Strip comments and blank lines.
    category=$(printf '%s' "$category" | sed 's/#.*//' | tr -d '[:space:]')
    [ -z "$category" ] && continue

    cat_dir="$BENCHMARKS_DIR/$category"
    if [ ! -d "$cat_dir" ]; then
        printf 'warning: category directory not found: %s\n' "$cat_dir" >&2
        continue
    fi

    printf '\n=== %s ===\n' "$category"
    count=0

    for src in "$cat_dir"/*.c; do
        [ -f "$src" ] || continue
        [ "$LIMIT" -gt 0 ] && [ "$count" -ge "$LIMIT" ] && break
        check_one "$src" "$category"
        count=$(( count + 1 ))
        total=$(( total + 1 ))
    done
done < "$CATEGORIES_FILE"

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
if [ -f "$CSV_FILE" ]; then
    safe=$(grep -c ',SAFE,' "$CSV_FILE" 2>/dev/null || true)
    unsafe=$(grep -c ',UNSAFE,' "$CSV_FILE" 2>/dev/null || true)
    unknown=$(grep -c ',UNKNOWN,' "$CSV_FILE" 2>/dev/null || true)
    errors=$(grep -c ',ERROR' "$CSV_FILE" 2>/dev/null || true)
fi

printf '\n=== Summary ===\n'
printf 'Total : %d\n' "$total"
printf 'SAFE  : %d\n' "$safe"
printf 'UNSAFE: %d\n' "$unsafe"
printf 'UNKNOWN: %d\n' "$unknown"
printf 'ERRORS: %d\n' "$errors"
printf 'Results written to: %s\n' "$CSV_FILE"
