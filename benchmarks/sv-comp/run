#!/usr/bin/env sh
# run.sh — compile and check SV-COMP benchmark files with Smash-plus-ultra.
#
# Usage
# -----
#   ./run.sh --benchmarks /path/to/sv-benchmarks [options]
#   ./run.sh --benchmarks /path/to/sv-benchmarks --file c/loops/compact.c [options]
#
# Required
#   --benchmarks DIR   Root of the sv-benchmarks repository clone.
#
# Options
#   --file REL         Run only this one file (relative to --benchmarks root).
#                      Looks up expected verdict from the matching .yml; if no
#                      .yml exists the expected verdict is shown as "unknown".
#   --categories FILE  Category list (default: categories.txt next to this script).
#   --out-dir DIR      Directory for converted sources and bitcode (default: ./out).
#   --limit N          Stop after N files per source directory (default: unlimited).
#   --checker PATH     Path to the checker binary (default: auto-detect via cargo).
#   --checker-flags F  Extra flags passed to the checker (default: --no-dot).
#   --csv FILE         Write results to this CSV file (default: results.csv).
#   --mem-limit MB     Virtual memory cap per checker run in MiB (default: 0 = unlimited).
#   --timeout S        Kill the checker after S seconds (default: 300; 0 = unlimited).
#
# Output
# ------
# For each benchmark file the script prints one line:
#   <verdict>  <file>
# where verdict is SAFE, UNSAFE, UNKNOWN, ERROR (compile/checker failure),
# or SKIP (no unreach-call property).
#
# CSV columns: file,directory,expected,verdict,time_s
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
CATEGORIES_FILE="$SCRIPT_DIR/categories.txt"
OUT_DIR="$SCRIPT_DIR/out"
LIMIT=0
CHECKER=""
CHECKER_FLAGS="--no-dot"
CSV_FILE="$SCRIPT_DIR/results.csv"
BENCHMARKS_DIR=""
MEM_LIMIT_MB=0
TIMEOUT_S=300
SINGLE_FILE=""

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [ $# -gt 0 ]; do
    case "$1" in
        --benchmarks)    BENCHMARKS_DIR="$2"; shift 2 ;;
        --file)          SINGLE_FILE="$2";    shift 2 ;;
        --categories)    CATEGORIES_FILE="$2"; shift 2 ;;
        --out-dir)       OUT_DIR="$2"; shift 2 ;;
        --limit)         LIMIT="$2"; shift 2 ;;
        --checker)       CHECKER="$2"; shift 2 ;;
        --checker-flags) CHECKER_FLAGS="$2"; shift 2 ;;
        --csv)           CSV_FILE="$2"; shift 2 ;;
        --mem-limit)     MEM_LIMIT_MB="$2"; shift 2 ;;
        --timeout)       TIMEOUT_S="$2";    shift 2 ;;
        -h|--help)
            sed -n '2,/^set -eu/p' "$0" | grep '^#' | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) printf 'Unknown option: %s\n' "$1" >&2; exit 1 ;;
    esac
done

if [ -z "$BENCHMARKS_DIR" ]; then
    printf 'error: --benchmarks is required\n' >&2; exit 1
fi

# ---------------------------------------------------------------------------
# Locate tools
# ---------------------------------------------------------------------------
if [ -z "$CHECKER" ]; then
    RELEASE_BIN="$REPO_ROOT/target/release/main"
    DEBUG_BIN="$REPO_ROOT/target/debug/main"
    if   [ -x "$RELEASE_BIN" ]; then CHECKER="$RELEASE_BIN"
    elif [ -x "$DEBUG_BIN"   ]; then CHECKER="$DEBUG_BIN"
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
printf 'file,directory,expected,verdict,time_s\n' > "$CSV_FILE"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Extract the expected verdict for the unreach-call property from a .yml file.
# Prints "safe", "unsafe", or "unknown".
yml_unreach_verdict() {
    yml="$1"
    # Find the block after "unreach-call.prp" and grab expected_verdict.
    # The YAML structure is:
    #   - property_file: ../properties/unreach-call.prp
    #     expected_verdict: true   ← we want this
    python3 - "$yml" <<'PYEOF'
import sys, re
text = open(sys.argv[1]).read()
# Find unreach-call block and the expected_verdict that follows it
m = re.search(r'unreach-call\.prp[^\n]*\n\s+expected_verdict:\s*(true|false)', text)
if m:
    print("safe" if m.group(1) == "true" else "unsafe")
else:
    print("unknown")
PYEOF
}

# Check one C source file; print result line and append to CSV.
check_one() {
    src="$1"       # absolute path to .c file
    src_dir="$2"   # relative source directory (e.g. c/loops)
    expected="$3"  # safe / unsafe / unknown

    stem=$(basename "$src" .c)
    safe_dir=$(printf '%s' "$src_dir" | tr '/' '_')
    conv="$OUT_DIR/${safe_dir}_${stem}.c"
    bc="$OUT_DIR/${safe_dir}_${stem}.bc"

    # Convert source.
    if ! "$PYTHON3" "$CONVERT" "$src" "$conv" 2>/dev/null; then
        printf '%-12s  %s\n' "ERROR(conv)" "$src"
        printf '%s,%s,%s,ERROR_CONVERT,0\n' "$stem" "$src_dir" "$expected" >> "$CSV_FILE"
        return
    fi

    # Compile to bitcode.
    if ! "$CLANG" -O0 -g -fno-inline -c -emit-llvm \
            "-I$SCRIPT_DIR" "$conv" -o "$bc" 2>/dev/null; then
        printf '%-12s  %s\n' "ERROR(cc)" "$src"
        printf '%s,%s,%s,ERROR_COMPILE,0\n' "$stem" "$src_dir" "$expected" >> "$CSV_FILE"
        return
    fi

    # Run checker; capture verdict.  Exit code 124 means timeout(1) killed it.
    start_ms=$(python3 -c "import time; print(int(time.time()*1000))" 2>/dev/null || echo 0)
    checker_exit=0
    checker_out=$(
        if [ "$MEM_LIMIT_MB" -gt 0 ]; then
            ulimit -v $((MEM_LIMIT_MB * 1024)) 2>/dev/null || true
        fi
        if [ "$TIMEOUT_S" -gt 0 ]; then
            timeout "$TIMEOUT_S" "$CHECKER" $CHECKER_FLAGS "$bc" 2>/dev/null
        else
            "$CHECKER" $CHECKER_FLAGS "$bc" 2>/dev/null
        fi
    ) || checker_exit=$?
    end_ms=$(python3 -c "import time; print(int(time.time()*1000))" 2>/dev/null || echo 0)
    elapsed_ms=$(( end_ms - start_ms ))
    time_s=$(python3 -c "print(f'{$elapsed_ms/1000:.2f}')" 2>/dev/null || echo "0.00")

    if [ "$checker_exit" -eq 124 ]; then
        printf '%-12s  %s\n' "TIMEOUT" "$(basename "$src")"
        printf '%s,%s,%s,%s,%s\n' "$stem" "$src_dir" "$expected" "TIMEOUT" "$time_s" >> "$CSV_FILE"
        return
    fi

    verdict=$(printf '%s' "$checker_out" \
              | grep -i 'module verdict:' \
              | sed 's/.*module verdict:[[:space:]]*//' \
              | tr '[:lower:]' '[:upper:]' | tr -d '[:space:]' | head -1)
    [ -z "$verdict" ] && verdict="UNKNOWN"

    printf '%-12s  %s\n' "$verdict" "$(basename "$src")"
    printf '%s,%s,%s,%s,%s\n' "$stem" "$src_dir" "$expected" "$verdict" "$time_s" >> "$CSV_FILE"
}

# ---------------------------------------------------------------------------
# Single-file mode
# ---------------------------------------------------------------------------
if [ -n "$SINGLE_FILE" ]; then
    src="$BENCHMARKS_DIR/$SINGLE_FILE"
    if [ ! -f "$src" ]; then
        printf 'error: file not found: %s\n' "$src" >&2; exit 1
    fi
    src_dir=$(dirname "$SINGLE_FILE")
    # Look for a matching .yml to get the expected verdict.
    stem=$(basename "$src" .c)
    yml="$BENCHMARKS_DIR/$src_dir/${stem}.yml"
    if [ -f "$yml" ]; then
        expected=$(yml_unreach_verdict "$yml")
    else
        expected="unknown"
    fi
    printf 'file,directory,expected,verdict,time_s\n' > "$CSV_FILE"
    check_one "$src" "$src_dir" "$expected"
    printf '\nExpected: %s\n' "$expected"
    exit 0
fi

# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------
total=0

while IFS= read -r line; do
    src_dir=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '[:space:]')
    [ -z "$src_dir" ] && continue

    cat_dir="$BENCHMARKS_DIR/$src_dir"
    if [ ! -d "$cat_dir" ]; then
        printf 'warning: directory not found: %s\n' "$cat_dir" >&2
        continue
    fi

    printf '\n=== %s ===\n' "$src_dir"
    count=0

    # Iterate over .yml files; only process those with unreach-call property.
    for yml in "$cat_dir"/*.yml; do
        [ -f "$yml" ] || continue
        [ "$LIMIT" -gt 0 ] && [ "$count" -ge "$LIMIT" ] && break

        expected=$(yml_unreach_verdict "$yml")
        [ "$expected" = "unknown" ] && continue   # no unreach-call property

        # Resolve input_files from the yml.
        input_file=$(grep 'input_files:' "$yml" \
                     | sed "s/.*input_files:[[:space:]]*//" \
                     | tr -d "'\""  | tr -d '[:space:]')
        src="$cat_dir/$input_file"
        [ -f "$src" ] || continue

        check_one "$src" "$src_dir" "$expected"
        count=$(( count + 1 ))
        total=$(( total + 1 ))
    done
done < "$CATEGORIES_FILE"

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
safe=$(grep -c ',SAFE,' "$CSV_FILE" 2>/dev/null || true)
unsafe=$(grep -c ',UNSAFE,' "$CSV_FILE" 2>/dev/null || true)
unknown=$(grep -c ',UNKNOWN,' "$CSV_FILE" 2>/dev/null || true)
errors=$(grep -c ',ERROR' "$CSV_FILE" 2>/dev/null || true)

printf '\n=== Summary ===\n'
printf 'Total  : %d\n' "$total"
printf 'SAFE   : %s\n' "$safe"
printf 'UNSAFE : %s\n' "$unsafe"
printf 'UNKNOWN: %s\n' "$unknown"
printf 'ERRORS : %s\n' "$errors"
printf 'Results written to: %s\n' "$CSV_FILE"
