#!/usr/bin/env sh
# bench.sh — sparse-clone sv-benchmarks, run the checker, update RESULTS.md.
#
# The clone is kept at benchmarks/sv-comp/.sv-benchmarks/ between runs.
# If it already exists, only a sparse-checkout update is performed (no re-clone).
#
# Usage
# -----
#   ./benchmarks/sv-comp/bench.sh [options]
#
# Options
#   --limit N          Stop after N files per source directory (default: 0 = all).
#   --mem-limit MB     Virtual memory cap per checker run in MiB (default: 0 = unlimited).
#   --timeout S        Kill the checker after S seconds (default: 300; 0 = unlimited).
#   --categories FILE  Category list (default: categories.txt next to this script).
#   --commit           Git-commit the updated RESULTS.md automatically.
#   --sv-url URL       sv-benchmarks Git URL
#                      (default: https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks.git)
#
# What it does
# ------------
#  1. Reads the active source directories from categories.txt.
#  2. Sparse-shallow-clones only those directories (skips if clone already exists).
#  3. Runs run.sh against the clone, writing results to a temporary CSV.
#  4. Passes the CSV to update_results.py, which prepends a new dated section
#     to RESULTS.md.
#  5. Optionally commits RESULTS.md.
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)

CATEGORIES_FILE="$SCRIPT_DIR/categories.txt"
CLONE_DIR="$SCRIPT_DIR/.sv-benchmarks"
LIMIT=0
MEM_LIMIT_MB=10240
TIMEOUT_S=300
COMMIT=0
SV_URL="https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks.git"

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [ $# -gt 0 ]; do
    case "$1" in
        --limit)        LIMIT="$2"; shift 2 ;;
        --mem-limit)    MEM_LIMIT_MB="$2"; shift 2 ;;
        --timeout)      TIMEOUT_S="$2";    shift 2 ;;
        --categories)   CATEGORIES_FILE="$2"; shift 2 ;;
        --commit)       COMMIT=1; shift ;;
        --sv-url)       SV_URL="$2"; shift 2 ;;
        -h|--help)
            sed -n '2,/^set -eu/p' "$0" | grep '^#' | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) printf 'Unknown option: %s\n' "$1" >&2; exit 1 ;;
    esac
done

# ---------------------------------------------------------------------------
# Collect active source directories from categories.txt
# ---------------------------------------------------------------------------
active_dirs=""
while IFS= read -r line; do
    dir=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '[:space:]')
    [ -z "$dir" ] && continue
    active_dirs="$active_dirs $dir"
done < "$CATEGORIES_FILE"

if [ -z "$active_dirs" ]; then
    printf 'error: no active directories in %s\n' "$CATEGORIES_FILE" >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Clone or update
# ---------------------------------------------------------------------------
if [ -d "$CLONE_DIR/.git" ]; then
    printf 'Clone already exists at %s — updating sparse checkout.\n' "$CLONE_DIR"
    (
        cd "$CLONE_DIR"
        # shellcheck disable=SC2086
        git sparse-checkout set properties $active_dirs
    )
else
    printf 'Cloning %s (sparse, depth=1)...\n' "$SV_URL"
    git clone \
        --depth 1 \
        --filter=blob:none \
        --sparse \
        --quiet \
        "$SV_URL" \
        "$CLONE_DIR"
    (
        cd "$CLONE_DIR"
        # shellcheck disable=SC2086
        git sparse-checkout set properties $active_dirs
    )
    printf 'Clone ready at %s\n' "$CLONE_DIR"
fi

# ---------------------------------------------------------------------------
# Run the checker
# ---------------------------------------------------------------------------
printf 'Running checker...\n'
CSV_TMP=$(mktemp)
trap 'rm -f "$CSV_TMP"' EXIT INT TERM

LIMIT_FLAG=""
[ "$LIMIT" -gt 0 ] && LIMIT_FLAG="--limit $LIMIT"
MEM_FLAG=""
[ "$MEM_LIMIT_MB" -gt 0 ] && MEM_FLAG="--mem-limit $MEM_LIMIT_MB"
TIMEOUT_FLAG="--timeout $TIMEOUT_S"

"$SCRIPT_DIR/run.sh" \
    --benchmarks "$CLONE_DIR" \
    --categories "$CATEGORIES_FILE" \
    --csv        "$CSV_TMP" \
    --out-dir    "$SCRIPT_DIR/out" \
    ${LIMIT_FLAG:-} \
    ${MEM_FLAG:-} \
    $TIMEOUT_FLAG

# ---------------------------------------------------------------------------
# Update RESULTS.md
# ---------------------------------------------------------------------------
RESULTS_MD="$SCRIPT_DIR/RESULTS.md"
TOOL_COMMIT=$(git -C "$REPO_ROOT" rev-parse --short HEAD 2>/dev/null || printf 'unknown')
RUN_DATE=$(date '+%Y-%m-%d')
LIMIT_NOTE="all files"
[ "$LIMIT" -gt 0 ] && LIMIT_NOTE="--limit $LIMIT (first $LIMIT files per directory)"

python3 "$SCRIPT_DIR/update_results.py" \
    --csv     "$CSV_TMP" \
    --results "$RESULTS_MD" \
    --date    "$RUN_DATE" \
    --commit  "$TOOL_COMMIT" \
    --note    "$LIMIT_NOTE"

printf '\nResults written to %s\n' "$RESULTS_MD"

# ---------------------------------------------------------------------------
# Optional git commit
# ---------------------------------------------------------------------------
if [ "$COMMIT" -eq 1 ]; then
    cd "$REPO_ROOT"
    git add "$RESULTS_MD"
    git commit -m "Update SV-COMP benchmark results ($RUN_DATE, $TOOL_COMMIT, $LIMIT_NOTE)"
    printf 'Committed RESULTS.md.\n'
fi
