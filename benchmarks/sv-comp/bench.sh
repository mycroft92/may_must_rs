#!/usr/bin/env sh
# bench.sh — sparse-clone sv-benchmarks, run the checker, update RESULTS.md,
#            then delete the clone.
#
# Usage
# -----
#   ./benchmarks/sv-comp/bench.sh [options]
#
# Options
#   --limit N          Stop after N files per category (default: 0 = all).
#   --categories FILE  Category list (default: categories.txt next to this script).
#   --commit           Git-commit the updated RESULTS.md automatically.
#   --sv-url URL       sv-benchmarks Git URL
#                      (default: git@gitlab.com:sosy-lab/benchmarking/sv-benchmarks.git)
#
# What it does
# ------------
#  1. Reads the active categories from categories.txt.
#  2. Sparse-shallow-clones only those subdirectories from sv-benchmarks.
#  3. Runs run.sh against the clone, writing results to a temporary CSV.
#  4. Passes the CSV to update_results.py, which prepends a new dated section
#     to RESULTS.md.
#  5. Deletes the clone and the temporary CSV.
#  6. Optionally commits RESULTS.md.
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)

CATEGORIES_FILE="$SCRIPT_DIR/categories.txt"
LIMIT=0
COMMIT=0
SV_URL="https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks.git"

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [ $# -gt 0 ]; do
    case "$1" in
        --limit)        LIMIT="$2"; shift 2 ;;
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
# Sparse-checkout paths
# ---------------------------------------------------------------------------
# Collect active (non-comment, non-blank) categories.
active_categories=""
while IFS= read -r line; do
    cat=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '[:space:]')
    [ -z "$cat" ] && continue
    active_categories="$active_categories $cat"
done < "$CATEGORIES_FILE"

if [ -z "$active_categories" ]; then
    printf 'error: no active categories in %s\n' "$CATEGORIES_FILE" >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Temporary directories / cleanup trap
# ---------------------------------------------------------------------------
CLONE_DIR=$(mktemp -d)
CSV_TMP=$(mktemp)

cleanup() {
    printf '\nCleaning up clone and temporary files...\n'
    rm -rf "$CLONE_DIR"
    rm -f  "$CSV_TMP"
}
trap cleanup EXIT INT TERM

# ---------------------------------------------------------------------------
# Sparse shallow clone
# ---------------------------------------------------------------------------
printf 'Cloning %s (sparse, depth=1)...\n' "$SV_URL"
git clone \
    --depth 1 \
    --filter=blob:none \
    --sparse \
    --quiet \
    "$SV_URL" \
    "$CLONE_DIR"

# Check out only the category subdirectories and the properties directory.
(
    cd "$CLONE_DIR"
    # shellcheck disable=SC2086
    git sparse-checkout set properties $active_categories
)

printf 'Clone ready at %s\n' "$CLONE_DIR"

# ---------------------------------------------------------------------------
# Run the checker
# ---------------------------------------------------------------------------
printf 'Running checker...\n'
LIMIT_FLAG=""
[ "$LIMIT" -gt 0 ] && LIMIT_FLAG="--limit $LIMIT"

"$SCRIPT_DIR/run.sh" \
    --benchmarks "$CLONE_DIR" \
    --categories "$CATEGORIES_FILE" \
    --csv        "$CSV_TMP" \
    --out-dir    "$SCRIPT_DIR/out" \
    ${LIMIT_FLAG:-}

# ---------------------------------------------------------------------------
# Update RESULTS.md
# ---------------------------------------------------------------------------
RESULTS_MD="$SCRIPT_DIR/RESULTS.md"
TOOL_COMMIT=$(git -C "$REPO_ROOT" rev-parse --short HEAD 2>/dev/null || printf 'unknown')
RUN_DATE=$(date '+%Y-%m-%d')
LIMIT_NOTE="all files"
[ "$LIMIT" -gt 0 ] && LIMIT_NOTE="--limit $LIMIT (first $LIMIT files per category)"

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
