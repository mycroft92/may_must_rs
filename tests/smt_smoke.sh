#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out_dir="$repo_root/tests/out"
cargo_flags=${CARGO_FLAGS:-}

cd "$repo_root"

./tests/build_ir.sh --out-dir "$out_dir" \
    tests/smash_must.c \
    tests/smt_assert_safe.c \
    tests/smt_assert_branch_prune.c
mkdir -p graph_dot

run_smt() {
    cargo run $cargo_flags --bin main -- "$out_dir/$1.bc" --engine smt
}

bug_output=$(run_smt smash_must)
printf '%s\n' "$bug_output"
printf '%s\n' "$bug_output" | grep 'Query <main: true => violate:any_may_assert>' >/dev/null
printf '%s\n' "$bug_output" | grep 'Result: BUG reachable (must summary)' >/dev/null
printf '%s\n' "$bug_output" | grep 'Summaries: 1 must, 0 not-may' >/dev/null

safe_output=$(run_smt smt_assert_safe)
printf '%s\n' "$safe_output"
printf '%s\n' "$safe_output" | grep 'Query <main: true => violate:any_may_assert>' >/dev/null
printf '%s\n' "$safe_output" | grep 'Result: SAFE (not-may summary)' >/dev/null
printf '%s\n' "$safe_output" | grep 'Summaries: 0 must, 1 not-may' >/dev/null

branch_output=$(run_smt smt_assert_branch_prune)
printf '%s\n' "$branch_output"
printf '%s\n' "$branch_output" | grep 'Query <main: true => violate:any_may_assert>' >/dev/null
printf '%s\n' "$branch_output" | grep 'Result: SAFE (not-may summary)' >/dev/null
printf '%s\n' "$branch_output" | grep 'Summaries: 0 must, 1 not-may' >/dev/null
