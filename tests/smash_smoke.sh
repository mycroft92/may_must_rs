#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out_dir="$repo_root/tests/out"
cargo_flags=${CARGO_FLAGS:-}

cd "$repo_root"

./tests/build_ir.sh --out-dir "$out_dir" \
    tests/smash_must.c \
    tests/smt_assert_safe.c
mkdir -p graph_dot

bug_output=$(cargo run $cargo_flags --bin main -- "$out_dir/smash_must.bc")
printf '%s\n' "$bug_output"

printf '%s\n' "$bug_output" | grep 'Query <main: true => assert_violation(' >/dev/null
printf '%s\n' "$bug_output" | grep 'Result: REACHABLE' >/dev/null
printf '%s\n' "$bug_output" | grep 'Stats:' >/dev/null

safe_output=$(cargo run $cargo_flags --bin main -- "$out_dir/smt_assert_safe.bc")
printf '%s\n' "$safe_output"

printf '%s\n' "$safe_output" | grep 'Query <main: true => false>' >/dev/null
printf '%s\n' "$safe_output" | grep 'Result: NOT REACHED' >/dev/null
printf '%s\n' "$safe_output" | grep 'Stats:' >/dev/null
