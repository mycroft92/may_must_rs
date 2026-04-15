#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out_dir="$repo_root/tests/out"
cargo_flags=${CARGO_FLAGS:-}

cd "$repo_root"

./tests/build_ir.sh --out-dir "$out_dir" tests/smash_must.c
mkdir -p graph_dot

output=$(cargo run $cargo_flags --bin main -- "$out_dir/smash_must.bc")
printf '%s\n' "$output"

printf '%s\n' "$output" | grep 'Query <main: true => violate:any_may_assert>' >/dev/null
printf '%s\n' "$output" | grep 'Result: BUG reachable (must summary)' >/dev/null
printf '%s\n' "$output" | grep 'Summaries: 1 must, 0 not-may' >/dev/null
