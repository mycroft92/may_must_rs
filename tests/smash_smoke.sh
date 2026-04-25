#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
out_dir="$repo_root/tests/out"
cargo_flags=${CARGO_FLAGS:-}

cd "$repo_root"

rm -f "$out_dir"/*.bc "$out_dir"/*.ll
./tests/build_ir.sh --out-dir "$out_dir"
mkdir -p graph_dot

cargo build $cargo_flags --bin main >/dev/null

for src in tests/flow/*.c; do
    stem=$(basename "$src" .c)
    "$repo_root/target/debug/main" --no-dot "$out_dir/$stem.bc" >/dev/null
done
