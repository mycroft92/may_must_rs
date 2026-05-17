#!/usr/bin/env sh
set -eu

out_dir="tests/out"
cflags="${CFLAGS:--O0 -g -fno-inline -I.}"

if [ "${CLANG:-}" ]; then
    clang_bin="$CLANG"
elif command -v llvm-config >/dev/null 2>&1; then
    llvm_bindir=$(llvm-config --bindir)
    if [ -x "$llvm_bindir/clang" ]; then
        clang_bin="$llvm_bindir/clang"
    else
        clang_bin="clang"
    fi
else
    clang_bin="clang"
fi

if [ "${1:-}" = "--out-dir" ]; then
    out_dir="$2"
    shift 2
fi

mkdir -p "$out_dir"
printf 'Using %s\n' "$("$clang_bin" --version | sed -n '1p')"

if [ "$#" -eq 0 ]; then
    set -- tests/flow/*.c
fi

for src in "$@"; do
    case "$src" in
        *.cpp|*.cc|*.cxx)
            stem=$(basename "$src" | sed 's/\.[^.]*$//')
            compiler="${clang_bin}++"
            lang_flags="-std=c++17 -fno-rtti"
            ;;
        *)
            stem=$(basename "$src" .c)
            compiler="$clang_bin"
            lang_flags=""
            ;;
    esac
    "$compiler" $cflags ${lang_flags} -S -emit-llvm "$src" -o "$out_dir/$stem.ll"
    "$compiler" $cflags ${lang_flags} -c -emit-llvm "$src" -o "$out_dir/$stem.bc"
    printf '%s -> %s, %s\n' "$src" "$out_dir/$stem.ll" "$out_dir/$stem.bc"
done
