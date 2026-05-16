#!/usr/bin/env python3
"""
convert.py — transform a SV-COMP C source file into a form the checker accepts.

Usage
-----
    python3 convert.py INPUT.c OUTPUT.c [--shim PATH/TO/svcomp_shim.h]

What it does
------------
1. Strips extern declarations for __VERIFIER_error, __VERIFIER_assume,
   __VERIFIER_assert, and reach_error (the macros in svcomp_shim.h replace
   call sites; keeping the declarations causes preprocessor collisions).
2. Strips standalone function definitions for those same sentinels (some
   benchmarks define the body themselves: `void __VERIFIER_error() { abort(); }`).
3. Strips __VERIFIER_nondet_* forward declarations (with or without `extern`):
   svcomp_shim.h maps each __VERIFIER_nondet_*() to a bounded nondet_*() macro
   from verification.h; a lingering declaration would conflict with the macro.
4. Prepends `#include "<shim>"` so the SV-COMP sentinels map to our intrinsics.
"""

import argparse
import os
import re
import sys


# ---------------------------------------------------------------------------
# Patterns for lines / blocks we want to strip
# ---------------------------------------------------------------------------

# Declarations that conflict with the macros in svcomp_shim.h.
_EXTERN_STRIP_PATTERNS = [
    re.compile(r"^\s*extern\s+void\s+__VERIFIER_error\s*\("),
    re.compile(r"^\s*extern\s+void\s+__VERIFIER_assume\s*\("),
    re.compile(r"^\s*extern\s+void\s+__VERIFIER_assert\s*\("),
    re.compile(r"^\s*extern\s+void\s+reach_error\s*\("),
    # Nondet *declarations* (with or without `extern`, any return type).
    # The type portion before the function name is only word chars/spaces/stars,
    # so assignment call sites like `n = __VERIFIER_nondet_uint()` are not matched.
    re.compile(r"^\s*(?:extern\s+)?[\w\s*]+\s+__VERIFIER_nondet_\w+\s*\([^)]*\)\s*(?:__attribute__[^;]*)?\s*;"),
]


def _strip_line_if(line: str) -> bool:
    """Return True if this single line should be dropped entirely."""
    for pat in _EXTERN_STRIP_PATTERNS:
        if pat.search(line):
            return True
    return False


def _strip_function_body(lines: list[str], start: int) -> int:
    """
    Given that lines[start] begins a __VERIFIER_error function definition,
    skip forward past the closing brace and return the index of the next line
    to process.
    """
    depth = 0
    i = start
    while i < len(lines):
        depth += lines[i].count("{") - lines[i].count("}")
        i += 1
        if depth <= 0:
            break
    return i


# Function definitions to strip (bodies replaced by shim macros).
# Handles: `void __VERIFIER_error(void) {`, `void __VERIFIER_error() {`, etc.
_FN_DEF_STRIP_PATTERNS = [
    re.compile(r"^\s*void\s+__VERIFIER_error\s*\("),
    re.compile(r"^\s*void\s+__VERIFIER_assume\s*\("),
    re.compile(r"^\s*void\s+__VERIFIER_assert\s*\("),
    re.compile(r"^\s*void\s+reach_error\s*\("),
]


def convert(src: str, shim_include: str) -> str:
    """
    Return the converted source text.

    `shim_include` is the literal string that will appear in the generated
    `#include` directive, e.g. `"svcomp_shim.h"` or `<svcomp_shim.h>`.
    """
    lines = src.splitlines(keepends=True)
    out: list[str] = []
    out.append(f'#include {shim_include}\n')

    i = 0
    while i < len(lines):
        line = lines[i]

        # Drop extern declarations that would conflict with our macros.
        if _strip_line_if(line):
            # Multi-line declarations (attribute on next line) are rare but
            # possible.  Consume continuation lines until we hit ';'.
            while ";" not in line and i + 1 < len(lines):
                i += 1
                line = lines[i]
            i += 1
            continue

        # Drop standalone function definitions replaced by shim macros.
        if any(pat.match(line) for pat in _FN_DEF_STRIP_PATTERNS):
            # The opening brace may be on this line or the next.
            if "{" in line:
                i = _strip_function_body(lines, i)
            else:
                # Signature without body on this line; advance until '{'.
                i += 1
                while i < len(lines) and "{" not in lines[i]:
                    i += 1
                if i < len(lines):
                    i = _strip_function_body(lines, i)
            continue

        out.append(line)
        i += 1

    return "".join(out)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("input",  help="SV-COMP source file (.c)")
    parser.add_argument("output", help="Converted output file (.c)")
    parser.add_argument(
        "--shim",
        default=None,
        help="Path to svcomp_shim.h (default: <dir of this script>/svcomp_shim.h); "
             "the generated #include uses a path relative to the output file.",
    )
    args = parser.parse_args()

    # Resolve the shim path and express it relative to the output file.
    script_dir = os.path.dirname(os.path.abspath(__file__))
    shim_abs = os.path.abspath(args.shim) if args.shim else os.path.join(script_dir, "svcomp_shim.h")
    out_dir   = os.path.dirname(os.path.abspath(args.output)) or "."
    shim_rel  = os.path.relpath(shim_abs, out_dir)
    shim_include = f'"{shim_rel}"'

    try:
        src = open(args.input, encoding="utf-8", errors="replace").read()
    except OSError as exc:
        sys.exit(f"error: cannot read {args.input!r}: {exc}")

    result = convert(src, shim_include)

    try:
        os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
        open(args.output, "w", encoding="utf-8").write(result)
    except OSError as exc:
        sys.exit(f"error: cannot write {args.output!r}: {exc}")


if __name__ == "__main__":
    main()
