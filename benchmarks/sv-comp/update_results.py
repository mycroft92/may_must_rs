#!/usr/bin/env python3
"""
update_results.py — parse the run CSV and prepend a new section to RESULTS.md.

Called by bench.sh; not intended for direct use.
"""

import argparse
import csv
import os
import re
from collections import defaultdict
from datetime import datetime


VERDICTS = ("SAFE", "UNSAFE", "UNKNOWN", "TIMEOUT", "ERROR_COMPILE", "ERROR_CONVERT")
VERDICT_COLS = ("SAFE", "UNSAFE", "UNKNOWN", "TIMEOUT", "ERROR")   # display columns


def load_csv(path: str) -> list[dict]:
    rows = []
    with open(path, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            rows.append(row)
    return rows


def bucket(verdict: str) -> str:
    """Collapse ERROR_* variants into a single ERROR display bucket."""
    if verdict.startswith("ERROR"):
        return "ERROR"
    return verdict if verdict in ("SAFE", "UNSAFE", "UNKNOWN", "TIMEOUT") else "UNKNOWN"


def build_table(rows: list[dict]) -> str:
    """Return a Markdown table summarising verdicts by category."""
    # category → verdict-bucket → count
    counts: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    # wrong[cat] = verdicts that contradict the expected outcome:
    #   SAFE when expected unsafe (missed bug) or UNSAFE when expected safe (false alarm)
    wrong: dict[str, int] = defaultdict(int)
    totals: dict[str, int] = defaultdict(int)
    total_wrong = 0

    for row in rows:
        cat = row.get("directory", row.get("category", "unknown"))
        v   = bucket(row.get("verdict", "UNKNOWN"))
        exp = row.get("expected", "").lower()
        counts[cat][v] += 1
        totals[v] += 1
        if (exp == "safe" and v == "UNSAFE") or (exp == "unsafe" and v == "SAFE"):
            wrong[cat] += 1
            total_wrong += 1

    # Short category label (drop "c/" prefix and "ReachSafety-" for readability)
    def label(cat: str) -> str:
        return cat.replace("c/ReachSafety-", "").replace("c/", "")

    lines = []
    lines.append("| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |")
    lines.append("|---|---|---|---|---|---|---|---|")

    for cat in sorted(counts):
        c = counts[cat]
        total = sum(c.values())
        w = wrong[cat]
        wrong_cell = f"**{w}**" if w > 0 else "0"
        lines.append(
            f"| {label(cat)} "
            f"| {c['SAFE']} "
            f"| {c['UNSAFE']} "
            f"| {c['UNKNOWN']} "
            f"| {c['TIMEOUT']} "
            f"| {c['ERROR']} "
            f"| {wrong_cell} "
            f"| {total} |"
        )

    grand = sum(totals.values())
    total_wrong_cell = f"**{total_wrong}**" if total_wrong > 0 else "**0**"
    lines.append(
        f"| **Total** "
        f"| **{totals['SAFE']}** "
        f"| **{totals['UNSAFE']}** "
        f"| **{totals['UNKNOWN']}** "
        f"| **{totals['TIMEOUT']}** "
        f"| **{totals['ERROR']}** "
        f"| {total_wrong_cell} "
        f"| **{grand}** |"
    )

    return "\n".join(lines)


def soundness_check(rows: list[dict]) -> list[str]:
    """
    Return lines flagging potentially unsound results:
    - expected=safe  but verdict=UNSAFE  → possible soundness issue
    - expected=unsafe but verdict=SAFE   → missed bug (unsound for bug-finding)
    """
    issues = []
    for row in rows:
        exp = row.get("expected", "").lower()
        v   = bucket(row.get("verdict", "UNKNOWN"))
        f   = row.get("file", "?")
        d   = row.get("directory", row.get("category", ""))
        if exp == "safe" and v == "UNSAFE":
            issues.append(f"  - UNSOUND: `{d}/{f}` expected SAFE, got UNSAFE")
        elif exp == "unsafe" and v == "SAFE":
            issues.append(f"  - MISSED:  `{d}/{f}` expected UNSAFE, got SAFE")
    return issues


def build_section(rows: list[dict], date: str, commit: str, note: str) -> str:
    table  = build_table(rows)
    issues = soundness_check(rows)

    lines = [
        f"## {date} — `{commit}`",
        "",
        f"Run: {note}",
        "",
        table,
    ]

    if issues:
        lines += ["", "**Soundness / completeness flags:**"]
        lines += issues
    else:
        lines += ["", "_No soundness flags._"]

    lines += ["", "---", ""]
    return "\n".join(lines)


def update_results_md(results_path: str, new_section: str, keep: int = 2) -> None:
    """Prepend new_section after the file header, keeping only `keep` run sections total."""
    if os.path.exists(results_path):
        existing = open(results_path, encoding="utf-8").read()
    else:
        existing = (
            "# SV-COMP Benchmark Results\n\n"
            "Newest run first.  Each section shows verdict counts per category "
            "and flags any soundness or completeness anomalies.\n\n"
            "> **Note**: This file is only updated on the `stable` branch (via CI).\n"
            "> Do not commit benchmark runs from `main`.\n\n"
            "---\n\n"
        )

    # Split at the first `---` separator (end of header block).
    marker = "\n---\n"
    idx = existing.find(marker)
    if idx == -1:
        header = existing.rstrip() + "\n"
        run_sections = []
    else:
        header = existing[: idx + len(marker)]
        # Each run section is delimited by "\n---\n"; collect them.
        after_header = existing[idx + len(marker):]
        run_sections = [s for s in re.split(r'\n---\n', after_header) if s.strip()]

    # Prepend new section; keep only the newest `keep` runs.
    run_sections = [new_section.rstrip()] + run_sections
    run_sections = run_sections[:keep]

    updated = header + "\n" + "\n\n---\n\n".join(run_sections) + "\n\n---\n\n"
    open(results_path, "w", encoding="utf-8").write(updated)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv",     required=True)
    parser.add_argument("--results", required=True)
    parser.add_argument("--date",    default=datetime.now().strftime("%Y-%m-%d"))
    parser.add_argument("--commit",  default="unknown")
    parser.add_argument("--note",    default="")
    args = parser.parse_args()

    rows = load_csv(args.csv)
    if not rows:
        print("warning: CSV is empty — no results to record.")
        return

    section = build_section(rows, args.date, args.commit, args.note)
    update_results_md(args.results, section)
    print(f"RESULTS.md updated ({len(rows)} benchmark files processed).")


if __name__ == "__main__":
    main()
