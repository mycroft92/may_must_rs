#!/usr/bin/env python3
"""
update_results.py — parse the run CSV and prepend a new section to RESULTS.md.

Called by bench.sh; not intended for direct use.
"""

import argparse
import csv
import os
from collections import defaultdict
from datetime import datetime


VERDICTS = ("SAFE", "UNSAFE", "UNKNOWN", "ERROR_COMPILE", "ERROR_CONVERT")
VERDICT_COLS = ("SAFE", "UNSAFE", "UNKNOWN", "ERROR")   # display columns


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
    return verdict if verdict in ("SAFE", "UNSAFE", "UNKNOWN") else "UNKNOWN"


def build_table(rows: list[dict]) -> str:
    """Return a Markdown table summarising verdicts by category."""
    # category → verdict-bucket → count
    counts: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    totals: dict[str, int] = defaultdict(int)

    for row in rows:
        cat = row.get("category", "unknown")
        v   = bucket(row.get("verdict", "UNKNOWN"))
        counts[cat][v] += 1
        totals[v] += 1

    # Short category label (drop "c/" prefix and "ReachSafety-" for readability)
    def label(cat: str) -> str:
        return cat.replace("c/ReachSafety-", "").replace("c/", "")

    lines = []
    lines.append("| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Total |")
    lines.append("|---|---|---|---|---|---|")

    for cat in sorted(counts):
        c = counts[cat]
        total = sum(c.values())
        lines.append(
            f"| {label(cat)} "
            f"| {c['SAFE']} "
            f"| {c['UNSAFE']} "
            f"| {c['UNKNOWN']} "
            f"| {c['ERROR']} "
            f"| {total} |"
        )

    grand = sum(totals.values())
    lines.append(
        f"| **Total** "
        f"| **{totals['SAFE']}** "
        f"| **{totals['UNSAFE']}** "
        f"| **{totals['UNKNOWN']}** "
        f"| **{totals['ERROR']}** "
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
        cat = row.get("category", "")
        if exp == "safe" and v == "UNSAFE":
            issues.append(f"  - UNSOUND: `{cat}/{f}` expected SAFE, got UNSAFE")
        elif exp == "unsafe" and v == "SAFE":
            issues.append(f"  - MISSED:  `{cat}/{f}` expected UNSAFE, got SAFE")
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


def update_results_md(results_path: str, new_section: str) -> None:
    """Prepend new_section after the file header, before previous run sections."""
    if os.path.exists(results_path):
        existing = open(results_path, encoding="utf-8").read()
    else:
        existing = (
            "# SV-COMP Benchmark Results\n\n"
            "Newest run first.  Each section shows verdict counts per category "
            "and flags any soundness or completeness anomalies.\n\n"
            "---\n\n"
        )

    # Split at the first `---` separator (end of header block).
    # Insert the new section right after it.
    marker = "\n---\n"
    idx = existing.find(marker)
    if idx == -1:
        # No separator yet — just append.
        updated = existing.rstrip() + "\n\n" + new_section
    else:
        after_header = existing[idx + len(marker):]
        updated = existing[: idx + len(marker)] + "\n" + new_section + after_header

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
