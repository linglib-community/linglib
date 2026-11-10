#!/usr/bin/env python3
"""Validate `[key]` citations in Lean sources against references.bib.

Scans Linglib/**/*.lean and Studies/**/*.lean for reference-style `[bibkey]`
brackets, checks them against the BibTeX entries, and warns about author-year-shaped
brackets with no matching entry (likely citation typos).

Usage:
    python3 scripts/check_citations.py           # report (always exit 0)
    python3 scripts/check_citations.py --strict  # exit 1 on warnings
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

PROJECT_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIRS = [PROJECT_ROOT / d for d in ("Linglib", "Studies")]
BIB_PATH = PROJECT_ROOT / "references.bib"

BRACKET_RE = re.compile(r"\[([^\[\]\n]+)\]")
YEAR_SHAPE = re.compile(r"-(?:19|20)\d{2}")


def parse_bib_keys(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    return {
        m.group(2).strip()
        for m in re.finditer(r"@(\w+)\s*\{([^,]+),", text)
    }


def main() -> None:
    strict = "--strict" in sys.argv
    keys = parse_bib_keys(BIB_PATH)
    cited_by: dict[str, list[str]] = defaultdict(list)
    unknown: list[tuple[str, str]] = []
    for lean_file in (f for d in LEAN_DIRS for f in d.rglob("*.lean")):
        try:
            text = lean_file.read_text(encoding="utf-8")
        except (UnicodeDecodeError, PermissionError):
            continue
        rel = str(lean_file.relative_to(PROJECT_ROOT))
        for m in BRACKET_RE.finditer(text):
            content = m.group(1).strip()
            if content in keys:
                if rel not in cited_by[content]:
                    cited_by[content].append(rel)
            elif YEAR_SHAPE.search(content):
                unknown.append((content, rel))

    warnings = [
        f"WARNING: [{k}] in {f} looks like a citation but is not in references.bib"
        for k, f in sorted(set(unknown))
    ]
    for w in warnings:
        print(w, file=sys.stderr)
    cite_count = sum(len(files) for files in cited_by.values())
    print(
        f"Found {cite_count} citation references "
        f"({len(cited_by)} distinct keys, {len(set(unknown))} unknown year-shaped)"
    )
    if strict and warnings:
        sys.exit(1)


if __name__ == "__main__":
    main()
