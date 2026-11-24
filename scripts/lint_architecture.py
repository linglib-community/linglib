#!/usr/bin/env python3
"""Architectural lint for linglib.

Three checks, all aimed at real problems rather than path-mirroring:

  layer
    Forbidden import patterns (e.g. Semantics → Pragmatics, Core → Theories).
    Catches dependency-discipline violations.

  banned-prefix
    A namespace's first segment may not be `Theories`, `Linglib`, or `Mathlib`
    — these are filesystem-organisation prefixes, not concepts. Mathlib's
    convention: namespaces describe types/concepts (`Nat`, `Group`), not file
    locations. The library prefix never appears in namespaces.

  directory-consistency
    Files in the same directory should share the first segment of their
    primary namespace. Mixed first-segments inside one directory usually mean
    a stale file or a typo'd namespace, not deliberate concept-driven naming.

Usage:
    python3 scripts/lint_architecture.py              # report all violations
    python3 scripts/lint_architecture.py --check      # exit 1 if violations
    python3 scripts/lint_architecture.py --rule layer
    python3 scripts/lint_architecture.py --rule banned-prefix
    python3 scripts/lint_architecture.py --rule directory-consistency
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIRS = [REPO_ROOT / d for d in ("Linglib", "Studies")]

BANNED_FIRST_SEGMENTS = {"Theories", "Linglib", "Mathlib"}


# ---------- Layer rules ----------

# (under_path_prefix, forbidden_import_prefix, reason)
LAYER_RULES: list[tuple[str, str, str]] = [
    ("Linglib/Theories/Semantics/", "Linglib.Theories.Pragmatics.",
     "Semantics must not depend on Pragmatics "
     "(compositional grounding goes Pragmatics → Semantics, not vice versa)"),
    ("Linglib/Theories/", "Linglib.Phenomena.",
     "Theories must not depend on Phenomena"),
    ("Linglib/Theories/", "Linglib.Languages.",
     "Theories must not depend on Languages"),
    ("Linglib/Languages/", "Linglib.Phenomena.",
     "Languages must not depend on Phenomena"),
    ("Linglib/Core/", "Linglib.Theories.",
     "Core is the foundation — must not depend on Theories"),
    ("Linglib/Core/", "Linglib.Phenomena.",
     "Core must not depend on Phenomena"),
    ("Linglib/Core/", "Linglib.Languages.",
     "Core must not depend on Languages"),
]


def find_lean_files() -> list[Path]:
    return sorted(f for d in SOURCE_DIRS for f in d.rglob("*.lean"))


def file_imports(filepath: Path) -> list[tuple[int, str]]:
    """Return (line_num, imported_module) for each `import` line."""
    out = []
    for line_num, line in enumerate(filepath.read_text().splitlines(), 1):
        m = re.match(r"^\s*import\s+(\S+)", line)
        if m:
            out.append((line_num, m.group(1)))
    return out


def check_layer() -> list[tuple[Path, int, str]]:
    violations = []
    for f in find_lean_files():
        rel = f.relative_to(REPO_ROOT).as_posix()
        for under, forbidden, reason in LAYER_RULES:
            if not rel.startswith(under):
                continue
            for line_num, imp in file_imports(f):
                if imp.startswith(forbidden):
                    violations.append((f, line_num,
                        f"imports `{imp}` ({reason})"))
    return violations


# ---------- Namespace parsing ----------

def top_level_namespaces(filepath: Path) -> list[tuple[int, str]]:
    """All top-level (depth 0) `namespace X.Y.Z` declarations.

    Tracks nested `namespace`/`section`/`end` so only depth-0 declarations
    are reported. Strips Lean block comments (`/- ... -/`, possibly nested)
    and line comments (`-- ...`).
    """
    in_comment_depth = 0
    stack: list[str] = []
    out: list[tuple[int, str]] = []
    for line_num, raw in enumerate(filepath.read_text().splitlines(), 1):
        i = 0
        clean = []
        while i < len(raw):
            if in_comment_depth > 0:
                if raw[i:i+2] == "-/":
                    in_comment_depth -= 1
                    i += 2
                elif raw[i:i+2] == "/-":
                    in_comment_depth += 1
                    i += 2
                else:
                    i += 1
            else:
                if raw[i:i+2] == "/-":
                    in_comment_depth += 1
                    i += 2
                elif raw[i:i+2] == "--":
                    break
                else:
                    clean.append(raw[i])
                    i += 1
        line = "".join(clean).strip()
        if not line:
            continue

        m_ns = re.match(r"^namespace\s+(\S+)", line)
        if m_ns:
            if not stack:
                out.append((line_num, m_ns.group(1)))
            stack.append("namespace")
            continue
        if re.match(r"^section\b", line):
            stack.append("section")
            continue
        if re.match(r"^end\b", line) and stack:
            stack.pop()
            continue
    return out


def primary_namespace(filepath: Path) -> tuple[int, str] | None:
    nss = top_level_namespaces(filepath)
    return nss[0] if nss else None


# ---------- Banned-prefix check ----------

def check_banned_prefix() -> list[tuple[Path, int, str]]:
    """Flag any top-level namespace whose first segment is in BANNED_FIRST_SEGMENTS.

    These are filesystem-organisation prefixes, not concepts. Convention:
    `Theories.Foo.Bar` should just be `Foo.Bar`.
    """
    violations = []
    for f in find_lean_files():
        for line_num, ns in top_level_namespaces(f):
            first = ns.split(".")[0]
            if first in BANNED_FIRST_SEGMENTS:
                stripped = ".".join(ns.split(".")[1:]) or "<empty>"
                violations.append((f, line_num,
                    f"namespace `{ns}` starts with banned prefix `{first}` "
                    f"(library/org prefixes don't belong in namespaces; "
                    f"use `{stripped}` instead)"))
    return violations


# ---------- Directory-consistency check ----------

def check_directory_consistency() -> list[tuple[Path, int, str]]:
    """Files in the same directory should share their primary namespace's first segment.

    Skips:
      - directories with only one .lean file (no comparison possible)
      - files with no top-level namespace
      - files with banned-prefix namespaces (reported by banned-prefix check)
      - `Phenomena/<X>/Studies/` directories: each study uses its own bare
        `<AuthorYear>` namespace by convention (mathlib pattern), so every
        file in the directory has a different first segment. Cross-directory
        consistency is meaningless here — only check that each file's
        namespace matches its basename.

    For directories with mixed first-segments, the majority wins and minorities
    are flagged. Ties (e.g. 2 files, 2 different segments) flag both.
    """
    violations = []
    by_dir: dict[Path, list[tuple[Path, int, str]]] = defaultdict(list)
    for f in find_lean_files():
        prim = primary_namespace(f)
        if prim is None:
            continue
        line_num, ns = prim
        first = ns.split(".")[0]
        if first in BANNED_FIRST_SEGMENTS:
            continue

        # Special case: Phenomena/X/Studies/...AuthorYear.lean.
        # We only flag the stale path-mirror form
        # `Phenomena.<X>.Studies....<AuthorYear>` — that's the leftover
        # from before the mathlib migration. Concept-driven namespaces
        # (e.g. `RSA.LassiterGoodman2017`, `Semantics.Tense.X`) are
        # legitimate mathlib style and intentionally varied; the bare
        # `<AuthorYear>` form is also fine. So only the path-mirror is
        # actionable.
        rel_parts = f.relative_to(REPO_ROOT).parts
        if (len(rel_parts) >= 5
                and rel_parts[1] == "Phenomena"
                and "Studies" in rel_parts):
            # Compute the path-mirror namespace and check if `ns` is it.
            path_mirror = ".".join(
                list(rel_parts[1:-1]) + [rel_parts[-1].removesuffix(".lean")]
            )
            if ns == path_mirror:
                violations.append((f, line_num,
                    f"study namespace `{ns}` is the stale path-mirror form; "
                    f"use bare `{f.stem}` (mathlib pattern) or a "
                    f"concept-driven namespace"))
            # Don't include in directory-consistency check either way.
            continue

        by_dir[f.parent].append((f, line_num, first))

    for dirpath, entries in by_dir.items():
        if len(entries) < 2:
            continue
        counts = Counter(e[2] for e in entries)
        if len(counts) == 1:
            continue
        # Majority = most common segment(s). Anything not in the majority is flagged.
        max_count = max(counts.values())
        majority = {seg for seg, c in counts.items() if c == max_count}
        # If there's a unique majority (one most-common), minority files are outliers.
        # If there's a tie, *all* tied groups get flagged.
        if len(majority) == 1:
            outlier_segs = set(counts) - majority
            majority_str = next(iter(majority))
            for f, line_num, seg in entries:
                if seg in outlier_segs:
                    violations.append((f, line_num,
                        f"namespace first segment `{seg}` differs from "
                        f"sibling files in `{dirpath.relative_to(REPO_ROOT).as_posix()}` "
                        f"(majority uses `{majority_str}`)"))
        else:
            seg_list = sorted(counts)
            for f, line_num, seg in entries:
                violations.append((f, line_num,
                    f"namespace first segment `{seg}` is one of several "
                    f"competing in `{dirpath.relative_to(REPO_ROOT).as_posix()}` "
                    f"({seg_list}) — pick one"))
    return violations


# ---------- Main ----------

def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if any violations found")
    parser.add_argument("--rule",
                        choices=["layer", "banned-prefix",
                                 "directory-consistency", "all"],
                        default="all", help="which rule to run")
    args = parser.parse_args()

    by_rule: dict[str, list[tuple[Path, int, str]]] = {}
    if args.rule in ("layer", "all"):
        by_rule["layer"] = check_layer()
    if args.rule in ("banned-prefix", "all"):
        by_rule["banned-prefix"] = check_banned_prefix()
    if args.rule in ("directory-consistency", "all"):
        by_rule["directory-consistency"] = check_directory_consistency()

    total = sum(len(v) for v in by_rule.values())
    if total == 0:
        print("no architectural violations found")
        return 0

    for rule, vs in by_rule.items():
        if not vs:
            continue
        print(f"\n=== {rule} ({len(vs)} violation(s)) ===")
        for f, line, msg in sorted(vs):
            rel = f.relative_to(REPO_ROOT).as_posix()
            print(f"  {rel}:{line}: {msg}")

    print(f"\n{total} total violation(s)")
    return 1 if args.check else 0


if __name__ == "__main__":
    sys.exit(main())
