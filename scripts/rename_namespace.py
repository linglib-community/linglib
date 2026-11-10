#!/usr/bin/env python3
"""Rename a namespace prefix across all .lean files in Linglib/ and Studies/.

Replaces `<old>` with `<new>` in non-import lines. Import lines use file
paths (`import Linglib.X.Y`), not namespaces, so they're left alone — file
paths don't change just because a namespace does.

Examples:
    # Strip the stale `Theories.` prefix from a subtree
    python3 scripts/rename_namespace.py 'Theories.Phonology' 'Phonology'

    # Match an Agreement subdir to its Minimalism siblings
    python3 scripts/rename_namespace.py 'Theories.Syntax.Minimalism' 'Minimalism'

    # Dry run
    python3 scripts/rename_namespace.py --dry-run 'Theories.Foo' 'Foo'
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIRS = [REPO_ROOT / d for d in ("Linglib", "Studies")]


def rename_in_file(filepath: Path, old: str, new: str, dry_run: bool) -> int:
    """Returns the number of substitutions made in the file."""
    pattern = re.compile(rf"(?<![A-Za-z0-9_.]){re.escape(old)}(?![A-Za-z0-9_])")
    # Read in binary mode to preserve line endings (some files use CRLF).
    raw = filepath.read_bytes()
    text = raw.decode("utf-8")
    new_lines = []
    total = 0
    # `splitlines(keepends=True)` keeps both \n and \r\n as-is.
    for line in text.splitlines(keepends=True):
        if re.match(r"^\s*import\s+", line):
            new_lines.append(line)
            continue
        new_line, n = pattern.subn(new, line)
        new_lines.append(new_line)
        total += n
    if total > 0 and not dry_run:
        filepath.write_bytes("".join(new_lines).encode("utf-8"))
    return total


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("old", help="namespace prefix to replace")
    parser.add_argument("new", help="replacement prefix")
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing")
    args = parser.parse_args()

    files_changed = 0
    total_subs = 0
    for f in sorted(f for d in SOURCE_DIRS for f in d.rglob("*.lean")):
        n = rename_in_file(f, args.old, args.new, args.dry_run)
        if n > 0:
            files_changed += 1
            total_subs += n
            rel = f.relative_to(REPO_ROOT).as_posix()
            print(f"  {rel}: {n} substitution(s)")

    verb = "would change" if args.dry_run else "changed"
    print(f"\n{verb} {total_subs} occurrence(s) across {files_changed} file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
