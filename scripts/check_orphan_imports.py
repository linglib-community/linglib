#!/usr/bin/env python3
"""Detect import statements in tracked .lean files that reference untracked
or missing Lean modules — the pattern that builds clean locally but breaks
CI on a fresh checkout.

Usage:
    python3 scripts/check_orphan_imports.py
        Exits 0 with "OK" if every import of one of this repository's modules
        (`Linglib.X.Y`, `Studies.X`) resolves to a git-tracked file.
        Exits 1 with a list of orphan imports otherwise.

Install as a pre-push hook:
    cp scripts/git-hooks/pre-push .git/hooks/pre-push
    chmod +x .git/hooks/pre-push
    # or set core.hooksPath = scripts/git-hooks for the whole hook dir.

Background: at 0.230.799 and 0.230.801, two CI failures landed because
`Linglib.lean` import lines pointed to files that existed on the author's
machine but were never `git add`ed (`ParasiticAttitudes`,
`VerbMovementParameter`, ...). `lake build` succeeds locally because the
file is on disk; CI fails because the file is not in the git index.
This check closes that gap.

Dependencies: pure stdlib + `git`.
"""

import re
import subprocess
import sys
from pathlib import Path


IMPORT_RE = re.compile(
    r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?((?:Linglib|Studies)(?:\.[A-Za-z0-9_]+)+)\s*$')


def tracked_lean_files() -> set[str]:
    """All .lean paths tracked by git, relative to repo root."""
    out = subprocess.check_output(
        ['git', 'ls-files', '*.lean'],
        text=True,
        cwd=_repo_root(),
    )
    return set(out.strip().splitlines())


def _repo_root() -> Path:
    out = subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True)
    return Path(out.strip())


def file_to_module(path: str) -> str:
    """Linglib/Data/Examples/Schema.lean -> Linglib.Data.Examples.Schema"""
    if not path.endswith('.lean'):
        raise ValueError(f"not a .lean path: {path}")
    return path[:-len('.lean')].replace('/', '.')


def main() -> int:
    root = _repo_root()
    tracked = tracked_lean_files()
    tracked_modules = {file_to_module(f) for f in tracked}

    errors: list[tuple[str, int, str]] = []  # (file, line_no, missing_module)
    for rel_path in sorted(tracked):
        full = root / rel_path
        try:
            text = full.read_text(encoding='utf-8')
        except (FileNotFoundError, UnicodeDecodeError):
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            mod = m.group(1)
            if mod not in tracked_modules:
                errors.append((rel_path, line_no, mod))

    if errors:
        print("ORPHAN IMPORTS DETECTED", file=sys.stderr)
        print("", file=sys.stderr)
        for f, line, mod in errors:
            print(f"  {f}:{line}: imports untracked module {mod}", file=sys.stderr)
        print("", file=sys.stderr)
        print(
            "These imports reference Lean modules whose files are not tracked by git.\n"
            "lake build passes locally (the file exists on disk) but CI will fail on\n"
            "a clean checkout. Either:\n"
            "  (a) git add the missing files, or\n"
            "  (b) remove the import lines from the importing file(s)",
            file=sys.stderr,
        )
        return 1

    print(f"OK: {len(tracked)} tracked .lean files, no orphan imports")
    return 0


if __name__ == '__main__':
    sys.exit(main())
