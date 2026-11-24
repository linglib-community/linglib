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

The same pass checks the layering of imports: nothing in `Linglib/Generalizations/` and no
shared file of `Linglib/Syntax/` or `Linglib/Morphology/` imports a framework, no framework of
syntax imports another and no framework of morphology imports another, and nothing in
`Linglib/Data/` imports outside `Linglib/Core/` and `Linglib/Data/`.

Dependencies: pure stdlib + `git`.
"""

import re
import subprocess
import sys
from pathlib import Path


IMPORT_RE = re.compile(
    r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?((?:Linglib|Studies)(?:\.[A-Za-z0-9_]+)+)\s*$')


# The frameworks of syntax, each a directory of `Linglib/Syntax/`, and the frameworks of
# morphology, each a directory of `Linglib/Morphology/`. A framework of morphology may build on
# one of syntax.
SYNTAX_FRAMEWORKS = ("Minimalist", "HPSG", "CCG", "DependencyGrammar", "ConstructionGrammar",
                     "Mereological")
MORPHOLOGY_FRAMEWORKS = ("DistributedMorphology", "Nanosyntax", "ParadigmFunctionMorphology",
                         "ConstructionMorphology")


def framework_of(module: str) -> str | None:
    """The framework a module belongs to, or None for a module shared by all of them."""
    parts = module.split(".")
    if len(parts) >= 3 and parts[1] == "Syntax" and parts[2] in SYNTAX_FRAMEWORKS:
        return parts[2]
    if len(parts) >= 3 and parts[1] == "Morphology" and parts[2] in MORPHOLOGY_FRAMEWORKS:
        return parts[2]
    return None


def layering_error(importer: str, imported: str) -> str | None:
    """Why `importer` may not import `imported`, or None when it may.

    A generalization is stated before any framework, a file of `Linglib/Syntax/` or
    `Linglib/Morphology/` outside the frameworks is shared by them, and one framework of syntax
    or of morphology does not build on another of its kind.
    `Linglib/Data/` holds observations and coding schemes that theory files import, so it
    imports no theory itself."""
    if importer.startswith("Linglib.Data.") and not imported.startswith(
            ("Linglib.Data.", "Linglib.Core.")):
        return "a file of Data imports outside Core and Data"
    target = framework_of(imported)
    if target is None:
        return None
    source = framework_of(importer)
    if importer.startswith("Linglib.Generalizations."):
        return f"a generalization imports the framework {target}"
    if importer.startswith("Linglib.Syntax.") and source is None:
        return f"a shared file of Syntax imports the framework {target}"
    if importer.startswith("Linglib.Morphology.") and source is None:
        return f"a shared file of Morphology imports the framework {target}"
    for frameworks in (SYNTAX_FRAMEWORKS, MORPHOLOGY_FRAMEWORKS):
        if source in frameworks and target in frameworks and source != target:
            return f"the framework {source} imports the framework {target}"
    return None


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
    layering: list[tuple[str, int, str, str]] = []  # (file, line_no, module, reason)
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
            why = layering_error(file_to_module(rel_path), mod)
            if why:
                layering.append((rel_path, line_no, mod, why))

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

    if layering:
        print("IMPORTS AGAINST THE LAYERING", file=sys.stderr)
        print("", file=sys.stderr)
        for f, line, mod, why in layering:
            print(f"  {f}:{line}: {why} ({mod})", file=sys.stderr)
        print("", file=sys.stderr)
        print(
            "A framework's map into a shared type lives in the framework, in a file named for\n"
            "the type. Move the declaration that needs the import into the framework.",
            file=sys.stderr,
        )
        return 1

    print(f"OK: {len(tracked)} tracked .lean files, no orphan imports")
    return 0


if __name__ == '__main__':
    sys.exit(main())
