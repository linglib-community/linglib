"""The marks of `Judgment` and the symbol a paper prints for each.

`MARK` is the one table the generators and the CLDF export read. Importing this module checks it
against the constructors of `Judgment` in `Linglib/Data/Examples/Judgment.lean`, so a mark added
to one and not the other stops every script that reads marks.
"""
import re
from pathlib import Path

LEAN = Path(__file__).resolve().parent.parent / "Linglib" / "Data" / "Examples" / "Judgment.lean"

MARK = {
    "acceptable": "",
    "marginal": "?",
    "questionable": "??",
    "unacceptable": "#",
    "nearlyUngrammatical": "?*",
    "ungrammatical": "*",
    "variable": "%",
}


def lean_marks():
    """The constructors of `Judgment`, in declaration order."""
    src = LEAN.read_text(encoding="utf-8")
    body = src[src.index("inductive Judgment where"):]
    return re.findall(r"^  \| (\w+)$", body[:body.index("deriving")], re.M)


if lean_marks() != list(MARK):
    raise SystemExit(f"FATAL: scripts/judgments.py lists {list(MARK)}, and "
                     f"{LEAN.name} declares {lean_marks()}")
