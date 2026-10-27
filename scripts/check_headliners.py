#!/usr/bin/env python3
"""Check that each study documents one to five theorems: its headline results.

A study's headline theorems are exactly the theorems that carry a docstring; the module docstring
does not list them again. Two rules:

- A study has one to five theorems with a docstring. Studies listed in
  `scripts/headliners_baseline.txt` predate the rule and are exempt until they are next audited;
  a listed study that passes is reported so it can leave the list.
- The module docstring has no `## Main results` (or `## Main statements`) section.

`--demote FILE NAME ...` turns the named theorems' docstrings into a `--` comment holding their
paper locators and citations (`-- Table 3`, `-- (12), p. 4 [key]`), or drops docstrings that have
neither, and confirms that nothing but comments changed.

Usage, from the repository root:

    python3 scripts/check_headliners.py                          # check every study
    python3 scripts/check_headliners.py --demote FILE NAME ...   # demote theorems to minor
    python3 scripts/check_headliners.py --write-baseline         # list the studies exempt
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "headliners_baseline.txt"
CAP = 5
MAIN =re.compile(r"^## Main (?:results|statements|theorems)\b", re.M)
CITE = re.compile(r"\[([a-z0-9][a-z0-9-]*-\d{4}[a-z]?)\]")
NUM = r"(?:[IVXLC]+\b|\d+(?:\.\d+)*[a-z]?)"
WORDS = (r"Tables?|Figures?|Fig\.|Sections?|Chapters?|Ch\.|Appendix|Definitions?|Def\.|"
         r"Propositions?|Prop\.|Theorems?|Thm\.|Lemmas?|Corollary|Corollaries|Examples?|Ex\.|"
         r"Rules?|Conditions?|Constraints?|Generalizations?|fn\.|footnotes?|notes?|Claims?|Facts?|"
         r"Observations?|Principles?|Axioms?|nn?\.")
LOCATOR = re.compile(
    r"\b(?:" + WORDS + r")\s+" + NUM + r"(?:\s*(?:,|–|-|and|&)\s*" + NUM + r")*"
    r"|§\s?\d+(?:\.\d+)*"
    r"|\bpp?\.\s?\d+(?:\s?[–-]\s?\d+)?"
    r"|(?<![\w)])\(\d{1,3}[a-z]?(?:[a-z]|[,–-]\s?\d{0,3}[a-z]?)*(?:\.[a-z\d]+)?\)"
    r"|(?<![\w)])\((?=[ivx])x{0,3}(?:ix|iv|v?i{0,3})\)")
DECL = re.compile(r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec|noncomputable) )*"
                  r"(theorem|lemma)\s+([^\s:({\[]+)")


def comment_end(t, i):
    """The index just past the `-/` closing the block comment that opens at `i`; they nest."""
    depth, j = 0, i
    while j < len(t) - 1:
        if t.startswith("/-", j):
            depth, j = depth + 1, j + 2
        elif t.startswith("-/", j):
            depth, j = depth - 1, j + 2
            if depth == 0:
                return j
        else:
            j += 1
    raise ValueError("unclosed comment")


def code(t):
    """The file without comments, docstrings or whitespace runs: what Lean elaborates."""
    out, j = [], 0
    while j < len(t):
        if t.startswith("/-", j):
            j = comment_end(t, j)
        elif t.startswith("--", j):
            j = t.find("\n", j) if "\n" in t[j:] else len(t)
        elif t[j] == '"':
            k = j + 1
            while k < len(t) and t[k] != '"':
                k += 2 if t[k] == "\\" else 1
            out.append(t[j:k + 1])
            j = k + 1
        else:
            out.append(t[j])
            j += 1
    return re.sub(r"\s+", " ", "".join(out)).strip()


def module_doc(t):
    """The span of the module docstring's text, or None. Comments nest, so a `/-je-/` in its prose
    does not end it."""
    i = t.find("/-!")
    return (i + 3, comment_end(t, i) - 2) if i >= 0 else None


def headliners(t):
    """The theorems that carry a docstring: (docstring start, docstring end, indent, docstring, name)."""
    span = module_doc(t)
    start = span[1] + 2 if span else 0
    for d in re.finditer(r"(?m)^([ \t]*)/--", t):
        if d.start() < start:
            continue
        end = comment_end(t, d.start() + len(d.group(1)))
        thm = DECL.match(t, end)
        if thm:
            yield d.start(), end, d.group(1), t[d.start() + len(d.group(1)) + 3:end - 2], thm.group(2)


def locators(doc):
    """The paper locators and citation keys a docstring gives, in order."""
    locs = list(dict.fromkeys(re.sub(r"\s+", " ", m.group(0)).strip() for m in LOCATOR.finditer(doc)))
    return locs, [f"[{k}]" for k in dict.fromkeys(CITE.findall(doc))]


def demote(t, names):
    """`t` with the docstrings of the theorems in `names` turned into locator comments."""
    out, i = [], 0
    for start, end, indent, doc, name in headliners(t):
        if not any(name == n or name.endswith("." + n) or n.endswith("." + name) for n in names):
            continue
        locs, keys = locators(doc)
        line_end = end + 1 if t[end:end + 1] == "\n" else end
        out.append(t[i:start])
        if locs or keys:
            out.append(indent + "-- " + " ".join(filter(None, [", ".join(locs), " ".join(keys)])) + "\n")
        if line_end == end:
            out.append(indent)
        i = line_end
    out.append(t[i:])
    return "".join(out)


def breach(t):
    """Why the file breaks the first rule, or None."""
    n = len(list(headliners(t)))
    return None if 1 <= n <= CAP else f"documents {n} theorems (one to {CAP})"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--demote", nargs="+", metavar=("FILE", "NAME"), help="demote theorems to minor")
    ap.add_argument("--write-baseline", action="store_true", help="list the studies the first rule exempts")
    args = ap.parse_args()
    studies = sorted((ROOT / "Studies").glob("*.lean"))

    if args.demote:
        f, names = Path(args.demote[0]), args.demote[1:]
        t = f.read_text(encoding="utf-8")
        new = demote(t, names)
        if code(new) != code(t):
            sys.exit(f"{f}: demoting would change code; edit it by hand")
        f.write_text(new, encoding="utf-8")
        print(f"{f}: {len(list(headliners(t))) - len(list(headliners(new)))} docstrings demoted")
        return

    if args.write_baseline:
        exempt = [f.stem for f in studies if breach(f.read_text(encoding="utf-8"))]
        BASELINE.write_text("\n".join(exempt) + "\n", encoding="utf-8")
        print(f"wrote {BASELINE.relative_to(ROOT)}: {len(exempt)} studies")
        return

    exempt = set(BASELINE.read_text(encoding="utf-8").split()) if BASELINE.exists() else set()
    breaches, leave = [], []
    for f in studies:
        t = f.read_text(encoding="utf-8")
        why = breach(t)
        if why and f.stem not in exempt:
            breaches.append(f"{f.relative_to(ROOT)}: {why}")
        elif not why and f.stem in exempt:
            leave.append(f.stem)
        span = module_doc(t)
        if span and MAIN.search(t, span[0], span[1]):
            breaches.append(f"{f.relative_to(ROOT)}: the module docstring lists main results; "
                            "the theorems with docstrings are the headline results")
    for b in breaches:
        print(b)
    for s in leave:
        print(f"note: {s} now passes; remove it from {BASELINE.relative_to(ROOT)}")
    print(f"{len(studies)} studies, {len(exempt)} exempt from the count, {len(breaches)} breaches")
    sys.exit(1 if breaches else 0)


if __name__ == "__main__":
    main()
