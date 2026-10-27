#!/usr/bin/env python3
"""Check that each study names at most five headline theorems and documents only those.

A study's headline theorems are the ones its module docstring lists under `## Main results` (or
`## Main statements`). Two rules:

- The section exists and names one to five theorems of the file. Studies listed in
  `scripts/headliners_baseline.txt` predate the rule and are exempt until they are next audited;
  a listed study that passes is reported so it can leave the list.
- A theorem the module docstring does not name has no docstring: a paper locator or citation goes
  in a `--` comment instead. When the section is missing, every theorem the docstring mentions
  counts as named. Theorems whose proof has `sorry`, or whose docstring mentions TODO, UNVERIFIED
  or `sorry`, keep their docstrings.

`--fix` rewrites the docstrings of unnamed theorems as such comments (`-- Table 3`, `-- (12), p. 4
[key]`), or drops those with neither, and confirms that nothing but comments changed.

Usage, from the repository root:

    python3 scripts/check_headliners.py                    # check every study, exit 1 on a breach
    python3 scripts/check_headliners.py --fix [FILE ...]   # rewrite minor docstrings (all studies)
    python3 scripts/check_headliners.py --write-baseline   # list the studies the first rule exempts
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "headliners_baseline.txt"
CAP = 5
MOD = re.compile(r"/-!(.*?)-/", re.S)
MAIN = re.compile(r"^## Main (?:results|statements)\s*\n(.*?)(?=^## |\Z)", re.S | re.M)
NAME = re.compile(r"`([A-Za-z_][\w.'₀-₉]*)`")
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
DECL = re.compile(r"\s*((?:@\[[^\]]*\]\s*)*)((?:(?:private|protected|nonrec|noncomputable) )*)"
                  r"(theorem|lemma)\s+([^\s:({\[]+)")
THEOREM = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec) )*"
                     r"(?:theorem|lemma)\s+([^\s:({\[]+)")


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


def header(t):
    """The names the module docstring lists as main results (None without the section), the names
    it mentions anywhere, and where it ends."""
    m = MOD.search(t)
    if not m:
        return None, set(), 0
    main = MAIN.search(m.group(1))
    listed = list(dict.fromkeys(NAME.findall(main.group(1)))) if main else None
    return listed, set(NAME.findall(m.group(1))), m.end()


def named(name, names):
    """Whether a declared theorem is among `names`, either written in full or by its last part."""
    return any(name == n or name.endswith("." + n) or n.endswith("." + name) for n in names)


def body_of(t, start):
    """The declaration from `start` to the next line that begins at column 0."""
    nl = t.find("\n", start)
    m = re.search(r"\n(?=\S)", t[nl:]) if nl >= 0 else None
    return t[start:nl + m.start()] if m else t[start:]


def locators(doc):
    """The paper locators and citation keys a docstring gives, in order."""
    locs = list(dict.fromkeys(re.sub(r"\s+", " ", m.group(0)).strip() for m in LOCATOR.finditer(doc)))
    return locs, [f"[{k}]" for k in dict.fromkeys(CITE.findall(doc))]


def minor_docstrings(t):
    """The docstrings of theorems the header does not name: (start, end, indent, doc, name)."""
    listed, mentioned, start = header(t)
    heads = mentioned if listed is None else set(listed)
    for m in re.finditer(r"(?m)^([ \t]*)/--", t):
        if m.start() < start:
            continue
        end = comment_end(t, m.start() + len(m.group(1)))
        d = DECL.match(t, end)
        if not d or named(d.group(4), heads):
            continue
        doc = t[m.start() + len(m.group(1)) + 3:end - 2]
        if re.search(r"\bsorry\b", body_of(t, d.start(3))) or re.search(r"TODO|UNVERIFIED|\bsorry\b", doc):
            continue
        yield m.start(), end, m.group(1), doc, d.group(4)


def fix(t):
    out, i = [], 0
    for start, end, indent, doc, _ in minor_docstrings(t):
        if start < i:
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


def cap_breach(t):
    """Why the file breaks the first rule, or None."""
    listed, _, _ = header(t)
    if listed is None:
        return "no `## Main results` section"
    theorems = THEOREM.findall(t)
    missing = [n for n in listed if not any(named(d, [n]) for d in theorems)]
    if missing:
        return "lists names that are not theorems of the file: " + ", ".join(missing)
    if not 1 <= len(listed) <= CAP:
        return f"lists {len(listed)} main results (at most {CAP})"
    return None


def studies(paths=None):
    return [Path(p) for p in paths] if paths else sorted((ROOT / "Studies").glob("*.lean"))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--fix", nargs="*", metavar="FILE", help="rewrite the docstrings of unnamed theorems")
    ap.add_argument("--write-baseline", action="store_true", help="list the studies the first rule exempts")
    args = ap.parse_args()

    if args.fix is not None:
        changed = 0
        for f in studies(args.fix):
            t = f.read_text(encoding="utf-8")
            new = fix(t)
            if new != t:
                if code(new) != code(t):
                    sys.exit(f"{f}: rewriting the docstrings would change code; fix it by hand")
                f.write_text(new, encoding="utf-8")
                changed += 1
        print(f"rewrote minor docstrings in {changed} files")
        return

    if args.write_baseline:
        exempt = [f.stem for f in studies() if cap_breach(f.read_text(encoding="utf-8"))]
        BASELINE.write_text("\n".join(exempt) + "\n", encoding="utf-8")
        print(f"wrote {BASELINE.relative_to(ROOT)}: {len(exempt)} studies")
        return

    exempt = set(BASELINE.read_text(encoding="utf-8").split()) if BASELINE.exists() else set()
    breaches, leave = [], []
    for f in studies():
        t = f.read_text(encoding="utf-8")
        why = cap_breach(t)
        if why and f.stem not in exempt:
            breaches.append(f"{f.relative_to(ROOT)}: {why}")
        elif not why and f.stem in exempt:
            leave.append(f.stem)
        for _, _, _, _, name in minor_docstrings(t):
            breaches.append(f"{f.relative_to(ROOT)}: `{name}` is not a main result but has a docstring "
                            "(run with --fix)")
    for b in breaches:
        print(b)
    for s in leave:
        print(f"note: {s} now passes; remove it from {BASELINE.relative_to(ROOT)}")
    print(f"{len(studies())} studies, {len(exempt)} exempt from the cap, {len(breaches)} breaches")
    sys.exit(1 if breaches else 0)


if __name__ == "__main__":
    main()
