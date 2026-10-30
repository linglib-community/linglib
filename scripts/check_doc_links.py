#!/usr/bin/env python3
"""Check that every `[text](##name)` link in a docstring resolves to a declaration.

doc-gen4 resolves a `##name` link in three steps (`DocGen4/Output/DocString.lean`, `nameToLink?`):
the exact full name of a documented declaration, constructor or structure field; else a module
name; else the first public declaration of the *same* module whose trailing name components
agree with the link's. Anything else becomes a search link to nothing. The docs site documents
only `Linglib`, `Studies`, `Eval` and `Lab`, so a link to a mathlib name never resolves, a
`private` declaration is never a target, and a link into another module needs the full name.

The checker parses declarations textually, as `check_headliners.py` does: namespaces, sections
and `mutual` blocks for the full names, `private` for visibility, and the constructors and fields
of inductives, structures and classes. Two rules:

- Every link in a module docstring (`/-! -/`) or declaration docstring (`/-- -/`) under
  `Linglib/` or `Studies/` resolves.
- A suffix match is unique: a short link that two declarations of the module end with is
  reported, since doc-gen4 silently takes the first.

Usage, from the repository root:

    python3 scripts/check_doc_links.py                   # check every file
    python3 scripts/check_doc_links.py FILE ...          # report only these files
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCUMENTED = ("Linglib", "Studies", "Eval", "Lab")
CHECKED = ("Linglib", "Studies")
LINK = re.compile(r"\]\(##([^)\s]+)\)")
IDENT = r"[^\s:({\[\]|,]+"
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|meta)\s+)*"
DECL = re.compile(r"[ \t]*(?:@\[[^\]\n]*\][ \t]*)*" + MODIFIERS +
                  r"(theorem|lemma|def|abbrev|instance|structure|class(?:\s+inductive)?|"
                  r"inductive|opaque|axiom|irreducible_def|alias)\s+(" + IDENT + r")")


COMMENT = re.compile(r"/-|-/")
START = re.compile(r'/-|--|"')


def comment_end(t, i):
    """The index just past the `-/` closing the block comment that opens at `i`; they nest."""
    depth = 0
    for m in COMMENT.finditer(t, i):
        depth += 1 if m.group() == "/-" else -1
        if depth == 0:
            return m.end()
    raise ValueError("unclosed comment")


def blank(t):
    """`t` with comments and strings replaced by spaces, newlines kept, and the docstrings:
    (start, end) of each `/-!` or `/--` comment."""
    out, docs, j = [], [], 0
    while (m := START.search(t, j)):
        a = m.start()
        if m.group() == "/-":
            e = comment_end(t, a)
            if t.startswith("/-!", a) or t.startswith("/--", a):
                docs.append((a, e))
        elif m.group() == "--":
            e = t.find("\n", a)
            e = len(t) if e < 0 else e
        else:
            e = a + 1
            while e < len(t) and t[e] != '"':
                e += 2 if t[e] == "\\" else 1
            e += 1
        out.append(t[j:a])
        out.append(re.sub(r"[^\n]", " ", t[a:e]))
        j = e
    out.append(t[j:])
    return "".join(out), docs


def components(name):
    """The components of a dotted name, keeping `«...»` atoms whole."""
    return re.findall(r"«[^»]*»|[^.]+", name)


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def declarations(code):
    """The (full name, private) pairs a file declares, with its constructors and fields, read from
    its text with comments and strings blanked."""
    lines = code.split("\n")
    scopes, decls = [], []
    body = None  # (owner, kind, indent) of the inductive or structure whose body is open

    def prefix():
        return [c for kind, cs in scopes if kind == "namespace" for c in cs]

    def full(name):
        cs = components(name)
        if cs and cs[0] == "_root_":
            return ".".join(cs[1:])
        return ".".join(prefix() + cs)

    for line in lines:
        stripped = line.strip()
        indent = len(line) - len(line.lstrip())
        if not stripped:
            continue
        if body and indent > 0:
            owner, kind, _ = body
            if kind == "inductive":
                for c in re.findall(r"\|\s*(" + IDENT + ")", line):
                    decls.append((owner + "." + c, False))
            else:
                m = re.match(r"\s+(?:(" + IDENT + r")\s*::|((?:" + IDENT + r"\s+)*" + IDENT +
                             r")\s*:(?!=))", line)
                if m and m.group(1):
                    decls.append((owner + "." + m.group(1), False))
                elif m and m.group(2) and not re.match(r"\s*(?:extends|deriving)\b", line):
                    for f in m.group(2).split():
                        decls.append((owner + "." + f, False))
            continue
        if indent == 0 or not body:
            body = None
        m = re.match(r"namespace\s+(\S+)", stripped)
        if m:
            scopes.append(("namespace", components(m.group(1))))
            continue
        if re.match(r"(?:@\[[^\]]*\]\s*)?(?:(?:public|noncomputable)\s+)*section\b", stripped) or \
                stripped == "mutual":
            scopes.append(("section", []))
            continue
        if re.match(r"end\b", stripped):
            if scopes:
                scopes.pop()
            continue
        m = DECL.match(line)
        if not m:
            continue
        kind, owner = m.group(1), full(m.group(2))
        modifiers = re.sub(r"@\[[^\]]*\]", " ", line[:m.start(1)]).split()
        decls.append((owner, "private" in modifiers))
        if kind in ("inductive", "class inductive"):
            body = (owner, "inductive", indent)
            for c in re.findall(r"\|\s*(" + IDENT + ")", line[m.end():]):
                decls.append((owner + "." + c, False))
        elif kind in ("structure", "class"):
            body = (owner, "structure", indent)
    return decls


def links(t, docs):
    """The (line, target) of every `##` link in the docstrings `docs` of `t`."""
    for a, b in docs:
        for m in LINK.finditer(t, a, b):
            yield t.count("\n", 0, m.start()) + 1, m.group(1)


def same_end(n1, n2):
    """doc-gen4's `sameEnd`: the trailing components agree, as far as the shorter name goes."""
    return all(a == b for a, b in zip(reversed(n1), reversed(n2)))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="*", type=Path, help="report only these files")
    args = ap.parse_args()

    files = sorted(f for d in DOCUMENTED for f in (ROOT / d).rglob("*.lean"))
    names, modules, members, texts = set(), set(), {}, {}
    for f in files:
        mod = module_name(f)
        modules.add(mod)
        t = f.read_text(encoding="utf-8")
        code, docs = blank(t)
        texts[f] = t, docs
        public = [n for n, private in declarations(code) if not private]
        names.update(public)
        members[mod] = [components(n) for n in public]

    report = {(ROOT / f).resolve() for f in args.files} if args.files else None
    problems, total, checked = [], 0, 0
    for f in files:
        if f.relative_to(ROOT).parts[0] not in CHECKED or report and f.resolve() not in report:
            continue
        checked += 1
        mod = module_name(f)
        for line, target in links(*texts[f]):
            total += 1
            if target in names or target in modules:
                continue
            hits = [n for n in members[mod] if same_end(n, components(target))]
            where = f"{f.relative_to(ROOT)}:{line}"
            if not hits:
                problems.append(f"{where}: `##{target}` resolves to no declaration")
            elif len({".".join(h) for h in hits}) > 1:
                cands = ", ".join(sorted({".".join(h) for h in hits}))
                problems.append(f"{where}: `##{target}` is ambiguous: {cands}")
    for p in problems:
        print(p)
    print(f"{total} links in {checked} files, {len(problems)} unresolved or ambiguous")
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
