#!/usr/bin/env python3
"""Check study files against the example rows they import.

A study reads `Data/Examples/<Paper>.json` through string literals: row ids, `paperFeatures`
keys and values, reading names, judgments. When a row is renamed or re-encoded those literals
go stale silently — a hypothesis such as `r.id ≠ "old_id"` excludes nothing, a `feature?` on a
missing key returns `none` everywhere and the theorem quantifies over no rows. This script
finds such literals, keys that repeat within a row but are read by a first-match lookup
(`feature?`, `parse?`, `nat?`, `int?`; `features` reads every value), and
`source.bibkey`s absent from `references.bib`. Example sets no module imports, and judgment
comparisons no row can satisfy, are reported as warnings.

Usage:
    python3 scripts/check_examples.py            # exit 1 on any error
"""

import collections
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXAMPLES = os.path.join(ROOT, "Linglib", "Data", "Examples")
FIRST_FUNS = r"(?:feature\?|parse\?|nat\?|int\?)"
KEY_FUNS = r"(?:feature\?|parse\?|nat\?|int\?|features)"
ID_LIKE = r'"([a-z][a-z0-9]*\d{4}[a-z]?_[A-Za-z0-9_.-]+)"'


def features(row):
    raw = row.get("paperFeatures", [])
    if isinstance(raw, dict):
        return list(raw.items())
    return [(x[0], str(x[1])) for x in raw if isinstance(x, list) and len(x) >= 2]


def load_papers():
    papers = {}
    for path in glob.glob(os.path.join(EXAMPLES, "*.json")):
        rows = json.load(open(path, encoding="utf-8"))
        if isinstance(rows, dict):
            rows = rows["examples"]
        info = dict(ids=set(), keys=set(), dupkeys=set(), vals=collections.defaultdict(set),
                    readings=set(), judgments=set(), bibkeys=set())
        for r in rows:
            info["ids"].add(r.get("id"))
            info["judgments"].add(r.get("judgment"))
            for src in (r.get("source"), r.get("reportedIn")):
                if isinstance(src, dict) and src.get("bibkey"):
                    info["bibkeys"].add(src["bibkey"])
            for rd in r.get("readings", []):
                info["readings"].add(rd.get("name") if isinstance(rd, dict) else rd[0])
            counts = collections.Counter(k for k, _ in features(r))
            for k, n in counts.items():
                info["keys"].add(k)
                if n > 1:
                    info["dupkeys"].add(k)
            for k, v in features(r):
                info["vals"][k].add(v)
        papers[os.path.basename(path)[:-5]] = info
    return papers


def strip_comments(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


def lean_sources():
    """The Lean files that may import an example set: the library's and the studies'."""
    return sorted(path for d in ("Linglib", "Studies")
                  for path in glob.glob(os.path.join(ROOT, d, "**", "*.lean"), recursive=True)
                  if os.sep + "Examples" + os.sep not in path)


def imported_sets():
    imps = set()
    for path in lean_sources():
        src = open(path, encoding="utf-8").read()
        imps |= set(re.findall(r"^(?:public )?import Linglib\.Data\.Examples\.(\w+)", src, flags=re.M))
    return imps


def check_bibkeys(papers, imported):
    bib = open(os.path.join(ROOT, "references.bib"), encoding="utf-8").read()
    keys = set(re.findall(r"@\w+\{\s*([^,\s]+)\s*,", bib))
    findings = []
    for name, info in sorted(papers.items()):
        if name not in imported:
            findings.append(("Data/Examples/%s.json" % name, "ORPHAN", name,
                             "no module imports this example set"))
            continue
        for k in sorted(info["bibkeys"] - keys):
            findings.append(("Data/Examples/%s.json" % name, "BIBKEY", k, "not in references.bib"))
    return findings


def check_study(path, papers):
    src = open(path, encoding="utf-8").read()
    imps = [i for i in re.findall(r"^(?:public )?import Linglib\.Data\.Examples\.(\w+)", src, flags=re.M)
            if i in papers]
    if not imps:
        return []
    body = strip_comments(src)
    union = lambda field: set().union(*(papers[i][field] for i in imps))
    ids, keys, dup = union("ids"), union("keys"), union("dupkeys")
    readings, judgments = union("readings"), union("judgments")
    vals = collections.defaultdict(set)
    for i in imps:
        for k, v in papers[i]["vals"].items():
            vals[k] |= v
    rel = os.path.relpath(path, ROOT)
    out = []
    for m in re.finditer(r'\.id\s*(?:=|≠|==|!=|∈|∉)\s*"([^"]*)"', body):
        if m.group(1) not in ids:
            out.append((rel, "ID", m.group(1), "no such row"))
    for m in re.finditer(ID_LIKE, body):
        if m.group(1) not in ids:
            out.append((rel, "ID", m.group(1), "no such row"))
    for m in re.finditer(KEY_FUNS + r'\s+"([^"]*)"', body):
        k = m.group(1)
        if k not in keys:
            out.append((rel, "KEY", k, "no row has this key"))
        elif k in dup and re.fullmatch(FIRST_FUNS, m.group(0).split()[0]):
            out.append((rel, "DUP-KEY", k, "repeats within a row; the lookup returns the first"))
    for m in re.finditer(r'\.(?:1|fst)\s*(?:=|==)\s*"([^"]*)"', body):
        k = m.group(1)
        if k not in keys and k not in readings:
            out.append((rel, "KEY", k, "no row has this key or reading"))
    for m in re.finditer(KEY_FUNS + r'\s+"([^"]*)"\s*(?:=|==|≠|!=)\s*some\s+"([^"]*)"', body):
        k, v = m.groups()
        if k in keys and v not in vals[k]:
            out.append((rel, "VALUE", "%s = %s" % (k, v), "no row has this value"))
    for m in re.finditer(r"judgment\s*(?:=|≠|==|!=)\s*\.(\w+)", body):
        if m.group(1) not in judgments:
            out.append((rel, "JUDGMENT", m.group(1), "rows have %s" % sorted(judgments)))
    return list(dict.fromkeys(out))


WARNINGS = {"ORPHAN", "JUDGMENT"}


def main():
    papers = load_papers()
    findings = check_bibkeys(papers, imported_sets())
    for path in lean_sources():
        findings += check_study(path, papers)
    errors = [f for f in findings if f[1] not in WARNINGS]
    for f in findings:
        print("%s\t%s" % ("WARNING" if f[1] in WARNINGS else "ERROR", "\t".join(f)))
    print("%d error(s), %d warning(s) over %d example sets"
          % (len(errors), len(findings) - len(errors), len(papers)), file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
