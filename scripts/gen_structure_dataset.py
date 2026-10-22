#!/usr/bin/env python3
"""Generate Lean 4 language-sample modules from per-paper CLDF StructureDataset JSON.

Usage:
    python3 scripts/gen_structure_dataset.py <AuthorYear>
    python3 scripts/gen_structure_dataset.py --all            # regenerate every paper
    python3 scripts/gen_structure_dataset.py --check [<P>]    # verify sync, no writes

Reads   Linglib/Data/StructureDataset/<AuthorYear>.json
Writes  Linglib/Data/StructureDataset/<AuthorYear>.lean, declaring
        `namespace <AuthorYear>.StructureDataset`.

JSON file format, the CLDF StructureDataset tables under CLDF column names:

  {
    "bibkey": "bobaljik-2012", "description": "...",
    "ContributionTable": [{"ID": "broad_sample", "Name": "Table A.1", "Lean": "broadSample",
                           "Source": "bobaljik-2012[Table A.1]", "Description": "..."}],
    "LanguageTable": [{"ID": "tamashek", "Name": "Tamashek", "Glottocode": "tama1365",
                       "Lineage": "Afro-Asiatic, Berber"}],
    "ParameterTable": [{"ID": "cmpr_typ", "Name": "CMPR TYP", "Lean": "CmprTyp",
                        "Description": "..."}],
                       # a parameter may add "Codes": "<parameter ID>" to take that one's codes
    "CodeTable": [{"ID": "cmpr_typ_ex", "Parameter_ID": "cmpr_typ", "Name": "EX",
                   "Lean": "exceed", "Description": "..."}],
    "ValueTable": [{"Language_ID": "tamashek", "Parameter_ID": "cmpr_typ",
                    "Code_ID": "cmpr_typ_st", "Contribution_ID": "broad_sample",
                    "Questionable": false, "Optional": false, "Minor": false}]
  }

Each contribution is one table of the source, and languages, parameters and codes are shared
among them. `Glottocode` may be null, with a `comment` saying why. A parameter's `Lean` is the
name of its generated type, a code's `Lean` the name of its constructor, and a contribution's
`Lean` the name of its list of rows. A parameter with `Codes` declares no codes of its own: its
values take the codes of the parameter it names, which declares none of its own `Codes`, and its
field has that parameter's type; a parameter whose codes others take and which has no values is
emitted as a type with no field. `Minor` marks a code the source qualifies as holding of only
some of the language's items. Within a contribution each language becomes one row with a
list-valued field per parameter, the rows in the order of the language's first value and the
values in the order of the `ValueTable`. `Value` (the printed form, where it differs from the
code's `Name`), `comment` (any table) and `Lineage` are validated and not emitted. The generator
rejects malformed input, unknown keys, dangling references, unused languages and unknown
bibkeys; it is idempotent, and `--check` exits 1 on drift.
"""

import json
import re
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "Linglib" / "Data" / "StructureDataset"
BIB = ROOT / "references.bib"

ID_RE = re.compile(r"^[a-z][a-z0-9_]*$")
GLOTTO_RE = re.compile(r"^[a-z0-9]{4}[0-9]{4}$")
TYPE_RE = re.compile(r"^[A-Z][A-Za-z0-9]*$")
CTOR_RE = re.compile(r"^[a-z][A-Za-z0-9]*$")
SOURCE_RE = re.compile(r"^\s*([^\[\]\s]+)\s*(?:\[(.*)\])?\s*$")
KEYWORDS = {"def", "if", "then", "else", "do", "fun", "let", "in", "at", "by", "end", "match",
            "with", "where", "from", "have", "show", "open", "for", "return", "import", "true",
            "false", "theorem", "structure", "class", "instance", "section", "namespace"}

TABLES = {"ContributionTable": {"ID", "Name", "Lean", "Source", "Description", "comment"},
          "LanguageTable": {"ID", "Name", "Glottocode", "Lineage", "comment"},
          "ParameterTable": {"ID", "Name", "Lean", "Description", "Codes", "comment"},
          "CodeTable": {"ID", "Parameter_ID", "Name", "Lean", "Description", "comment"},
          "ValueTable": {"Language_ID", "Parameter_ID", "Code_ID", "Contribution_ID", "Value",
                         "Questionable", "Optional", "Minor", "comment"}}


def fail(msg: str):
    raise ValueError(msg)


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def doc(s: str, where: str) -> str:
    if "-/" in s or "/-" in s:
        fail(f"{where}: text contains a comment delimiter")
    return s


def check_keys(row: dict, table: str, where: str):
    extra = set(row) - TABLES[table]
    if extra:
        fail(f"{where}: unknown keys {sorted(extra)}")
    for k in ("comment", "Lineage", "Value"):
        if k in row and not isinstance(row[k], str):
            fail(f"{where}: {k} must be a string")


def req(row: dict, key: str, where: str) -> str:
    v = row.get(key)
    if not isinstance(v, str) or not v.strip():
        fail(f"{where}: {key} is required and non-empty")
    return v


def lower_first(s: str) -> str:
    return s[0].lower() + s[1:]


def emit_module(paper: str, data: dict) -> str:
    unknown = set(data) - set(TABLES) - {"bibkey", "description"}
    if unknown:
        fail(f"unknown top-level keys {sorted(unknown)}")
    keys = set(re.findall(r"^@\w+\{([^,]+),", BIB.read_text(encoding="utf-8"), re.M))
    if data.get("bibkey") not in keys:
        fail(f"bibkey {data.get('bibkey')!r} is not in references.bib")

    contribs = {}
    for r in data.get("ContributionTable") or []:
        where = f"contribution {r.get('ID')!r}"
        check_keys(r, "ContributionTable", where)
        cid = req(r, "ID", where)
        if not ID_RE.match(cid) or cid in contribs:
            fail(f"{where}: bad or duplicate ID")
        lean = req(r, "Lean", where)
        if (not CTOR_RE.match(lean) or lean in KEYWORDS
                or lean in [c["Lean"] for c in contribs.values()]):
            fail(f"{where}: Lean {lean!r} is not a fresh definition name")
        m = SOURCE_RE.match(r.get("Source") or "")
        if not m or m.group(1) not in keys:
            fail(f"{where}: Source must be bibkey[locator] with a bibkey in references.bib")
        req(r, "Name", where)
        req(r, "Description", where)
        contribs[cid] = {**r, "source": f"{m.group(1)}, {m.group(2)}" if m.group(2) else m.group(1),
                         "rows": {}}
    if not contribs:
        fail("ContributionTable is required and non-empty")

    params = {}
    for r in data.get("ParameterTable") or []:
        where = f"parameter {r.get('ID')!r}"
        check_keys(r, "ParameterTable", where)
        pid = req(r, "ID", where)
        if not ID_RE.match(pid) or pid in params:
            fail(f"{where}: bad or duplicate ID")
        if not TYPE_RE.match(req(r, "Lean", where)):
            fail(f"{where}: Lean must be a type name")
        req(r, "Name", where)
        if "Codes" in r and (r["Codes"] not in params or "Codes" in params[r["Codes"]]):
            fail(f"{where}: Codes must name an earlier parameter with codes of its own")
        params[pid] = {**r, "codes": []}
    owner = {pid: p.get("Codes", pid) for pid, p in params.items()}
    codes = {}
    for r in data.get("CodeTable") or []:
        where = f"code {r.get('ID')!r}"
        check_keys(r, "CodeTable", where)
        cid = req(r, "ID", where)
        if cid in codes:
            fail(f"{where}: duplicate ID")
        pid = req(r, "Parameter_ID", where)
        if pid not in params:
            fail(f"{where}: parameter {pid!r} not in ParameterTable")
        if owner[pid] != pid:
            fail(f"{where}: parameter {pid!r} takes the codes of {owner[pid]!r}")
        ctor = req(r, "Lean", where)
        if not CTOR_RE.match(ctor) or ctor in KEYWORDS:
            fail(f"{where}: Lean {ctor!r} is not a constructor name")
        if ctor in [c["Lean"] for c in params[pid]["codes"]]:
            fail(f"{where}: duplicate constructor {ctor!r}")
        req(r, "Name", where)
        codes[cid] = r
        params[pid]["codes"].append(r)

    langs = {}
    for r in data.get("LanguageTable") or []:
        where = f"language {r.get('ID')!r}"
        check_keys(r, "LanguageTable", where)
        lid = req(r, "ID", where)
        if not ID_RE.match(lid) or lid in langs or lid in KEYWORDS:
            fail(f"{where}: bad or duplicate ID")
        g = r.get("Glottocode")
        if g is None:
            if not r.get("comment"):
                fail(f"{where}: a language without a Glottocode needs a comment saying why")
        elif not (isinstance(g, str) and GLOTTO_RE.match(g)):
            fail(f"{where}: Glottocode {g!r} is not a Glottocode")
        req(r, "Name", where)
        if lid in [c["Lean"] for c in contribs.values()]:
            fail(f"{where}: ID {lid!r} is the Lean name of a contribution")
        langs[lid] = r

    valued = set()
    for k, r in enumerate(data.get("ValueTable") or []):
        where = f"value {k}"
        check_keys(r, "ValueTable", where)
        lid, pid, cid, con = (req(r, x, where) for x in
                              ("Language_ID", "Parameter_ID", "Code_ID", "Contribution_ID"))
        if lid not in langs:
            fail(f"{where}: language {lid!r} not in LanguageTable")
        if pid not in params:
            fail(f"{where}: parameter {pid!r} not in ParameterTable")
        if cid not in codes or codes[cid]["Parameter_ID"] != owner[pid]:
            fail(f"{where}: code {cid!r} is not a code of {pid!r}")
        if con not in contribs:
            fail(f"{where}: contribution {con!r} not in ContributionTable")
        for flag in ("Questionable", "Optional", "Minor"):
            if flag in r and not isinstance(r[flag], bool):
                fail(f"{where}: {flag} must be a boolean")
        valued.add(pid)
        row = contribs[con]["rows"].setdefault(lid, {p: [] for p in params})
        row[pid].append(f"⟨.{codes[cid]['Lean']}, {str(r.get('Questionable', False)).lower()}, "
                        f"{str(r.get('Optional', False)).lower()}, "
                        f"{str(r.get('Minor', False)).lower()}⟩")
    unused = set(langs) - {lid for c in contribs.values() for lid in c["rows"]}
    if unused:
        fail(f"languages without values: {sorted(unused)}")

    taken = {owner[q] for q in params if owner[q] != q}
    fielded = [pid for pid in params if pid in valued or pid not in taken]
    out = []
    for p in params.values():
        if "Codes" in p:
            continue
        ctors = "\n".join(f"  /-- `{doc(c['Name'], c['ID'])}`: {doc(c.get('Description', ''), c['ID'])} -/\n"
                          f"  | {c['Lean']}" for c in p["codes"])
        out.append(f"/-- {p['Name']}: {doc(p.get('Description', ''), p['ID'])} -/\n"
                   f"inductive {p['Lean']} where\n{ctors}\n  deriving DecidableEq, Repr")
    fields = "\n".join(f"  /-- The codes for {params[pid]['Name']}. -/\n  "
                       f"{lower_first(params[pid]['Lean'])} : "
                       f"List (Coded {params[owner[pid]]['Lean']})" for pid in fielded)
    out.append(f"/-- A row of a sample: a language with its codes for each parameter. -/\n"
               f"structure Row where\n  /-- The language. -/\n  language : Language\n{fields}\n"
               f"  deriving DecidableEq, Repr")
    for lid, r in langs.items():
        g = f"some {lean_string(r['Glottocode'])}" if r.get("Glottocode") else "none"
        out.append(f"def {lid} : Language :=\n  {{ id := {lean_string(lid)}, "
                   f"name := {lean_string(r['Name'])}, glottocode := {g} }}")
    for c in contribs.values():
        rows = []
        for lid, vals in c["rows"].items():
            vs = ",\n    ".join(f"{lower_first(params[p]['Lean'])} := [{', '.join(vals[p])}]"
                                for p in fielded)
            rows.append(f"  {{ language := {lid},\n    {vs} }}")
        out.append(f"/-- {doc(c['Description'], c['ID'])} The rows of {c['Name']}, in the order "
                   f"of the source ({c['source']}). -/\n"
                   f"def {c['Lean']} : List Row := [\n" + ",\n".join(rows) + "]")
    body = "\n\n".join(out)
    return f"""import Linglib.Data.StructureDataset.Schema

/-!
# `{paper}`: language samples

Auto-generated from `Linglib/Data/StructureDataset/{paper}.json` by
`scripts/gen_structure_dataset.py`. Do not edit by hand; edit the JSON and re-run the generator.
Declarations live in `namespace {paper}.StructureDataset`.
-/

namespace {paper}.StructureDataset

open Data.StructureDataset

{body}

end {paper}.StructureDataset
"""


def process(paper: str, check: bool) -> bool:
    path = JSON_DIR / f"{paper}.json"
    if not path.exists():
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)} not found\n")
        sys.exit(1)
    try:
        text = as_module_if_possible(emit_module(paper, json.loads(path.read_text(encoding="utf-8"))))
    except (ValueError, json.JSONDecodeError) as e:
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)
    target = JSON_DIR / f"{paper}.lean"
    in_sync = target.exists() and target.read_text(encoding="utf-8") == text
    rel = target.relative_to(ROOT)
    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel} in sync\n")
        else:
            sys.stderr.write(f"[check] DRIFT: {rel}; run scripts/gen_structure_dataset.py {paper}\n")
        return in_sync
    if not in_sync:
        target.write_text(text, encoding="utf-8")
    sys.stdout.write(f"[gen] {rel} {'unchanged' if in_sync else 'written'}\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    if args == ["--all"] or (not args and check):
        papers = sorted(p.stem for p in JSON_DIR.glob("*.json"))
    elif len(args) == 1 and not args[0].startswith("-"):
        papers = args
    else:
        sys.stderr.write(__doc__)
        sys.exit(1)
    if not all([process(p, check) for p in papers]):
        sys.exit(1)


if __name__ == "__main__":
    main()
