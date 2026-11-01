#!/usr/bin/env python3
"""Generate typed modules of a paper's printed statistics from canonical per-paper JSON.

The statistics a paper prints, from an experiment, a corpus, a survey, a typological sample or a
model, are canonical JSON at `Linglib/Data/Statistics/<Paper>.json`; this emits the typed Lean
module
`Linglib/Data/Statistics/<Paper>.lean`, in `namespace <Paper>` beside the paper's study, so
that the study reads the tables and extends the paper's types without opening anything.
The generated Lean is never hand-edited: edit the JSON and re-run.

A JSON file has four parts:

* `meta`: `bibkey` (a `references.bib` key), `description`, `method`, and `rawData`, the
  links to the data the authors released (each a `url` and a `doc`), emitted in the module
  docstring. The `method` is how the paper's statistics were obtained: `experiment`, `corpus`,
  `lexicon` (a dictionary or lexical database), `survey` (sociolinguistic interviews or
  questionnaires), `typology` (a sample of languages coded from their descriptions) or `model`
  (values a model fits or simulates).
* `types`: the paper's own coding labels, each emitted as an enum. A level has a
  Lean `name`, the `label` the paper prints, and a `doc`.
* `constants`: design values the paper states once (`nat`, `decimal`).
* `tables`: one per printed table, emitted as a structure and a list of rows in the
  paper's order. A table has a `name`, a `structure` name, a `doc`, a `locator`, a
  `verified` status (`raw-data`, `page-image`, `text-layer` or `unverified`), its `columns`
  and its `rows`, and a `method` where it differs from the paper's. A row may carry a `note`, emitted as a comment. A table with a
  `key`, a list of enum columns whose every combination of levels has exactly one
  row, is emitted as a total function from the key to the other columns.

Column types form a closed vocabulary:

* `nat`, `int`
* `decimal`: a JSON string as printed ("99.1", "75", "0", or a power of ten "10^-5"),
  emitted as `Data.Statistics.Decimal`
* `pvalue`: a p-value as printed, a decimal with the relation it is printed with
  ("< 0.001", "> 0.4", or "0.15" for a value), emitted as `Data.Statistics.PValue`
* `<Type>`: a level of a declared type, written by its label
* `literals <Type>`: a signed feature list in the paper's notation,
  "[+IHCr, -Mediation]", emitted as `List (<Type> × Sign)`
* `option <T>`, `list <T>` for any of the above (`null` is `none`)

    python3 scripts/gen_statistics.py Hafeez2025       # (re)generate
    python3 scripts/gen_statistics.py --check [<P>]    # verify, no writes (CI)
    python3 scripts/gen_statistics.py --all            # every JSON
"""
import json
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "Statistics"
BIB = ROOT / "references.bib"
VERIFIED = {"raw-data": "recomputed from the authors' released data by `scripts/check_statistics.py`",
            "page-image": "checked against the page images",
            "text-layer": "checked against the PDF text layer only",
            "unverified": "not yet checked against the source"}
METHODS = {"experiment": "from an experiment",
           "corpus": "counted in a corpus",
           "lexicon": "counted in a dictionary or lexical database",
           "survey": "from a sociolinguistic survey",
           "typology": "from a sample of languages coded from their descriptions",
           "model": "fitted or simulated by a model"}
IDENT = re.compile(r"^[a-z][A-Za-z0-9]*$")
TYPE_IDENT = re.compile(r"^[A-Z][A-Za-z0-9]*$")
DECIMAL = re.compile(r"^(-?)(\d+)(?:\.(\d+))?$")
POWER = re.compile(r"^10\^-(\d+)$")
PVALUE = re.compile(r"^(?:([<>]) )?(\S+)$")
LITERAL = re.compile(r"^([+-])\s*(\S+)$")


def fatal(where: str, msg: str):
    sys.stderr.write(f"FATAL: {where}: {msg}\n")
    sys.exit(1)


class Types:
    def __init__(self, types: list, where: str):
        self.levels = {}
        for i, t in enumerate(types):
            w = f"{where}.types[{i}]"
            if not TYPE_IDENT.match(t.get("name", "")):
                fatal(w, f"type name {t.get('name')!r} is not an UpperCamel identifier")
            by_label = {}
            for j, lv in enumerate(t["levels"]):
                if not IDENT.match(lv["name"]):
                    fatal(f"{w}.levels[{j}]", f"level name {lv['name']!r} is not lowerCamel")
                if lv["label"] in by_label or lv["name"] in by_label.values():
                    fatal(f"{w}.levels[{j}]", f"duplicate level {lv['label']!r}")
                by_label[lv["label"]] = lv["name"]
            self.levels[t["name"]] = by_label

    def level(self, ty: str, label, where: str) -> str:
        if not isinstance(label, str) or label not in self.levels[ty]:
            fatal(where, f"{label!r} is not a level of {ty}")
        return f".{self.levels[ty][label]}"


def parse_type(s: str, types: Types, where: str):
    parts = s.split()
    if parts[0] in ("option", "list") and len(parts) > 1:
        return (parts[0], parse_type(" ".join(parts[1:]), types, where))
    if parts[0] == "literals" and len(parts) == 2 and parts[1] in types.levels:
        return ("literals", parts[1])
    if len(parts) == 1 and parts[0] in ("nat", "int", "decimal", "pvalue"):
        return (parts[0],)
    if len(parts) == 1 and parts[0] in types.levels:
        return ("enum", parts[0])
    fatal(where, f"unknown column type {s!r}")


def lean_type(t) -> str:
    match t[0]:
        case "nat": return "ℕ"
        case "int": return "ℤ"
        case "decimal": return "Decimal"
        case "pvalue": return "PValue"
        case "enum": return t[1]
        case "literals": return f"List ({t[1]} × Sign)"
        case "option": return f"Option {paren(lean_type(t[1]))}"
        case "list": return f"List {paren(lean_type(t[1]))}"


def decimal_lit(v, where: str) -> str:
    p = POWER.match(v) if isinstance(v, str) else None
    if p:
        return f"⟨1, {int(p.group(1))}⟩"
    m = DECIMAL.match(v) if isinstance(v, str) else None
    if not m:
        fatal(where, f"decimal {v!r} is not a printed decimal string")
    sign, whole, frac = m.group(1), m.group(2), m.group(3) or ""
    return f"⟨{sign}{int(whole + frac)}, {len(frac)}⟩"


def pvalue_lit(v, where: str) -> str:
    m = PVALUE.match(v) if isinstance(v, str) else None
    if not m:
        fatal(where, f"{v!r} is not a printed p-value")
    rel = {"<": ".lt", ">": ".gt", None: ".eq"}[m.group(1)]
    return f"⟨{rel}, {decimal_lit(m.group(2), where)}⟩"


def literals_lit(v, ty: str, types: Types, where: str) -> str:
    if not (isinstance(v, str) and v.startswith("[") and v.endswith("]")):
        fatal(where, f"{v!r} is not a bracketed literal list")
    items, seen = [], set()
    for part in filter(None, (p.strip() for p in v[1:-1].split(","))):
        m = LITERAL.match(part)
        if not m:
            fatal(where, f"{part!r} is not a signed feature")
        if m.group(2) in seen:
            fatal(where, f"feature {m.group(2)!r} repeats")
        seen.add(m.group(2))
        sign = ".plus" if m.group(1) == "+" else ".minus"
        items.append(f"({types.level(ty, m.group(2), where)}, {sign})")
    return "[" + ", ".join(items) + "]"


def value_lit(v, t, types: Types, where: str) -> str:
    match t[0]:
        case "nat":
            if not (isinstance(v, int) and v >= 0):
                fatal(where, f"{v!r} is not a natural number")
            return str(v)
        case "int":
            if not isinstance(v, int):
                fatal(where, f"{v!r} is not an integer")
            return str(v)
        case "decimal": return decimal_lit(v, where)
        case "pvalue": return pvalue_lit(v, where)
        case "enum": return types.level(t[1], v, where)
        case "literals": return literals_lit(v, t[1], types, where)
        case "option":
            return "none" if v is None else f"some {paren(value_lit(v, t[1], types, where))}"
        case "list":
            if not isinstance(v, list):
                fatal(where, f"{v!r} is not a list")
            return "[" + ", ".join(value_lit(x, t[1], types, f"{where}[{i}]")
                                   for i, x in enumerate(v)) + "]"


def paren(s: str) -> str:
    if s.startswith("-"):
        return f"({s})"
    return f"({s})" if " " in s and not s.startswith(("[", "⟨", "(")) else s


def wrap_field(f: str, end: str, indent: str = "     ") -> list:
    """A field of a wrapped row on its own line, or a long list one element per line."""
    if len(indent) + len(f) + len(end) <= 100 or not f.startswith("["):
        return [f"{indent}{f}{end}"]
    elems, depth, start = [], 0, 1
    for i, ch in enumerate(f):
        if ch in "[(⟨":
            depth += 1
        elif ch in "])⟩":
            depth -= 1
        elif ch == "," and depth == 1:
            elems.append(f[start:i].strip())
            start = i + 1
    elems.append(f[start:-1].strip())
    lines = [f"{indent}[{elems[0]},"]
    lines += [f"{indent} {e}," for e in elems[1:-1]]
    lines.append(f"{indent} {elems[-1]}]{end}")
    return lines


def doc(text: str, indent: str = "") -> str:
    body = textwrap.fill(text, 100 - len(indent) - 7, subsequent_indent=indent)
    return f"{indent}/-- {body} -/"


def render_enum(t: dict) -> str:
    lines = [doc(t["doc"]), f"inductive {t['name']} where"]
    for lv in t["levels"]:
        lines.append(doc(f"{lv['label']}: {lv['doc']}", "  "))
        lines.append(f"  | {lv['name']}")
    lines.append("  deriving DecidableEq, Repr, Fintype")
    return "\n".join(lines)


def render_constant(c: dict, types: Types, where: str) -> str:
    t = parse_type(c["type"], types, where)
    status = VERIFIED.get(c.get("verified"))
    if status is None or not c.get("locator"):
        fatal(where, "a constant needs a locator and a verified status")
    return (doc(f"{c['doc']} ({c['locator']}; {status}.)") + "\n"
            + f"def {c['name']} : {lean_type(t)} := {value_lit(c['value'], t, types, where)}")


def render_table(tb: dict, types: Types, where: str, method: str) -> str:
    status = VERIFIED.get(tb.get("verified"))
    if status is None or not tb.get("locator"):
        fatal(where, "a table needs a locator and a verified status")
    method = tb.get("method", method)
    if method not in METHODS:
        fatal(where, f"method {method!r} is not one of {', '.join(METHODS)}")
    status = f"{METHODS[method]}; {status}"
    cols = [(c["name"], parse_type(c["type"], types, f"{where}.columns[{i}]"), c["doc"])
            for i, c in enumerate(tb["columns"])]
    names = [n for n, _, _ in cols]
    key = tb.get("key", [])
    for k in key:
        t = next((t for n, t, _ in cols if n == k), None)
        if t is None or t[0] != "enum":
            fatal(where, f"key column {k!r} is not a declared enum column")
    fields = [(n, t, d) for n, t, d in cols if n not in key]
    if not fields:
        fatal(where, "a table needs a column besides its key")
    struct = [doc(f"A row of {tb['locator']}: {tb['doc']}"), f"structure {tb['structure']} where"]
    for n, t, d in fields:
        struct += [doc(d, "  "), f"  {n} : {lean_type(t)}"]
    struct.append("  deriving DecidableEq, Repr")
    rows = []
    for i, r in enumerate(tb["rows"]):
        w = f"{where}.rows[{i}]"
        extra = set(r) - set(names) - {"note"}
        missing = set(names) - set(r)
        if extra or missing:
            fatal(w, f"columns missing {sorted(missing)}, undeclared {sorted(extra)}")
        rows.append(([value_lit(r[n], t, types, f"{w}.{n}") for n, t, _ in fields], r.get("note"),
                     tuple(r[k] for k in key)))
    if key:
        return "\n".join(struct) + "\n\n" + render_keyed(tb, key, cols, rows, types, status, where)
    body = []
    for i, (fields, note, _) in enumerate(rows):
        lead = "  [" if i == 0 else "   "
        sep = "," if i < len(rows) - 1 else "]"
        comment = f"  -- {note}" if note else ""
        line = f"{lead}⟨{', '.join(fields)}⟩{sep}"
        if len(line) + len(comment) <= 100:
            body.append(line + comment)
        else:
            body.append(f"{lead}⟨{fields[0]},{comment}")
            for j, f in enumerate(fields[1:], 1):
                end = "," if j < len(fields) - 1 else f"⟩{sep}"
                body += wrap_field(f, end)
    lede = (f"The row of {tb['locator']}" if len(rows) == 1
            else f"The {len(rows)} rows of {tb['locator']}, in the paper's order")
    defn = [doc(f"{lede}; {status}."),
            f"def {tb['name']} : List {tb['structure']} :=", *body]
    return "\n".join(struct) + "\n\n" + "\n".join(defn)


def render_keyed(tb: dict, key: list, cols: list, rows: list, types: Types, status: str,
                 where: str) -> str:
    """A table keyed by enum columns, as a total function by exhaustive `match`."""
    ktypes = [next(t[1] for n, t, _ in cols if n == k) for k in key]
    seen = {}
    for i, (_, _, kv) in enumerate(rows):
        if kv in seen:
            fatal(f"{where}.rows[{i}]", f"key {list(kv)} repeats row {seen[kv]}")
        seen[kv] = i
    cells = [()]
    for ty in ktypes:
        cells = [c + (lab,) for c in cells for lab in types.levels[ty]]
    missing = [list(c) for c in cells if c not in seen]
    if missing:
        fatal(where, f"keys {missing} have no row")
    arms = []
    for fields, note, kv in rows:
        pat = ", ".join(types.level(ty, lab, where) for ty, lab in zip(ktypes, kv))
        comment = f"  -- {note}" if note else ""
        line = f"  | {pat} => ⟨{', '.join(fields)}⟩"
        if len(line) + len(comment) <= 100:
            arms.append(line + comment)
        else:
            arms.append(f"  | {pat} =>{comment}")
            arms.append(f"    ⟨{fields[0]}," if len(fields) > 1 else f"    ⟨{fields[0]}⟩")
            for j, f in enumerate(fields[1:], 1):
                arms += wrap_field(f, "," if j < len(fields) - 1 else "⟩")
    sig = " → ".join(ktypes + [tb["structure"]])
    return "\n".join([doc(f"The cells of {tb['locator']}, by {' and '.join(key)}; {status}."),
                      f"def {tb['name']} : {sig}", *arms])


def bibkeys() -> set:
    return set(re.findall(r"^@\w+\{([^,\s]+),", BIB.read_text(encoding="utf-8"), re.M))


def render(paper: str, d: dict) -> str:
    meta = d["meta"]
    if meta.get("bibkey") not in bibkeys():
        fatal(f"{paper}.meta", f"bibkey {meta.get('bibkey')!r} not in references.bib")
    raw = meta.get("rawData", [])
    for i, r in enumerate(raw):
        if not str(r.get("url", "")).startswith("https://") or not r.get("doc"):
            fatal(f"{paper}.meta.rawData[{i}]", "a raw-data link needs an https url and a doc")
    for i, tb in enumerate(d.get("tables", [])):
        if tb.get("verified") == "raw-data" and not raw:
            fatal(f"{paper}.tables[{i}]", "verified from raw data, but meta.rawData lists none")
    if meta.get("method") not in METHODS:
        fatal(f"{paper}.meta", f"method {meta.get('method')!r} is not one of {', '.join(METHODS)}")
    types = Types(d.get("types", []), paper)
    parts = [render_enum(t) for t in d.get("types", [])]
    parts += [render_constant(c, types, f"{paper}.constants[{i}]")
              for i, c in enumerate(d.get("constants", []))]
    parts += [render_table(tb, types, f"{paper}.tables[{i}]", meta["method"])
              for i, tb in enumerate(d.get("tables", []))]
    first = f"Auto-generated from `Linglib/Data/Statistics/{paper}.json` by"
    tail = "Do not edit by hand: edit the JSON and re-run the generator."
    if len(first) + len(" `scripts/gen_statistics.py`.") <= 100:
        auto = f"{first} `scripts/gen_statistics.py`.\n{tail}"
    else:
        auto = f"{first}\n`scripts/gen_statistics.py`. {tail}"
    desc = textwrap.fill(meta["description"], 100)
    if raw:
        links = "\n".join(textwrap.fill(f"* <{r['url']}>: {r['doc']}", 100, subsequent_indent="  ")
                          for r in raw)
        desc += f"\n\n## Raw data\n\n{links}"
    body = "\n\n".join(parts)
    return f"""module

public import Linglib.Data.Statistics.Schema

/-!
# {paper}: statistics (generated)

{auto}

{desc}

## References

* [{meta['bibkey']}]
-/

@[expose] public section

namespace {paper}

open Data.Statistics

{body}

end {paper}
"""


def process(paper: str, check: bool) -> bool:
    src = DATA_DIR / f"{paper}.json"
    if not src.exists():
        fatal(paper, f"JSON not found at {src.relative_to(ROOT)}")
    content = render(paper, json.loads(src.read_text(encoding="utf-8")))
    out = DATA_DIR / f"{paper}.lean"
    if check:
        if not out.exists() or out.read_text(encoding="utf-8") != content:
            sys.stderr.write(f"[check] DRIFT: {out.relative_to(ROOT)} out of sync with JSON\n")
            return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {src.relative_to(ROOT)}\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    if args == ["--all"] or (not args and check):
        papers = sorted(p.stem for p in DATA_DIR.glob("*.json"))
    elif len(args) == 1:
        papers = args
    else:
        sys.stderr.write(__doc__)
        sys.exit(2)
    sys.exit(0 if all([process(p, check) for p in papers]) else 1)


if __name__ == "__main__":
    main()
