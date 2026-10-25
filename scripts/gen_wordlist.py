#!/usr/bin/env python3
"""Generate Lean 4 word-form modules from per-paper JSON files.

Usage:
    python3 scripts/gen_wordlist.py <AuthorYear>
    python3 scripts/gen_wordlist.py --all                   # regenerate every paper
    python3 scripts/gen_wordlist.py --check [<AuthorYear>]  # verify sync, no writes
    python3 scripts/gen_wordlist.py --fmt [<AuthorYear>]    # canonical JSON format

Reads   Linglib/Data/Wordlist/<AuthorYear>.json
Writes  Linglib/Data/Wordlist/<AuthorYear>.lean, declaring `namespace <AuthorYear>.Wordlist`.

JSON file format: an object of tables, the CLDF Wordlist tables under CLDF column names, with
Paralex's lexemes and cells and four linglib extensions:

  {
    "description": "...",                                   // optional, not emitted
    "Types": {"Clitic": [{"Value": "kin", "Lean": "kin",    // enumerations for cell features
                          "Description": "..."}]},          // and analysis columns UD lacks
    "CellTable": [{"ID": "nom_sg", "Name": "nominative singular",
                   "Features": "Case=Nom|Number=Sing|Clitic=kin"}],
    "ParameterTable": [{"ID": "house", "Name": "house", "Description": ""}],
    "LexemeTable": [{"ID": "house", "Language_ID": "finn1318", "Parameter_ID": "house",
                     "Name": "talo", "Variety": "", "POS": "NOUN"}],
    "FormTable": [{"ID": "karlsson2017_talokin", "Lexeme_ID": "house", "Cell": "nom_sg",
                   "Form": "talokin", "Segments": ["t", "a", ...], "Morphs": ["talo", "kin"],
                   "Judgment": "ungrammatical", "Comment": "", "Source": ["karlsson-2017[p. 1]"]}],
    "FormRelationTable": [{"ID": ..., "Form_ID": ..., "Target_ID": ..., "Relation": ...,
                           "Source": [...]}],
    "ParadigmTable": [{"ID": ..., "Lexeme_ID": ..., "Form_IDs": [...], "Source": [...]}],
    "RootClassTable": [{"ID": ..., "Lexeme_ID": ..., "Form_IDs": [...],
                        "Classes": {"positive": "A", ...}, "Source": [...], "Cognates": ""}],
    "AnalysisColumns": [{"Name": "Underlying", "Lean": "underlying", "Type": "String",
                         "Description": "..."}],
    "AnalysisTable": [{"Form_ID": ..., "Underlying": "/ip-un/"}]
  }

A cell's `Features` are Universal Dependencies features in the CoNLL-U syntax, checked against
`Linglib/Data/UD/Features.lean`, and features named by a key of `Types`; a dataset with the latter
gets a `Cell` structure extending `UD.MorphFeatures`. A form without `Cell` has the empty cell. A
form's `Judgment` is one of the names `Judgment.ofName?` reads, `acceptable` when absent; the
accepted forms are emitted in `all`, the others in `marked`. An analysis column's `Type` is
`String`, `List String` or a key of `Types`; its field is an `Option` unless every form's analysis
gives it. Every form has an analysis, empty where the source gives none. `Source` entries use the
CLDF reference syntax `bibkey[label]`.

`description`, `Comment`, `Cognates` and the `ParameterTable` are validated and not emitted. The
generator rejects malformed input, unknown keys, dangling references, duplicate Lean names and
unknown bibkeys; it is idempotent, `--check` exits 1 on drift, and `--fmt` rewrites the JSON
canonically and refuses to write if the data would change.
"""

import json
import re
import sys
import textwrap
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "Linglib" / "Data" / "Wordlist"
UD_FEATURES = ROOT / "Linglib" / "Data" / "UD" / "Features.lean"
UD_UPOS = ROOT / "Linglib" / "Data" / "UD" / "UPOS.lean"
BIB = ROOT / "references.bib"

WIDTH = 100  # the column the emitted lines stay within, where the names allow

ID_RE = re.compile(r"^[a-zA-Z0-9_\-]+$")  # CLDF 1.3 `id` format
GLOTTO_RE = re.compile(r"^[a-z0-9]{4}[0-9]{4}$")
SOURCE_RE = re.compile(r"^\s*([^\[\]\s]+)\s*(?:\[(.*)\])?\s*$")
TYPE_RE = re.compile(r"^[A-Z][A-Za-z0-9]*$")
CTOR_RE = re.compile(r"^[a-z][A-Za-z0-9_]*$")
LEAN_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")  # the IDs that name declarations
KEYWORDS = {"def", "if", "then", "else", "do", "fun", "let", "in", "at", "by", "end", "match",
            "with", "where", "from", "have", "show", "open", "for", "return", "import", "true",
            "false", "theorem", "structure", "class", "instance", "section", "namespace", "all",
            "marked", "lexemes", "relations", "analysisRelations", "paradigms", "rootClasses",
            "analyses", "Cell",
            "Analysis", "Form", "Lexeme", "Paradigm", "RootClasses", "FormRelation"}

# UD feature -> (`UD.MorphFeatures` field, `UD` type)
FEATURES = {"PronType": ("pronType", "PronType"), "NumType": ("numType", "NumType"),
            "Gender": ("gender", "Gender"), "Animacy": ("animacy", "Animacy"),
            "Number": ("number", "Number"), "Case": ("case", "Case"),
            "Definite": ("definite", "Definite"), "Degree": ("degree", "Degree"),
            "VerbForm": ("verbForm", "VerbForm"), "Mood": ("mood", "Mood"),
            "Tense": ("tense", "Tense"), "Aspect": ("aspect", "Aspect"),
            "Voice": ("voice", "Voice"), "Evident": ("evident", "Evident"),
            "Polarity": ("polarity", "Polarity"), "Person": ("person", "Person"),
            "Polite": ("polite", "Polite"), "Clusivity": ("clusivity", "Clusivity")}
# UD features whose one value is `Yes` -> their `Bool` field of `UD.MorphFeatures`
FLAGS = {"Poss": "poss", "Reflex": "reflex", "Foreign": "foreign", "Abbr": "abbr", "Typo": "typo"}
PERSON = {"0": "zero", "1": "first", "2": "second", "3": "third", "4": "fourth"}
# the names `Judgment.ofName?` reads, `Linglib/Data/Examples/Judgment.lean`
JUDGMENTS = {"acceptable", "marginal", "questionable", "unacceptable", "ungrammatical"}

TABLES = {
    "CellTable": ["ID", "Name", "Features", "Comment"],
    "ParameterTable": ["ID", "Name", "Description", "Comment"],
    "LexemeTable": ["ID", "Language_ID", "Variety", "Parameter_ID", "Name", "POS", "Comment"],
    "FormTable": ["ID", "Lexeme_ID", "Cell", "Form", "Segments", "Morphs", "Judgment", "Comment",
                  "Source"],
    "FormRelationTable": ["ID", "Form_ID", "Target_ID", "Relation", "Comment", "Source"],
    "ParadigmTable": ["ID", "Lexeme_ID", "Form_IDs", "Comment", "Source"],
    "RootClassTable": ["ID", "Lexeme_ID", "Form_IDs", "Classes", "Cognates", "Comment", "Source"],
    "AnalysisColumns": ["Name", "Lean", "Type", "Description"],
}
TOP = ["description", "Types", "CellTable", "ParameterTable", "LexemeTable", "FormTable",
       "FormRelationTable", "ParadigmTable", "RootClassTable", "AnalysisColumns", "AnalysisTable"]
TYPE_KEYS = ["Value", "Lean", "Description"]


def fail(msg: str):
    raise ValueError(msg)


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lower_first(s: str) -> str:
    return s[0].lower() + s[1:]


def upper_first(s: str) -> str:
    return s[0].upper() + s[1:]


def doc(s: str, where: str) -> str:
    if "-/" in s or "/-" in s:
        fail(f"{where}: text contains a comment delimiter")
    return s


def constructors(path: Path) -> dict[str, set[str]]:
    """The constructors of each inductive of a Lean file."""
    ctors, current = {}, None
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^inductive (\w+) where", line)
        if m:
            current = m.group(1)
            ctors[current] = set()
            continue
        m = re.match(r"^\s*\|\s*(\w+)", line)
        if m and current:
            ctors[current].add(m.group(1))
        elif line.strip() and not line.startswith(" ") and not line.startswith("--"):
            current = None
    return ctors


def bibkeys() -> set[str]:
    return set(re.findall(r"^@\w+\{([^,]+),", BIB.read_text(encoding="utf-8"), re.M))


def check_keys(row, table: str, where: str):
    if not isinstance(row, dict):
        fail(f"{where}: a row must be an object")
    extra = set(row) - set(TABLES[table])
    if extra:
        fail(f"{where}: unknown keys {sorted(extra)}")
    for k in ("Comment", "Cognates", "Description"):
        if k in row and not isinstance(row[k], str):
            fail(f"{where}: {k} must be a string")


def req(row: dict, key: str, where: str) -> str:
    v = row.get(key)
    if not isinstance(v, str) or not v.strip():
        fail(f"{where}: {key} is required and non-empty")
    return v


def opt(row: dict, key: str, where: str) -> str:
    v = row.get(key, "")
    if not isinstance(v, str):
        fail(f"{where}: {key} must be a string")
    return v


def req_id(row: dict, key: str, where: str) -> str:
    v = req(row, key, where)
    if not ID_RE.match(v):
        fail(f"{where}: {key} {v!r} violates the CLDF id format [a-zA-Z0-9_-]+")
    return v


def lean_identifier(row_id: str, prefix: str) -> str:
    local = row_id[len(prefix):] if row_id.lower().startswith(prefix) else row_id
    local = "".join(c if c.isalnum() or c == "_" else "_" for c in local)
    if not local or not local[0].isalpha():
        local = "f_" + local
    return local


def strings(xs, key: str, where: str, nonempty: bool = True) -> list[str]:
    if not isinstance(xs, list) or (nonempty and not xs) or \
            not all(isinstance(x, str) and x for x in xs):
        fail(f"{where}: {key} must be a {'non-empty ' if nonempty else ''}list of non-empty "
             "strings")
    return xs


def fill(head: str, items: list[str], tail: str, indent: str) -> str:
    """`head`, the comma-separated `items` and `tail`, broken before an item that would pass
    column `WIDTH` and continued at `indent`."""
    out = head
    for k, item in enumerate(items):
        piece = item + ("," if k + 1 < len(items) else tail)
        if k and len(out.rsplit("\n", 1)[-1]) + 1 + len(piece.split("\n", 1)[0]) > WIDTH:
            out += "\n" + indent + piece
        else:
            out += (" " if k else "") + piece
    return out if items else out + tail


def docstring(text: str, indent: str = "") -> str:
    """`text` as a docstring at `indent`, filled to column `WIDTH`."""
    return textwrap.fill(f"{indent}/-- {text} -/", WIDTH, subsequent_indent=indent,
                         break_long_words=False, break_on_hyphens=False)


def emit_strings(xs: list[str], head: str = "[", indent: str = "      ") -> str:
    return fill(head, [lean_string(x) for x in xs], "]", indent)


def emit_sources(xs, keys: set[str], where: str, indent: str) -> str:
    """A `List SourceRef`, each reference on its own line so that the bracketed bibkeys are not
    mistaken for `[key]` citations."""
    if xs is None:
        return "[]"
    if not isinstance(xs, list) or not all(isinstance(x, str) for x in xs):
        fail(f"{where}: Source must be a list of strings")
    items = []
    for x in xs:
        m = SOURCE_RE.match(x)
        if not m:
            fail(f"{where}: bad Source reference {x!r}; expected bibkey[label]")
        if m.group(1) not in keys:
            fail(f"{where}: bibkey {m.group(1)!r} is not in references.bib")
        items.append(f"⟨{lean_string(m.group(1))}, {lean_string(m.group(2) or '')}⟩")
    if not items:
        return "[]"
    return "[\n" + ",\n".join(indent + "  " + it for it in items) + "\n" + indent + "]"


class Module:
    """The declarations of one dataset, checked for unique Lean names."""

    def __init__(self, paper: str, data: dict):
        self.paper, self.data = paper, data
        self.prefix = paper.lower() + "_"
        self.keys = bibkeys()
        self.ud = constructors(UD_FEATURES)
        self.upos = constructors(UD_UPOS).get("UPOS", set())
        self.names: set[str] = set()
        self.out: list[str] = []

    def name(self, n: str, where: str) -> str:
        if not all(LEAN_RE.match(part) for part in n.split(".")):
            fail(f"{where}: {n!r} is not a Lean name")
        if n in self.names or n in KEYWORDS:
            fail(f"{where}: Lean name {n!r} is taken")
        self.names.add(n)
        return n

    def types(self):
        self.enums = {}
        types = self.data.get("Types") or {}
        if not isinstance(types, dict):
            fail("Types must be an object of enumerations")
        for ty, vals in types.items():
            where = f"type {ty!r}"
            if not TYPE_RE.match(ty) or ty in FEATURES:
                fail(f"{where}: bad type name")
            if not isinstance(vals, list) or not vals:
                fail(f"{where}: values must be a non-empty list")
            table = {}
            for v in vals:
                if not isinstance(v, dict) or set(v) - set(TYPE_KEYS):
                    fail(f"{where}: a value is an object with keys {TYPE_KEYS}")
                val, ctor = req(v, "Value", where), req(v, "Lean", where)
                if not CTOR_RE.match(ctor) or ctor in KEYWORDS or ctor in table.values():
                    fail(f"{where}: bad or duplicate constructor {ctor!r}")
                if val in table:
                    fail(f"{where}: duplicate value {val!r}")
                table[val] = ctor
            self.enums[ty] = table
            ctors = "\n".join(
                docstring(upper_first(f"{doc(v['Description'], where)}, `{doc(v['Value'], where)}` "
                                      "in the source.") if v.get("Description")
                          else f"The value `{doc(v['Value'], where)}`.", "  ")
                + f"\n  | {v['Lean']}" for v in vals)
            self.out.append(f"/-- The values of `{ty}` the source distinguishes. -/\n"
                            f"inductive {self.name(ty, where)} where\n{ctors}\n"
                            f"  deriving DecidableEq, Repr")

    def enum_value(self, ty: str, val: str, where: str) -> str:
        table = self.enums.get(ty)
        if table is None or val not in table:
            fail(f"{where}: {val!r} is not a value of {ty}")
        return f"{ty}.{table[val]}"

    def cells(self):
        rows = self.data.get("CellTable") or []
        parsed = {}
        extended = []
        for r in rows:
            check_keys(r, "CellTable", "CellTable row")
            cid = req_id(r, "ID", "CellTable row")
            where = f"cell {cid!r}"
            req(r, "Name", where)
            feats = opt(r, "Features", where)
            fields = []
            for feat in [x for x in feats.split("|") if x]:
                fname, _, value = feat.partition("=")
                if fname in FEATURES:
                    field, ty = FEATURES[fname]
                    ctor = PERSON.get(value) if fname == "Person" else value
                    if ctor not in self.ud.get(ty, set()):
                        fail(f"{where}: {fname}={value} is not a constructor of UD.{ty}")
                    fields.append((field, f"↑UD.{ty}.{ctor}"))
                elif fname in FLAGS:
                    if value != "Yes":
                        fail(f"{where}: {fname}={value} is not {fname}=Yes")
                    fields.append((FLAGS[fname], "true"))
                elif fname in self.enums:
                    if fname not in extended:
                        extended.append(fname)
                    fields.append((lower_first(fname), f"↑{self.enum_value(fname, value, where)}"))
                else:
                    fail(f"{where}: unknown feature {fname!r}")
            if len({f for f, _ in fields}) != len(fields):
                fail(f"{where}: a feature given twice")
            if cid in parsed:
                fail(f"{where}: duplicate ID")
            parsed[cid] = (r["Name"], feats, fields)
        if extended:
            extra = "\n".join(f"  /-- The `{t}` feature. -/\n  {lower_first(t)} : Flat {t} := ⊥"
                              for t in extended)
            self.out.append("/-- A cell of the source's tables, by its Universal Dependencies "
                            "features and the features UD\nlacks. -/\n"
                            f"structure Cell extends UD.MorphFeatures where\n{extra}\n"
                            "  deriving DecidableEq, Repr")
        else:
            self.out.append("/-- A cell of the source's tables, by its Universal Dependencies "
                            "features. -/\nabbrev Cell := UD.MorphFeatures")
        self.names.add("Cell")
        for cid, (label, feats, fields) in parsed.items():
            head = f"def {self.name(cid, f'cell {cid!r}')} : Cell :="
            items = [f"{f} := {v}" for f, v in fields]
            body = head + (" { " + ", ".join(items) + " }" if items else " {}")
            if len(body) > WIDTH:
                body = fill(head + "\n  { ", items, " }", "    ")
            label = doc(label, cid)
            self.out.append(docstring(f"The {label} cell, `{feats or '∅'}`.") + "\n" + body)
        self.cell_ids = set(parsed)

    def lexemes(self):
        params = set()
        for r in self.data.get("ParameterTable") or []:
            check_keys(r, "ParameterTable", "ParameterTable row")
            pid = req_id(r, "ID", "ParameterTable row")
            req(r, "Name", f"parameter {pid!r}")
            if pid in params:
                fail(f"parameter {pid!r}: duplicate ID")
            params.add(pid)
        self.lexeme_ids = []
        for r in self.data.get("LexemeTable") or []:
            check_keys(r, "LexemeTable", "LexemeTable row")
            lid = req_id(r, "ID", "LexemeTable row")
            where = f"lexeme {lid!r}"
            g = req(r, "Language_ID", where)
            if not GLOTTO_RE.match(g):
                fail(f"{where}: Language_ID {g!r} is not a Glottocode")
            pid = req(r, "Parameter_ID", where)
            if pid not in params:
                fail(f"{where}: Parameter_ID {pid!r} not in ParameterTable")
            fields = [f"id := {lean_string(lid)}", f"languageId := {lean_string(g)}"]
            if opt(r, "Variety", where):
                fields.append(f"variety := {lean_string(r['Variety'])}")
            fields.append(f"parameterId := {lean_string(pid)}")
            if opt(r, "Name", where):
                fields.append(f"label := {lean_string(r['Name'])}")
            if opt(r, "POS", where):
                if r["POS"] not in self.upos:
                    fail(f"{where}: POS {r['POS']!r} is not a UD.UPOS constructor")
                fields.append(f"pos := ↑UD.UPOS.{r['POS']}")
            self.out.append(fill(f"def {self.name('Lexemes.' + lid, where)} : Lexeme :=\n  {{ ",
                                 fields, " }", "    "))
            self.lexeme_ids.append(lid)

    def forms(self):
        self.form_rows = {}
        self.local_of = {}
        self.accepted, self.marked = [], []
        for r in self.data.get("FormTable") or []:
            check_keys(r, "FormTable", "FormTable row")
            rid = req_id(r, "ID", "FormTable row")
            where = f"form {rid!r}"
            if rid in self.form_rows:
                fail(f"{where}: duplicate ID")
            lx = req(r, "Lexeme_ID", where)
            if lx not in self.lexeme_ids:
                fail(f"{where}: Lexeme_ID {lx!r} not in LexemeTable")
            cell = r.get("Cell")
            if cell is not None and cell not in self.cell_ids:
                fail(f"{where}: Cell {cell!r} not in CellTable")
            opt(r, "Comment", where)
            j = r.get("Judgment", "acceptable")
            if j not in JUDGMENTS or (j == "acceptable" and "Judgment" in r):
                fail(f"{where}: Judgment {j!r} is not one of {sorted(JUDGMENTS - {'acceptable'})}")
            local = self.name(lean_identifier(rid, self.prefix), where)
            lines = [f"{{ id := {lean_string(rid)}", f"lexeme := Lexemes.{lx}",
                     f"cell := {cell if cell else '{}'}",
                     f"form := {lean_string(req(r, 'Form', where))}"]
            for col, field in (("Segments", "segments"), ("Morphs", "morphs")):
                if col in r:
                    xs = strings(r[col], col, where)
                    lines.append(emit_strings(xs, f"    {field} := [")[4:])
            if j != "acceptable":
                lines.append(f"judgment := .{j}")
            lines.append(f"source := {emit_sources(r.get('Source'), self.keys, where, '    ')} }}")
            self.out.append(f"def {local} : Form Cell :=\n  " + "\n    ".join(lines))
            self.form_rows[rid] = r
            self.local_of[rid] = local
            (self.accepted if j == "acceptable" else self.marked).append(local)

    def form_list(self, r: dict, lx: str, where: str) -> list[str]:
        fs = r.get("Form_IDs")
        if not isinstance(fs, list) or not fs:
            fail(f"{where}: Form_IDs must be a non-empty list")
        for f in fs:
            if f not in self.form_rows:
                fail(f"{where}: form {f!r} not in FormTable")
            if self.form_rows[f]["Lexeme_ID"] != lx:
                fail(f"{where}: form {f!r} is not a form of {lx!r}")
        return fs

    def relations(self):
        self.rel_rows = []
        for r in self.data.get("FormRelationTable") or []:
            check_keys(r, "FormRelationTable", "FormRelationTable row")
            rid = req_id(r, "ID", "FormRelationTable row")
            where = f"relation {rid!r}"
            ends = []
            for k in ("Form_ID", "Target_ID"):
                if r.get(k) not in self.local_of:
                    fail(f"{where}: {k} not in FormTable")
                ends.append(self.local_of[r[k]])
            self.rel_rows.append((rid, ends, req(r, 'Relation', where),
                                  emit_sources(r.get('Source'), self.keys, where, '    ')))

    def paradigms(self):
        self.paradigm_names = []
        for r in self.data.get("ParadigmTable") or []:
            check_keys(r, "ParadigmTable", "ParadigmTable row")
            pid = req_id(r, "ID", "ParadigmTable row")
            where = f"paradigm {pid!r}"
            lx = req(r, "Lexeme_ID", where)
            fs = self.form_list(r, lx, where)
            if len({self.form_rows[f].get("Cell") for f in fs}) != len(fs):
                fail(f"{where}: two forms in one cell")
            n = self.name(f"{pid}.paradigm", where)
            self.paradigm_names.append(n)
            src = emit_sources(r.get('Source'), self.keys, where, '    ')
            self.out.append(f"def {n} : Paradigm Cell :=\n{self.members(pid, lx, fs)}\n"
                            f"    source := {src} }}")

    def members(self, rid: str, lx: str, fs: list[str]) -> str:
        """The first fields of a paradigm or a root-class judgment: its ID, lexeme and forms."""
        return (fill("  { ", [f"id := {lean_string(rid)}", f"lexeme := Lexemes.{lx}"], ",", "    ")
                + "\n" + fill("    forms := [", [self.local_of[f] for f in fs], "],", "      "))

    def root_classes(self):
        self.roots_names = []
        for r in self.data.get("RootClassTable") or []:
            check_keys(r, "RootClassTable", "RootClassTable row")
            cid = req_id(r, "ID", "RootClassTable row")
            where = f"root classes {cid!r}"
            lx = req(r, "Lexeme_ID", where)
            fs = self.form_list(r, lx, where)
            cls = r.get("Classes")
            if not isinstance(cls, dict) or not cls:
                fail(f"{where}: Classes must be a non-empty object from cells to letters")
            pairs = []
            for c, letter in cls.items():
                if c not in self.cell_ids:
                    fail(f"{where}: cell {c!r} not in CellTable")
                if not (isinstance(letter, str) and re.fullmatch(r"[A-Z]", letter)):
                    fail(f"{where}: class of {c!r} must be one capital letter")
                pairs.append(f"({c}, {ord(letter) - ord('A')})")
            for f in fs:
                if self.form_rows[f].get("Cell") not in cls:
                    fail(f"{where}: form {f!r} is in a cell with no class")
            n = self.name(f"{cid}.roots", where)
            self.roots_names.append(n)
            src = emit_sources(r.get('Source'), self.keys, where, '    ')
            self.out.append(f"def {n} : RootClasses Cell :=\n{self.members(cid, lx, fs)}\n"
                            + fill("    classes := [", pairs, "],", "      ") + "\n"
                            f"    source := {src} }}")

    def analyses(self):
        cols = self.data.get("AnalysisColumns") or []
        rows = self.data.get("AnalysisTable") or []
        self.analysis_names = []
        self.has_analyses = bool(cols or rows)
        if not cols and not rows:
            return
        spec = {}
        for c in cols:
            check_keys(c, "AnalysisColumns", "AnalysisColumns row")
            name = req(c, "Name", "AnalysisColumns row")
            lean = req(c, "Lean", "AnalysisColumns row")
            ty = req(c, "Type", f"analysis column {name!r}")
            if not CTOR_RE.match(lean) or lean in KEYWORDS or lean == "form" or \
                    lean in [s[0] for s in spec.values()]:
                fail(f"analysis column {name!r}: bad or duplicate Lean name {lean!r}")
            if ty not in ("String", "List String") and ty not in self.enums:
                fail(f"analysis column {name!r}: Type {ty!r} is not String, List String or a type")
            spec[name] = (lean, ty, c.get("Description", ""))
        seen = set()
        for r in rows:
            if not isinstance(r, dict):
                fail("AnalysisTable: a row must be an object")
            extra = set(r) - set(spec) - {"Form_ID", "Comment"}
            if extra:
                fail(f"AnalysisTable row {r.get('Form_ID')!r}: unknown keys {sorted(extra)}")
            if r.get("Form_ID") not in self.local_of or r["Form_ID"] in seen:
                fail(f"AnalysisTable row {r.get('Form_ID')!r}: unknown or repeated Form_ID")
            seen.add(r["Form_ID"])
        analysed = {r["Form_ID"]: r for r in rows}
        total = {n: all(n in analysed.get(f, {}) for f in self.local_of) for n in spec}
        fields = []
        for n, (lean, ty, desc) in spec.items():
            lty = f"({ty})" if " " in ty else ty
            fields.append(docstring(f"The `{n}` column{', ' + doc(desc, n) if desc else ''}.", "  ")
                          + f"\n  {lean} : " + (lty if total[n] else f"Option {lty} := none"))
        self.out.append("/-- The source's analysis of a form, its parse rather than data. -/\n"
                        "structure Analysis where\n  /-- The form analysed. -/\n"
                        "  form : Form Cell\n" + "\n".join(fields)
                        + "\n  deriving DecidableEq, Repr")
        self.names.add("Analysis")
        by_form = {r["Form_ID"]: r for r in rows}
        for rid, local in self.local_of.items():
            r = by_form.get(rid, {"Form_ID": rid})
            where = f"analysis of {rid!r}"
            vals = [f"form := {local}"]
            for n, (lean, ty, _) in spec.items():
                if n not in r:
                    continue
                v = r[n]
                head = f"{lean} := {'' if total[n] else 'some '}"
                if ty == "List String":
                    vals.append(emit_strings(strings(v, n, where, nonempty=False),
                                             f"    {head}[")[4:])
                    continue
                if not isinstance(v, str):
                    fail(f"{where}: {n} must be a string")
                vals.append(head + (lean_string(v) if ty == "String"
                                    else self.enum_value(ty, v, where)))
            n = self.name(f"{local}.analysis", where)
            if rid in by_form:
                self.analysis_names.append(n)
            self.out.append(f"def {n} : Analysis :=\n  {{ " + ",\n    ".join(vals) + " }")

    def rel_list(self, suffix: str) -> str:
        if not self.rel_rows:
            return " []"
        return " [\n" + ",\n".join(
            fill("  { ", [f"id := {lean_string(rid)}", f"form := {ends[0]}{suffix}",
                          f"target := {ends[1]}{suffix}", f"relation := {lean_string(rel)}",
                          f"source := {src}"], " }", "    ")
            for rid, ends, rel, src in self.rel_rows) + "]"

    @staticmethod
    def def_list(doc_: str, head: str, names: list[str]) -> str:
        """A list of every declaration in `names`, with its docstring."""
        return f"/-- {doc_} -/\n" + fill(head + " [", names, "]", "  ")

    def emit(self) -> str:
        unknown = set(self.data) - set(TOP)
        if unknown:
            fail(f"unknown top-level keys {sorted(unknown)}")
        if "description" in self.data and not isinstance(self.data["description"], str):
            fail("description must be a string")
        self.types()
        self.cells()
        self.lexemes()
        self.forms()
        self.relations()
        self.paradigms()
        self.root_classes()
        self.analyses()
        lists = [
            self.def_list("Every lexeme of the data.", "def lexemes : List Lexeme :=",
                          ["Lexemes." + l for l in self.lexeme_ids]),
            self.def_list("Every form the sources accept.", "def all : List (Form Cell) :=",
                          self.accepted),
            self.def_list("Every form a source marks, as marginal, questionable, unacceptable or "
                          "ungrammatical.", "def marked : List (Form Cell) :=", self.marked),
            "/-- Every relation the sources assert between forms. -/\n"
            "def relations : List (FormRelation (Form Cell)) :=" + self.rel_list("")]
        if self.rel_rows and self.has_analyses:
            lists.append("/-- Every relation the sources assert, between the forms' analyses. -/\n"
                         "def analysisRelations : List (FormRelation Analysis) :="
                         + self.rel_list(".analysis"))
        if self.paradigm_names:
            lists.append(self.def_list("Every paradigm of the data.",
                                       "def paradigms : List (Paradigm Cell) :=",
                                       self.paradigm_names))
        if self.roots_names:
            lists.append(self.def_list("Every root-class judgment of the data.",
                                       "def rootClasses : List (RootClasses Cell) :=",
                                       self.roots_names))
        if self.analysis_names:
            lists.append(self.def_list("Every analysis of the data.",
                                       "def analyses : List Analysis :=", self.analysis_names))
        body = "\n\n".join(self.out + lists)
        header = textwrap.fill(
            f"Auto-generated from `Linglib/Data/Wordlist/{self.paper}.json` by "
            "`scripts/gen_wordlist.py`. "
            "Do not edit by hand; edit the JSON and re-run the generator. Declarations live in "
            f"`namespace {self.paper}.Wordlist`.", WIDTH, break_on_hyphens=False)
        return f"""import Linglib.Data.Wordlist.Schema

/-!
# `{self.paper}`: word forms

{header}
-/

namespace {self.paper}.Wordlist

open CLDF.Wordlist

{body}

end {self.paper}.Wordlist
"""


def load(paper: str) -> dict:
    path = JSON_DIR / f"{paper}.json"
    if not path.exists():
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)} not found\n")
        sys.exit(1)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)}: invalid JSON: {e}\n")
        sys.exit(1)
    if not isinstance(data, dict):
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)}: top level must be an object\n")
        sys.exit(1)
    return data


def process(paper: str, check: bool) -> bool:
    path = JSON_DIR / f"{paper}.json"
    try:
        text = as_module_if_possible(Module(paper, load(paper)).emit())
    except ValueError as e:
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)
    target = JSON_DIR / f"{paper}.lean"
    in_sync = target.exists() and target.read_text(encoding="utf-8") == text
    rel = target.relative_to(ROOT)
    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel} in sync\n")
        else:
            sys.stderr.write(f"[check] DRIFT: {rel}; run scripts/gen_wordlist.py {paper}\n")
        return in_sync
    if not in_sync:
        target.write_text(text, encoding="utf-8")
    sys.stdout.write(f"[gen] {rel} {'unchanged' if in_sync else 'written'}\n")
    return True


def _j(v) -> str:
    return json.dumps(v, ensure_ascii=False)


def _fmt_row(row: dict, keys: list[str], indent: str) -> str:
    ks = [k for k in keys if k in row] + [k for k in row if k not in keys]
    return "{\n" + ",\n".join(f"{indent}  {_j(k)}: {_j(row[k])}" for k in ks) + f"\n{indent}}}"


def format_data(data: dict) -> str:
    keys = [k for k in TOP if k in data] + [k for k in data if k not in TOP]
    out = ["{"]
    for ki, k in enumerate(keys):
        comma = "," if ki < len(keys) - 1 else ""
        v = data[k]
        if isinstance(v, list) and v:
            order = TABLES.get(k, ["Form_ID"])
            out.append(f"  {_j(k)}: [")
            for ri, row in enumerate(v):
                rc = "," if ri < len(v) - 1 else ""
                out.append("    " + _fmt_row(row, order, "    ") + rc)
            out.append(f"  ]{comma}")
        elif isinstance(v, dict) and v:
            out.append(f"  {_j(k)}: {{")
            items = list(v.items())
            for ii, (tk, vals) in enumerate(items):
                ic = "," if ii < len(items) - 1 else ""
                out.append(f"    {_j(tk)}: [")
                for vi, val in enumerate(vals):
                    vc = "," if vi < len(vals) - 1 else ""
                    out.append("      " + _j({kk: val[kk] for kk in TYPE_KEYS if kk in val}
                                               | {kk: vv for kk, vv in val.items()
                                                  if kk not in TYPE_KEYS}) + vc)
                out.append(f"    ]{ic}")
            out.append(f"  }}{comma}")
        else:
            out.append(f"  {_j(k)}: {_j(v)}{comma}")
    out.append("}")
    return "\n".join(out) + "\n"


def fmt(paper: str) -> bool:
    data = load(paper)
    path = JSON_DIR / f"{paper}.json"
    text = format_data(data)
    if json.loads(text) != data:
        sys.stderr.write(f"[fmt] REFUSING {path.relative_to(ROOT)}: round-trip mismatch\n")
        return False
    if path.read_text(encoding="utf-8") == text:
        sys.stdout.write(f"[fmt] {path.relative_to(ROOT)} unchanged\n")
    else:
        path.write_text(text, encoding="utf-8")
        sys.stdout.write(f"[fmt] {path.relative_to(ROOT)} reformatted\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    do_fmt = "--fmt" in args
    args = [a for a in args if a not in ("--check", "--fmt")]
    if args == ["--all"] or (not args and (check or do_fmt)):
        papers = sorted(p.stem for p in JSON_DIR.glob("*.json"))
    elif len(args) == 1 and not args[0].startswith("-"):
        papers = args
    else:
        sys.stderr.write(__doc__)
        sys.exit(1)
    run = fmt if do_fmt else (lambda p: process(p, check))
    if not all([run(p) for p in papers]):
        sys.exit(1)


if __name__ == "__main__":
    main()
