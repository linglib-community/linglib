#!/usr/bin/env python3
"""Generate the Lean 4 example modules, lists of `Datum`, from per-paper JSON files.

Usage:
    python3 scripts/gen_examples.py <AuthorYear>
    python3 scripts/gen_examples.py --all                # regenerate every paper and the languages
    python3 scripts/gen_examples.py --check [<AuthorYear>]  # verify sync, no writes
    python3 scripts/gen_examples.py --fmt <AuthorYear>   # canonical JSON for one paper

Example:
    python3 scripts/gen_examples.py Charlow2014
        Reads:   Linglib/Data/Examples/Charlow2014.json
        Writes:  Linglib/Data/Examples/Charlow2014.lean — a standalone
                 auto-generated module declaring `namespace
                 Charlow2014.Examples`. Consumers (the paper's study file,
                 test-suite hubs) `import Linglib.Data.Examples.Charlow2014`.

The `Linglib.lean` root import is not touched: the lakefile globs every
submodule, and `scripts/mk_all.py` regenerates the root before a release.

JSON file format: a single top-level JSON array of example objects. Each
object's keys are the fields of the `Datum` Lean struct, plus the
record-only keys `discourseSegments`, `translation`, `comment` and `verified`:

  {
    "id": "charlow2014_donkey1",
    "source":     {"bibkey": "geach-1962", "paperLabel": "ch. III, ..."},
    "reportedIn": {"bibkey": "charlow-2014", "paperLabel": "Ch. 2"},  // optional
    "method": "corpus",                      // optional: overrides the paper's in contributions.csv
    "language": "stan1293",                  // Glottocode; "" for a constructed string
    "primaryText": "...",
    "discourseSegments": [],                 // empty for single-sentence
    "glossedTokens": [["Every", "every"], ...],  // pairs as 2-arrays
    "translation": "...",
    "context": "",
    "judgment": "acceptable",                // one of the 6 cases
    "verdict": true,                         // optional: a truth-value judgment in the context
    "alternatives": [{"form": "...", "judgment": "unacceptable"}],
    "readings":     [{"name": "strong", "judgment": "acceptable"},
                     {"name": "weak",   "judgment": "acceptable"}],
    "paperFeatures": [["key", "value"], ...],  // the paper's own columns
    "comment": "..."
  }

Behavior:
- Errors out (exit 1) if the JSON file doesn't exist.
- Reads each paper's method from `contributions.csv` (one of `introspection`, `elicitation`,
  `corpus`, `experiment`, `description`, or `unclassified`) and errors out on a paper with no row
  there; a row's `method` overrides it, and the method is emitted as `Datum.method` (`none` where
  unclassified).
- Validates but does not emit the record-only keys: the CLDF export carries
  them, and no theorem reads them, so the Lean rows that `decide` reduces stay
  small. `verified` (`"page-image"`, `"text-layer"` or `"supplement"`) is how the row was last
  checked against its source.
- Errors out on schema violations (a key that is not a field, an id outside
  the CLDF identifier characters `[A-Za-z0-9_-]`, a language that is neither
  empty nor a Glottocode of `languages.csv`, unknown judgment value (also as
  the value of an `alsoJudged` paper feature),
  malformed gloss pair, missing id or source.bibkey).
- Idempotent: re-running on unchanged JSON produces no diff.
- `--check` regenerates in-memory and exits 1 on any drift (CI guard);
  writes nothing.
- `--all` and a bare `--check` also generate (or verify) `Linglib/Data/Examples/Languages.lean`
  from `languages.csv`: one `Glottocode` per row, in `namespace Glottocode`, named by its
  Glottolog name in lowerCamelCase (`Glottocode.mandarinChinese`), so that a study names the
  languages of its sample rather than typing their codes.
- `--fmt` rewrites the named paper's JSON in canonical format. It needs a
  paper name (or `--all` for a PR whose subject is the reformat): most JSON
  files predate the formatter, and reformatting them all buries a diff.

Dependencies: pure stdlib (json module).
"""

import csv
import json
import re
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402

ROOT       = Path(__file__).resolve().parent.parent
JSON_DIR   = ROOT / "Linglib" / "Data" / "Examples"
LANGUAGES  = JSON_DIR / "languages.csv"
CONTRIBUTIONS = JSON_DIR / "contributions.csv"
METHODS = ("introspection", "elicitation", "corpus", "experiment", "description")


def known_languages() -> set[str]:
    """The Glottocodes of `languages.csv`, the example data's language table."""
    with open(LANGUAGES, encoding="utf-8") as f:
        return {row["ID"] for row in csv.DictReader(f)}


KNOWN_LANGUAGES = known_languages()


def contribution_methods() -> dict[str, str]:
    """Each paper's default method from `contributions.csv`, one of `METHODS` or `unclassified`."""
    with open(CONTRIBUTIONS, encoding="utf-8") as f:
        rows = {row["ID"]: row["Method"] for row in csv.DictReader(f)}
    for paper, method in rows.items():
        if method not in METHODS + ("unclassified",):
            sys.stderr.write(f"FATAL: {CONTRIBUTIONS.relative_to(ROOT)}: {paper}: method "
                             f"{method!r}; expected one of {', '.join(METHODS)} or unclassified\n")
            sys.exit(1)
    return rows


CONTRIBUTION_METHODS = contribution_methods()

VALID_JUDGMENTS = {
    "acceptable", "marginal", "questionable", "unacceptable", "ungrammatical", "variable",
}


def lean_string(s: str) -> str:
    """Quote a string for Lean source. Escapes backslashes and quotes."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_identifier(example_id: str, author_year_lower: str) -> str:
    """Derive a Lean-valid identifier from a JSON example ID.

    `charlow2014_donkey1` → `donkey1` (strip the AuthorYear_ prefix and use
    the rest as the local identifier inside `namespace Examples`).
    """
    prefix = author_year_lower + "_"
    if example_id.lower().startswith(prefix):
        local = example_id[len(prefix):]
    else:
        local = example_id
    local = "".join(c if c.isalnum() or c in "_'" else "_" for c in local)
    if not local or not local[0].isalpha():
        local = "ex_" + local
    return local


def parse_judgment(raw: str, where: str) -> str:
    j = (raw or "").strip().lower()
    if j not in VALID_JUDGMENTS:
        raise ValueError(
            f"{where}: invalid judgment {raw!r}; expected one of "
            f"{sorted(VALID_JUDGMENTS)}"
        )
    return f".{j}"


def emit_source_ref(s: dict, where: str) -> str:
    """Emit a SourceRef literal from a {bibkey, paperLabel} object."""
    if not isinstance(s, dict):
        raise ValueError(f"{where}: source/reportedIn must be an object, got {type(s).__name__}")
    bib = (s.get("bibkey") or "").strip()
    lab = (s.get("paperLabel") or "").strip()
    if not bib:
        raise ValueError(f"{where}: source.bibkey is required and non-empty")
    return f"⟨{lean_string(bib)}, {lean_string(lab)}⟩"


def emit_reported_in(r, where: str) -> str:
    """Emit `none` for null/absent, `some ⟨…⟩` for a SourceRef object."""
    if r is None:
        return "none"
    return f"some {emit_source_ref(r, where + '.reportedIn')}"


def emit_string_list(xs, where: str) -> str:
    if not isinstance(xs, list) or not all(isinstance(x, str) for x in xs):
        raise ValueError(f"{where}: expected list of strings")
    if not xs:
        return "[]"
    return "[" + ", ".join(lean_string(x) for x in xs) + "]"


def emit_glossed_tokens(xs, where: str) -> str:
    """Emit a List (String × String) literal from JSON pairs.

    Each entry must be a 2-element array: [analyzedWord, gloss].
    """
    if not isinstance(xs, list):
        raise ValueError(f"{where}: glossedTokens must be an array")
    if not xs:
        return "[]"
    items = []
    for i, pair in enumerate(xs):
        if not (isinstance(pair, list) and len(pair) == 2
                and all(isinstance(s, str) for s in pair)):
            raise ValueError(
                f"{where}.glossedTokens[{i}]: expected 2-string array, got {pair!r}"
            )
        items.append(f"({lean_string(pair[0])}, {lean_string(pair[1])})")
    return "[" + ", ".join(items) + "]"


def emit_string_pair_list(xs, where: str) -> str:
    """Emit a List (String × String) literal from JSON.

    Accepts either:
    - list of 2-element arrays:  [["key", "value"], ...]
    - list of objects:           [{"key": "...", "value": "..."}, ...]
    - object (treated as dict):  {"k1": "v1", "k2": "v2"}
    """
    if isinstance(xs, dict):
        items = list(xs.items())
    elif isinstance(xs, list):
        items = []
        for i, entry in enumerate(xs):
            if isinstance(entry, list) and len(entry) == 2 and all(isinstance(s, str) for s in entry):
                items.append((entry[0], entry[1]))
            elif isinstance(entry, dict) and "key" in entry and "value" in entry:
                if not (isinstance(entry["key"], str) and isinstance(entry["value"], str)):
                    raise ValueError(f"{where}[{i}]: key/value must be strings")
                items.append((entry["key"], entry["value"]))
            else:
                raise ValueError(
                    f"{where}[{i}]: expected 2-string array or {{key, value}} object"
                )
    else:
        raise ValueError(f"{where}: expected array or object")
    if not items:
        return "[]"
    return "[" + ", ".join(
        f"({lean_string(k)}, {lean_string(v)})" for k, v in items
    ) + "]"


def emit_form_judgment_list(xs, where: str, key: str) -> str:
    """Emit a List (String × Judgment) literal.

    Each entry is `{key: <string>, judgment: <judgment>}`. `key` is "form"
    for alternatives or "name" for readings.
    """
    if not isinstance(xs, list):
        raise ValueError(f"{where}: expected an array")
    if not xs:
        return "[]"
    items = []
    for i, entry in enumerate(xs):
        if not isinstance(entry, dict):
            raise ValueError(f"{where}[{i}]: expected an object")
        s = entry.get(key)
        j = entry.get("judgment")
        if not isinstance(s, str):
            raise ValueError(f"{where}[{i}].{key}: expected a string")
        items.append(f"({lean_string(s)}, {parse_judgment(j, f'{where}[{i}].judgment')})")
    return "[" + ", ".join(items) + "]"


def emit_example(ex: dict, author_year_lower: str, default_method: str) -> str:
    ex_id   = (ex.get("id") or "").strip()
    if not ex_id:
        raise ValueError("example missing required `id`")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", ex_id):
        raise ValueError(f"id {ex_id!r}: a CLDF identifier uses only [A-Za-z0-9_-]")
    where   = f"example {ex_id!r}"
    local   = lean_identifier(ex_id, author_year_lower)
    unknown = [k for k in ex if k not in KEY_ORDER]
    if unknown:
        raise ValueError(f"{where}: {', '.join(map(repr, unknown))} not a key of the example schema")
    if ex.get("verified", "page-image") not in VERIFIED:
        raise ValueError(f"{where}: verified {ex['verified']!r}; expected one of {sorted(VERIFIED)}")

    src         = emit_source_ref(ex.get("source") or {}, where + ".source")
    reported_in = emit_reported_in(ex.get("reportedIn"), where)
    if "method" in ex and ex["method"] not in METHODS:
        raise ValueError(f"{where}: method {ex['method']!r}; expected one of {', '.join(METHODS)}")
    method      = ex.get("method", default_method)
    language    = (ex.get("language") or "").strip()
    if language and language not in KNOWN_LANGUAGES:
        raise ValueError(
            f"{where}: language {language!r} is not in {LANGUAGES.relative_to(ROOT)}; if it is a "
            f"Glottocode, add it with scripts/export_examples_cldf.py --sync-languages")
    for key in ("translation", "comment"):
        if not isinstance(ex.get(key, ""), str):
            raise ValueError(f"{where}.{key}: expected a string")
    emit_string_list(ex.get("discourseSegments", []), where + ".discourseSegments")
    primary     = ex.get("primaryText") or ""
    glossed     = emit_glossed_tokens(ex.get("glossedTokens", []), where)
    context     = ex.get("context") or ""
    judgment    = parse_judgment(ex.get("judgment", ""), where + ".judgment")
    verdict     = ex.get("verdict")
    if verdict is not None and not isinstance(verdict, bool):
        raise ValueError(f"{where}.verdict: expected a JSON boolean")
    alternatives = emit_form_judgment_list(ex.get("alternatives", []), where + ".alternatives", "form")
    readings    = emit_form_judgment_list(ex.get("readings", []), where + ".readings", "name")
    features    = emit_string_pair_list(ex.get("paperFeatures", []), where + ".paperFeatures")
    raw = ex.get("paperFeatures", [])
    pairs = raw.items() if isinstance(raw, dict) else [
        (e[0], e[1]) if isinstance(e, list) else (e["key"], e["value"]) for e in raw]
    for k, v in pairs:
        if k == "alsoJudged":
            parse_judgment(v, where + ".paperFeatures.alsoJudged")

    method_line = "" if method == "unclassified" else f"\n    method := some .{method}"
    verdict_line = ""
    if verdict is not None:
        verdict_line = f"\n    verdict := some {'true' if verdict else 'false'}"
    return f"""def {local} : Datum :=
  {{ id := {lean_string(ex_id)}
    source := {src}
    reportedIn := {reported_in}{method_line}
    language := {lean_string(language)}
    primaryText := {lean_string(primary)}
    glossedTokens := {glossed}
    context := {lean_string(context)}
    judgment := {judgment}{verdict_line}
    alternatives := {alternatives}
    readings := {readings}
    paperFeatures := {features} }}"""


def emit_module(author_year: str, examples: list) -> str:
    ay_lower = author_year.lower()
    if author_year not in CONTRIBUTION_METHODS:
        raise ValueError(f"no row in {CONTRIBUTIONS.relative_to(ROOT)}; add `{author_year},<method>` "
                         f"with the paper's method, or `unclassified`")
    default_method = CONTRIBUTION_METHODS[author_year]
    if not examples:
        body = "-- (no examples in JSON)"
        all_def = "def all : List Datum := []"
    else:
        body = "\n\n".join(emit_example(e, ay_lower, default_method) for e in examples)
        local_ids = [
            lean_identifier((e.get("id") or "").strip(), ay_lower)
            for e in examples
        ]
        all_def = f"def all : List Datum := [{', '.join(local_ids)}]"

    return f"""import Linglib.Data.Examples.Schema

/-!
# `{author_year}` — typed example data

Auto-generated from `Linglib/Data/Examples/{author_year}.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace {author_year}.Examples`.
-/

namespace {author_year}.Examples

{body}

{all_def}

end {author_year}.Examples
"""


def process(author_year: str, check: bool) -> bool:
    """Generate (or, with `check`, verify) one paper's module.

    Returns True on success / in-sync; False on drift in check mode.
    Exits on malformed input (both modes)."""
    json_path = JSON_DIR / f"{author_year}.json"
    if not json_path.exists():
        sys.stderr.write(f"FATAL: JSON not found at {json_path.relative_to(ROOT)}\n")
        sys.exit(1)

    try:
        with open(json_path, encoding="utf-8") as f:
            examples = json.load(f)
    except json.JSONDecodeError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: invalid JSON: {e}\n")
        sys.exit(1)

    if not isinstance(examples, list):
        sys.stderr.write(
            f"FATAL: {json_path.relative_to(ROOT)}: top level must be an array of "
            f"example objects (got {type(examples).__name__})\n"
        )
        sys.exit(1)

    try:
        module_text = as_module_if_possible(emit_module(author_year, examples))
    except ValueError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)

    module_path = JSON_DIR / f"{author_year}.lean"
    rel_module = module_path.relative_to(ROOT)
    rel_json = json_path.relative_to(ROOT)
    n = len(examples)

    in_sync = (
        module_path.exists()
        and module_path.read_text(encoding="utf-8") == module_text
    )

    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel_module} in sync\n")
        else:
            sys.stderr.write(
                f"[check] DRIFT: {rel_module} does not match {rel_json}; "
                f"run scripts/gen_examples.py {author_year}\n"
            )
        return in_sync

    if in_sync:
        sys.stdout.write(f"[gen] {rel_module} unchanged\n")
    else:
        module_path.write_text(module_text, encoding="utf-8")
        sys.stdout.write(
            f"[gen] {rel_module} \u2190 {rel_json} ({n} example{'s' if n != 1 else ''})\n"
        )

    return True


LEAN_KEYWORDS = {
    "at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "then", "with",
    "from", "open", "show", "where", "for", "unless", "return", "mut", "calc", "def", "theorem",
    "example", "instance", "class", "structure", "inductive", "namespace", "section", "variable",
    "universe", "import", "axiom", "deriving", "local", "scoped", "private", "protected", "public",
    "partial", "unsafe", "macro", "syntax", "attribute", "abbrev", "opaque", "omit", "include",
}


def language_identifier(name: str, where: str) -> str:
    """The lowerCamelCase Lean name of a Glottolog name: its words, the first lowercased, the
    others capitalized, letters kept as Glottolog writes them (`Hixkaryána` → `hixkaryána`) and
    apostrophes dropped within a word (`K'iche'` → `kiche`)."""
    words = re.findall(r"[^\W_]+", re.sub(r"['’ʼ]", "", name))
    if not words:
        sys.stderr.write(f"FATAL: {where}: no Lean name for {name!r}\n")
        sys.exit(1)
    ident = words[0][0].lower() + words[0][1:] + "".join(w[0].upper() + w[1:] for w in words[1:])
    return f"«{ident}»" if ident in LEAN_KEYWORDS or ident[0].isdigit() else ident


def emit_languages() -> str:
    with open(LANGUAGES, encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    names: dict[str, str] = {}
    defs = []
    for row in rows:
        where = f"{LANGUAGES.relative_to(ROOT)}: {row['ID']}"
        ident = language_identifier(row["Name"], where)
        if ident in names:
            sys.stderr.write(
                f"FATAL: {where}: {ident} also names {names[ident]}; the generator needs "
                f"distinct Glottolog names\n")
            sys.exit(1)
        names[ident] = row["ID"]
        iso = f" (ISO 639-3 `{row['ISO639P3code']}`)" if row["ISO639P3code"] else ""
        level = "" if row["Level"] == "language" else f", a {row['Level']}"
        defs.append(f"/-- {row['Name']}, `{row['ID']}`{iso}{level}. -/\n"
                    f"def {ident} : Glottocode := {lean_string(row['ID'])}")
    body = "\n\n".join(defs)
    return f"""import Linglib.Data.Examples.Schema

/-!
# The languages of the example data

Auto-generated from `Linglib/Data/Examples/languages.csv` by
`scripts/gen_examples.py --all`. Do not edit by hand; edit the table and re-run
the generator. Each Glottolog languoid of the table, a language, a dialect or a
family, is a `Glottocode` named after its Glottolog name, so that a study names
the languages of its sample, `Glottocode.english`, rather than their codes.
-/

namespace Glottocode

{body}

end Glottocode
"""


def process_languages(check: bool) -> bool:
    """Generate (or, with `check`, verify) the module of the language table."""
    module_text = as_module_if_possible(emit_languages())
    module_path = JSON_DIR / "Languages.lean"
    rel_module = module_path.relative_to(ROOT)
    in_sync = module_path.exists() and module_path.read_text(encoding="utf-8") == module_text
    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel_module} in sync\n")
        else:
            sys.stderr.write(f"[check] DRIFT: {rel_module} does not match "
                             f"{LANGUAGES.relative_to(ROOT)}; run scripts/gen_examples.py --all\n")
        return in_sync
    if in_sync:
        sys.stdout.write(f"[gen] {rel_module} unchanged\n")
    else:
        module_path.write_text(module_text, encoding="utf-8")
        sys.stdout.write(f"[gen] {rel_module} \u2190 {LANGUAGES.relative_to(ROOT)}\n")
    return True


# Canonical JSON formatting: 2-space indent, schema key order, and compact
# leaf collections (gloss pairs packed onto wrapped lines; one feature pair /
# alternative / reading per line) so a python round-trip never explodes them.

KEY_ORDER = [
    "id", "source", "reportedIn", "method", "language", "primaryText",
    "discourseSegments", "glossedTokens", "translation", "context",
    "judgment", "verdict", "alternatives", "readings", "paperFeatures", "comment",
    "verified",
]

# `discourseSegments`, `translation`, `comment` and `verified` are the source's record rather than
# fields: the utterances of a discourse, the translation, notes, and how the row was last checked
# against its source. They are validated here and exported to CLDF; the generated Lean module does
# not carry them.
VERIFIED = {
    "page-image": "every field checked against the page images of the source",
    "text-layer": "checked against the text layer of the source's PDF only",
    "supplement": "checked against the source's published supplementary materials (stimuli, data)",
}

MAX_WIDTH = 98


def _j(v) -> str:
    return json.dumps(v, ensure_ascii=False)


def _fmt_inline_list(items: list[str], indent: str) -> str:
    """Render pre-serialized items inside [...], packing them onto lines of
    at most MAX_WIDTH characters."""
    if not items:
        return "[]"
    lines, cur = [], ""
    for it in items:
        cand = it if not cur else f"{cur}, {it}"
        if cur and len(indent) + 2 + len(cand) > MAX_WIDTH:
            lines.append(cur + ",")
            cur = it
        else:
            cur = cand
    lines.append(cur)
    body = "\n".join(f"{indent}  {l}" for l in lines)
    return f"[\n{body}\n{indent}]"


def _fmt_per_line_list(items: list[str], indent: str) -> str:
    """Render pre-serialized items inside [...], one per line."""
    if not items:
        return "[]"
    body = ",\n".join(f"{indent}  {it}" for it in items)
    return f"[\n{body}\n{indent}]"


def _fmt_obj_inline(o: dict) -> str:
    return "{" + ", ".join(f"{_j(k)}: {_j(v)}" for k, v in o.items()) + "}"


def _fmt_value(key: str, v, indent: str) -> str:
    if v is None or isinstance(v, (str, int, float, bool)):
        return _j(v)
    if isinstance(v, dict):
        return _fmt_obj_inline(v)
    if isinstance(v, list):
        if key == "glossedTokens":
            return _fmt_inline_list([_j(x) for x in v], indent)
        if key in ("paperFeatures", "alternatives", "readings"):
            items = [
                _fmt_obj_inline(x) if isinstance(x, dict) else _j(x) for x in v
            ]
            return _fmt_per_line_list(items, indent)
        if key == "discourseSegments":
            return _fmt_per_line_list([_j(x) for x in v], indent)
        return _j(v)
    return _j(v)


def format_examples(examples: list) -> str:
    """Canonical text for a per-paper JSON file."""
    out = ["["]
    for i, ex in enumerate(examples):
        out.append("  {")
        keys = [k for k in KEY_ORDER if k in ex]
        keys += [k for k in ex if k not in KEY_ORDER]  # never drop unknown keys; the generator rejects them
        for j, k in enumerate(keys):
            comma = "," if j < len(keys) - 1 else ""
            out.append(f"    {_j(k)}: {_fmt_value(k, ex[k], '    ')}{comma}")
        out.append("  }," if i < len(examples) - 1 else "  }")
    out.append("]")
    return "\n".join(out) + "\n"


def fmt(author_year: str) -> bool:
    """Rewrite a JSON file in canonical format. Refuses to write (and
    returns False) if the formatted text does not parse back to the
    identical data."""
    json_path = JSON_DIR / f"{author_year}.json"
    with open(json_path, encoding="utf-8") as f:
        examples = json.load(f)
    text = format_examples(examples)
    if json.loads(text) != examples:
        sys.stderr.write(
            f"[fmt] REFUSING {json_path.relative_to(ROOT)}: round-trip mismatch\n"
        )
        return False
    if json_path.read_text(encoding="utf-8") == text:
        sys.stdout.write(f"[fmt] {json_path.relative_to(ROOT)} unchanged\n")
    else:
        json_path.write_text(text, encoding="utf-8")
        sys.stdout.write(f"[fmt] {json_path.relative_to(ROOT)} reformatted\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    do_fmt = "--fmt" in args
    args = [a for a in args if a not in ("--check", "--fmt")]

    every = args == ["--all"] or (not args and check)
    if every:
        papers = sorted(p.stem for p in JSON_DIR.glob("*.json"))
    elif len(args) == 1 and not args[0].startswith("-"):
        papers = [args[0]]
    else:
        sys.stderr.write(
            "Usage: python3 scripts/gen_examples.py <AuthorYear> | --all\n"
            "       python3 scripts/gen_examples.py --check [<AuthorYear>]\n"
            "       python3 scripts/gen_examples.py --fmt <AuthorYear> | --all\n"
            "  --all    regenerate every Linglib/Data/Examples/*.json\n"
            "  --check  verify generated modules match JSON (no writes); "
            "exit 1 on drift\n"
            "  --fmt    rewrite JSON in canonical format (data-preserving); needs a\n"
            "           paper name, or --all for a PR whose subject is the reformat\n"
        )
        sys.exit(1)

    if do_fmt:
        if not all([fmt(p) for p in papers]):
            sys.exit(1)
        return

    ok = all([process(p, check) for p in papers])
    if every and not do_fmt:
        ok = process_languages(check) and ok
    if not ok:
        sys.exit(1)


if __name__ == "__main__":
    main()
