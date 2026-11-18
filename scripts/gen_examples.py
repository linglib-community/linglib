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

JSON file format: a top-level JSON array of example objects, or an object
`{"features": [...], "readings": {...}, "spans": {...}, "examples": [...]}` that also declares
the paper's feature taxonomy, its readings and the labels and lexemes of its spans (see Typed
features, Typed readings and Spans below). Each
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
    "glossedTokens": [["Every", "every"], ...],  // pairs as 2-arrays; the gloss is "" for a
                                             // word the source segments without glossing
    "translation": "...",
    "context": "",
    "judgment": "acceptable",                // one of the 6 cases
    "verdict": true,                         // optional: a truth-value judgment in the context
    "contrasts": [{"form": "...", "judgment": "unacceptable"}],
    "readings":     [{"name": "strong", "judgment": "acceptable"},
                     {"name": "weak",   "judgment": "acceptable"}],
    "spans":        [{"start": 3, "length": 3, "label": "definite"},     // optional: runs of
                     {"start": 3, "label": "determiner", "lexeme": "na"}], // `glossedTokens`
    "paperFeatures": [["key", "value"], ...],  // the paper's own columns
    "comment": "..."
  }

Behavior:
- Errors out (exit 1) if the JSON file doesn't exist.
- Reads each paper's method from `contributions.csv` (one of `elicitation`, `corpus`,
  `experiment`, `description`, or `unclassified`) and errors out on a paper with no row there; a
  row's `method` overrides it, `unclassified` included, and the method is emitted as
  `Datum.method` (`none` where unclassified).
- Validates but does not emit the record-only keys: the CLDF export carries
  them, and no theorem reads them, so the Lean rows that `decide` reduces stay
  small. `verified` (`"page-image"`, `"text-layer"` or `"supplement"`) is how the row was last
  checked against its source.
- Emits, beside `glossedTokens`, the derived `glossedWords`, each word with its gloss and, when
  the two are segmented alike, its morpheme-gloss pairs, as `pyigt` models a glossed word, and
  `lgrConformance`, the example's CLDF `LGR_Conformance` (`scripts/lgr.py`, shared with the CLDF
  export). They are lists of characters, so that no theorem splits a string in the kernel.
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

Typed features: a declared feature names a `paperFeatures` key, the Lean `type` of its values and
the `lean` name of its reader, and lists its levels, each a Lean `name`, the `label` the rows
write and a `doc`:

  {"key": "complementizer", "lean": "complementizer", "type": "Complementizer",
   "doc": "The complementizer of the embedded clause.", "multiple": false,
   "levels": [{"name": "oti", "label": "oti", "doc": "oti 'that'"}, ...]}

Every value a row records under a declared key must be one of its labels, a key not declared
`multiple` occurs at most once in a row, and every declared key occurs in some row. The module
emits each type as an enum and its reader over `Datum`, an `Option` of the type or, for a
`multiple` key, the `List` of the values, so that a study reads the feature by a total map from
the enum rather than a table of strings, and a value that drifts fails here rather than leaving
a theorem silently vacuous. Undeclared keys stay strings.

Typed readings: a paper whose readings form a closed set declares them once, beside `features`:

  "readings": {"lean": "reading", "type": "Reading", "doc": "The readings the paper tests.",
               "levels": [{"name": "boundVariable", "label": "bound variable", "doc": "..."}, ...]}

Every reading a row judges must then be a declared level, a row judges a reading at most once,
and every level is judged in some row. The module emits the enum, its `label` and a reader
`reading : Datum → Reading → Option Judgment`, so that a study names a reading by a constructor
and a name that drifts fails here. A paper that does not declare its readings keeps them as
strings.

Spans: a row's `spans` mark runs of its `glossedTokens`, each by the `start`, the position of its first word,
and its `length` (1 if omitted, 0 for an element the source's analysis posits without a word),
under a `label`, with the `lexeme` the span is a form of where it is one. A file whose rows have
spans declares their labels and lexemes beside `features`:

  "spans": {"labels":   {"type": "SpanLabel", "doc": "...", "levels": [{"name": "definite", ...}]},
            "lexemes": {"type": "Lexeme", "doc": "...", "levels": [{"name": "na", ...}]}}

Every label and lexeme a span names must be a declared level, every level is named by some span,
and a span lies within the row's gloss line. The module emits the two enums and the readers
`label? : Datum.Span → Option SpanLabel` and `lexeme? : Datum.Span → Option Lexeme`, so that a study
maps each lexeme to its entry in a language's fragment by a total function: the row names the
entry, and the study proves that the span is written as the entry is, rather than finding the
entry by its spelling.

Boundaries: the generator segments a word at the separators of the Leipzig rules, `-`, `=` and
`~`. A source with its own notation declares its symbols beside `features`:

  "boundaries": {"type": "Boundary", "doc": "...",
                 "levels": [{"name": "compound", "symbol": "=", "leipzig": "-", "doc": "..."}],
                 "marks":  [{"symbol": "+", "doc": "the weak grade of consonant gradation"}]}

A word is then segmented at the declared symbols and no others, each morpheme keeps the symbol
before it as the source prints it, and a mark is dropped from the morphemes while the word keeps
it. The module emits the enum and the reader `boundary? : GlossedMorpheme → Option Boundary`.
`leipzig` gives the Leipzig separator the symbol is written as in the CLDF export and in the
conformance level. Every declared symbol is one character that some word of the rows writes.

Dependencies: pure stdlib (json module).
"""

import csv
import json
import re
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402
from lgr import glossed_morphemes, leipzig_pairs, lgr_conformance  # noqa: E402

ROOT       = Path(__file__).resolve().parent.parent
JSON_DIR   = ROOT / "Linglib" / "Data" / "Examples"
LANGUAGES  = JSON_DIR / "languages.csv"
CONTRIBUTIONS = JSON_DIR / "contributions.csv"
METHODS = ("elicitation", "corpus", "experiment", "description")


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


def lean_chars(s: str) -> str:
    """A `List Char` literal: the kernel reduces it without decoding a string."""
    esc = {"'": "\\'", "\\": "\\\\", "\n": "\\n", "\t": "\\t"}
    return "[" + ", ".join(f"'{esc.get(c, c)}'" for c in s) + "]"


def emit_glossed_words(xs, boundaries=None) -> str:
    """Emit the `List GlossedWord` of the validated gloss pairs `xs`, segmented at the boundary
    symbols the file declares, if it declares any."""
    words = []
    for word, gloss in xs:
        gms = glossed_morphemes(word, gloss, boundaries) or []
        items = ", ".join(
            f"⟨{lean_chars(m)}, {lean_chars(g)}, {'none' if sep is None else f'some {lean_chars(sep)[1:-1]}'}⟩"
            for m, g, sep in gms)
        words.append(f"⟨{lean_chars(word)}, {lean_chars(gloss)}, [{items}]⟩")
    return "[" + ", ".join(words) + "]"


CONFORMANCE = {"WORD_ALIGNED": ".wordAligned", "MORPHEME_ALIGNED": ".morphemeAligned"}


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
    for contrasts or "name" for readings.
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


def emit_example(ex: dict, author_year_lower: str, default_method: str,
                 boundaries: dict | None = None) -> str:
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
    if "method" in ex and ex["method"] not in METHODS + ("unclassified",):
        raise ValueError(f"{where}: method {ex['method']!r}; expected one of "
                         f"{', '.join(METHODS)} or unclassified")
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
    pairs_      = ex.get("glossedTokens", [])
    gloss_lines = ""
    if pairs_:
        gloss_lines = f"\n    glossedWords := {emit_glossed_words(pairs_, boundaries)}"
        level = lgr_conformance(leipzig_pairs(pairs_, boundaries))
        if level is not None:
            gloss_lines += f"\n    lgrConformance := some {CONFORMANCE[level]}"
    context     = ex.get("context") or ""
    judgment    = parse_judgment(ex.get("judgment", ""), where + ".judgment")
    verdict     = ex.get("verdict")
    if verdict is not None and not isinstance(verdict, bool):
        raise ValueError(f"{where}.verdict: expected a JSON boolean")
    contrasts   = emit_form_judgment_list(ex.get("contrasts", []), where + ".contrasts", "form")
    readings    = emit_form_judgment_list(ex.get("readings", []), where + ".readings", "name")
    features    = emit_string_pair_list(ex.get("paperFeatures", []), where + ".paperFeatures")
    spans_line  = ""
    span_items  = []
    for i, p in enumerate(ex.get("spans", [])):
        w = f"{where}.spans[{i}]"
        if (not isinstance(p, dict) or set(p) - {"start", "length", "label", "lexeme"}
                or not isinstance(p.get("label"), str)
                or not isinstance(p.get("lexeme", ""), str)):
            raise ValueError(f"{w}: expected `start`, `label` and optionally `length` and `lexeme`")
        idx, ln = p.get("start"), p.get("length", 1)
        if type(idx) is not int or type(ln) is not int or idx < 0 or ln < 0:
            raise ValueError(f"{w}: `start` and `length` are natural numbers")
        if idx + ln > len(pairs_) or idx + max(ln, 1) > len(pairs_):
            raise ValueError(f"{w}: the span lies outside the {len(pairs_)} words of the gloss line")
        lex = "none" if "lexeme" not in p else f"some {lean_string(p['lexeme'])}"
        span_items.append(f"⟨{idx}, {ln}, {lean_string(p['label'])}, {lex}⟩")
    if span_items:
        spans_line = f"\n    spans := [{', '.join(span_items)}]"
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
    glossedTokens := {glossed}{gloss_lines}
    context := {lean_string(context)}
    judgment := {judgment}{verdict_line}
    contrasts := {contrasts}
    readings := {readings}{spans_line}
    paperFeatures := {features} }}"""


IDENT = re.compile(r"^[a-z][A-Za-z0-9]*$")
TYPE_IDENT = re.compile(r"^[A-Z][A-Za-z0-9]*$")


def split_data(data, where: str):
    """The declared features, the declared readings (or `None`), the declared labels and lexemes
    of spans (or `None`) and the example rows of a paper's JSON."""
    if isinstance(data, list):
        return [], None, None, None, data
    keys = {"features", "readings", "spans", "boundaries", "examples"}
    if isinstance(data, dict) and set(data) <= keys and "examples" in data:
        return (data.get("features", []), data.get("readings"), data.get("spans"),
                data.get("boundaries"), data["examples"])
    raise ValueError(f"{where}: top level must be an array of examples or an object with "
                     f"`examples` and optionally `features`, `readings`, `spans` and `boundaries`")


def validate_levels(levels: list, w: str) -> set:
    """Check the levels of a declared taxonomy and return their labels."""
    names, labels = set(), set()
    for lv in levels:
        if set(lv) != {"name", "label", "doc"}:
            raise ValueError(f"{w}: a level needs exactly `name`, `label` and `doc`")
        if not IDENT.match(lv["name"]) or lv["name"] in LEAN_KEYWORDS:
            raise ValueError(f"{w}: level name {lv['name']!r} is not a Lean identifier")
        if lv["name"] in names or lv["label"] in labels:
            raise ValueError(f"{w}: duplicate level {lv['name']!r} / {lv['label']!r}")
        names.add(lv["name"]); labels.add(lv["label"])
    return labels


def validate_readings(rd, features: list, examples: list, where: str) -> None:
    if rd is None:
        return
    w = f"{where}.readings"
    if set(rd) != {"lean", "type", "doc", "levels"}:
        raise ValueError(f"{w}: needs exactly `lean`, `type`, `doc` and `levels`")
    if not IDENT.match(rd["lean"]) or rd["lean"] in LEAN_KEYWORDS:
        raise ValueError(f"{w}: `lean` {rd['lean']!r} is not a Lean identifier")
    if not TYPE_IDENT.match(rd["type"]):
        raise ValueError(f"{w}: `type` {rd['type']!r} is not a Lean type name")
    if any(rd["lean"] == ft["lean"] or rd["type"] == ft["type"] for ft in features):
        raise ValueError(f"{w}: `lean` or `type` repeats a declared feature's")
    labels = validate_levels(rd["levels"], w)
    seen = set()
    for ex in examples:
        names = [x["name"] for x in ex.get("readings", [])]
        for n in names:
            if n not in labels:
                raise ValueError(f"{where}: {ex.get('id')}: reading {n!r} is not a declared "
                                 f"level of {rd['type']}")
        if len(names) != len(set(names)):
            raise ValueError(f"{where}: {ex.get('id')}: a reading is judged twice")
        seen |= set(names)
    if seen != labels:
        raise ValueError(f"{w}: no row judges {sorted(labels - seen)}")


def validate_features(features: list, examples: list, where: str) -> None:
    keys, types, leans = set(), set(), set()
    for i, ft in enumerate(features):
        w = f"{where}.features[{i}]"
        extra = set(ft) - {"key", "lean", "type", "doc", "levels", "multiple"}
        if extra:
            raise ValueError(f"{w}: unknown keys {sorted(extra)}")
        for k in ("key", "lean", "type", "doc", "levels"):
            if k not in ft:
                raise ValueError(f"{w}: missing `{k}`")
        if not IDENT.match(ft["lean"]) or ft["lean"] in LEAN_KEYWORDS:
            raise ValueError(f"{w}: `lean` {ft['lean']!r} is not a Lean identifier")
        if not TYPE_IDENT.match(ft["type"]):
            raise ValueError(f"{w}: `type` {ft['type']!r} is not a Lean type name")
        for seen, v, what in ((keys, ft["key"], "key"), (types, ft["type"], "type"), (leans, ft["lean"], "lean")):
            if v in seen:
                raise ValueError(f"{w}: duplicate {what} {v!r}")
            seen.add(v)
        labels = validate_levels(ft["levels"], w)
        occurs = False
        for ex in examples:
            vals = [v for k, v in ex.get("paperFeatures", []) if k == ft["key"]]
            occurs = occurs or bool(vals)
            if len(vals) > 1 and not ft.get("multiple", False):
                raise ValueError(f"{where}: {ex.get('id')}: `{ft['key']}` repeats but is not `multiple`")
            for v in vals:
                if v not in labels:
                    raise ValueError(f"{where}: {ex.get('id')}: `{ft['key']}` value {v!r} is not a "
                                     f"declared level of {ft['type']}")
        if not occurs:
            raise ValueError(f"{w}: no row records `{ft['key']}`")


def validate_boundaries(decl, taken: set, examples: list, where: str) -> None:
    if decl is None:
        return
    w = f"{where}.boundaries"
    if set(decl) - {"type", "doc", "levels", "marks"} or not {"type", "doc", "levels"} <= set(decl):
        raise ValueError(f"{w}: needs `type`, `doc`, `levels` and optionally `marks`")
    if not TYPE_IDENT.match(decl["type"]) or decl["type"] in taken:
        raise ValueError(f"{w}: `type` {decl['type']!r} is not a fresh Lean type name")
    words = "".join(p[0] for ex in examples for p in ex.get("glossedTokens", []))
    names, symbols = set(), set()
    for lv in decl["levels"]:
        if set(lv) != {"name", "symbol", "leipzig", "doc"}:
            raise ValueError(f"{w}: a level needs exactly `name`, `symbol`, `leipzig` and `doc`")
        if not IDENT.match(lv["name"]) or lv["name"] in LEAN_KEYWORDS or lv["name"] in names:
            raise ValueError(f"{w}: level name {lv['name']!r} is not a fresh Lean identifier")
        if lv["leipzig"] not in ("-", "=", "~"):
            raise ValueError(f"{w}: `leipzig` of {lv['name']!r} must be one of `-`, `=`, `~`")
        names.add(lv["name"])
    for d in decl["levels"] + decl.get("marks", []):
        s = d.get("symbol")
        if not isinstance(s, str) or len(s) != 1 or s.isalnum() or s.isspace() or s in symbols:
            raise ValueError(f"{w}: symbol {s!r} must be one fresh character, not a letter or digit")
        if s not in words:
            raise ValueError(f"{w}: no word of the rows writes {s!r}")
        symbols.add(s)
    for m in decl.get("marks", []):
        if set(m) != {"symbol", "doc"}:
            raise ValueError(f"{w}: a mark needs exactly `symbol` and `doc`")


def emit_boundaries(decl: dict) -> str:
    ctors = "\n".join(f"  /-- `{lv['symbol']}`: {lv['doc']} -/\n  | {lv['name']}"
                      for lv in decl["levels"])
    table = ", ".join(f"({lean_chars(lv['symbol'])[1:-1]}, .{lv['name']})" for lv in decl["levels"])
    return (f"/-- {decl['doc']} -/\ninductive {decl['type']} where\n{ctors}\n"
            f"  deriving DecidableEq, Repr, Fintype\n\n"
            f"/-- The boundary before a morpheme, by the symbol the source writes there. -/\n"
            f"def boundary? (m : GlossedMorpheme) : Option {decl['type']} :=\n"
            f"  m.sep.bind (List.lookup · [{table}])")


SPAN_KINDS = (("labels", "label"), ("lexemes", "lexeme"))


def validate_spans(decl, features: list, readings, examples: list, where: str) -> None:
    w = f"{where}.spans"
    if decl is None:
        for ex in examples:
            if ex.get("spans"):
                raise ValueError(f"{where}: {ex.get('id')} has spans but the file declares no "
                                 f"`spans` with their labels and lexemes")
        return
    if "labels" not in decl or set(decl) - {"labels", "lexemes"}:
        raise ValueError(f"{w}: needs `labels` and optionally `lexemes`")
    taken = {ft["type"] for ft in features} | ({readings["type"]} if readings else set())
    names = {ft["lean"] for ft in features} | ({readings["lean"]} if readings else set())
    if names & {"label?", "lexeme?"}:
        raise ValueError(f"{w}: a feature or the readings use the reader name `label?` or `lexeme?`")
    for kind, key in SPAN_KINDS:
        d = decl.get(kind)
        if d is None:
            continue
        if set(d) != {"type", "doc", "levels"}:
            raise ValueError(f"{w}.{kind}: needs exactly `type`, `doc` and `levels`")
        if not TYPE_IDENT.match(d["type"]) or d["type"] in taken:
            raise ValueError(f"{w}.{kind}: `type` {d['type']!r} is not a fresh Lean type name")
        taken.add(d["type"])
        labels = validate_levels(d["levels"], f"{w}.{kind}")
        seen = set()
        for ex in examples:
            for p in ex.get("spans", []):
                if key in p:
                    if p[key] not in labels:
                        raise ValueError(f"{where}: {ex.get('id')}: {key} {p[key]!r} is not a "
                                         f"declared level of {d['type']}")
                    seen.add(p[key])
        if seen != labels:
            raise ValueError(f"{w}.{kind}: no span names {sorted(labels - seen)}")
    if "lexemes" not in decl and any("lexeme" in p for ex in examples for p in ex.get("spans", [])):
        raise ValueError(f"{w}: a span names a lexeme but the file declares no `lexemes`")


def emit_spans(decl: dict) -> str:
    out = []
    for kind, key in SPAN_KINDS:
        d = decl.get(kind)
        if d is None:
            continue
        ctors = "\n".join(f"  /-- {lv['label']}: {lv['doc']} -/\n  | {lv['name']}" for lv in d["levels"])
        table = ", ".join(f"({lean_string(lv['label'])}, .{lv['name']})" for lv in d["levels"])
        if key == "label":
            reader = (f"/-- The label of a span, where it is a declared one. -/\n"
                      f"def label? (p : Datum.Span) : Option {d['type']} :=\n"
                      f"  List.lookup p.label [{table}]")
        else:
            reader = (f"/-- The lexeme a span is a form of, where it names a declared one. -/\n"
                      f"def lexeme? (p : Datum.Span) : Option {d['type']} :=\n"
                      f"  p.lexeme.bind (List.lookup · [{table}])")
        out.append(f"/-- {d['doc']} -/\ninductive {d['type']} where\n{ctors}\n"
                   f"  deriving DecidableEq, Repr, Fintype\n\n{reader}")
    return "\n\n".join(out)


def emit_feature(ft: dict) -> str:
    ctors = "\n".join(f"  /-- {lv['label']}: {lv['doc']} -/\n  | {lv['name']}" for lv in ft["levels"])
    entries = [f"({lean_string(lv['label'])}, .{lv['name']})" for lv in ft["levels"]]
    lines, cur = [], ""
    for i, en in enumerate(entries):
        piece = en + ("," if i < len(entries) - 1 else "")
        if cur and len(cur) + 1 + len(piece) > 92:
            lines.append(cur); cur = piece
        else:
            cur = f"{cur} {piece}" if cur else piece
    lines.append(cur)
    table = "\n    ".join(lines)
    if ft.get("multiple", False):
        reader = (f"/-- The values a row records under `{ft['key']}`. -/\n"
                  f"def {ft['lean']} (e : Datum) : List {ft['type']} :=\n"
                  f"  (e.features {lean_string(ft['key'])}).filterMap (List.lookup · [{table}])")
    else:
        reader = (f"/-- The value a row records under `{ft['key']}`. -/\n"
                  f"def {ft['lean']} (e : Datum) : Option {ft['type']} :=\n"
                  f"  e.parse? {lean_string(ft['key'])} [{table}]")
    return (f"/-- {ft['doc']} -/\ninductive {ft['type']} where\n{ctors}\n"
            f"  deriving DecidableEq, Repr, Fintype\n\n{reader}")


def emit_readings(rd: dict) -> str:
    ctors = "\n".join(f"  /-- {lv['label']}: {lv['doc']} -/\n  | {lv['name']}" for lv in rd["levels"])
    arms = "\n".join(f"  | .{lv['name']} => {lean_string(lv['label'])}" for lv in rd["levels"])
    return (f"/-- {rd['doc']} -/\ninductive {rd['type']} where\n{ctors}\n"
            f"  deriving DecidableEq, Repr, Fintype\n\n"
            f"/-- The name the rows give the reading. -/\n"
            f"def {rd['type']}.label : {rd['type']} → String\n{arms}\n\n"
            f"/-- The judgment a row records for the reading, if it records one. -/\n"
            f"def {rd['lean']} (e : Datum) (r : {rd['type']}) : Option Judgment :=\n"
            f"  e.readings.lookup r.label")


def emit_module(author_year: str, examples: list, features: list | None = None,
                readings: dict | None = None, spans: dict | None = None,
                boundaries: dict | None = None) -> str:
    ay_lower = author_year.lower()
    if author_year not in CONTRIBUTION_METHODS:
        raise ValueError(f"no row in {CONTRIBUTIONS.relative_to(ROOT)}; add `{author_year},<method>` "
                         f"with the paper's method, or `unclassified`")
    default_method = CONTRIBUTION_METHODS[author_year]
    if not examples:
        body = "-- (no examples in JSON)"
        all_def = "def all : List Datum := []"
    else:
        body = "\n\n".join(emit_example(e, ay_lower, default_method, boundaries)
                           for e in examples)
        local_ids = [
            lean_identifier((e.get("id") or "").strip(), ay_lower)
            for e in examples
        ]
        all_def = f"def all : List Datum := [{', '.join(local_ids)}]"
    features = features or []
    feats = "".join("\n\n" + emit_feature(ft) for ft in features)
    if readings is not None:
        feats += "\n\n" + emit_readings(readings)
    if spans is not None:
        feats += "\n\n" + emit_spans(spans)
    if boundaries is not None:
        feats += "\n\n" + emit_boundaries(boundaries)
    typed = features or readings is not None or spans is not None or boundaries is not None
    imports = "import Linglib.Data.Examples.Schema" + (
        "\nimport Linglib.Data.Examples.Readers" if features else "") + (
        "\nimport Mathlib.Tactic.DeriveFintype" if typed else "")

    return f"""{imports}

/-!
# `{author_year}` — typed example data

Auto-generated from `Linglib/Data/Examples/{author_year}.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace {author_year}.Examples`.
-/

namespace {author_year}.Examples

{body}

{all_def}{feats}

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

    try:
        where = str(json_path.relative_to(ROOT))
        features, readings, spans, boundaries, examples = split_data(examples, where)
        validate_features(features, examples, where)
        validate_readings(readings, features, examples, where)
        validate_spans(spans, features, readings, examples, where)
        taken = {ft["type"] for ft in features} | ({readings["type"]} if readings else set())
        taken |= {d["type"] for d in (spans or {}).values()}
        validate_boundaries(boundaries, taken, examples, where)
        module_text = as_module_if_possible(
            emit_module(author_year, examples, features, readings, spans, boundaries))
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
    "judgment", "verdict", "contrasts", "readings", "spans", "paperFeatures", "comment",
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
        if key in ("paperFeatures", "contrasts", "readings", "spans"):
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
        data = json.load(f)
    if isinstance(data, dict):
        features, readings, spans, boundaries, examples = split_data(data, str(json_path))
        body = format_examples(examples).rstrip("\n").replace("\n", "\n  ")
        head = ""
        for key, val in (("features", features if "features" in data else None),
                         ("readings", readings), ("spans", spans), ("boundaries", boundaries)):
            if val is not None:
                dumped = json.dumps(val, ensure_ascii=False, indent=2).replace("\n", "\n  ")
                head += f'  "{key}": {dumped},\n'
        text = f'{{\n{head}  "examples": {body}\n}}\n'
        examples = data
    else:
        text = format_examples(data)
        examples = data
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
