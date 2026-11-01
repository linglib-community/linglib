#!/usr/bin/env python3
"""Export the per-paper example data as a CLDF dataset and validate it.

Usage:
    python3 scripts/export_examples_cldf.py <outdir>              # write the dataset
    python3 scripts/export_examples_cldf.py --validate <outdir>   # write, then validate (CI)
    python3 scripts/export_examples_cldf.py --sync-languages [<glottolog languages.csv>]
    python3 scripts/export_examples_cldf.py --report              # per-paper rows to check

Reads every `Linglib/Data/Examples/<AuthorYear>.json`, `Linglib/Data/Examples/languages.csv` and
`references.bib`, and writes a CLDF dataset of the Generic module (Forkel et al. 2018;
specification 1.3):

- `examples.csv` (ExampleTable): one row per example. `Analyzed_Word` and `Gloss` are the two
  sides of `glossedTokens`; `LGR_Conformance` is derived from them rather than stored:
  `WORD_ALIGNED` for a glossed example, `MORPHEME_ALIGNED` when every word and its gloss also
  have the same number of `-` and of `=` boundaries (Leipzig Glossing Rules, Rules 2 and 2A) and
  at least one word is segmented. `Grammaticality_Judgement` is the mark the paper prints
  (empty, `?`, `??`, `#`, `*`). `Source` is `bibkey[locator]` for `source` and `reportedIn`.
  The linglib-specific fields are custom columns: `Context`, and JSON-valued
  `Discourse_Segments`, `Alternatives`, `Readings`, `Paper_Features`.
- `languages.csv` (LanguageTable): the rows of `Linglib/Data/Examples/languages.csv`, plus one
  item with no Glottocode for the constructed strings (formal-language patterns) whose
  `language` is empty, and, for each language with a judged example (a non-empty
  `Grammaticality_Judgement`), one item `<glottocode>-judged` with no Glottocode that such
  examples link to. The CLDF examples component requires this of ungrammatical examples, so that
  an aggregator ignoring the judgement does not assign a starred string to the language; a `?`,
  `??` or `#` example is no safer to assign, so every marked example gets it.
- `contributions.csv` (ContributionTable): one row per data file; each example links to its file.
- `sources.bib`: the entries of `references.bib` the examples cite.

`--validate` fails on any error or warning the CLDF validator reports, and on any entry of
`references.bib` a BibTeX parser rejects. Every export fails on a row value whose key names no
column, which the CLDF writer would otherwise drop without a word.

`--report` prints, per paper, the rows to check against their source that CLDF validation does
not flag: a non-English example with no gloss or translation (a gap only if the source gives
one, since a row records what the source prints), a gloss breaking Leipzig Rule 2, a source with
no locator or one with no recognizable head (an example number, page, section, chapter,
footnote, table or figure), a family-level Glottocode, a discourse whose segments do not join to
its text, and a word with a digit between letters or a capital after a lowercase letter, the
shapes a PDF text layer leaves when it renders a letter as another glyph (O'dam ɨ as `1`, ɣ as
`G`). Some languages write such words on purpose (Jyutping tone digits, Mayan `7` for the glottal
stop, capitals for retroflexes); the column is a list to look at, not an error. It needs no
`pycldf`.

`--sync-languages` rewrites `Linglib/Data/Examples/languages.csv` with the Glottolog row of every
Glottocode the examples use or the table already lists, from a Glottolog CLDF `languages.csv` (by
default the pinned release below, downloaded), and fails on a code Glottolog does not have. A row
added by hand for a language that only a study names is kept. It needs no `pycldf`.

The export and validation need `pycldf` (`pip install pycldf`).
"""

import csv
import json
import logging
import re
import sys
import tempfile
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "Linglib" / "Data" / "Examples"
LANGUAGES = JSON_DIR / "languages.csv"
CONTRIBUTIONS = JSON_DIR / "contributions.csv"
BIB = ROOT / "references.bib"
META_LANGUAGE = "stan1293"
GLOTTOLOG = ("https://raw.githubusercontent.com/glottolog/glottolog-cldf/v5.3/cldf/"
             "languages.csv")
LANGUAGE_COLUMNS = ["ID", "Name", "Glottocode", "ISO639P3code", "Level", "Macroarea",
                    "Latitude", "Longitude"]
NO_LANGUAGE = {"ID": "no-language", "Name": "No language (a constructed string)"}
TERMS = "http://cldf.clld.org/v1.0/terms.rdf#"

MARK = {
    "acceptable": "",
    "marginal": "?",
    "questionable": "??",
    "unacceptable": "#",
    "ungrammatical": "*",
    "variable": "%",
}

CUSTOM_COLUMNS = [
    {"name": "Context", "dc:description": "The scenario the paper gives for the judgment."},
    {"name": "Verdict", "datatype": "boolean",
     "dc:description": "The truth-value judgment the source reports for the expression in the "
                       "context, where the task is truth rather than acceptability."},
    {"name": "Discourse_Segments", "datatype": "json",
     "dc:description": "The utterances of a discourse example, in order."},
    {"name": "Alternatives", "datatype": "json",
     "dc:description": "Other forms the paper judges in the same frame, with their marks."},
    {"name": "Readings", "datatype": "json",
     "dc:description": "The readings the paper distinguishes, with their marks."},
    {"name": "Paper_Features", "datatype": "json",
     "dc:description": "The paper's own classifications of the example, as key-value pairs."},
    {"name": "Verified",
     "dc:description": "How the row was last checked against its source: page-image or "
                       "text-layer; empty when it has not been."},
    {"name": "Method",
     "dc:description": "How the example and its judgment were obtained: introspection, "
                       "elicitation, corpus, experiment or description; empty when not yet "
                       "classified."},
]


def contribution_methods():
    """Each data file's default method, `None` where it is not yet classified."""
    with open(CONTRIBUTIONS, encoding="utf-8") as f:
        return {r["ID"]: (None if r["Method"] == "unclassified" else r["Method"])
                for r in csv.DictReader(f)}


CONTRIBUTION_METHODS = contribution_methods()


def load():
    papers = {}
    for path in sorted(JSON_DIR.glob("*.json")):
        with open(path, encoding="utf-8") as f:
            papers[path.stem] = json.load(f)
    return papers


def features(row):
    raw = row.get("paperFeatures", [])
    if isinstance(raw, dict):
        return [[k, v] for k, v in raw.items()]
    return [[x["key"], x["value"]] if isinstance(x, dict) else list(x) for x in raw]


def lgr_conformance(pairs):
    if not pairs:
        return None
    aligned = all(w.count("-") == g.count("-") and w.count("=") == g.count("=")
                  for w, g in pairs)
    segmented = any("-" in w or "=" in w for w, _ in pairs)
    return "MORPHEME_ALIGNED" if aligned and segmented else "WORD_ALIGNED"


def source_ref(ref):
    # `;` separates the references of a CLDF `Source` value, so it cannot occur in a locator.
    label = (ref.get("paperLabel") or "").strip().replace(";", ",")
    return f"{ref['bibkey']}[{label}]" if label else ref["bibkey"]


def judged_id(code):
    """The LanguageTable item, with no Glottocode, that the judged examples of `code` link to."""
    return f"{code}-judged"


def example_row(paper, row):
    pairs = row.get("glossedTokens") or []
    refs = [source_ref(row["source"])]
    if row.get("reportedIn"):
        refs.append(source_ref(row["reportedIn"]))
    code = row.get("language")
    return {
        "ID": row["id"],
        "Language_ID": (NO_LANGUAGE["ID"] if not code
                        else judged_id(code) if MARK[row["judgment"]] else code),
        "Primary_Text": row.get("primaryText", ""),
        "Analyzed_Word": [w for w, _ in pairs],
        "Gloss": [g for _, g in pairs],
        "Translated_Text": row.get("translation") or None,
        "Meta_Language_ID": META_LANGUAGE,
        "LGR_Conformance": lgr_conformance(pairs),
        "Comment": row.get("comment") or None,
        "Source": refs,
        "Grammaticality_Judgement": MARK[row["judgment"]] or None,
        "Contribution_ID": paper,
        "Context": row.get("context") or None,
        "Verdict": row.get("verdict"),
        "Discourse_Segments": row.get("discourseSegments") or None,
        "Alternatives": [{"form": a["form"], "mark": MARK[a["judgment"]]}
                         for a in row.get("alternatives", [])] or None,
        "Readings": [{"name": r["name"], "mark": MARK[r["judgment"]]}
                     for r in row.get("readings", [])] or None,
        "Paper_Features": features(row) or None,
        "Verified": row.get("verified"),
        "Method": row.get("method") or CONTRIBUTION_METHODS.get(paper),
    }


def used_codes(papers):
    return sorted({r["language"] for rows in papers.values() for r in rows if r["language"]}
                  | {META_LANGUAGE})


def sync_languages(glottolog_csv):
    if glottolog_csv is None:
        with urllib.request.urlopen(GLOTTOLOG) as resp:
            text = resp.read().decode("utf-8")
    else:
        text = Path(glottolog_csv).read_text(encoding="utf-8")
    glottolog = {r["ID"]: r for r in csv.DictReader(text.splitlines())}
    with open(LANGUAGES, encoding="utf-8") as f:
        listed = {r["ID"] for r in csv.DictReader(f)}
    codes = sorted(set(used_codes(load())) | listed)
    unknown = [c for c in codes if c not in glottolog]
    if unknown:
        sys.stderr.write(f"not Glottocodes: {', '.join(unknown)}\n")
        sys.exit(1)
    with open(LANGUAGES, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=LANGUAGE_COLUMNS, lineterminator="\n")
        w.writeheader()
        for c in codes:
            w.writerow({k: glottolog[c].get(k, "") for k in LANGUAGE_COLUMNS})
    sys.stdout.write(f"{LANGUAGES.relative_to(ROOT)}: {len(codes)} languages\n")


def read_bib():
    """The entries of `references.bib`, each parsed on its own so that a malformed entry is
    reported by key. The header is `%`-commented prose that mentions `@article`, which a BibTeX
    parser reads as an entry, so comment lines are dropped first."""
    from simplepybtex.database import parse_string
    from pycldf.sources import Source

    text = "".join(l for l in BIB.read_text(encoding="utf-8").splitlines(keepends=True)
                   if not l.lstrip().startswith("%"))
    sources, broken = [], []
    for chunk in re.split(r"(?m)^(?=@)", text):
        if not chunk.lstrip().startswith("@"):
            continue
        try:
            db = parse_string(chunk, "bibtex")
        except Exception as e:  # the parser raises several error types
            m = re.match(r"@\w+\{([^,]*)", chunk.lstrip())
            broken.append(f"{m.group(1) if m else chunk[:40]!r}: {e}")
            continue
        sources.extend(Source.from_entry(k, e) for k, e in db.entries.items())
    return sources, broken


def export(outdir: Path):
    from pycldf import Generic

    papers = load()
    examples = [example_row(p, r) for p, rows in papers.items() for r in rows]
    with open(LANGUAGES, encoding="utf-8") as f:
        languages = [{k: (v or None) for k, v in r.items()} for r in csv.DictReader(f)]
    if any(e["Language_ID"] == NO_LANGUAGE["ID"] for e in examples):
        languages.append(dict(NO_LANGUAGE))
    used = {e["Language_ID"] for e in examples}
    for lang in list(languages):
        if lang["ID"] != NO_LANGUAGE["ID"] and judged_id(lang["ID"]) in used:
            languages.append({"ID": judged_id(lang["ID"]),
                              "Name": f"{lang['Name']} (judged examples)"})
    cited = {re.sub(r"\[.*$", "", s) for e in examples for s in e["Source"]}
    sources, broken = read_bib()

    ds = Generic.in_dir(outdir)
    ds.add_component("ExampleTable")
    ds.add_component("LanguageTable")
    ds.add_component("ContributionTable")
    # A column is a CLDF property only when named by its term URI; a bare term name makes a plain
    # string column (named `source`) that the rows' `Source` values never reach.
    ds.add_columns("ExampleTable",
                   *(f"{TERMS}{t}" for t in ("source", "grammaticalityJudgement",
                                             "contributionReference")),
                   *CUSTOM_COLUMNS)
    ds.add_columns("ContributionTable",
                   {"name": "Method", "dc:description": "How the file's examples were obtained, "
                    "unless a row says otherwise; empty when not yet classified."})
    ds.add_columns("LanguageTable",
                   {"name": "Level", "dc:description": "The Glottolog level of the languoid."})
    ds.properties["dc:title"] = "Linglib linguistic examples"
    ds.properties["dc:description"] = (
        "The per-paper example data of Linglib (Linglib/Data/Examples), exported from its JSON "
        "files by scripts/export_examples_cldf.py. Languages from Glottolog 5.3.")
    ds.add_sources(*[s for s in sources if s.id in cited])
    for table, rows in (("ExampleTable", examples), ("LanguageTable", languages)):
        # `ds.write` silently drops a value whose key names no column.
        if extra := set().union(*rows) - {c.name for c in ds[table].tableSchema.columns}:
            raise ValueError(f"{table} has no column for {sorted(extra)}")
    ds.write(
        ExampleTable=examples,
        LanguageTable=languages,
        ContributionTable=[{"ID": p, "Name": p, "Method": CONTRIBUTION_METHODS.get(p)}
                           for p in papers],
    )
    return ds, broken


REPORT_COLUMNS = [
    ("unglossed", "a non-English example with no gloss"),
    ("untranslated", "a non-English example with no translation"),
    ("rule2", "a segmented gloss whose word and gloss differ in `-` or `=` boundaries"),
    ("nolocator", "a source with no locator"),
    ("locator", "a locator with no recognizable head: a descriptive name instead of a place"),
    ("coarse", "a Glottocode at family level"),
    ("discourse", "discourse segments whose single-space join is not primaryText"),
    ("glyphs", "a word with a digit between letters or a capital after a lowercase letter"),
]

# The head of a locator: an example number (`(12a)`, `[3b]`, `ex. 4`, `E52`), a page, a section,
# a chapter, a footnote, a table, figure, appendix or experiment, or the supplementary material.
# Anything may follow the head (`(53) 1a`, `(22)/(23b)`, `Exp. 1, scalar condition`).
LOCATOR_HEAD = re.compile(r"""^(?:
    (?:ex\.?\s*)?(?:\([^()]*\d[^()]*\)|\((?:[ivx]+[a-z]?|[a-z]|[ivx]+\s[a-z]|[IVX]+[a-z]?)\)
                     |\[\w+\]|[A-Z]{0,3}\d+[a-z]?(?:[._]\w+)*'?)
  | pp?\.\s*(?:\d+|[ivxlc]+)
  | n\.p\.
  | §\s*(?:\d+|[IVX]+)
  | (?:Section|Sect\.|section)\s*(?:\d+|[IVX]+)
  | (?:ch\.|Ch\.|Chapter|chapter)\s*(?:\d+|[IVX]+)
  | (?:fn\.?|footnote)\s*\d+
  | (?:Tables?|Figures?|Figs?\.|Appendix|Example|example|Experiment|Exp\.?)\s*\(?[A-Z]?\d+
  | SI\b
)""", re.X)

# A digit between two letters, or a lowercase letter followed by a capital, inside one word.
GLYPH = re.compile(r"[^\W\d_]\d+[^\W\d_]|[^\W\d_](?<=[a-zß-ÿā-ž])[A-Z]")


def report():
    """Per paper, the rows to check against their source that CLDF validation does not flag. A row
    verified against page images is settled, and a sign language's examples are written as
    glosses, so neither counts as unglossed."""
    with open(LANGUAGES, encoding="utf-8") as f:
        languages = list(csv.DictReader(f))
    level = {r["ID"]: r["Level"] for r in languages}
    signed = {r["ID"] for r in languages if "Sign Language" in r["Name"]}
    table, verified = {}, 0
    for paper, rows in load().items():
        counts = dict.fromkeys(k for k, _ in REPORT_COLUMNS)
        for k in counts:
            counts[k] = 0
        for r in rows:
            if r.get("verified") == "page-image":
                verified += 1
                continue
            pairs = r.get("glossedTokens") or []
            foreign = r["language"] not in ("", META_LANGUAGE)
            counts["unglossed"] += foreign and not pairs and r["language"] not in signed
            counts["untranslated"] += foreign and not r.get("translation")
            counts["rule2"] += (lgr_conformance(pairs) == "WORD_ALIGNED"
                                and any("-" in w or "=" in w for w, _ in pairs))
            refs = [r["source"]] + ([r["reportedIn"]] if r.get("reportedIn") else [])
            labels = [(ref.get("paperLabel") or "").strip() for ref in refs]
            counts["nolocator"] += not labels[0]
            counts["locator"] += any(l and not LOCATOR_HEAD.match(l) for l in labels)
            counts["coarse"] += level.get(r["language"]) == "family"
            segments = r.get("discourseSegments") or []
            counts["discourse"] += bool(segments) and r["primaryText"] != " ".join(segments)
            words = r["primaryText"].split() + [w for w, _ in pairs]
            counts["glyphs"] += any(GLYPH.search(w) for w in words)
        if any(counts.values()):
            table[paper] = counts
    keys = [k for k, _ in REPORT_COLUMNS]
    sys.stdout.write("paper\t" + "\t".join(keys) + "\n")
    for paper, counts in sorted(table.items(), key=lambda kv: -sum(kv[1].values())):
        sys.stdout.write(paper + "\t" + "\t".join(str(counts[k]) for k in keys) + "\n")
    totals = {k: sum(c[k] for c in table.values()) for k in keys}
    sys.stdout.write("total\t" + "\t".join(str(totals[k]) for k in keys) + "\n")
    sys.stdout.write(f"# rows verified against page images: {verified}\n")
    for k, what in REPORT_COLUMNS:
        sys.stdout.write(f"# {k}: {what}\n")


class _Count(logging.Handler):
    def __init__(self):
        super().__init__(logging.WARNING)
        self.n = 0

    def emit(self, record):
        self.n += 1
        sys.stderr.write(f"{record.levelname} {record.getMessage()}\n")


def main():
    args = sys.argv[1:]
    if args and args[0] == "--sync-languages":
        sync_languages(args[1] if len(args) > 1 else None)
        return
    if args == ["--report"]:
        report()
        return
    validate = "--validate" in args
    args = [a for a in args if a != "--validate"]
    if len(args) != 1:
        sys.stderr.write(__doc__)
        sys.exit(1)
    ds, broken = export(Path(args[0]))
    for b in broken:
        sys.stderr.write(f"ERROR references.bib: {b}\n")
    if validate:
        count = _Count()
        log = logging.getLogger("cldf")
        log.propagate = False
        log.addHandler(count)
        ok = ds.validate(log=log)
        if not ok or count.n or broken:
            sys.stderr.write(f"CLDF validation failed: {count.n} issue(s), "
                             f"{len(broken)} malformed bib entr(ies)\n")
            sys.exit(1)
        sys.stdout.write("CLDF validation passed\n")


if __name__ == "__main__":
    main()
