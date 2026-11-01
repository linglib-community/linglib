# `Linglib/Data/Examples/` — typed linguistic example data

One JSON file per source paper (`Charlow2014.json`, `Hofmann2025.json`, ...)
co-located with the [`Schema.lean`](Schema.lean) they instantiate. An
example is what the paper prints under a number; a row is a `Datum`, one
piece of data the paper reports with an example (Tonhauser and Matthewson
2016): an expression, the context it is judged in, and the judgment. Each
file is a top-level JSON array of rows: the fields of the `Datum` Lean
struct plus four record-only keys (see Schema below).

## Generator

```bash
python3 scripts/gen_examples.py <AuthorYear>   # generate one paper's module
python3 scripts/gen_examples.py --all          # regenerate every paper and Languages.lean
python3 scripts/gen_examples.py --check        # verify modules match JSON (CI)
python3 scripts/gen_examples.py --fmt <AuthorYear>  # rewrite one JSON in canonical format
python3 scripts/check_examples.py              # study literals vs rows, bibkeys (CI)
python3 scripts/export_examples_cldf.py --validate <dir>  # CLDF export + validation (CI; needs pycldf)
python3 scripts/export_examples_cldf.py --sync-languages  # rebuild languages.csv from Glottolog
python3 scripts/export_examples_cldf.py --report          # per-paper rows to check against sources
```

`--fmt` emits the canonical format (2-space indent, schema key order, gloss
pairs packed onto wrapped lines, one feature/alternative/reading per line)
and refuses to write if reformatting would change the parsed data. It needs
a paper name: most JSON files predate the formatter, and reformatting them
all buries the diff. The generator rejects a key that is neither a field of
`Datum` nor one of the four record-only keys.

Reads `Linglib/Data/Examples/<AuthorYear>.json` and writes a standalone
auto-generated module at `Linglib/Data/Examples/<AuthorYear>.lean`
declaring `namespace <AuthorYear>.Examples` (so consumer call sites read
`Examples.all`, `Examples.ex29a`, ... inside `namespace <AuthorYear>`).
Consumers (the paper's study file, and any module pooling several papers'
examples) import `Linglib.Data.Examples.<AuthorYear>`. The generated module is never
edited by hand; the JSON is the source of truth.

## Schema

See `Linglib/Data/Examples/Schema.lean` for the canonical type, and
`Linglib/Data/Examples/Readers.lean` for the lookups and fits a study makes on rows; a study
that reads rows imports it beside its data module. Quick key reference:

| Key | Type | Notes |
|---|---|---|
| `id` | string | `<authoryear>_<local>`, e.g. `"charlow2014_donkey1"`; only `[A-Za-z0-9_-]` (a CLDF identifier: write `(3.1)` as `3_1`, a prime as `_prime`) |
| `source` | `{bibkey, paperLabel}` | **originating** paper (e.g. `geach-1962` for the donkey) |
| `reportedIn` | `{bibkey, paperLabel}` or `null` | citing paper whose file holds the row, when different from `source` |
| `language` | string (Glottocode) | e.g. `"stan1293"` for Standard English; must be in `languages.csv`; `""` only for a constructed string of no language (a formal-language pattern) |
| `primaryText` | string | surface form; for a discourse, its utterances joined by single spaces |
| `discourseSegments` | array of strings | empty `[]` for a single sentence; the utterances of a discourse, in order |
| `glossedTokens` | array of 2-string arrays | `[[surface, gloss], ...]`. Empty `[]` if no IGT (e.g., English-glossed-as-English) |
| `translation` | string | English translation; empty for an English example |
| `context` | string | scenario/discourse context where the judgment holds |
| `judgment` | one of `acceptable, marginal, questionable, unacceptable, ungrammatical, variable` | sentence-level felicity; `variable` is the mark `%`, speakers differing |
| `alternatives` | array of `{form, judgment}` | within-example contrast pairs (e.g., Schwarz's `vom` vs `von dem`) |
| `readings` | array of `{name, judgment}` | multiple LFs / scope readings (e.g., donkey strong vs weak) |
| `paperFeatures` | array of `[key, value]` | what the paper states about the example (its design cell, the class it assigns); a key repeats when the example bears the property twice |
| `comment` | string | analyst notes |
| `verified` | `"page-image"` or `"text-layer"`, optional | how the row was last checked against its source |

`discourseSegments`, `translation`, `comment` and `verified` are the source's record, not Lean
fields: no theorem reads them, and every field of the Lean row is paid for when a kernel `decide`
reduces it. The generator validates them and the CLDF export carries them.

Translations are English, so there is no metalanguage field. CLDF's
`LGR_Conformance` is not recorded either: `glossedTokens` pairs are word
aligned by construction, and morpheme alignment is a property of the pairs.
Printed results (ratings, rates, statistics) go to `Data/Experiments/`, not
`paperFeatures`.

## Languages

`languages.csv` is the language table of the data: one Glottolog row (name, level, macroarea,
coordinates) for each Glottocode the examples use, from Glottolog 5.3, and for each language
only a study names, added by hand from the same release. The generator rejects a `language` not
listed there. A new language is added by writing its Glottocode in the JSON and running
`scripts/export_examples_cldf.py --sync-languages`, which keeps the rows already listed and fails
on a code Glottolog does not have.

`gen_examples.py --all` also writes `Languages.lean`, one `Glottocode` constant per row named by
its Glottolog name in lowerCamelCase (`Glottocode.english`, `Glottocode.mandarinChinese`). A
study names the languages of its sample by these constants, never by a code string, and reads a
row through them with `Datum.byLanguage [(.english, …), (.japanese, …)]`; a theorem over the rows
then states that every row is read, since a language missing from the table reads as `none`. Use the code of the variety the source names: a dialect Glottolog lists under its own
code, otherwise the language; a family code only for a claim about the family.

## CLDF export

`scripts/export_examples_cldf.py` writes the data as a CLDF dataset (Generic module, CLDF 1.3):
an `ExampleTable` with the judgment as CLDF's `Grammaticality_Judgement` mark (`?`, `??`, `#`,
`*`), the Leipzig conformance derived from the gloss pairs, and `bibkey[locator]` sources; a
`LanguageTable` from `languages.csv`; a `ContributionTable` of the data files; and the cited
entries of `references.bib`. An example with a mark links to a languoid `<glottocode>-judged`
with no Glottocode, as the CLDF examples component requires of ungrammatical examples, so that a
consumer ignoring the judgment does not attribute a marked string to the language. CI runs it with `--validate`, which fails
on any issue the CLDF validator reports, on any bib entry a BibTeX parser rejects, and on a row
value with no column to hold it.

## Verification

`verified` records that a row was checked against its source: `"page-image"` when every field
was compared with the page images (the form, the gloss as printed, the translation, the
judgment mark, the locator), `"text-layer"` when only the PDF's text was used. A checked row
whose gloss or translation is empty records that the source prints none. `--report` counts only
rows not verified against page images, so the queue it prints is the work left. The generated
Lean module does not carry the key; the CLDF export does, as `Verified`.

## One sentence per row

`primaryText` is one sentence, without judgment marks or variant notation. A line a source
prints with slashes, parentheses or stars (`kto-nibud'/kto-libo`, `some (*any)`) packs several
sentences: write each variant as its own row with its own `judgment` and `paperFeatures`,
sharing the `paperLabel`, when the variants differ in what the paper classifies; keep a
contrast the paper does not classify in `alternatives`. A feature a sentence bears twice (two
indefinite series in one clause) is two entries under the same key, not a slash-joined value.
The mark `%` says that speakers differ without saying how, and is the judgment `variable`; a row
records who accepts the example, a variety or a stage, as a paper feature where the source says.
A mark a source prints split between speakers (`*/??`, `?/√`) gives one sentence several marks.
The row's `judgment` is the first mark printed, and each further mark is a `paperFeatures` entry
`["alsoJudged", <judgment>]`, in printed order; the generator rejects a value that is not a
judgment.
A judgment that holds only in a scenario records the scenario in `context`.
A discourse is one row: `discourseSegments` lists its utterances, `primaryText`
joins them with single spaces, and the judgment is of the last utterance in
the context of the others.
Transcribe from page images, not a PDF's text layer: keep the source's morpheme hyphens and
diacritics, and where the source has an evident misprint give the normal form and record what
the source prints in `comment`.

## Leipzig glossing conventions

The `gloss` component of `glossedTokens` follows the **Leipzig Glossing Rules**:

> Comrie, B., Haspelmath, M., & Bickel, B. (2008). The Leipzig Glossing
> Rules: Conventions for interlinear morpheme-by-morpheme glosses.
> Department of Linguistics of the Max Planck Institute for Evolutionary
> Anthropology & the Department of Linguistics of the University of Leipzig.

Spec: <https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf>

Quick reference:
- `-` separates segmentable morphemes (affix boundaries), with exactly as
  many hyphens in the gloss as in the word (Rule 2)
- `.` separates two glosses corresponding to one form (fusion / portmanteau)
- `=` separates clitics from hosts
- SMALL CAPS for grammatical category labels (e.g., `INDEF`, `3SG`, `PST`,
  `NOM`, `REL`); plain lowercase for lexical glosses (`farmer`, `dog`)
- `1`/`2`/`3` for person; `SG`/`DU`/`PL` for number; gender
  (`M`/`F`/`N`) when relevant; case labels (`NOM`/`ACC`/`GEN`/...)
- Subscript indices for coreference (`Mary₁ ... her₁`) — not yet
  representable in the schema; `comment` field for now

## File-format style

Pretty-printed JSON, but **compact `glossedTokens`**: pack 3–4
`[surface, gloss]` pairs per line so the IGT alignment can be read at a
glance instead of scrolling through one-pair-per-line. Other arrays
(`discourseSegments`, `alternatives`, `readings`) get one element per line
for diff-friendliness — those entries are usually long strings or
structured objects.

```json
"glossedTokens": [
  ["Every", "every"], ["farmer", "farmer"], ["who", "REL.ANIM"],   ["owns", "own.PRS.3SG"],
  ["a",     "INDEF"], ["donkey", "donkey"], ["beats", "beat.PRS.3SG"], ["it",  "3SG.N"]
]
```

Whitespace in the JSON file does not affect generator output (the JSON is
parsed structurally).

## Provenance discipline

Hierarchical citation is the rule, not the exception. Most examples in
the literature are reported through later papers:

- Schwarz 2013 cites Ebert 1971a's Fering examples
- Charlow 2014 cites Geach 1962's donkey
- Hofmann 2025 cites Krahmer & Muskens 1995, Roberts 1989, Frank 1996

Convention: `source` is the **originating** paper (where the example was
first introduced or attested); `reportedIn` is the paper whose JSON file
this row sits in, when that paper is not the originator. For papers that
introduce their own examples, `reportedIn` is `null`.

## Bib entry requirement

Every `bibkey` (in both `source` and `reportedIn`) must resolve to an
entry in `references.bib` at the repository root. Per CLAUDE.md, fabrication is not
allowed — if a paper has no bib entry, add one (with verified DOI / title
/ journal / pages) before referencing the key.

## What this format does **not** yet support

The schema is consciously narrower than the literature it's eventually
aimed at. Known gaps:

- **Coreference indexing** (binder/bound subscripts) — Reinhart 1976,
  Fering Schwarz (8). Use `comment` field for now.
- **Tree-structured examples** where the bracketing IS the data
  (Bakay et al. 2026, syntactic minimal pairs).
- **Paradigm clusters** where N sentences only mean something together
  (Reinhart's (11a)–(11d)).
- **Typed columns**: `paperFeatures` values are strings that each study
  reads through its own table of labels (`parse?`), so a value the table
  omits is skipped silently rather than rejected when the module is
  generated.

Extensions land when a consuming study demands them.
