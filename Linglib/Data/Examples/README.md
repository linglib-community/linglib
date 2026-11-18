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
| `method` | one of `elicitation, corpus, experiment, description, unclassified`, optional | how the example and its judgment were obtained, where it differs from the paper's method in `contributions.csv` (see Methods) |
| `language` | string (Glottocode) | e.g. `"stan1293"` for Standard English; must be in `languages.csv`; `""` only for a constructed string of no language (a formal-language pattern) |
| `primaryText` | string | surface form; for a discourse, its utterances joined by single spaces |
| `discourseSegments` | array of strings | empty `[]` for a single sentence; the utterances of a discourse, in order |
| `glossedTokens` | array of 2-string arrays | `[[surface, gloss], ...]`. Empty `[]` if the source prints no word line (e.g., English-glossed-as-English). Where it prints segmented words without glosses, as a reference grammar may, each word has the gloss `""`: CLDF's `Analyzed_Word` without `Gloss`. The generator then segments each word at its own boundaries, as `pyigt` segments a word alone, and the row has no `LGR_Conformance` |
| `glossedWords`, `lgrConformance` | derived, not written | the generator pairs each word of `glossedTokens` with its morphemes and their glosses, and records the example's CLDF `LGR_Conformance` (`scripts/lgr.py`, shared with the CLDF export) |
| `translation` | string | English translation; empty for an English example |
| `context` | string | scenario/discourse context where the judgment holds |
| `judgment` | one of `acceptable, marginal, questionable, unacceptable, ungrammatical, variable` | sentence-level felicity; `variable` is the mark `%`, speakers differing |
| `contrasts` | array of `{form, judgment}` | within-example contrast pairs (e.g., Schwarz's `vom` vs `von dem`) |
| `readings` | array of `{name, judgment}` | multiple LFs / scope readings (e.g., donkey strong vs weak) |
| `spans` | array of `{start, length, label, lexeme}`, optional | runs of `glossedTokens` the row marks, each naming the lexeme it is a form of where it is one (see Spans) |
| `paperFeatures` | array of `[key, value]` | what the paper states about the example (its design cell, the class it assigns); a key repeats when the example bears the property twice |
| `comment` | string | analyst notes |
| `verified` | `"page-image"` or `"text-layer"`, optional | how the row was last checked against its source |

`discourseSegments`, `translation`, `comment` and `verified` are the source's record, not Lean
fields: no theorem reads them, and every field of the Lean row is paid for when a kernel `decide`
reduces it. The generator validates them and the CLDF export carries them.

Translations are English, so there is no metalanguage field. CLDF's
`LGR_Conformance` is not recorded either: `glossedTokens` pairs are word
aligned by construction, and morpheme alignment is a property of the pairs.
Printed results (ratings, rates, statistics) go to `Data/Statistics/`, not
`paperFeatures`.

## Typed features

A column whose values form a closed set is declared, not left as strings. The data file is then
an object `{"features": [...], "examples": [...]}`, and each feature names a `paperFeatures` key,
the Lean `type` of its values, the `lean` name of its reader and its `levels`:

```json
{"key": "antecedent", "lean": "antecedent", "type": "Antecedent",
 "doc": "The subject antecedents the paper compares.",
 "levels": [{"name": "atomic", "label": "atomic", "doc": "a singular noun phrase ..."}, ...]}
```

The generator emits the type as an enum in `<AuthorYear>.Examples` with its reader
(`Examples.antecedent : Datum → Option Examples.Antecedent`, or a `List` for a feature declared
`"multiple": true`), and rejects a row whose value is not a declared level, a key that repeats
without `multiple`, and a declared key no row records. A study defines its analysis as functions
on the enum and writes no table of labels, so a value that drifts fails when the module is
generated instead of leaving a theorem vacuous. `Rakosi2020.json` and `Angelopoulos2026.json` are
examples.

Declare a column when the paper's own taxonomy is finite: its constructions, conditions,
diagnostics, classes. Leave as a string a column that names a lexical entry by its form (a verb,
a particle), which a study matches against a fragment's inventory, and a number, which
`Datum.nat?` reads. A column that restates what the gloss line shows (the person and number of a
verb, the case of a noun) is not recorded at all: read it off the gloss
(`GlossedWord.features`).

### Typed readings

The readings a paper tests are declared the same way when they form a closed set, under a
top-level `readings` key beside `features`:

```json
"readings": {"lean": "reading", "type": "Reading", "doc": "The readings the paper tests.",
             "levels": [{"name": "boundVariable", "label": "bound variable", "doc": "..."}, ...]}
```

The generator emits the enum, its `label` and a reader
`Examples.reading : Datum → Examples.Reading → Option Judgment`, and rejects a row that judges a
reading not declared, a row that judges one twice, and a level no row judges. A study then writes
`Examples.reading e .boundVariable` where it wrote `e.readings.lookup "bound variable"`, and maps
its own reading type into the enum by a total function (`AghaJeretic2026.forceReading`). A paper
whose readings are open-ended, paraphrases or scope orders over arbitrary operators, leaves them
as strings.

### Spans

A row links its words to the lexical entries of a language by naming them, not by their spelling.
A span marks a run of the row's `glossedTokens` by the position `start` of its first word, counted
from zero, and its `length` (1 if omitted), under a `label`, and gives the `lexeme` the run is a
form of where it is one. A span of length zero is an element the source's analysis posits without
a word, such as a null article, placed before the word at `start`. The file declares the labels
and the lexemes beside `features`:

```json
"spans": {"labels":  {"type": "SpanLabel", "doc": "...",
                      "levels": [{"name": "definite", "label": "definite", "doc": "..."}, ...]},
          "lexemes": {"type": "Lexeme", "doc": "...",
                      "levels": [{"name": "na", "label": "na", "doc": "Mandarin na 'that'"}, ...]}}
```

and a row writes `"spans": [{"start": 3, "length": 3, "label": "definite"}, {"start": 3, "label":
"determiner", "lexeme": "na"}]`. The generator rejects a span outside the gloss line, a label or
lexeme not declared and a level no span names, and emits the two enums with the readers
`Examples.label?` and `Examples.lexeme?` on `Datum.Span`. `Datum.Span.words` and `Datum.spansIn`
in `Readers.lean` give the glossed words a span covers and the spans within a span. A span may
carry no lexeme: it then marks the word under test, as a source marks it in italics or bold, and
replaces a column that repeats the word (`Karlsson2017.json`, whose rows have words and no
glosses).

The data layer does not see the fragments, so a lexeme is the file's own identifier and the study
gives its entry by a total function, `Examples.Lexeme.entry : Examples.Lexeme → Entry`. A lexeme
without a case, or an entry the fragment no longer has, then fails to compile. The study states
three checks beside its prediction, so that a wrong or forgotten span fails a theorem and does not
pass as an unmarked word:

* each lexeme a row names is an entry of the fragment of the row's language;
* each span that names a lexeme is printed as the entry is written, under the transcription of
  the source, which the fragment gives (`Mandarin.toneless`), or as a form the entry realizes;
* within a marked phrase, no word written as an entry of the inventory goes unmarked.

Spelling confirms a named entry and does not find one: transcriptions differ between sources and
lose distinctions, as pinyin without tone marks writes several words alike. `Jenks2018.json`
with `Studies/Jenks2018.lean`, and `Rakosi2020.json` with `Studies/Rakosi2020.lean`, where the
check compares the phonemes the words write, are the examples. Most data files instead name the
item under test in a column by its form; such a column becomes a span when its study is next
audited.

### Boundaries

The generator segments a word at the separators of the Leipzig rules, `-` before an affix, `=`
before a clitic and `~` before a reduplicant. A source with its own notation declares its
symbols, since a row records the words as the source prints them. Karlsson's grammar writes `-`
between a stem and an inflectional ending or a clitic, `=` between the words of a compound and
`>` before a derivational suffix, and puts `+` before a word in the weak grade:

```json
"boundaries": {"type": "Boundary", "doc": "...",
               "levels": [{"name": "inflection", "symbol": "-", "leipzig": "-", "doc": "..."},
                          {"name": "compound", "symbol": "=", "leipzig": "-", "doc": "..."},
                          {"name": "derivation", "symbol": ">", "leipzig": "-", "doc": "..."}],
               "marks": [{"symbol": "+", "doc": "the weak grade of consonant gradation"}]}
```

The words are then segmented at the declared symbols and no others, and a mark is dropped from
the morphemes while the word keeps it. The module emits the enum and the reader
`Examples.boundary? : GlossedMorpheme → Option Examples.Boundary`, so a study asks for a kind of
boundary, as `Karlsson2017` takes the morphs before the first inflectional one as the stem.
`leipzig` gives the separator each symbol is written as in the CLDF export and in the
conformance level, where the Leipzig rules have no symbol of their own for it. A distinction
the source does not draw is not recovered: Karlsson's clitics are exported under `-`.

### Index

A study that selects, excludes or lists some of a file's rows names them. A file that declares
`"index": {"type": "Example", "doc": "..."}` gets the finite type of its examples, one constructor
per row under the row's own name, a `Fintype`, with `Examples.Example.datum`, the row of each, and
`Examples.Example.all`, the list of them in the file's order. A study then quantifies over the
type, `∀ x : Examples.Example, x ∉ modelled → … x.datum …`, and lists rows as
`[.ex_30b, .ex_51b]`.

Comparing two names costs the kernel nothing. Comparing two rows compares every string of both,
and the kernel frees nothing within one declaration: on a file of 75 rows a statement testing
`row ∈ rows` took 6 GiB, and `AlonsoOvalleRoyer2024`, whose theorems excluded and listed rows
that way, went from 3.8 GiB and 24 s to 1.05 GiB and 4.5 s on the index. Do not decide the
equality or membership of rows.

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

## Methods

A row records how the example and its judgment were obtained, as `Datum.method`, where the
source names one of four ways: elicitation from native-speaker consultants, a corpus (a text, a
corpus or the web), an experiment that measured the judgment, or citation from a grammar or
dictionary that does not say (`description`). It is evidence of different kinds: an attested
example is no evidence that other forms are impossible, and an experiment measures what a
consultant reports. `contributions.csv` gives each data file's method, or `unclassified` where
none of the four is recorded, and a row's `method` key overrides it, `unclassified` included; the
generator rejects a data file with no row there. A paper is classified when it is audited, from
its own statement of where its data come from.

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
contrast the paper does not classify in `contrasts`. A feature a sentence bears twice (two
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

### Alignment

The generator emits each row's gloss line as `Datum.glossedWords`, modelled on `pyigt`'s
`GlossedWord` and `GlossedMorpheme`: a word with its gloss and, when the two are segmented alike
by the same separators (`-`, `=`, and `~` for reduplication), the pairs of a morpheme and its
gloss. A study reads morphemes and category labels from it without splitting a string in the
kernel. The generator also records the example's `LGR_Conformance` as the CLDF export derives
it: `MORPHEME_ALIGNED` when every word is segmented as its gloss is and some word is segmented,
otherwise `WORD_ALIGNED`.

A word the source prints with a different segmentation than its gloss (`képet` glossed
`picture-ACC`) is transcribed as printed. It has no morphemes (`GlossedWord.IsValid` fails) but
keeps its category labels and lexical gloss (`GlossedWord.labels`, `GlossedWord.features`).

Two departures from `pyigt`: a morpheme's form drops only the punctuation of `scripts/lgr.py`,
so that an apostrophe stays inside a word, and a word that is not valid has no morpheme pairs
where `pyigt` keeps those before the mismatch.

## File-format style

Pretty-printed JSON, but **compact `glossedTokens`**: pack 3–4
`[surface, gloss]` pairs per line so the IGT alignment can be read at a
glance instead of scrolling through one-pair-per-line. Other arrays
(`discourseSegments`, `contrasts`, `readings`) get one element per line
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
- **Declared abbreviations.** A gloss element counts as a category label when it has no
  lower-case letter, which misses sources that write `2.sg` or `caus`. The Leipzig rules let a
  work list its own abbreviations; a data file would declare them and the generator would check
  its labels against the standard list and the declared ones.
- **Readings into a collection.** `Datum.Fits` and `Datum.Checks` take a reader into `Option`.
  A column that names a lexical entry is matched against a `Finset` inventory, so such a
  theorem is written with a bounded quantifier over the inventory and carries no coverage
  count; a fit over `Option`, `List` and `Finset` readers alike would cover it.
- **Typed features in the CLDF export.** A declared feature is a CLDF parameter with its codes,
  but the export writes every feature into the custom JSON column `Paper_Features`. Whether the
  declared ones fit CLDF's `ParameterTable` and `CodeTable` for values attached to an example
  is to be checked against the specification before anything is written.
- **Adoption of typed features.** Most data files predate them and their studies read closed
  columns through `parse?` tables; a column is declared when its study is next audited.

Extensions land when a consuming study demands them.
