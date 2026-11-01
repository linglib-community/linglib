# `Linglib/Data/` — typed datasets and example data

Three sibling directories at this level:

| Subdir | Purpose | Source format | Generated Lean |
|---|---|---|---|
| `Examples/` | Per-paper typed examples (`Datum` schema) | JSON, one file per paper | `Examples/{AuthorYear}.lean` |
| `Statistics/` | Per-paper printed statistics (counts, rates, means, tests, fits), each table with the method that produced it | JSON, one file per paper | `Statistics/{AuthorYear}.lean` |
| `Wordlist/` | Per-paper word forms, CLDF Wordlist and Paralex (`LexemeTable`, `CellTable`, `FormTable`; custom relation, paradigm, root-class and analysis tables) | JSON, one file per paper | `Wordlist/{AuthorYear}.lean` |
| `StructureDataset/` | Per-paper CLDF language samples (`ContributionTable`, `LanguageTable`, `ParameterTable`, `CodeTable`, `ValueTable`) | JSON, one file per paper | `StructureDataset/{AuthorYear}.lean` |
| `PHOIBLE/` | Cross-linguistic phonological inventories | CSV (raw under `PHOIBLE/raw/`) | `Inventories/{Lang}.lean` |
| `WALS/` | World Atlas of Language Structures | CSV (raw under `WALS/raw/`) | `Features/F*.lean`, the features some module imports |

Generated `.lean` files are checked in alongside the raw data so `lake build`
works without running any generation scripts. Generators document the
exact transformation and can be re-run to update or extend coverage.

## Layout convention

```
Linglib/Data/
  README.md                  # this file
  {SOURCE}/                  # PHOIBLE / WALS / ...
    Schema.lean              # typed Lean schema (where applicable)
    raw/                     # upstream raw data dump
    {generated subdirs}/     # generator output
  Examples/
    Schema.lean              # the row type, `Datum`
    Readers.lean             # the lookups and fits studies make on rows
    README.md                # JSON format + Leipzig conventions
    {AuthorYear}.json        # per-paper example data
    {AuthorYear}.lean        # generated from the JSON
```

## Datasets

### Examples — typed `Datum` data

See [`Examples/README.md`](Examples/README.md). Per-paper JSON; the generator
writes a module per paper that studies import. JSON (not CSV) because the
schema has nested fields. `scripts/export_examples_cldf.py` exports the whole
set as a CLDF dataset, validated in CI, with its languages in
`Examples/languages.csv` (Glottolog 5.3).

### Wordlist — word forms, paradigms and their analyses

Per-paper word-level data in the shape of the Cross-Linguistic Data Formats
Wordlist and of the Paralex standard for lexicons of inflected forms, which
shares its column names: a `ParameterTable` (the concepts), a `LexemeTable`
(each word of a language by its concept and citation form), a `CellTable`
(cells as bundles of Universal Dependencies features, extended by
dataset-specific enumerations from a `Types` table where UD has no feature),
and a `FormTable` (a lexeme's form in a cell, its segments and printed morphs,
the source's judgment of it, and its source). A form a source rejects is a row
of its own, marked as CLDF marks examples, so disagreeing sources sit side by
side; the generated `all` holds the accepted forms and `marked` the others.
Linglib extension tables record what sources assert over forms: relations
(stem and past, base and derivative), paradigms (the forms a table prints for
a lexeme), and root classes (a source's judgment of which cells share a root,
since root identity, *better* and *best*, is not identity of strings). What a
paper's theory assigns to a form (an underlying representation, a root, a
class) is that paper's parse: it goes to an `AnalysisTable` with typed columns,
never to the form, and the generator resolves every reference to forms and
analyses, so no study joins rows by identifier. Comments, cognate lists and
the `ParameterTable` are validated but not emitted. The morphological
counterpart of `Examples/`, whose datum is a sentence and its gloss.

- **Schema**: `Linglib/Data/Wordlist/Schema.lean`
- **Generator**: `scripts/gen_wordlist.py` (`--check` verifies sync, `--fmt` canonical JSON)
- **Input/Output**: `Linglib/Data/Wordlist/{AuthorYear}.json` → `{AuthorYear}.lean`

### StructureDataset — CLDF language samples

Per-paper language samples in the shape of the CLDF StructureDataset: a
`ContributionTable` (each table of the paper, emitted as its own list of rows,
with languages, parameters and codes shared among them), a `LanguageTable`
(the sample, with Glottocodes where the source's name determines one, and a
comment saying why where it does not), a `ParameterTable` and `CodeTable`
(each parameter with its codes, including codes no language takes, or with the
codes of another parameter, as semantic types share their parts of speech),
and a `ValueTable` (a language's codes, marked questionable, optional or minor
as the source marks them). Each parameter with codes of its own becomes an
inductive type; the long `ValueTable` is emitted as one row per language with
a list-valued field per parameter, so a theorem reads each language once.

- **Schema**: `Linglib/Data/StructureDataset/Schema.lean`
- **Generator**: `scripts/gen_structure_dataset.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/StructureDataset/{AuthorYear}.json` → `{AuthorYear}.lean`

### Statistics

The statistics a paper prints, one table per printed table: for an experiment, the stimulus
inventory with its coding, the design constants, and the statistics (shares of ceiling ratings,
counts, means, tests) at the precision the paper prints them, as `Decimal`s that keep the printed
digits; likewise counts over a corpus or a lexicon, rates from a sociolinguistic survey, figures
from a typological sample, and the values a model fits. The directories of `Data/` are kinds of
datum (an example, a form, a coded value, a statistic), and how a statistic was obtained is a
field of its table: `meta.method` gives a paper's method and a table's `method` overrides it, one
of `experiment`, `corpus`, `lexicon`, `survey`, `typology` and `model`. A paper's coding labels (its factors, predictors, response types) are generated enums,
declared with the tables in `namespace <Paper>` beside the paper's study, which reads them and
extends them without opening anything; the study maps them into its theory types by total
functions and defines there what it concludes from the numbers (a prototype, a preference, a
significant difference). Each table records its
locator and whether it was checked against the page images, and a row may carry a note on how
it departs from the print.

The released data behind a paper, where there is any, is linked from its JSON (`meta.rawData`)
and the generated module's docstring, but not committed: the tables stay at the granularity the
paper argues at. A table the authors' data reproduces is marked `raw-data`, and
`scripts/check_statistics.py <Paper>` downloads the data and recomputes it through
`scripts/statistics/<Paper>.py`.

- **Schema**: `Linglib/Data/Statistics/Schema.lean`
- **Generator**: `scripts/gen_statistics.py` (`--check` verifies sync; the column vocabulary is
  in its docstring)
- **Raw-data check**: `scripts/check_statistics.py` (needs network access; run by hand)
- **Input/Output**: `Linglib/Data/Statistics/{Paper}.json` → `{Paper}.lean`

### UD dependency length by language

Per-paper corpus statistics over Universal Dependencies treebanks: the
proportion of head-final dependencies and the mean dependency length per word
at fixed sentence lengths, as a paper prints them (values as scaled integers).

- **Schema**: `Linglib/Data/UD/DependencyLength/Schema.lean`
- **Generator**: `scripts/gen_ud_deplength.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/UD/DependencyLength/{Paper}.json` → `{Paper}.lean`

### Verb class catalogues

A book's catalogue of verb classes, one entry per class in the book's order: the section number
and title it prints, the page on which the class begins, the members by citation form and those
the book marks as doubtful, and the property table, each line naming an alternation by its section
number in the book's catalogue of alternations or a further property, with the book's diacritic,
scope and any further qualifier. The vocabulary is Levin's (1993); a catalogue with another
vocabulary needs its own schema. `LevinClass.entry` reads a class's entry by constructor index,
checked against the section numbers.

- **Schema**: `Linglib/Data/VerbClasses/Schema.lean`
- **Generator**: `scripts/gen_verb_classes.py` (`--check` verifies sync; alternation numbers are
  validated against `DiathesisAlternation.number`)
- **Input/Output**: `Linglib/Data/VerbClasses/{Book}.json` → `{Book}.lean`

### Hiatus resolution samples

A paper's report of which vowel elides where two vowels meet: for each language it reports on,
the kind of juncture (two lexical words, a lexical word before a function word, a prefix before
a root, a root before a suffix, two suffixes, two enclitics) and the vowel that elides there,
with the reports the paper marks as uncertain flagged.

- **Schema**: `Linglib/Data/Hiatus/Schema.lean`
- **Generator**: `scripts/gen_hiatus.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/Hiatus/{Paper}.json` → `{Paper}.lean`

### Word order samples

A paper's classification of its language sample: dominant clause order, adposition
type, noun–dependent orders, and the further per-language properties the paper records,
plus its table of order types with the languages attesting each (Greenberg 1963,
Appendices I and II, with the properties of the text and footnotes).

- **Schema**: `Linglib/Data/WordOrder/Schema.lean`
- **Generator**: `scripts/gen_word_order.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/WordOrder/{Paper}.json` → `{Paper}.lean`

### Corpus word-order data

The word-order data a paper draws from corpora: per-language counts of the two relative
orders of subject and object, per-language printed statistics of that order (its entropy and
the mutual information between case marking and syntactic role), and individually annotated
clauses recording the order of object and verb with text type, object length, and animacy.

- **Schema**: `Linglib/Data/WordOrder/Corpus/Schema.lean`
- **Generator**: `scripts/gen_word_order_corpus.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/WordOrder/Corpus/{Paper}.json` → `{Paper}.lean`

### PHOIBLE 2.0

- **Source**: [PHOIBLE Online](https://phoible.org/) (Moran & McCloy 2019)
- **Format**: Single CSV (~23 MB, 105K rows)
- **License**: CC BY-SA 3.0
- **Citation**: Moran, Steven & McCloy, Daniel (eds.) 2019. *PHOIBLE 2.0*. Jena: Max Planck Institute for the Science of Human History. <http://phoible.org>. DOI: 10.5281/zenodo.2626687
- **Download**: <https://github.com/phoible/dev/blob/master/data/phoible.csv> (`PHOIBLE/raw/phoible.csv`)
- **Generator**: `scripts/gen_phoible.py`
- **Output**: `Linglib/Data/PHOIBLE/Inventories/{Lang}.lean`, and `Linglib/Data/PHOIBLE/Chart.lean`, the feature matrix of each glyph. A glyph has the same feature values in every PHOIBLE inventory, so the chart is language-independent; it leaves out tones and the glyphs with contour values such as `-,+`.
- **Coverage**: 23 languages (Akan, Arabic, Czech, English, Finnish, French, Georgian, German, Hindi-Urdu, Hungarian, Indonesian, Japanese, Korean, Mandarin, Maori, Persian, Russian, Spanish, Swahili, Tagalog, Turkish, Yoruba, Zulu); the first inventory per ISO unless `ISO=ID` names another. A phoneme's feature matrix is its chart entry, written inline only for tones and contour-valued glyphs, where a contour such as `-,+` leaves the feature unspecified. PHOIBLE's `NA` is `none`; the sources differ in whether they record allophones, tones and marginal phonemes (15 of the 23 inventories are from SPA, which does not mark marginal phonemes, and Yoruba's is from UPSID, which records no tones).

#### Regenerating

```bash
python3 scripts/gen_phoible.py            # every inventory already generated
python3 scripts/gen_phoible.py jpn ces    # specific ISOs
python3 scripts/gen_phoible.py kor=2197   # a chosen inventory, by InventoryID
python3 scripts/gen_phoible.py --chart    # the glyph chart
python3 scripts/gen_phoible.py --check    # chart and inventories in sync (CI)
```

### WALS v2020.4

- **Source**: [World Atlas of Language Structures](https://wals.info/) (Dryer & Haspelmath, eds.)
- **Format**: CLDF (Cross-Linguistic Data Formats) CSV
- **License**: CC BY 4.0
- **Citation**: Dryer, Matthew S. & Haspelmath, Martin (eds.) 2013. *WALS Online*, CLDF release v2020.4. <https://doi.org/10.5281/zenodo.13950591>
- **Download**: <https://doi.org/10.5281/zenodo.13950591> (wals-v2020.4.zip → `WALS/raw/`)
- **Generator**: `scripts/gen_wals.py`
- **Output**: `Linglib/Data/WALS/Features/F{ID}.lean`, generated only for the features some
  module imports (the import graph is the manifest); `Languages.lean` likewise only when
  imported.

A WALS chapter is one author's classification with its coded sample, so a feature enters the
library when a study formalizes the chapter's classification or a later paper engages its
coding. Each module holds the chapter's value enum and `allData : List (String × V)`, keyed by
WALS code and sorted by it, each row commented with the lect's name; lookup is core
`List.lookup`. The WALS code is the only key: several lects share an ISO 639-3 code or a
Glottocode, often with different values. A feature listed in the generator's `WITH_SOURCES` also
carries `sources`, the WALS references each row was coded from.

#### Regenerating

```bash
python3 scripts/gen_wals.py            # every imported feature
python3 scripts/gen_wals.py 81A        # a feature a study is about to import
python3 scripts/gen_wals.py --prune    # also delete features nothing imports
python3 scripts/gen_wals.py --check    # verify sync (CI)
```
