/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar
public import Linglib.Data.Examples.Judgment

/-!
# Data from examples

This file defines the data a study reads off a paper's examples; the lookups a study makes on
them are in `Data/Examples/Readers.lean`. An example is what the paper prints under a number; a `Datum` is one piece of data the paper
reports with it in the sense of Tonhauser and Matthewson: an expression (the example, or one
alternant of it), the context it is judged in, and the judgment, less the information about the
speakers that papers seldom give. A datum is a row of the Examples component of the
Cross-Linguistic Data Formats of Forkel et al., in version 1.3, and the
sentence-level counterpart of `Data/Wordlist/`.

## Main definitions

* `Datum`: a piece of data about an example, with the judgment layer (`judgment`,
  `alternatives`, `readings`) and the paper's own columns (`paperFeatures`).
* `SourceRef`: a reference to a paper, a bibkey with a locator.

## Implementation notes

* Per-paper data lives in `Linglib/Data/Examples/{AuthorYear}.json` and is compiled by
  `scripts/gen_examples.py` into `Linglib/Data/Examples/{AuthorYear}.lean`, declaring
  `namespace {AuthorYear}.Examples`. The JSON keys are the field names, and `id` uses only the
  characters of a CLDF identifier. `scripts/export_examples_cldf.py` writes the data as a CLDF
  dataset, which CI validates.
* Four JSON keys are the source's record and not fields, since no theorem reads them and every
  field is paid for when a kernel `decide` reduces a row: `translation` (`Translated_Text`, empty
  for an English example), `discourseSegments` (the utterances of a discourse), `comment`, and
  `verified` (how the row was last checked against its source). The generator validates them and
  the CLDF export carries them.
* `language` is a Glottocode, which the generator checks against `languages.csv`, the language
  table of the data drawn from Glottolog; it is empty for a constructed string that belongs to no
  language, such as a pattern of a formal language.
* `glossedTokens` pairs each analysed word with its gloss, so the word-by-word alignment of Rule 1
  of the Leipzig Glossing Rules holds by construction. CLDF's `LGR_Conformance` column is not
  stored: whether a gloss also aligns morpheme by morpheme (Rule 2) is a property of the pairs.
* Translations are into English, the default of CLDF's `Meta_Language_ID`, which is therefore not
  stored.
* A discourse is one datum: `primaryText` joins its utterances with single spaces, and the
  judgment is of the last utterance in the context of the others.
* `paperFeatures` are the paper's own columns: what the paper states about the datum, such as
  the cell of its design or the class it assigns. The results a paper prints for an experiment
  belong in `Data/Statistics/`, and an analysis the formaliser derives belongs in the study. A key
  repeats when the expression bears the property twice (two indefinite series in one clause), so
  the list is not a map: `feature?` reads the first value, `features` every value.
* The file imports no tactic library: every module with example data imports it, and names such
  a library brings into scope (mathlib's root `Tree`) would reach every study that reads rows.
* The lookups and fits on rows are in `Data/Examples/Readers.lean`, which only the studies that
  read rows import, so a new reader rebuilds those studies and not every module of example
  data.

## TODO

* 86 rows in 21 papers with `discourseSegments` do not have their concatenation as
  `primaryText` (the `discourse` column of `scripts/export_examples_cldf.py --report`).

## References

* [forkel-etal-2018]
* [forkel-etal-2024]
* [tonhauser-matthewson-2016]
* [comrie-haspelmath-bickel-2008]
-/

@[expose] public section

/-- A Glottolog language identifier, such as `"stan1293"` for Standard English. -/
abbrev Glottocode := String

/-- A `SourceRef` is a CLDF source reference `bibkey[locator]` with its two parts kept apart. -/
structure SourceRef where
  /-- The key of the paper's entry in `references.bib`. -/
  bibkey : String
  /-- The locator in the paper: its example number, table or page. -/
  paperLabel : String
  deriving DecidableEq, Repr

/-- How an example and its judgment were obtained. -/
inductive Datum.Method where
  /-- Constructed and judged by the author. -/
  | introspection
  /-- Elicited from, or judged by, native-speaker consultants. -/
  | elicitation
  /-- Attested in a text, a corpus or on the web. -/
  | corpus
  /-- A stimulus whose judgment an experiment measured. -/
  | experiment
  /-- Cited from a grammar or dictionary that does not say how it was obtained. -/
  | description
  deriving DecidableEq, Repr

/-- A `Datum` is a piece of data a paper reports with one of its examples
[tonhauser-matthewson-2016]: an expression of a language with its gloss, the context it is judged
in, the judgment, the forms and readings the paper judges with it, and the paper's own
classifications of it. It is the part of a row of a CLDF `ExampleTable` that theorems read. -/
structure Datum where
  /-- The `ID` column holds a stable identifier keyed to the paper, `{authoryear}_{label}`. -/
  id : String
  /-- The paper that introduced the example. -/
  source : SourceRef
  /-- The paper whose data file holds the row, when it only reports an example from `source`. -/
  reportedIn : Option SourceRef := none
  /-- How the example and its judgment were obtained; `none` where that is not yet classified. -/
  method : Option Datum.Method := none
  /-- The `Language_ID` column holds the Glottocode of the language of the expression; empty for
  a constructed string of no language. -/
  language : Glottocode
  /-- The `Primary_Text` column holds the expression without judgment marks. -/
  primaryText : String
  /-- The `Analyzed_Word` and `Gloss` columns paired, each word with its gloss; empty when the
  source gives no gloss. -/
  glossedTokens : List (String × String)
  /-- The scenario the source gives for the judgment; empty when it gives none. -/
  context : String
  /-- The judgment the source reports for the expression in the context. -/
  judgment : Judgment
  /-- The truth-value judgment the source reports, where the task is truth in the context rather
  than the acceptability that `judgment` records; `none` where the source reports none. -/
  verdict : Option Bool := none
  /-- The other forms the source judges in the same frame, each a whole sentence, with their
  judgments. -/
  alternatives : List (String × Judgment) := []
  /-- The readings the source distinguishes for the expression, each with its judgment. -/
  readings : List (String × Judgment) := []
  /-- The paper's own columns, as key-value pairs. -/
  paperFeatures : List (String × String) := []
  deriving DecidableEq, Repr
