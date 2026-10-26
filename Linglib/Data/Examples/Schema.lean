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

This file defines the data a study reads off a paper's examples, and the lookups it makes on
them. An example is what the paper prints under a number; a `Datum` is one piece of data the paper
reports with it in the sense of Tonhauser and Matthewson: an expression (the example, or one
alternant of it), the context it is judged in, and the judgment, less the information about the
speakers that papers seldom give. A datum is a row of the Examples component of the
Cross-Linguistic Data Formats of Forkel et al., in version 1.3, and the
sentence-level counterpart of `Data/Wordlist/`.

## Main definitions

* `Datum`: a piece of data about an example, with the judgment layer (`judgment`,
  `alternatives`, `readings`) and the paper's own columns (`paperFeatures`).
* `SourceRef`: a reference to a paper, a bibkey with a locator.
* `Datum.feature?`, `Datum.features`: the first value and every value of a key of
  `paperFeatures`.
* `Datum.parse?`: the first value of a key read through a table.
* `Datum.digits?`, `Datum.nat?`, `Datum.int?`: numerals.
* `Datum.bool?`: a truth value written `true` or `false`.
* `Datum.judgments`, `Datum.JudgedFelicitous`: every printed mark, and felicity as the mark and
  the prose give it.
* `Datum.Fits`, `Datum.ReadCount`: a prediction's fit with the judgment band of what a reader
  reads off a row, and the count of rows a reader reads, the coverage witness beside a fit.
* `Datum.FitsVerdict`: a prediction's fit with the truth-value judgment of a row whose task is
  truth in the context.
* `Datum.Checks`, `Datum.ChecksVerdict`: the statement a study makes, a fit over the rows
  bundled with its coverage count, so a fit cannot go silently vacuous.

## Main statements

* `mem_features`, `features_eq_nil`, `head?_features`, `feature?_eq_none`: the lookups in terms of
  membership in `paperFeatures`, in the shape of `List.mem_lookupAll`, `List.lookupAll_eq_nil`,
  `List.head?_lookupAll` and `List.dlookup_eq_none`.

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
  belong in `Data/Experiments/`, and an analysis the formaliser derives belongs in the study. A key
  repeats when the expression bears the property twice (two indefinite series in one clause), so
  the list is not a map: `feature?` reads the first value, `features` every value.
* A feature is either a stimulus column, naming in the paper's own taxonomy the items,
  construction or condition the example instantiates, or a claim column, recording what the paper
  says the judgment shows. Only stimulus columns may feed a prediction (`Datum.Fits`): predicting
  a judgment from the paper's claim about that judgment checks nothing. A claim column is read as
  a target, checking that the formal account derives what the paper asserts, or stands as
  documentation; prose commentary belongs in `comment`. A stimulus value is a key into a finite
  taxonomy, so a `parse?` table can read it. A truth-value judgment in a context is the `verdict`
  field, never a feature: the response of a truth task is a field of the datum, like the mark of
  an acceptability task, which on such a row records only well-formedness.
* A datum answers a question put about the expression, and each question has its own response
  channel. Is it acceptable? — the mark in `judgment`, fitted through `Judgment.band`. Is it true
  in this context? — `verdict`, fitted through `FitsVerdict`. Can it mean this? — that reading's
  entry in `readings`. Is this variant acceptable in the same frame? — its entry in
  `alternatives`. Is it felicitous, though well formed? — the `felicity` feature that
  `JudgedFelicitous` reads. A study fits its prediction against the channel whose question the
  paper asked. Implication judgments, whether an utterance conveys an inference, and relational
  judgments, whether two sentences are equivalent or contradictory, have no channel yet and sit
  in claim columns.
* Studies decide propositions over rows, so every lookup reduces in the kernel. `digits?` reads a
  numeral by a fold over its characters because `String.toNat?` is well-founded recursive and
  does not.
* The file imports no tactic library: every module with example data imports it, and names such
  a library brings into scope (mathlib's root `Tree`) would reach every study that reads rows.

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

namespace Datum

/-- `digits? cs` is the number that the nonempty string of decimal digits `cs` denotes. -/
def digits? (cs : List Char) : Option ℕ :=
  if cs ≠ [] ∧ cs.all Char.isDigit then
    some (cs.foldl (fun n c ↦ 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

variable (e : Datum) (key : String)

/-- `e.surfaceTokens` is the `Analyzed_Word` column, the words of `e.glossedTokens`. -/
def surfaceTokens : List String := e.glossedTokens.map Prod.fst

/-- `e.glossLine` is the `Gloss` column, the glosses of `e.glossedTokens`. -/
def glossLine : List String := e.glossedTokens.map Prod.snd

/-- `e.feature? key` is the first value of `key` in `e.paperFeatures`, if there is one. -/
def feature? : Option String := e.paperFeatures.lookup key

/-- `e.features key` is the list of values of `key` in `e.paperFeatures`, in order. -/
def features : List String :=
  e.paperFeatures.filterMap fun kv ↦ if kv.1 = key then some kv.2 else none

/-- `e.parse? key table` is the entry of `table` under the first value of `key` in `e`, if `e`
has the key and `table` lists its value. -/
def parse? {α : Type*} (table : List (String × α)) : Option α :=
  (e.feature? key).bind (List.lookup · table)

/-- `e.nat? key` is the first value of `key` in `e` read as a decimal numeral. -/
def nat? : Option ℕ := (e.feature? key).bind fun s ↦ digits? s.toList

/-- `e.int? key` is the first value of `key` in `e` read as a decimal integer, an optional `-`
followed by digits. -/
def int? : Option ℤ :=
  (e.feature? key).bind fun s ↦
    match s.toList with
    | '-' :: cs => (digits? cs).map fun n ↦ -(n : ℤ)
    | cs => (digits? cs).map fun n ↦ (n : ℤ)

/-- `e.decimal? key` is the first value of `key` in `e` read as an unsigned decimal numeral,
digits with an optional fractional part after a point. -/
def decimal? : Option Rat :=
  (e.feature? key).bind fun s ↦
    match s.toList.span (· ≠ '.') with
    | (i, []) => (digits? i).map fun n ↦ (n : Rat)
    | (i, _ :: f) => do pure ((← digits? i) + (← digits? f) / 10 ^ f.length)

/-- `e.bool? key` is the first value of `key` in `e` read as `true` or `false`. -/
def bool? : Option Bool := e.parse? key [("true", true), ("false", false)]

/-- `e.judgments` is every mark the paper prints on `e`: its judgment, then the further marks
of a split mark such as `??/*`, recorded as `alsoJudged`. -/
def judgments : List Judgment := e.judgment :: (e.features "alsoJudged").filterMap Judgment.ofName?

/-- The paper judges `e` felicitous: it prints no mark on `e`, and its prose does not call `e`
infelicitous, which the row records as `felicity: infelicitous`. -/
def JudgedFelicitous : Prop :=
  e.judgment = .acceptable ∧ e.feature? "felicity" ≠ some "infelicitous"

instance : Decidable e.JudgedFelicitous := inferInstanceAs (Decidable (_ ∧ _))

/-- The prediction `P` over what the reader `f` reads off `e` fits the row: the band of `e`'s
judgment is the predicted band. A row the reader does not read is unconstrained, so a `Fits`
theorem is paired with a `Datum.ReadCount` for its reader. -/
def Fits {α : Type*} (f : Datum → Option α) (P : α → Judgment.Band) : Prop :=
  ∀ a ∈ f e, e.judgment.band = P a

instance {α : Type*} (f : Datum → Option α) (P : α → Judgment.Band) :
    Decidable (e.Fits f P) :=
  inferInstanceAs (Decidable (∀ a ∈ f e, _ = _))

/-- The prediction `P` over what the reader `f` reads off `e` fits the row's truth-value
judgment: where the source reports a verdict, it is the predicted one. The `judgment` of such a
row records only that the expression is well formed, so a truth-value row is read by
`FitsVerdict`, not `Fits`. -/
def FitsVerdict {α : Type*} (f : Datum → Option α) (P : α → Bool) : Prop :=
  ∀ a ∈ f e, ∀ b ∈ e.verdict, b = P a

instance {α : Type*} (f : Datum → Option α) (P : α → Bool) :
    Decidable (e.FitsVerdict f P) :=
  inferInstanceAs (Decidable (∀ a ∈ f e, ∀ b ∈ e.verdict, _ = _))

/-- The reader `f` reads exactly `n` of `rows`: the coverage witness beside a `Fits` or other
row-quantified theorem, without which the theorem goes silently vacuous when a feature key or a
table value drifts. -/
def ReadCount {α : Type*} (f : Datum → Option α) (rows : List Datum) (n : ℕ) : Prop :=
  (rows.filterMap f).length = n

instance {α : Type*} (f : Datum → Option α) (rows : List Datum) (n : ℕ) :
    Decidable (ReadCount f rows n) :=
  inferInstanceAs (Decidable (_ = _))

/-- The prediction `P` fits every row of `rows` the reader `f` reads, and `f` reads exactly `n`
of them: the one statement a study makes about a cluster of rows. -/
def Checks {α : Type*} (f : Datum → Option α) (P : α → Judgment.Band) (rows : List Datum)
    (n : ℕ) : Prop :=
  (∀ e ∈ rows, e.Fits f P) ∧ ReadCount f rows n

instance {α : Type*} (f : Datum → Option α) (P : α → Judgment.Band) (rows : List Datum)
    (n : ℕ) : Decidable (Checks f P rows n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The truth-value counterpart of `Datum.Checks`: the prediction matches every reported verdict
on a row the reader reads, and exactly `n` rows have both. -/
def ChecksVerdict {α : Type*} (f : Datum → Option α) (P : α → Bool) (rows : List Datum)
    (n : ℕ) : Prop :=
  (∀ e ∈ rows, e.FitsVerdict f P) ∧
    (rows.filter fun e ↦ (f e).isSome ∧ e.verdict.isSome).length = n

instance {α : Type*} (f : Datum → Option α) (P : α → Bool) (rows : List Datum) (n : ℕ) :
    Decidable (ChecksVerdict f P rows n) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {e key} {v : String}

@[simp]
theorem mem_features : v ∈ e.features key ↔ (key, v) ∈ e.paperFeatures := by
  simp [features, and_comm, eq_comm]

theorem features_eq_nil : e.features key = [] ↔ ∀ v, (key, v) ∉ e.paperFeatures := by
  simp [List.eq_nil_iff_forall_not_mem]

@[simp]
theorem head?_features : (e.features key).head? = e.feature? key := by
  simp only [features, feature?, List.head?_filterMap, List.lookup_eq_findSome?, beq_iff_eq]
  congr 1; funext kv; simp only [eq_comm]

theorem feature?_eq_none : e.feature? key = none ↔ ∀ v, (key, v) ∉ e.paperFeatures := by
  rw [← head?_features, List.head?_eq_none_iff, features_eq_nil]

end Datum
