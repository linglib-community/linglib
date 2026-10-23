module

public import Linglib.Fragments.Tigrinya.Complementizers
public import Linglib.Fragments.Tigrinya.Negation
public import Linglib.Data.Examples.Cacchioli2026

/-!
# Cacchioli (2026): The Syntax of Clausal Prefixes in Tigrinya

Tigrinya is head-final and yet marks its subordinate clauses with prefixes. This file formalizes
the two descriptive generalizations of a thesis arguing that the position is syntactic rather than
a morphological quirk: *zɨ-* is a reflex of successive-cyclic Ā-movement rather than a
complementizer head, *kɛmzɨ-* is *kɛm* plus that reflex, so its complement clauses are relative
clauses with a null nominal moved, *kɨ-* is a subjunctive marker heading a projection below tense,
and *ʔaj-…-(ɨ)n* is split negation whose prefix sits below tense and whose suffix heads a polarity
projection above it.

The first generalization is which verb classes take which clause-typer, the thesis's own summary
table. The second is the distribution of the negative suffix, which appears exactly in the clauses
whose structure reaches the polarity projection — root declaratives, *ʔɨlu*-complements and the
negative future — and is missing wherever the clause is reduced. Both are checked against the
thesis's own examples, and both are attested on each side, so neither check is vacuous.

## Main definitions

* `VerbClass`, `selects` — the verb classes and the clause-typers each admits
* `ClauseKind`, `HasPolP` — the clause types and which of them carry the polarity projection

## Main results

* `kemzi_or_ki`, `kemzi_of_ilu`, `kemzi_and_ki_iff` — the shape of the selection table: every class
  takes one of the two prefixes, *ʔɨlu* occurs only where *kɛmzɨ-* does, and the two prefixes
  overlap on the fiction and perception verbs alone
* `selects_covers_data`, `each_typer_attested` — the table admits every attested pairing, and each
  typer is attested
* `suffix_iff_polP`, `polP_clauses_attested` — the suffix of the Tigrinya fragment's circumfix,
  read off each example's negative word, appears exactly in the clauses carrying the polarity
  projection, and every such clause type is attested with it
* `variants_ungrammatical` — the starred variants are those that break the generalization

## References

* [cacchioli-2026]
* [cacchioli-2023]
-/

@[expose] public section
namespace Cacchioli2026

open Tigrinya.Complementizers

/-! ### Selection -/

/-- The verb classes of the thesis's selection table (ch. 6). -/
inductive VerbClass where
  | factive | cognitiveNonFactive | fiction | utterance | perception
  | directive | desire | modal | emotiveFactive | control | ecm
  deriving DecidableEq, Fintype, Repr

/-- The clause-typers a class's complement may take. -/
def selects : VerbClass → List Complementizer
  | .factive => [kemzi]
  | .cognitiveNonFactive | .utterance => [kemzi, ilu]
  | .fiction => [kemzi, ki, ilu]
  | .perception => [kemzi, ki]
  | .directive | .desire | .modal | .emotiveFactive | .control | .ecm => [ki]

theorem kemzi_or_ki (c : VerbClass) : kemzi ∈ selects c ∨ ki ∈ selects c := by
  cases c <;> decide

theorem kemzi_of_ilu {c : VerbClass} (h : ilu ∈ selects c) : kemzi ∈ selects c := by
  revert h; cases c <;> decide

theorem kemzi_and_ki_iff (c : VerbClass) :
    kemzi ∈ selects c ∧ ki ∈ selects c ↔ c = .fiction ∨ c = .perception := by
  cases c <;> decide

/-- The thesis's verb-class labels. -/
def parseVerbClass : String → Option VerbClass
  | "factive" => some .factive
  | "cognitive_non_factive" => some .cognitiveNonFactive
  | "fiction" => some .fiction
  | "utterance" => some .utterance
  | "perception" => some .perception
  | "directive" => some .directive
  | "desire" => some .desire
  | "modal" => some .modal
  | "emotive_factive" => some .emotiveFactive
  | "control" => some .control
  | "ecm" => some .ecm
  | _ => none

/-- The thesis's clause-typer labels. -/
def parseTyper : String → Option Complementizer
  | "kemzi" => some kemzi
  | "ki" => some ki
  | "ilu" => some ilu
  | _ => none

/-- A matrix verb of a given class attested with a given clause-typer. -/
structure SelectionDatum where
  verbClass : VerbClass
  typer : Complementizer
  deriving DecidableEq, Repr

/-- The selection pairing an example records, where it records one. -/
def selectionDatum (e : Datum) : Option SelectionDatum := do
  let c ← parseVerbClass (← e.paperFeatures.lookup "verb_class")
  let t ← parseTyper (← e.paperFeatures.lookup "typer")
  some ⟨c, t⟩

/-- The attested (verb class, typer) pairs of the thesis's examples. -/
def selectionData : List SelectionDatum := Examples.all.filterMap selectionDatum

theorem selects_covers_data : ∀ d ∈ selectionData, d.typer ∈ selects d.verbClass := by
  decide

theorem each_typer_attested :
    (∃ d ∈ selectionData, d.typer = kemzi) ∧ (∃ d ∈ selectionData, d.typer = ki) ∧
      (∃ d ∈ selectionData, d.typer = ilu) := by decide

/-! ### Sentential negation -/

/-- The clause types in which the thesis negates a verb (ch. 5). -/
inductive ClauseKind where
  | root | ilu | future | relative | seem | conditional | complement | subjunctive | purpose
  deriving DecidableEq, Repr

/-- Clauses carrying the PolP layer that hosts *-(ɨ)n*: root declaratives,
*ʔɨlu*-complements and the negative future. -/
def HasPolP : ClauseKind → Prop
  | .root | .ilu | .future => True
  | _ => False

instance : DecidablePred HasPolP
  | .root | .ilu | .future => isTrue trivial
  | .relative | .seem | .conditional | .complement | .subjunctive | .purpose => isFalse id

/-- The thesis's clause-type labels. -/
def parseClauseKind : String → Option ClauseKind
  | "root" => some .root
  | "ilu" => some .ilu
  | "future" => some .future
  | "relative" => some .relative
  | "seem" => some .seem
  | "conditional" => some .conditional
  | "complement" => some .complement
  | "subjunctive" => some .subjunctive
  | "purpose" => some .purpose
  | _ => none

/-- A negated clause, with its kind and its negative word as the forms of its morphs. -/
structure NegationDatum where
  clause : ClauseKind
  word : List String
  deriving DecidableEq, Repr

/-- The negative word ends in the fragment's suffix *-(ɨ)n*. -/
def NegationDatum.HasSuffix (d : NegationDatum) : Prop :=
  d.word.getLast? = some Tigrinya.Negation.n.form

instance : DecidablePred NegationDatum.HasSuffix := fun d ↦
  inferInstanceAs (Decidable (d.word.getLast? = some Tigrinya.Negation.n.form))

/-- The negative word among the words of a sentence is the one bearing the fragment's negative
prefix, *ʔaj-* or its allomorph *ɛj-*, given as the forms of its morphs. -/
def negativeWord (ws : List (List (List Char))) : Option (List String) :=
  (ws.find? fun w ↦
    Tigrinya.Negation.aj.form.toList ∈ w ∨ Tigrinya.Negation.ej.form.toList ∈ w).map
    (·.map String.ofList)

/-- The negated clause an example records, where it records one. -/
def negationDatum (e : Datum) : Option NegationDatum := do
  let c ← parseClauseKind (← e.paperFeatures.lookup "clause")
  let w ← negativeWord (e.surfaceTokens.flatMap Morphology.Morph.wordsOf)
  some ⟨c, w⟩

/-- The negated clauses of the thesis's examples. -/
def negationData : List NegationDatum := Examples.all.filterMap negationDatum

theorem suffix_iff_polP :
    (∀ e ∈ Examples.all, (e.paperFeatures.lookup "clause").isSome → (negationDatum e).isSome) ∧
      ∀ d ∈ negationData, d.HasSuffix ↔ HasPolP d.clause := by
  decide +kernel

/-- The negated variants the thesis judges beside its examples, in the same clause. -/
def variantData : List (NegationDatum × Judgment) :=
  Examples.all.flatMap fun e ↦ e.alternatives.filterMap fun (f, j) ↦ do
    let c ← parseClauseKind (← e.paperFeatures.lookup "clause")
    let w ← negativeWord (Morphology.Morph.wordsOf f)
    some (⟨c, w⟩, j)

/-- The negated variants the thesis stars are those that break the generalization: in the
*ʔɨlu*-complement of (25) the negative without the suffix, in the relative clause of (12a) the
negative with it. -/
theorem variants_ungrammatical :
    variantData ≠ [] ∧
      ∀ v ∈ variantData, v.2 = .ungrammatical ∧ (v.1.HasSuffix ↔ ¬ HasPolP v.1.clause) := by
  decide +kernel

theorem polP_clauses_attested :
    (∃ d ∈ negationData, d.clause = .root ∧ d.HasSuffix) ∧
    (∃ d ∈ negationData, d.clause = .ilu ∧ d.HasSuffix) ∧
    (∃ d ∈ negationData, d.clause = .future ∧ d.HasSuffix) ∧
    ∃ d ∈ negationData, ¬ d.HasSuffix := by
  decide +kernel

end Cacchioli2026
