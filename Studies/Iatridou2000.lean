module

public import Linglib.Semantics.Mood.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Disjoint

/-!
# Iatridou (2000): The grammatical ingredients of counterfactuality

This file formalizes [iatridou-2000]'s account of the past morphology of counterfactuals as
an exclusion feature. The feature's skeletal meaning (49) is that the topic excludes what,
for all the speaker knows, is the speaker's: over times the topic time excludes the utterance
time, temporal past, and over worlds the topic worlds exclude the actual worlds,
counterfactuality (`Excludes`). What is asserted is a relation to the topic, not to the
situation, so the counterfactual inference is cancellable and *John was in the classroom; in
fact he still is* is consistent (`Claim.consistent_with_inclusion`).

One feature over worlds leaves the rest of the antecedent to be evaluated as with present
tense, so the future less vivid and the present counterfactual readings are the future and
present evaluation times of the predicate's Aktionsart: Table 1 is Table 2 (`readings`), and
the pluperfect's second layer makes a past counterfactual whatever the predicate. Aspect and
mood are not ingredients: the imperfective of Greek and French is absent from English
(`imperfective_not_universal`), and the subjunctive appears in a counterfactual only where a
past subjunctive paradigm lets it co-occur with the feature, so French, having lost its past
subjunctive, keeps the past indicative (`antecedent_french`).

## Implementation notes

Exclusion is disjointness of sets of times or worlds, the speaker's coordinate being a set of
epistemically accessible alternatives; the *before* of temporal past is `TemporalPast`.

## References

* [iatridou-2000]
-/

@[expose] public section

namespace Iatridou2000

/-! ### The exclusion feature -/

variable {X : Type*}

/-- The topic excludes the speaker's, as sets of times or of worlds, (49). -/
def Excludes (topic speaker : Set X) : Prop := Disjoint topic speaker

/-- Temporal past is exclusion augmented by *before* (footnote 19). -/
def TemporalPast [Preorder X] (topic speaker : Set X) : Prop :=
  ∀ t ∈ topic, ∀ u ∈ speaker, t < u

theorem excludes_of_temporalPast [Preorder X] {topic speaker : Set X}
    (h : TemporalPast topic speaker) : Excludes topic speaker :=
  Set.disjoint_left.2 fun t ht hu ↦ lt_irrefl t (h t ht t hu)

/-- The claim the feature contributes to an assertion is that the situation, the p-worlds or
the situation time, holds throughout a topic that excludes the speaker's. -/
structure Claim (X : Type*) where
  topic : Set X
  speaker : Set X
  situation : Set X
  topic_subset : topic ⊆ situation
  excludes : Excludes topic speaker

/-- The claim leaves open whether the situation includes the speaker's worlds or times, so the
counterfactual inference is an implicature and *in fact, he still is* is consistent,
(58)–(59). -/
theorem Claim.consistent_with_inclusion :
    ∃ c : Claim Bool, c.speaker ⊆ c.situation ∧ c.topic.Nonempty ∧ c.speaker.Nonempty :=
  ⟨⟨{true}, {false}, Set.univ, Set.subset_univ _, by simp [Excludes]⟩,
    Set.subset_univ _, Set.singleton_nonempty _, Set.singleton_nonempty _⟩

theorem Claim.excludes_situation_iff (c : Claim X) :
    Excludes c.situation c.speaker ↔ ∀ x ∈ c.speaker, x ∉ c.situation :=
  Set.disjoint_right

/-! ### The three counterfactuals -/

/-- The counterfactual conditionals of the paper are the future less vivid, the present
counterfactual and the past counterfactual. -/
inductive CounterfactualType where
  | flv
  | presCF
  | pastCF
  deriving DecidableEq, Repr

/-- The coordinates an exclusion feature ranges over: the temporal and the modal past are one
feature on different coordinates, not a lexical ambiguity. -/
inductive ExclDimension where
  | temporal
  | modal
  deriving DecidableEq, Repr

/-- A counterfactual has one exclusion feature over worlds, and the past counterfactual a
second, the pluperfect's second layer, over times. -/
def CounterfactualType.dimensions : CounterfactualType → Finset ExclDimension
  | .flv | .presCF => {.modal}
  | .pastCF => {.modal, .temporal}

/-- The Aktionsart of the antecedent's predicate is telic, activity (footnote 24),
individual-level stative or stage-level stative. -/
inductive Aktionsart where
  | telic
  | activity
  | ilStative
  | slStative
  deriving DecidableEq, Fintype, Repr

/-- The times at which an antecedent can be evaluated. -/
inductive Evaluation where
  | future
  | now
  deriving DecidableEq, Repr

/-- The earliest evaluation of a present-tense antecedent by the predicate's Aktionsart,
Table 2 and (65)–(67). -/
def Aktionsart.evaluation : Aktionsart → Finset Evaluation
  | .telic | .activity => {.future}
  | .ilStative => {.now}
  | .slStative => {.future, .now}

/-- After one feature has set up the topic worlds, evaluation in the future is the future
less vivid and evaluation now the present counterfactual. -/
def Evaluation.reading : Evaluation → CounterfactualType
  | .future => .flv
  | .now => .presCF

/-- The readings of a conditional with one exclusion feature on a predicate of the given
Aktionsart, Table 1 derived from Table 2. -/
def readings (a : Aktionsart) : Finset CounterfactualType := a.evaluation.image Evaluation.reading

theorem readings_telic : readings .telic = {.flv} := by decide

theorem readings_ilStative : readings .ilStative = {.presCF} := by decide

/-- A stage-level stative yields either reading, (64). -/
theorem readings_slStative : readings .slStative = {.flv, .presCF} := by decide

theorem pastCF_notMem_readings (a : Aktionsart) : .pastCF ∉ readings a := by
  cases a <;> decide

theorem exists_mem_readings_iff (c : CounterfactualType) :
    (∃ a, c ∈ readings a) ↔ c.dimensions = {.modal} := by
  cases c <;> decide

/-! ### Aspect and mood -/

/-- A language requires the imperfective in its counterfactuals, no aspect, or either aspect
(Section 5). -/
inductive CFAspect where
  | imperfective
  | none
  | either
  deriving DecidableEq, Repr

/-- The languages whose counterfactual morphology Section 5 compares. -/
inductive AspectLanguage where
  | greek
  | french
  | english
  | polish
  deriving DecidableEq, Repr

/-- Greek and French require the imperfective, English has no such requirement, and Polish
allows either aspect. -/
def AspectLanguage.cfAspect : AspectLanguage → CFAspect
  | .greek | .french => .imperfective
  | .english => .none
  | .polish => .either

theorem imperfective_not_universal : ¬ ∀ l, AspectLanguage.cfAspect l = .imperfective :=
  fun h ↦ absurd (h .english) (by decide)

/-- Whether a language has a past subjunctive paradigm (Section 6.1). -/
inductive SubjunctiveParadigm where
  | past
  | nonpastOnly
  | none
  deriving DecidableEq, Repr

/-- A counterfactual antecedent is subjunctive when a past subjunctive exists and indicative
otherwise; a nonpast subjunctive never expresses the feature, so it loses to the past
indicative, the French choice of (99). -/
def antecedentForm : SubjunctiveParadigm → Mood.Grammatical
  | .past => .subjunctive
  | .nonpastOnly | .none => .indicative

/-- A counterfactual carries the subjunctive only in a language with a past subjunctive
paradigm (Section 6.1). -/
theorem antecedentForm_eq_subjunctive_iff {p : SubjunctiveParadigm} :
    antecedentForm p = .subjunctive ↔ p = .past := by
  cases p <;> simp [antecedentForm]

/-- French has only a nonpast subjunctive, so its counterfactual antecedents carry the past
indicative, (99). -/
theorem antecedent_french : antecedentForm .nonpastOnly = .indicative := rfl

theorem antecedent_german : antecedentForm .past = .subjunctive := rfl

end Iatridou2000
