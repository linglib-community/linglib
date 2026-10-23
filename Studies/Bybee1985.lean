module

public import Linglib.Morphology.Morphotactics.RelevanceHierarchy
public import Mathlib.Tactic.DeriveFintype

/-!
# Bybee 1985: relevance and lexical strength

A morpheme category whose meaning is more relevant to the verb stem should have morphological
expression, inflectional or derivational, in more languages, sit closer to the stem where it is,
and fuse with it more tightly; whether the expression is inflectional depends on generality as
well, which works against the most relevant categories. This file formalizes the evidence for the
first two predictions, from a fifty-language stratified
sample: the frequency surveys of chapter 2 and the morpheme-order counts of the same chapter, in
which every tested pair confirms the predicted direction and aspect against tense and against mood
does so without a single counterexample.

The order those counts determine is then shown to be the relevance hierarchy's order rather than a
table chosen to match it: on the four categories the survey covers, the relation derived from the
counts and the hierarchy's order are the same. Fusion, the third claim, is
qualitative in the source.

Chapter 5's notion of lexical strength closes the file: an irregular verb keeps its irregularity
where its token frequency is high, and the Strong Verbs that regularized are the infrequent ones.

## Main definitions

* `BybeeCategory` — the verbal-inflectional categories of Ch 2, in relevance order.
* `inflectionalCount50`, `derivOrInflCount50` — the Ch 2 §5 frequency surveys (Figs 1+2).
* `orderPairs` — the Ch 2 §6 morpheme-order counts, one `OrderPair` per tested category pair.
* `toRelevanceHierarchy` — the hierarchy category of each surveyed category.
* `SurveyedCloser` — the stem-proximity order *derived from* `orderPairs`.
* `strongStillStrong`, `strongRegularized` — the Ch 5 §6 strong-verb frequency table.

## Main results

* `valence_highest_when_derivOrInfl`, `valence_lowest_when_inflectional` — the
  relevance and generality frequency predictions.
* `predicted_outnumbers_counter`, `aspect_categorical_against_tense_and_mood` — the order
  predictions.
* `survey_order_iso_relevance` — on the surveyed categories `SurveyedCloser` and the hierarchy's
  `<` coincide via `toRelevanceHierarchy`: the hierarchy is the order the §6 survey forces, not a
  stipulated table.
* `bybeeSurveyedOrder_respects_hierarchy` — the surveyed order is sorted by the hierarchy.
* `strong_verbs_higher_frequency_than_regularized` — the Ch 5 §6 diachronic
  claim: still-Strong verbs have a strictly higher mean token frequency than
  the regularized ones.

## References

* [bybee-1985]
* [francis-kucera-1982]
* [perkins-1980]
* [sweet-1882]
-/

@[expose] public section

namespace Bybee1985

open Morphology

/-! ### Verbal categories (Ch 2 §3)

Bybee's six core categories in relevance order: valence, voice, aspect, tense,
mood, agreement (number/person/gender are agreement sub-types). -/

/-- Bybee's Ch 2 verbal-inflectional categories, in her relevance order (stem
first). Constructor docstrings paraphrase the coding definitions of Ch 2 §4, which
distinguish subject, object and indirect-object agreement; Figures 1 and 2 split only person
agreement, into "person" (the text's subject agreement) and "person (object)". -/
inductive BybeeCategory where
  /-- Differences in the number or role of the arguments the verb stem takes. -/
  | valence
  /-- The perspective from which the situation described by the verb stem is
  viewed. -/
  | voice
  /-- The way the internal temporal constituency of the situation is viewed. -/
  | aspect
  /-- The situation's placement in time, relative to the moment of speech or
  some other established point. -/
  | tense
  /-- The way the speaker presents the truth of the proposition: probability,
  possibility, certainty; evidentials are included under mood. -/
  | mood
  /-- Concord by number with one or more arguments of the verb. -/
  | numberAgr
  /-- Concord by person with the subject. -/
  | personAgr
  /-- Concord by person with the object. -/
  | personAgrObj
  /-- Concord with arguments by lexical class, assigned arbitrarily or by
  inherent qualities of the referent. -/
  | genderAgr
  deriving DecidableEq, Repr, Fintype

/-! ### Cross-linguistic frequency (Ch 2 §5, Figs 1+2)

Fig 1 counts the 50-sample languages with *inflectional* expression of a
category; Fig 2 counts those with inflectional *or* derivational expression.
Counts are integers because the sample is exactly 50 (count = percentage / 2). -/

/-- Languages (of 50) with *inflectional* expression of `c` (Fig 1). -/
def inflectionalCount50 : BybeeCategory → Nat
  | .valence       => 3   -- 6%
  | .voice         => 13  -- 26%
  | .aspect        => 26  -- 52%
  | .tense         => 24  -- 48%
  | .mood          => 34  -- 68%
  | .numberAgr     => 27  -- 54%
  | .personAgr     => 28  -- 56%
  | .personAgrObj  => 14  -- 28%
  | .genderAgr     => 8   -- 16%

/-- Languages (of 50) with *inflectional or derivational* expression of `c`
(Fig 2). Valence reaches 90% once valence-changing derivation is counted; only
Haitian, Karankawa, Navaho, Serbo-Croatian, and Vietnamese lack it. -/
def derivOrInflCount50 : BybeeCategory → Nat
  | .valence       => 45  -- 90%
  | .voice         => 28  -- 56%
  | .aspect        => 37  -- 74%
  | .tense         => 25  -- 50%
  | .mood          => 34  -- 68%
  | .numberAgr     => 33  -- 66%
  | .personAgr     => 28  -- 56%
  | .personAgrObj  => 14  -- 28%
  | .genderAgr     => 8   -- 16%

/-- The relevance prediction, tested on Figure 2, which counts derivational as well as
inflectional expression: valence is the most frequent category, reflecting near-universal
valence-changing morphology. -/
theorem valence_highest_when_derivOrInfl :
    ∀ c : BybeeCategory, derivOrInflCount50 c ≤ derivOrInflCount50 .valence := by
  decide

/-- The generality prediction: restricted to *inflection*, valence is the least
frequent category (6%, down from 90%) — generality "predicts fewer inflections
among the most highly relevant categories", because highly relevant morphology
is rarely obligatory across all stems. -/
theorem valence_lowest_when_inflectional :
    ∀ c : BybeeCategory, inflectionalCount50 .valence ≤ inflectionalCount50 c := by
  decide

theorem gender_lowest_when_derivOrInfl :
    ∀ c : BybeeCategory, derivOrInflCount50 .genderAgr ≤ derivOrInflCount50 c := by
  decide

/-! ### Morpheme order (Ch 2 §6)

The order prediction: the most relevant categories sit closest to the stem, the least
relevant furthest. Bybee tests the four most frequent — aspect, tense, mood,
person — counting, per pair, how many languages place one closer than the other.
A language with both categories is untestable when the morphemes are
portmanteau, on opposite sides of the stem (unless only one is stem-adjacent),
or mutually exclusive in one slot; a morpheme expressed by stem modification
counts as closer than one expressed by affixation. -/

/-- A Ch 2 §6 morpheme-order pair. -/
structure OrderPair where
  /-- The category predicted closer to the stem. -/
  closer : BybeeCategory
  /-- The category predicted further from the stem. -/
  further : BybeeCategory
  /-- The languages confirming the predicted order. -/
  closerCount : Nat
  /-- The languages showing the opposite order. -/
  furtherCount : Nat
  /-- The languages having both categories, testable or not. -/
  total : Nat
  deriving Repr

/-- The six pairs Bybee tests in Ch 2 §6; counts verified against the book, each
inline comment quoting its source passage. -/
def orderPairs : List OrderPair := [
  -- p. 34: "Aspect markers were found to be closer to the stem than tense
  -- markers in 8 languages, while the opposite order did not occur in the
  -- sample. There were a total of 18 languages that have both aspect and
  -- tense, but in 10 cases their ordering was not relevant to the hypothesis."
  ⟨.aspect, .tense, 8, 0, 18⟩,
  -- p. 35: "Aspect markers were found to be closer to the stem than mood
  -- markers in 10 languages, out of a total of 23 that have both aspect
  -- and mood. There were no languages in the sample in which the mood
  -- marker occurred closer to the stem than the aspect marker."
  ⟨.aspect, .mood, 10, 0, 23⟩,
  -- p. 35: "Aspect markers were found to be closer to the stem than person
  -- markers in 12 out of 21 languages. In one language, Navaho, the person
  -- markers occur closer to the stem than the aspect marker."
  ⟨.aspect, .personAgr, 12, 1, 21⟩,
  -- p. 35: "Tense markers occur closer to the stem than mood markers in 8
  -- languages out of 20 that have both tense and mood. In one language,
  -- Ojibwa, the mood marker occurs closer to the stem than the tense marker."
  ⟨.tense, .mood, 8, 1, 20⟩,
  -- p. 35: "Tense markers occur closer to the stem than person markers in
  -- 8 languages out of the 17 that have both tense and mood. In one
  -- language, Navaho, the person markers occur closer to the stem than
  -- the tense markers." The book's "tense and mood" is a misprint for
  -- tense and person, the pair under test.
  ⟨.tense, .personAgr, 8, 1, 17⟩,
  -- p. 35: "Mood markers occur closer to the stem than person markers in
  -- 13 languages out of 26. In 5 languages the opposite order occurs."
  ⟨.mood, .personAgr, 13, 5, 26⟩
]

/-- Aspect vs. tense and aspect vs. mood are categorical: zero counterexamples
in the whole sample, the strongest confirmations Bybee reports. -/
theorem aspect_categorical_against_tense_and_mood :
    ∀ p ∈ orderPairs,
      p.closer = .aspect → (p.further = .tense ∨ p.further = .mood) →
      p.furtherCount = 0 := by
  decide

theorem mood_person_ordering_is_freest :
    ∀ p ∈ orderPairs, ∀ q ∈ orderPairs,
      q.closer = .mood → p.closer ≠ .mood →
      p.furtherCount * q.total < q.furtherCount * p.total := by
  decide

/-- In every one of the six pairs the predicted direction outnumbers the
counter-direction (Ch 2 §6 summary). -/
theorem predicted_outnumbers_counter :
    ∀ p ∈ orderPairs, p.furtherCount < p.closerCount := by
  decide

/-! ### The relevance hierarchy

The survey codes agreement finer than the hierarchy ranks it: number, person, object person and
gender agreement are all the hierarchy's agreement. -/

/-- The hierarchy category a surveyed category belongs to. -/
def toRelevanceHierarchy : BybeeCategory → RelevanceHierarchy
  | .valence       => .valence
  | .voice         => .voice
  | .aspect        => .aspect
  | .tense         => .tense
  | .mood          => .mood
  | .numberAgr     => .agreement
  | .personAgr     => .agreement
  | .personAgrObj  => .agreement
  | .genderAgr     => .agreement

/-! ### Grounding the hierarchy in the survey

On the four categories Bybee surveyed (aspect, tense, mood, person), the
hierarchy's order is not a free choice: `SurveyedCloser`, derived from
`orderPairs`, coincides with the hierarchy's `<` via `toRelevanceHierarchy`
(`survey_order_iso_relevance`). So a sortedness check over these categories
rests on an order isomorphism, not a stipulated table. -/

/-- `a` is *surveyed closer to the stem than* `b` when some tested Ch 2 §6 pair
predicts `a` closer than `b` and the language counts confirm that direction
(predicted majority). Derived from `orderPairs`, not stipulated. -/
def SurveyedCloser (a b : BybeeCategory) : Prop :=
  ∃ p ∈ orderPairs, p.closer = a ∧ p.further = b ∧ p.furtherCount < p.closerCount

instance : DecidableRel SurveyedCloser := fun _ _ =>
  inferInstanceAs (Decidable (∃ _ ∈ orderPairs, _))

/-- A category is *surveyed* if it appears in any tested Ch 2 §6 pair. -/
def Surveyed (c : BybeeCategory) : Prop :=
  ∃ p ∈ orderPairs, p.closer = c ∨ p.further = c

instance : DecidablePred Surveyed := fun _ =>
  inferInstanceAs (Decidable (∃ _ ∈ orderPairs, _))

theorem surveyedCloser_irrefl : ∀ a : BybeeCategory, ¬ SurveyedCloser a a := by
  decide

/-- `SurveyedCloser` is transitive — the §6 survey tested every pair among its
categories, so the confirmed dominances compose. -/
theorem surveyedCloser_trans : ∀ a b c : BybeeCategory,
    SurveyedCloser a b → SurveyedCloser b c → SurveyedCloser a c := by
  decide

/-- `SurveyedCloser` is total on the surveyed categories, so the §6 survey alone fixes a strict
total order on them. -/
theorem surveyedCloser_total : ∀ a b : BybeeCategory,
    Surveyed a → Surveyed b → a ≠ b → SurveyedCloser a b ∨ SurveyedCloser b a := by
  decide

/-- On the surveyed categories, `SurveyedCloser` coincides with the relevance hierarchy's order
(§6). -/
theorem survey_order_iso_relevance : ∀ a b : BybeeCategory,
    Surveyed a → Surveyed b →
      (SurveyedCloser a b ↔ toRelevanceHierarchy a < toRelevanceHierarchy b) := by
  decide

/-- The stem-outward ordering of the surveyed categories — a literal, but
validated as fully `SurveyedCloser`-sorted (`bybeeSurveyedOrder_sorted`) and
exhaustive (`bybeeSurveyedOrder_complete`). -/
def bybeeSurveyedOrder : List BybeeCategory :=
  [.aspect, .tense, .mood, .personAgr]

theorem bybeeSurveyedOrder_sorted : bybeeSurveyedOrder.Pairwise SurveyedCloser := by
  decide

theorem bybeeSurveyedOrder_complete : ∀ c : BybeeCategory,
    Surveyed c → c ∈ bybeeSurveyedOrder := by decide

/-- The data-derived surveyed order is sorted by the relevance hierarchy, closing
the loop between Bybee's §6 evidence and the hierarchy. -/
theorem bybeeSurveyedOrder_respects_hierarchy :
    (bybeeSurveyedOrder.map toRelevanceHierarchy).SortedLE := by decide

/-! ### Lexical strength

Chapter 5 replaces the question whether an item is in the lexicon with two gradient notions. Each
token of use strengthens an item's representation — "etching it with deeper and darker lines each
time" — and strength declines with disuse; and items bear semantic and phonological connections to
one another, a parallel pair of which constitutes a morphological relation. The consequence tested
below is diachronic: an irregular verb survives as irregular where its lexical strength is high.

The table on p. 120 lists the modern descendants of the Class I, II and VII Strong Verbs of
[sweet-1882]'s *Anglo-Saxon Primer* with their all-forms token frequencies; *slit* and *beat* now
take the zero allomorph of the past tense. -/

/-- A verb with its all-forms token frequency, which is what lexical strength amounts to here. -/
structure VerbFrequency where
  /-- The verb, by its modern form. -/
  verb : String
  /-- The all-forms token frequency ([francis-kucera-1982]). -/
  tokenFreq : Nat
  deriving Repr

/-- The Strong Verbs that have stayed Strong (p. 120), with all-forms token
frequencies. -/
def strongStillStrong : List VerbFrequency := [
  -- Class I (mean 223)
  ⟨"drive", 203⟩, ⟨"rise", 199⟩, ⟨"ride", 126⟩, ⟨"write", 561⟩, ⟨"bite", 26⟩,
  -- Class II (mean 140)
  ⟨"choose", 177⟩, ⟨"fly", 92⟩, ⟨"shoot", 117⟩, ⟨"lose", 274⟩, ⟨"flee", 40⟩,
  -- Class VII (mean 515)
  ⟨"fall", 239⟩, ⟨"hold", 509⟩, ⟨"know", 1473⟩, ⟨"grow", 300⟩, ⟨"blow", 52⟩
]

/-- The Strong Verbs that have regularized or become Weak (p. 120), with
all-forms token frequencies. -/
def strongRegularized : List VerbFrequency := [
  -- Class I (mean 5)
  ⟨"bide", 1⟩, ⟨"reap", 5⟩, ⟨"slit", 3⟩, ⟨"sneak", 11⟩,
  -- Class II (mean 22)
  ⟨"rue", 0⟩, ⟨"seethe", 0⟩, ⟨"smoke", 26⟩, ⟨"float", 23⟩, ⟨"shove", 16⟩,
  -- Class VII (mean 21)
  ⟨"wax", 6⟩, ⟨"weep", 28⟩, ⟨"beat", 66⟩, ⟨"hew", 1⟩, ⟨"leap", 33⟩,
  ⟨"mow", 1⟩, ⟨"sow", 6⟩, ⟨"flow", 40⟩, ⟨"row", 5⟩
]

/-- The mean token frequency of the still-Strong verbs strictly exceeds that of
the regularized ones — irregularity survives where lexical strength is high.
Stated as the cross-multiplied sum comparison to stay in `Nat`. -/
theorem strong_verbs_higher_frequency_than_regularized :
    (strongRegularized.map (·.tokenFreq)).sum * strongStillStrong.length
    < (strongStillStrong.map (·.tokenFreq)).sum * strongRegularized.length := by
  decide

end Bybee1985
