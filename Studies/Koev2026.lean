module

public import Mathlib.MeasureTheory.Measure.Count
public import Studies.Kennedy2007
public import Studies.Lassiter2017
public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Data.Examples.Koev2026

/-!
# Koev (2026): a strong force semantics of *believe*

Koev renders the weak semantics of Hawthorne, Rothschild and Spectre as a relation between the
holder's credence in the complement and a degree (4), and argues that its scale gives *believe*
strong force. *Believe* takes maximizers and no minimizers, so its scale is upper closed, and
Interpretive Economy gives it the maximum standard, the force of Hintikka's semantics (1). Three
tentative pieces of further evidence, comparison classes, the antonym *doubt* and percentage
modifiers, pattern it with maximum-standard adjectives. This file checks the paper's judgments
against the fragment's *believe* and *doubt*.

## Main statements

* `fitsModifierRows_iff`: the modifier judgments fit the upper closed scale and no other.
* `fitsModifierRowsPos_iff`: read off the positive form, they fix the maximum standard.
* `weakBelieve_fitsModifierRows`: read off the scale, they leave the weak semantics open.
* `gradability_weakBelieve`: the weak semantics gives *believe* the degree semantics of *confident*.
* `furtherEvidence_iff`: the rows of §3 make *believe* and *doubt* complementary.
* `holdsAt_hintikka_iff`: maximal credence is Hintikka's *believe* over the credence's support.

## Implementation notes

Rows name predicates by form, looked up as a `Degree.Gradability` among the fragment's adjectives
and its *believe* and *doubt*. Credences are degrees of a linear order with a top, and probability
measures over a countable discrete space for the comparison with Hintikka.

## TODO

* (21): the objective reading of *sure*, measuring commitment, which (2) needs; the fragment's
  *sure* shares the scale of *believe*, so (2) does not yet come out consistent.
* The percentage judgments (19)–(20) and the ratings of fn. 9, the second condition of
  [hawthorne-rothschild-spectre-2016] that fn. 1 sets aside, and fn. 8's exhaustification of
  *doubt*.

## References

* [koev-2026]
* [hawthorne-rothschild-spectre-2016]
* [hintikka-1969]
* [kennedy-mcnally-2005]
* [kennedy-2007]
* [lassiter-2017]
* [cariani-santorio-wellwood-2024]
-/

@[expose] public section

namespace Koev2026

open Degree

/-! ### The fragment's predicates -/

/-- The verbs of the paper. -/
def verbs : List Verb := [English.Verbs.believe.toVerb, English.Verbs.doubt.toVerb]

/-- The degree semantics of the predicate a row names, among the fragment's adjectives and the
verbs `vs`. -/
def gradabilityIn (vs : List Verb) (form : String) : Option Gradability :=
  (English.Adjectives.lookup form).bind (·.gradability?) <|>
    (vs.find? (·.form == form)).bind (·.gradability?)

/-- The positive standard of the predicate a row names. -/
def standardOf (form : String) : Option PositiveStandard :=
  (gradabilityIn verbs form).map (·.standard)

/-- The endpoint modifier a row's `modifier` feature names. -/
def modifierOf : String → Option EndpointModifier
  | "maximizer" => some .maximizer
  | "minimizer" => some .minimizer
  | _ => none

/-! ### The scale of *believe* (§2) -/

-- (7), (10)
theorem degreeConstruction_rows :
    ∀ row ∈ Examples.all, row.feature? "degreeConstruction" ≠ none →
      ∀ f ∈ row.feature? "predicate", gradabilityIn verbs f ≠ none := by
  decide

/-- A scale fits the modifier judgments of *believe* when each modifier row is acceptable exactly
if the scale licenses its modifier, the maximizers of (12) and the minimizer of fn. 4. -/
def FitsModifierRows (b : Boundedness) : Prop :=
  ∀ row ∈ Examples.all, row.feature? "predicate" = some "believe" →
    ∀ m ∈ (row.feature? "modifier").bind modifierOf, (row.judgment = .acceptable ↔ b.Licenses m)

instance : DecidablePred FitsModifierRows := fun _ ↦ by unfold FitsModifierRows; infer_instance

/-- The judgments fit the upper closed scale and no other, since (12) needs a maximum and fn. 4
excludes a minimum. -/
theorem fitsModifierRows_iff {b : Boundedness} : FitsModifierRows b ↔ b = .upperClosed := by
  cases b <;> decide

-- §2, (1)
theorem defaultStandard_eq_maxEndpoint_of_fitsModifierRows {b : Boundedness}
    (h : FitsModifierRows b) : b.defaultStandard = .maxEndpoint :=
  Boundedness.defaultStandard_eq_maxEndpoint_iff.2
    (Boundedness.eq_upperClosed_iff.1 (fitsModifierRows_iff.1 h)).1

theorem fitsModifierRows_believe :
    ∃ b ∈ English.Verbs.believe.boundedness, FitsModifierRows b := by
  decide

/-- A standard fits the modifier judgments of *believe* when each modifier row is acceptable
exactly if the positive form at the standard licenses its modifier, as [lassiter-2017] reads
maximizers and minimizers. -/
def FitsModifierRowsPos (s : PositiveStandard) : Prop :=
  ∀ row ∈ Examples.all, row.feature? "predicate" = some "believe" →
    ∀ m ∈ (row.feature? "modifier").bind modifierOf,
      (row.judgment = .acceptable ↔ Lassiter2017.LicensesPos m s)

instance : DecidablePred FitsModifierRowsPos := fun _ ↦ by
  unfold FitsModifierRowsPos; infer_instance

/-- The positive-form judgments fix the maximum standard without Interpretive Economy (§2), though
*confident* takes *completely* with a contextual standard ([cariani-santorio-wellwood-2024]). -/
theorem fitsModifierRowsPos_iff {s : PositiveStandard} :
    FitsModifierRowsPos s ↔ s = .maxEndpoint := by
  cases s <;> decide

/-- The weak semantics of [hawthorne-rothschild-spectre-2016] is *believe* with a contextual
standard fixed in its lexicon. -/
def weakBelieve : Verb := { English.Verbs.believe.toVerb with lexicalStandard := some .contextual }

/-- The weak semantics gives *believe* the degree semantics of the fragment's *confident*
([cariani-santorio-wellwood-2024]). -/
theorem gradability_weakBelieve :
    weakBelieve.gradability? = English.Adjectives.confident.gradability? := by
  decide

/-- Read off the scale, the judgments leave the weak semantics open: its scale fits them, and
only Interpretive Economy, which does not admit its standard, excludes it. -/
theorem weakBelieve_fitsModifierRows :
    ∃ γ ∈ weakBelieve.gradability?,
      FitsModifierRows γ.boundedness ∧ ¬ γ.boundedness.Admits γ.standard := by
  decide

/-! ### Further evidence (§3) -/

/-- The comparison-class rows are judged as the standards `σ` predict: acceptable exactly with a
standard that needs a comparison class. -/
def ComparisonClassRows (σ : String → Option PositiveStandard) : Prop :=
  ∀ row ∈ Examples.all, row.feature? "comparisonClass" = some "overt" →
    ∀ s ∈ (row.feature? "predicate").bind σ,
      (row.judgment = .acceptable ↔ s.RequiresComparisonClass)

/-- The entailment rows are judged as the standards `σ` predict: denying a pole entails its
antonym exactly when the two standards are complementary. -/
def EntailmentRows (σ : String → Option PositiveStandard) : Prop :=
  ∀ row ∈ Examples.all, ∀ r ∈ row.feature? "relation",
    ∀ s ∈ (row.feature? "negated").bind σ, ∀ t ∈ (row.feature? "antonym").bind σ,
      (r = "entails" ↔ s.Complementary t)

/-- The double-denial rows are judged as the standards `σ` predict: denying both poles is
felicitous exactly when their standards leave a gap. -/
def DoubleDenialRows (σ : String → Option PositiveStandard) : Prop :=
  ∀ row ∈ Examples.all, row.feature? "construction" = some "doubleDenial" →
    ∀ s ∈ (row.feature? "negated").bind σ, ∀ t ∈ (row.feature? "antonym").bind σ,
      (row.judgment = .acceptable ↔ ¬ s.Complementary t)

instance (σ : String → Option PositiveStandard) : Decidable (ComparisonClassRows σ) := by
  unfold ComparisonClassRows; infer_instance

instance (σ : String → Option PositiveStandard) : Decidable (EntailmentRows σ) := by
  unfold EntailmentRows; infer_instance

instance (σ : String → Option PositiveStandard) : Decidable (DoubleDenialRows σ) := by
  unfold DoubleDenialRows; infer_instance

-- (13a), fn. 6, (14b), (15a), (16a), (17a), (15b), (17b), (14a)
theorem rows_standardOf :
    ComparisonClassRows standardOf ∧ EntailmentRows standardOf ∧ DoubleDenialRows standardOf := by
  decide

/-- The fragment's standards, with *believe* and *doubt* fixing `s` and `t` in their lexicon. -/
def standardWith (s t : PositiveStandard) (form : String) : Option PositiveStandard :=
  (gradabilityIn [{ English.Verbs.believe.toVerb with lexicalStandard := some s },
    { English.Verbs.doubt.toVerb with lexicalStandard := some t }] form).map (·.standard)

/-- The rows of §3 hold of *believe* and *doubt* exactly when their standards are complementary
endpoints, excluding the contextual standard of [hawthorne-rothschild-spectre-2016]. -/
theorem furtherEvidence_iff {s t : PositiveStandard} :
    ComparisonClassRows (standardWith s t) ∧ EntailmentRows (standardWith s t) ∧
      DoubleDenialRows (standardWith s t) ↔ s.Complementary t := by
  cases s <;> cases t <;> decide +kernel

section Credence
variable {α D : Type*} [LinearOrder D] [OrderTop D] (Cr : α → D)

-- (17)
theorem isCompl_maxStandard_minStandard_dual :
    IsCompl (Cr ⁻¹' Set.Ici ⊤) ((OrderDual.toDual ∘ Cr) ⁻¹' Set.Ioi ⊥) :=
  (Kennedy2007.antonyms_isCompl (OrderDual.toDual ∘ Cr)).symm

end Credence

-- (17), fn. 4 [lassiter-2017]
theorem not_complementary_probability :
    ¬ (Boundedness.ofOrder Lassiter2017.Probability).defaultStandard.Complementary
        (Boundedness.ofOrder Lassiter2017.Probability).dual.defaultStandard := by
  simp [Lassiter2017.ofOrder_probability, Boundedness.complementary_defaultStandard_dual_iff]

theorem complementary_Ioc :
    (Boundedness.ofOrder (Set.Ioc (0 : ℝ) 1)).defaultStandard.Complementary
      (Boundedness.ofOrder (Set.Ioc (0 : ℝ) 1)).dual.defaultStandard := by
  simp [Boundedness.ofOrder_Ioc zero_lt_one, Boundedness.complementary_defaultStandard_dual_iff]

/-! ### Hintikka's semantics (§4) -/

section Hintikka
open MeasureTheory ModalLogic
variable {E W : Type*} [MeasurableSpace W] (Cr : E → W → Measure W)

/-- Hintikka's *believe* (1) over the worlds to which a credence gives positive mass, the
identification of doxastic alternatives with the credence's support that relates (1) to (4)
([hintikka-1969]). -/
def hintikka : Doxastic.DoxasticPredicate W E where
  access x := {(w, v) | Cr x w {v} ≠ 0}
  veridicality := .nonVeridical

/-- *Believe* at the maximum standard of the credence scale is Hintikka's *believe* over the
credence's support, the universal force of (1). -/
theorem holdsAt_hintikka_iff [DiscreteMeasurableSpace W] [Countable W]
    [∀ x w, IsProbabilityMeasure (Cr x w)] (x : E) (p : Set W) (w : W) :
    (hintikka Cr).HoldsAt x (· ∈ p) w ↔ p ∈ Lassiter2017.likelihood (Cr x w) ⁻¹' Set.Ici ⊤ := by
  rw [← Lassiter2017.certain_eq_preimage, Lassiter2017.mem_certain_iff,
    measureReal_def, ENNReal.toReal_eq_one_iff, ← prob_compl_eq_zero_iff .of_discrete,
    ← mem_ae_iff, ← Filter.eventually_mem_set, ae_iff_of_countable]
  simp [Doxastic.DoxasticPredicate.holdsAt_iff, hintikka, Doxastic.VeridicalityHolds, box_iff]

end Hintikka

end Koev2026
