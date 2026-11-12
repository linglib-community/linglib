module

public import Studies.Kennedy2007
public import Studies.Lassiter2017
public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Data.Examples.Koev2026
public import Linglib.Data.Examples.Readers

/-!
# Koev (2026): a strong force semantics of *believe*

Hawthorne, Rothschild and Spectre take *believe* to hold when its holder's credence in the
complement exceeds a contextual threshold, the positive form of a relative predicate. Koev keeps
the credence scale and argues from its shape for a strong force. *Believe* takes maximizers and no
minimizers, which [only an upper closed scale licenses](##Koev2026.fitsModifiers_iff), and on such
a scale Interpretive Economy selects the maximum standard, so that unmodified *believe* is
[Hintikka's universal quantification](##Koev2026.holdsAt_hintikka_iff) over the worlds the
credence leaves open. Comparison classes and the antonym *doubt*
[place its standard at an endpoint](##Koev2026.furtherEvidence_iff) as well, where *believe* and
*doubt* are contradictories while *likely* and *unlikely*
[leave a gap](##Koev2026.not_likely_and_not_unlikely).

## Implementation notes

The positive form at a standard is the preimage of the standard under the measure, as in
`Semantics/Degree/PositiveStandard.lean`, and credences are probability measures where the
comparison with Hintikka needs them. A row's predicates and its endpoint modifier are read off its
words, the predicates as the fragment's entries, and the antonym of a predicate is the entry on
its dimension at the other pole; the rows keep as features only what the paper prints about them,
the entailment arrow and the comparison-class construction. The fragment has no *likely*, whose
scale is disputed, so the comparison-class row for *likely* is read without a predicate and the
gap of *likely* and *unlikely* is stated on Lassiter's threshold semantics.

## TODO

* The objective reading of *sure*, a measure of commitment beside the credence, which makes *I
  believe it but I'm not sure* consistent; the fragment's *sure* shares the scale of *believe*.
* The percentage judgments and their ratings, the second condition of
  [hawthorne-rothschild-spectre-2016] that the paper sets aside, and the exhaustification that
  strengthens unembedded *doubt*.

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

open English.Verbs English.Adjectives

/-! ### The scale of *believe* (§2) -/

/-- The endpoint modifiers of the paper's examples, by form. -/
def endpointModifiers : List (String × EndpointModifier) :=
  [("fully", .maximizer), ("completely", .maximizer), ("entirely", .maximizer),
    ("slightly", .minimizer)]

/-- The gradable predicates of the paper's examples, the fragment's entries, by citation form. -/
def lexicon : List (List Char × Gradability) :=
  [tall, short, bent, straight, full].filterMap (fun a ↦ a.gradability?.map (a.form.toList, ·)) ++
    [believe, doubt].filterMap fun v ↦ v.gradability?.map (v.form.toList, ·)

/-- The gradable predicates among the words of a row, in order, a word being a citation form or
one with the agreement suffix *-s*. -/
def predicates (e : Datum) : List Gradability :=
  (Datum.wordsOf e.primaryText).filterMap fun w ↦
    (lexicon.find? fun p ↦ w = p.1 ∨ w = p.1 ++ ['s']).map (·.2)

/-- The antonym of a predicate is the one that measures the same dimension towards the other
pole. -/
def antonym? (g : Gradability) : Option Gradability :=
  (lexicon.map (·.2)).find? fun h ↦ h.dimension = g.dimension ∧ h.polarity ≠ g.polarity

/-- The rows whose predicate is *believe* with an endpoint modifier among their words, each as
its judgment and the modifier. -/
def modifierRows : List (Judgment.Band × EndpointModifier) :=
  Examples.all.filterMap fun e ↦
    if (predicates e).head? = believe.gradability? then
      ((Datum.wordsOf e.primaryText).findSome? fun w ↦
        (endpointModifiers.find? (·.1.toList = w)).map (·.2)).map (e.judgment.band, ·)
    else none

-- (12a), (12b), (12c), fn. 4
theorem modifierRows_eq : modifierRows =
    [(.accepted, .maximizer), (.accepted, .maximizer), (.accepted, .maximizer),
      (.rejected, .minimizer)] := by
  decide +kernel

/-- A scale fits the modifier judgments of *believe* when each row is accepted exactly if the
scale licenses its modifier. -/
def FitsModifiers (b : Boundedness) : Prop :=
  ∀ x ∈ modifierRows, x.1 = .ofProp (b.Licenses x.2)

/-- The modifier judgments fit the upper closed scale and no other, since the maximizers of (12)
need a maximum and the minimizer of fn. 4 excludes a minimum. -/
theorem fitsModifiers_iff {b : Boundedness} : FitsModifiers b ↔ b = .upperClosed := by
  rw [FitsModifiers, modifierRows_eq]
  cases b <;> decide

-- §2: Interpretive Economy selects the maximum standard on that scale and excludes the contextual
-- standard of the weak semantics, (6b).
theorem defaultStandard_of_fitsModifiers {b : Boundedness} (h : FitsModifiers b) :
    b.defaultStandard = .maxEndpoint ∧ ¬ b.Admits .contextual := by
  obtain rfl := fitsModifiers_iff.1 h
  decide

theorem believe_fitsModifiers : ∃ b ∈ believe.boundedness, FitsModifiers b :=
  ⟨.upperClosed, rfl, fitsModifiers_iff.2 rfl⟩

-- §2, first remark: licensed by the standard of the positive form, as [lassiter-2017] licenses
-- them, the modifiers fix the maximum standard without Interpretive Economy.
theorem forall_licensesPos_iff {s : PositiveStandard} :
    (∀ x ∈ modifierRows, x.1 = .ofProp (Lassiter2017.LicensesPos x.2 s)) ↔ s = .maxEndpoint := by
  rw [modifierRows_eq]
  cases s <;> decide

/-- The weak semantics makes *believe* a verbal *confident*: the fragment's *confident* is on the
scale of *believe* with the contextual standard of [cariani-santorio-wellwood-2024], a standard
Interpretive Economy does not admit there, so the argument from the scale does not extend to it. -/
theorem confident_not_admits :
    ∃ g ∈ confident.gradability?, believe.boundedness = some g.boundedness ∧
      g.standard = .contextual ∧ ¬ g.boundedness.Admits g.standard := by
  decide

/-! ### Further evidence (§3) -/

/-- The fragment's standards, with `s` and `t` for *believe* and *doubt*. -/
def standardWith (s t : PositiveStandard) (g : Gradability) : PositiveStandard :=
  if some g = believe.gradability? then s else if some g = doubt.gradability? then t
  else g.standard

/-- The rows the paper marks as putting a predicate with an overt comparison class, each as its
judgment and the predicate, if the fragment has it. -/
def comparisonClassRows : List (Judgment × Option Gradability) :=
  Examples.all.filterMap fun e ↦
    if e.feature? "comparisonClass" = some "overt" then some (e.judgment, (predicates e).head?)
    else none

/-- The rows that deny a pole and print whether that entails the antonym, each as the printed
relation, the pole and its antonym. -/
def entailmentRows : List (Bool × Option Gradability × Option Gradability) :=
  Examples.all.filterMap fun e ↦
    (e.parse? "relation" [("entails", true), ("does_not_entail", false)]).map fun r ↦
      (r, (predicates e).head?, (predicates e).head?.bind antonym?)

/-- The rows that deny a predicate and its antonym, each as its judgment and the two poles. -/
def bothDeniedRows : List (Judgment × Option Gradability × Option Gradability) :=
  Examples.all.filterMap fun e ↦
    match predicates e with
    | [g, h] => if antonym? g = some h then some (e.judgment, some g, some h) else none
    | _ => none

-- (13a), (13b), (14a), (14b), fn. 6
theorem comparisonClassRows_eq : comparisonClassRows =
    [(.acceptable, tall.gradability?), (.questionable, full.gradability?), (.marginal, none),
      (.unacceptable, believe.gradability?), (.marginal, full.gradability?)] := by
  decide +kernel

-- (15a), (16a), (17a)
theorem entailmentRows_eq : entailmentRows =
    [(true, bent.gradability?, straight.gradability?),
      (false, tall.gradability?, short.gradability?),
      (true, doubt.gradability?, believe.gradability?)] := by
  decide +kernel

-- (15b), (16b), (17b)
theorem bothDeniedRows_eq : bothDeniedRows =
    [(.unacceptable, bent.gradability?, straight.gradability?),
      (.acceptable, tall.gradability?, short.gradability?),
      (.unacceptable, believe.gradability?, doubt.gradability?)] := by
  decide +kernel

/-- The judgments of §3 are as the standards `σ` predict. An overt comparison class is acceptable
exactly with a standard that requires one; denying a pole entails its antonym exactly when the two
standards are complementary; and denying both poles is acceptable exactly when they are not. -/
def FurtherEvidence (σ : Gradability → PositiveStandard) : Prop :=
  (∀ x ∈ comparisonClassRows, ∀ g ∈ x.2,
    (x.1 = .acceptable ↔ (σ g).RequiresComparisonClass)) ∧
  (∀ x ∈ entailmentRows, ∀ g ∈ x.2.1, ∀ h ∈ x.2.2,
    (x.1 = true ↔ (σ g).Complementary (σ h))) ∧
  ∀ x ∈ bothDeniedRows, ∀ g ∈ x.2.1, ∀ h ∈ x.2.2,
    (x.1 = .acceptable ↔ ¬ (σ g).Complementary (σ h))

/-- The judgments of §3 hold of *believe* and *doubt* exactly when their standards are
complementary endpoints, which excludes the contextual standard of the weak semantics but not a
minimum for *believe* with a maximum for *doubt*; the modifiers of §2 decide between the two. -/
theorem furtherEvidence_iff {s t : PositiveStandard} :
    FurtherEvidence (standardWith s t) ↔ s.Complementary t := by
  rw [FurtherEvidence, comparisonClassRows_eq, entailmentRows_eq, bothDeniedRows_eq]
  cases s <;> cases t <;> decide

theorem furtherEvidence_fragment : FurtherEvidence Gradability.standard := by
  rw [FurtherEvidence, comparisonClassRows_eq, entailmentRows_eq, bothDeniedRows_eq]
  decide

section Credence
variable {α D : Type*} [LinearOrder D] [OrderTop D] (Cr : α → D)

-- (17): *believe* at the maximum standard and *doubt* at the minimum of the reversed scale.
theorem isCompl_maxStandard_minStandard_dual :
    IsCompl (Cr ⁻¹' Set.Ici ⊤) ((OrderDual.toDual ∘ Cr) ⁻¹' Set.Ioi ⊥) :=
  (Kennedy2007.antonyms_isCompl (OrderDual.toDual ∘ Cr)).symm

end Credence

section Likelihood
open MeasureTheory
variable {W : Type*} [MeasurableSpace W] (P : Measure W) {A : Set W} {θ θ' : ℝ}

/-- At a chance of exactly one half a proposition is neither *likely* nor *unlikely* (18), whatever
thresholds the two take on either side of it: relative antonyms leave the gap that *believe* and
*doubt* do not. -/
theorem not_likely_and_not_unlikely (hθ' : θ' ≤ 1 / 2) (hθ : 1 / 2 ≤ θ) (h : P.real A = 1 / 2) :
    A ∉ Lassiter2017.likely P θ ∧ A ∉ P.real ⁻¹' Set.Iio θ' :=
  ⟨(h.trans_le hθ).not_gt, (hθ'.trans_eq h.symm).not_gt⟩

end Likelihood

-- fn. 7: on the totally closed probability scale of [lassiter-2017] both poles would take the
-- maximum, as *full* and *empty* do, and not be contradictory.
theorem not_complementary_probability :
    ¬ (Boundedness.ofOrder Lassiter2017.Probability).defaultStandard.Complementary
        (Boundedness.ofOrder Lassiter2017.Probability).dual.defaultStandard := by
  simp [Lassiter2017.ofOrder_probability, Boundedness.complementary_defaultStandard_dual_iff]

-- fn. 4: without the minimum they are.
theorem complementary_Ioc :
    (Boundedness.ofOrder (Set.Ioc (0 : ℝ) 1)).defaultStandard.Complementary
      (Boundedness.ofOrder (Set.Ioc (0 : ℝ) 1)).dual.defaultStandard := by
  simp [Boundedness.ofOrder_Ioc zero_lt_one, Boundedness.complementary_defaultStandard_dual_iff]

/-! ### Hintikka's semantics (§4) -/

section Hintikka
open MeasureTheory ModalLogic
variable {E W : Type*} [MeasurableSpace W] (Cr : E → W → Measure W)

/-- Hintikka's *believe* (1) over the worlds to which a credence gives positive mass, the
doxastic alternatives being the credence's support ([hintikka-1969]). -/
def hintikka : Doxastic.DoxasticPredicate W E where
  access x := {(w, v) | Cr x w {v} ≠ 0}

/-- *Believe* at the standard Interpretive Economy selects on the credence scale is Hintikka's
*believe* over the credence's support, the universal force of (1): full credence is almost-sure
truth, closed under conjunction as a threshold below the maximum is not. -/
theorem holdsAt_hintikka_iff [DiscreteMeasurableSpace W] [Countable W]
    [∀ x w, IsProbabilityMeasure (Cr x w)] (x : E) (p : Set W) (w : W)
    {U : UpperSet Lassiter2017.Probability}
    (hU : U ∈ (Boundedness.ofOrder Lassiter2017.Probability).defaultStandard.standards _) :
    (hintikka Cr).HoldsAt x (· ∈ p) w ↔ p ∈ Lassiter2017.likelihood (Cr x w) ⁻¹' U := by
  rw [Boundedness.standards_defaultStandard_ofOrder] at hU
  rw [hU, UpperSet.coe_Ici, ← Lassiter2017.certain_eq_preimage,
    Lassiter2017.mem_certain_iff_mem_ae _ .of_discrete, ← Filter.eventually_mem_set,
    ae_iff_of_countable]
  simp [Doxastic.DoxasticPredicate.holdsAt_iff, Doxastic.DoxasticPredicate.IsFactive, hintikka,
    box_iff]

end Hintikka

end Koev2026
