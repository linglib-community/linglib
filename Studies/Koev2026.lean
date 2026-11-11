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
comparison with Hintikka needs them. A row's endpoint modifier is read off its words; the
predicates of the antonym and comparison-class rows are named by form and looked up in a table
built from the fragment's entries. The fragment has no *likely*, whose scale is disputed, so the
comparison-class row for *likely* is not read and the gap of *likely* and *unlikely* is stated on
Lassiter's threshold semantics.

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

/-- The endpoint modifier among the words of a row about *believe*. -/
def modifier? (e : Datum) : Option EndpointModifier :=
  if e.feature? "predicate" = some believe.form then
    (Datum.wordsOf e.primaryText).findSome? fun w ↦
      (endpointModifiers.find? (·.1.toList = w)).map (·.2)
  else none

/-- A scale fits the modifier judgments of *believe* when each of the rows (12a)–(12c) and fn. 4
is accepted exactly if the scale licenses its modifier. -/
def FitsModifiers (b : Boundedness) : Prop :=
  Datum.Checks modifier? (fun m ↦ .ofProp (b.Licenses m)) Examples.all 4

instance : DecidablePred FitsModifiers :=
  fun b ↦ inferInstanceAs (Decidable (Datum.Checks modifier? (fun m ↦ .ofProp (b.Licenses m)) _ _))

/-- The modifier judgments fit the upper closed scale and no other, since the maximizers of (12)
need a maximum and the minimizer of fn. 4 excludes a minimum. -/
theorem fitsModifiers_iff {b : Boundedness} : FitsModifiers b ↔ b = .upperClosed := by
  cases b <;> decide +kernel

-- §2: Interpretive Economy selects the maximum standard on that scale and excludes the contextual
-- standard of the weak semantics, (6b).
theorem defaultStandard_of_fitsModifiers {b : Boundedness} (h : FitsModifiers b) :
    b.defaultStandard = .maxEndpoint ∧ ¬ b.Admits .contextual := by
  obtain rfl := fitsModifiers_iff.1 h
  decide

theorem believe_fitsModifiers : ∃ b ∈ believe.boundedness, FitsModifiers b := by
  decide +kernel

-- §2, first remark: licensed by the standard of the positive form, as [lassiter-2017] licenses
-- them, the modifiers fix the maximum standard without Interpretive Economy.
theorem checks_licensesPos_iff {s : PositiveStandard} :
    Datum.Checks modifier? (fun m ↦ .ofProp (Lassiter2017.LicensesPos m s)) Examples.all 4 ↔
      s = .maxEndpoint := by
  cases s <;> decide +kernel

/-- The weak semantics makes *believe* a verbal *confident*: the fragment's *confident* is on the
scale of *believe* with the contextual standard of [cariani-santorio-wellwood-2024], a standard
Interpretive Economy does not admit there, so the argument from the scale does not extend to it. -/
theorem confident_not_admits :
    ∃ g ∈ confident.gradability?, believe.boundedness = some g.boundedness ∧
      g.standard = .contextual ∧ ¬ g.boundedness.Admits g.standard := by
  decide

/-! ### Further evidence (§3) -/

/-- The positive standards of the predicates of §3 by form, the fragment's for the adjectives and
`s` and `t` for *believe* and *doubt*. -/
def standards (s t : PositiveStandard) : List (String × PositiveStandard) :=
  [tall, short, bent, straight, full].filterMap (fun a ↦ a.standard.map (a.form, ·)) ++
    [(believe.form, s), (doubt.form, t)]

variable (σ : List (String × PositiveStandard))

/-- The standard of the predicate of a row with an overt comparison class. -/
def comparisonClass? (e : Datum) : Option PositiveStandard :=
  if e.feature? "comparisonClass" = some "overt" then e.parse? "predicate" σ else none

/-- The standards of the pole a row denies and of its antonym. -/
def denial? (e : Datum) : Option (PositiveStandard × PositiveStandard) :=
  (e.parse? "negated" σ).bind fun s ↦ (e.parse? "antonym" σ).map (s, ·)

/-- The judgments of §3 are as the standards `σ` predict. An overt comparison class is acceptable
exactly with a standard that requires one ((13), (14b), fn. 6); denying a pole entails its antonym
exactly when the two standards are complementary ((15a), (16a), (17a)); and denying both poles is
acceptable exactly when they are not ((15b), (16b), (17b)). -/
def FurtherEvidence : Prop :=
  (∀ e ∈ Examples.all, ∀ s ∈ comparisonClass? σ e,
    (e.judgment = .acceptable ↔ s.RequiresComparisonClass)) ∧
  (∀ e ∈ Examples.all, ∀ p ∈ denial? σ e, ∀ r ∈ e.feature? "relation",
    (r = "entails" ↔ p.1.Complementary p.2)) ∧
  (∀ e ∈ Examples.all, e.feature? "construction" = some "doubleDenial" → ∀ p ∈ denial? σ e,
    (e.judgment = .acceptable ↔ ¬ p.1.Complementary p.2)) ∧
  Datum.ReadCount (comparisonClass? σ) Examples.all 4 ∧ Datum.ReadCount (denial? σ) Examples.all 6

instance : Decidable (FurtherEvidence σ) := by unfold FurtherEvidence; infer_instance

variable {σ}

/-- The judgments of §3 hold of *believe* and *doubt* exactly when their standards are
complementary endpoints, which excludes the contextual standard of the weak semantics but not a
minimum for *believe* with a maximum for *doubt*; the modifiers of §2 decide between the two. -/
theorem furtherEvidence_iff {s t : PositiveStandard} :
    FurtherEvidence (standards s t) ↔ s.Complementary t := by
  cases s <;> cases t <;> decide +kernel

theorem furtherEvidence_fragment :
    ∃ s ∈ believe.standard, ∃ t ∈ doubt.standard, FurtherEvidence (standards s t) := by
  decide +kernel

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

/-- *Believe* at the maximum standard of the credence scale is Hintikka's *believe* over the
credence's support, the universal force of (1). -/
theorem holdsAt_hintikka_iff [DiscreteMeasurableSpace W] [Countable W]
    [∀ x w, IsProbabilityMeasure (Cr x w)] (x : E) (p : Set W) (w : W) :
    (hintikka Cr).HoldsAt x (· ∈ p) w ↔ p ∈ Lassiter2017.likelihood (Cr x w) ⁻¹' Set.Ici ⊤ := by
  rw [← Lassiter2017.certain_eq_preimage, Lassiter2017.mem_certain_iff,
    measureReal_def, ENNReal.toReal_eq_one_iff, ← mem_ae_iff_prob_eq_one .of_discrete,
    ← Filter.eventually_mem_set, ae_iff_of_countable]
  simp [Doxastic.DoxasticPredicate.holdsAt_iff, hintikka, box_iff]

end Hintikka

end Koev2026
