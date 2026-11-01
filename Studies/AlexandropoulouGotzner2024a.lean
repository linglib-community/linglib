module

public import Studies.Krifka2007b
public import Linglib.Fragments.English.Adjectives
public import Linglib.Data.Examples.AlexandropoulouGotzner2024a
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Experiments.AlexandropoulouGotzner2024a

/-!
# Alexandropoulou and Gotzner (2024a): relative and absolute adjectives under negation

This file sets Horn's account of negative strengthening against Krifka's on antonymic adjectives
under negation. On Horn's, *not large* is R-strengthened to its antonym *small* and *not small* is
restricted to the semantic gap left by its simpler antonym *large*, an asymmetric pattern. On
Krifka's, the M principle gives each negated form the non-stereotypical part of its co-extensive
antonym's range, a symmetric pattern, unless *small* carries a covert negative morpheme, as
Ruytenbeek, Verheyen and Spector's Negative Adjectives Complexity Hypothesis (NACH) has it, so that
[*not small* deviates further](##deviation_eq_iff). Horn's account needs a semantic gap and
Krifka's a co-extensive antonym, so [weak relative, weak absolute and strong pairs pull the two
apart](##table1). Two rating experiments found [an asymmetry for the weak relative pair
only](##finding_eq_asymmetric_iff), the pattern [Horn's account predicts](##horn_confirmed_on_weak)
and [Krifka's does not, whatever the cost of the covert morpheme](##krifka_refuted).

## Implementation notes

* The paper's positive and negative adjectives are the evaluatively positive and negative ones.
  On the four pairs used here they are the Fragment's positive and negative poles, which
  `row_factors` checks on the stimuli. The paper itself orients the absolute scale by dirtiness,
  with *dirty* the dimensionally positive pole; either orientation gives the same complementary
  standards.
* A cell of the design is represented by the pair of its example item, *gigantic* for the relative
  adjectives and *pristine* for the absolute ones.
* Communicated ranges are sets of Krifka's four regions, ordered along the scale. Horn's
  antonyms take the contrary denotation with thresholds at the two border regions, which form the
  semantic gap; Krifka's take the contradictory one.
* NACH is a complexity cost of the negative pole. The complexity on which Krifka's quadruplet is
  computed already has that shape (`complexity_eq_cost`), yet weak optimality returns a symmetric
  quadruplet, since it compares two pairs only when they share a form or an interpretation. NACH's
  asymmetry is one of degree, the difference in stereotype deviation of the two negated forms.
* A cell is interpreted asymmetrically when its Negation effect is significant at .05; the
  marginal effect for strong absolute pairs counts as no asymmetry, as in the paper.

## References

* [alexandropoulou-gotzner-2024a]
* [horn-1989]
* [krifka-2007b]
* [ruytenbeek-verheyen-spector-2017]
* [buring-2007]
-/

@[expose] public section

namespace AlexandropoulouGotzner2024a

open Degree Krifka2007b English.Adjectives Data.Experiments
open AntonymForm (strengthenedDenotation strengthenedDenotation_notNegative_diff_positive)

variable {t : AdjectiveType} {s : Strength}

/-! ### Design cells -/

/-- The antonym pair of a cell in the example items *gigantic* and *pristine* (Tables 2 and 3),
its positive pole the evaluatively positive member. -/
def pair : AdjectiveType → Strength → AntonymPair
  | .relative, .weak => size
  | .relative, .strong => extremeSize
  | .absolute, .weak => cleanliness
  | .absolute, .strong => pristineness

theorem pair_standard_eq_extreme_iff : (pair t s).pos.standard = .extreme ↔ s = .strong := by
  revert t s; decide

theorem pair_isRelative_iff : (pair t s).pos.boundedness.IsRelative ↔ t = .relative := by
  revert t s; decide

theorem complementaryStandards_pair_iff :
    (pair t s).ComplementaryStandards ↔ t = .absolute ∧ s = .weak := by
  revert t s; decide

/-! ### Communicated ranges -/

/-- A `Ranges` assigns each surface form the scale regions it may communicate. -/
abbrev Ranges := AntonymForm → Finset Region

/-- A negated antonym pair is interpreted asymmetrically when the negated positive and the negated
negative forms diverge, and symmetrically when they behave in parallel. -/
inductive Asymmetry where
  | asymmetric
  | symmetric
  deriving Repr, DecidableEq, Fintype

/-- Positive and negative forms communicate mirror-image ranges. -/
def Ranges.Symmetric (r : Ranges) : Prop := ∀ f, r f.flip = (r f).image Region.flip

instance (r : Ranges) : Decidable r.Symmetric := Fintype.decidableForallFintype

/-- The interpretation pattern of a `Ranges`. -/
def Ranges.asymmetry (r : Ranges) : Asymmetry :=
  if r.Symmetric then .symmetric else .asymmetric

/-- Horn's antonyms are contrary, with the thresholds of `hornPair`, whose gap is the two border
regions. -/
def hornPair : ThresholdPair Region := ⟨.plateauHigh, .plateauLow⟩

/-- Horn's ranges R-strengthen the negated positive to the antonym it conceals, a face-threatening
statement, and Q/R-restrict the double negative to what its simpler antonym could not describe. -/
def hornRanges : Ranges
  | .notPositive => (strengthenedDenotation hornPair .negative).toFinset
  | .notNegative => (strengthenedDenotation hornPair .notNegative \
      strengthenedDenotation hornPair .positive).toFinset
  | f => (strengthenedDenotation hornPair f).toFinset

-- (7), p. 376
theorem coe_hornRanges_notNegative : (hornRanges .notNegative : Set Region) = hornPair.gap :=
  (Set.coe_toFinset _).trans (strengthenedDenotation_notNegative_diff_positive _)

/-- Krifka's ranges are the quadruplet that weak optimality selects
(`Krifka2007b.superoptimal_quadruplet`). -/
def krifkaRanges : Ranges := fun f ↦ (krifkaQuadruplet.filter (·.1 = f)).image (·.2)

theorem hornRanges_asymmetric : hornRanges.asymmetry = .asymmetric := by decide

theorem krifkaRanges_symmetric : krifkaRanges.asymmetry = .symmetric := by decide

/-! ### The Negative Adjectives Complexity Hypothesis -/

/-- The complexity of a form whose sentential negation costs `n` and whose negative pole costs `k`
more than its positive pole, as the covert negative morpheme of [buring-2007] would under NACH
([ruytenbeek-verheyen-spector-2017]); without NACH, `k = 0`. -/
def cost (n k : ℕ) : AntonymForm → ℕ
  | .positive => 0
  | .negative => k
  | .notPositive => n
  | .notNegative => n + k

theorem complexity_eq_cost : AntonymForm.complexity = cost 3 2 := by
  funext f; cases f <;> rfl

/-- The stereotype deviation of a form is its excess complexity over the co-extensive simple form,
which the M principle turns into a non-stereotypical reading. -/
def deviation (n k : ℕ) (f : AntonymForm) : ℤ := cost n k f - cost n k (simple f)

-- p. 378
theorem deviation_eq_iff (n k : ℕ) :
    deviation n k .notPositive = deviation n k .notNegative ↔ k = 0 := by
  simp only [deviation, cost, simple]
  omega

/-! ### Predictions -/

/-- Horn's prediction for a cell, made where its pair leaves a semantic gap. -/
def horn (t : AdjectiveType) (s : Strength) : Option Asymmetry :=
  if (pair t s).ComplementaryStandards then none else some hornRanges.asymmetry

/-- Krifka's prediction for a cell, with negation cost `n` and negative-pole cost `k`. It is made
where the negated forms have co-extensive simple antonyms, by bivalence for relative pairs and by
entailment for absolute ones, which an extreme pair with its semantic gap lacks. Negated forms
that deviate equally get Krifka's ranges, and unequal deviations an asymmetry. -/
def krifka (n k : ℕ) (t : AdjectiveType) (s : Strength) : Option Asymmetry :=
  if (pair t s).pos.standard = .extreme then none
  else some (if deviation n k .notPositive = deviation n k .notNegative then krifkaRanges.asymmetry
    else .asymmetric)

/-- Table 1: Horn's account predicts an asymmetry except for the gapless weak absolute pairs, and
Krifka's predicts symmetry without NACH and an asymmetry with it, for the weak pairs only. -/
theorem table1 (t : AdjectiveType) (s : Strength) (n k : ℕ) :
    horn t s = (if t = .absolute ∧ s = .weak then none else some .asymmetric) ∧
      krifka n k t s =
        if s = .strong then none else some (if k = 0 then .symmetric else .asymmetric) := by
  simp only [horn, krifka, complementaryStandards_pair_iff, pair_standard_eq_extreme_iff,
    deviation_eq_iff, hornRanges_asymmetric, krifkaRanges_symmetric, and_self]

/-! ### Findings -/

/-- A cell is interpreted asymmetrically when its Negation effect is significant at .05. -/
def finding (t : AdjectiveType) (s : Strength) : Asymmetry :=
  if (negationEffect t s).p.Significant (1 / 20) then .asymmetric else .symmetric

theorem finding_eq (t : AdjectiveType) (s : Strength) :
    finding t s = if t = .relative ∧ s = .weak then .asymmetric else .symmetric := by
  revert t s; decide +kernel

/-- Only the weak relative pairs were interpreted asymmetrically under negation (pp. 390–391). -/
theorem finding_eq_asymmetric_iff : finding t s = .asymmetric ↔ t = .relative ∧ s = .weak := by
  simp [finding_eq]

/-- Horn's account matches the pattern on both weak pairs, the contradictory absolute pair, to
which it does not apply, being interpreted symmetrically (pp. 380, 393). -/
theorem horn_confirmed_on_weak (t : AdjectiveType) :
    (horn t .weak).getD .symmetric = finding t .weak := by
  cases t <;> simp [(table1 _ _ 0 0).1, finding_eq]

-- p. 393
theorem horn_unsupported_on_strong (t : AdjectiveType) :
    horn t .strong ≠ some (finding t .strong) := by
  simp [(table1 _ _ 0 0).1, finding_eq]

/-- Whatever the cost of the negative pole, Krifka's account mispredicts one of the weak pairs
(p. 393). -/
theorem krifka_refuted (n k : ℕ) : ∃ t, krifka n k t .weak ≠ some (finding t .weak) := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨.relative, by simp [(table1 _ _ n 0).2, finding_eq]⟩
  · exact ⟨.absolute, by simp [(table1 _ _ n k).2, hk, finding_eq]⟩

/-- An asymmetry arose only where the pair leaves a semantic gap (p. 393). -/
theorem gap_precondition : finding t s = .asymmetric → ¬ (pair t s).ComplementaryStandards := by
  simp +contextual [finding_eq_asymmetric_iff, complementaryStandards_pair_iff]

/-! ### Rows -/

/-- `formOf row` is the surface form of a statement row, read off its polarity and negation
conditions. -/
def formOf (row : Datum) : Option AntonymForm :=
  match row.feature? "polarity", row.feature? "negation" with
  | some "positive", some "nonNegated" => some .positive
  | some "positive", some "negated" => some .notPositive
  | some "negative", some "nonNegated" => some .negative
  | some "negative", some "negated" => some .notNegative
  | _, _ => none

theorem row_factors :
    ∀ row ∈ Examples.all, ∀ a ∈ (row.feature? "adjective").bind lookup,
      (row.feature? "strength" = some "strong" ↔ a.standard = .extreme) ∧
        (row.feature? "adjectiveType" = some "relative" ↔ a.boundedness.IsRelative) ∧
        (row.feature? "polarity" = some "positive" ↔ a.polarity = .positive) := by
  decide

theorem negated_iff_not :
    ∀ row ∈ Examples.all, ∀ n ∈ row.feature? "negation",
      (n = "negated" ↔ " not ".toList <:+: row.primaryText.toList) := by
  decide

end AlexandropoulouGotzner2024a
