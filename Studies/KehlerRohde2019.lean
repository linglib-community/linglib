module

public import Studies.KehlerRohde2013
public import Linglib.Data.Statistics.KehlerRohde2019

/-!
# Kehler and Rohde (2019): Prominence and coherence in a Bayesian theory of pronoun interpretation

No single notion of prominence mediates between producing a pronoun and resolving one: the
interpretation of a pronoun is Bayes' rule over a next-mention prior and a production rate, which
answer to different factors. The two rival models are its halves, [the Mirror Model the Bayesian
model against a uniform prior and the Expectancy Model the Bayesian model with constant
production](##mirror_expectancy), and the Bayesian odds of two referents are [the Mirror odds times
the Expectancy odds](##bayesian_odds). One prior and one production rate [print as all three
columns of Table 4](##objectReference_eq), and [the Bayesian prediction is the closest to the
observed interpretation, with the best fit](##bayesian_closest).

## Implementation notes

* A model's prediction is a measure on the subject and the object of an object-biased
  implicit-causality context; the pronoun prompt is the one form conditioned on.
* The PDF read is the accepted manuscript, whose pagination differs from the journal's; tables
  are cited by number.

## TODO

* -- UNVERIFIED: the accepted manuscript's Table 3 prints the effect of the relative clause on
  pronominalization as z = 2.34, p = 0.08, though its coefficient over its standard error is 2.24
  and either z gives p of about 0.02 to 0.03; in Table 2 the z of the RC×Prompt row and of the
  FreePrompt RC row also differ from coefficient over standard error. Check the published tables.
* -- UNVERIFIED: the manuscript writes the production rate as P(referent | pronoun) where it
  states the third prediction, the reverse of its definition at (3).

## References

* [kehler-rohde-2019]
* [kehler-rohde-2013]
-/

@[expose] public section

namespace KehlerRohde2019

open MeasureTheory ProbabilityTheory KehlerRohde2013
open scoped ENNReal

/-! ### The three models -/

section Models

variable {R : Type*} [MeasurableSpace R] [Fintype R] [MeasurableSingletonClass R]
  (μ : Measure R) (ρ : R → ℝ≥0∞)

/-- The Bayesian Model (3) interprets a pronoun by reweighting the next-mention prior `μ` by the
production rate `ρ`, normalized. -/
noncomputable def bayesian : Measure R := Kernel.ofDensity μ (fun (_ : Unit) r ↦ ρ r) ()

/-- The Mirror Model (10) interprets a pronoun by the normalized production rate. -/
noncomputable def mirror : Measure R := Kernel.ofWeights (fun (_ : Unit) r ↦ ρ r) ()

/-- The Expectancy Model (11) interprets a pronoun by the normalized next-mention prior. -/
noncomputable def expectancy : Measure R := μ[|Set.univ]

/-- The Mirror Model is the Bayesian model against the counting measure, a uniform prior, and the
Expectancy Model is the Bayesian model with a production rate constant across referents. -/
theorem mirror_expectancy {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    mirror ρ = bayesian Measure.count ρ ∧ expectancy μ = bayesian μ fun _ ↦ c := by
  refine ⟨by rw [mirror, bayesian, Kernel.ofDensity_count], ?_⟩
  rw [expectancy, bayesian, Kernel.ofDensity_apply_eq_of_eq_mul μ (f := fun _ _ ↦ 1) hc0 hc
    fun _ ↦ (mul_one c).symm, Kernel.ofDensity_apply]
  congr 1
  exact (withDensity_one (μ := μ)).symm

/-- The Bayesian odds of two referents are the Mirror odds times the Expectancy odds, the
production ratio times the prior odds. -/
theorem bayesian_odds (a b : R) :
    bayesian μ ρ {a} * (mirror ρ {b} * expectancy μ {b}) =
      bayesian μ ρ {b} * (mirror ρ {a} * expectancy μ {a}) := by
  simp only [bayesian, mirror, expectancy, Kernel.ofDensity_apply_singleton,
    Kernel.ofWeights_apply_singleton, cond_apply MeasurableSet.univ, Set.univ_inter, div_eq_mul_inv]
  ring

end Models

/-! ### Table 4 -/

/-- The two referents of an object-biased implicit-causality context. -/
inductive Referent where
  | subject
  | object
  deriving DecidableEq, Fintype

instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- Weights in ten-thousandths, `w` on the object and the rest on the subject. -/
def weights (w : ℕ) : Referent → ℕ
  | .subject => 10000 - w
  | .object => w

private theorem bayesian_real_object (μ : Measure Referent) [IsFiniteMeasure μ]
    (ρ : Referent → ℝ≥0∞) (hρ : ∀ r, ρ r ≠ ∞) :
    (bayesian μ ρ).real {.object} = (ρ .object).toReal * μ.real {.object} /
      ((ρ .subject).toReal * μ.real {.subject} + (ρ .object).toReal * μ.real {.object}) := by
  rw [bayesian, Kernel.ofDensity_real_singleton μ _ () hρ,
    show (Finset.univ : Finset Referent) = {.subject, .object} by decide,
    Finset.sum_pair (by decide)]

/-- One prior and one production rate print as all three predictions of Table 4: the Mirror and
Expectancy columns, and the Bayesian column that combines them. -/
theorem objectReference_eq (c : RC) :
    ∃ m e : ℕ, RoundsTo ((mirror fun r ↦ (weights m r : ℝ≥0∞)).real {.object})
        (objectReference c).mirror ∧
      RoundsTo ((expectancy (∑ r, (weights e r : ℝ≥0∞) • Measure.dirac r)).real
        {.object}) (objectReference c).expectancy ∧
      RoundsTo ((bayesian (∑ r, (weights e r : ℝ≥0∞) • Measure.dirac r)
        fun r ↦ (weights m r : ℝ≥0∞)).real {.object}) (objectReference c).bayesian := by
  have hm (m : ℕ) : mirror (fun r ↦ (weights m r : ℝ≥0∞)) =
      bayesian Measure.count fun r ↦ (weights m r : ℝ≥0∞) :=
    (mirror_expectancy Measure.count _ one_ne_zero ENNReal.one_ne_top).1
  have he (e : ℕ) : expectancy (∑ r, (weights e r : ℝ≥0∞) • Measure.dirac r) =
      bayesian (∑ r, (weights e r : ℝ≥0∞) • Measure.dirac r) fun _ ↦ 1 :=
    (mirror_expectancy _ (fun _ ↦ (1 : ℝ≥0∞)) one_ne_zero ENNReal.one_ne_top).2
  cases c
  on_goal 1 => refine ⟨3214, 3854, ?_, ?_, ?_⟩
  on_goal 4 => refine ⟨3344, 5424, ?_, ?_, ?_⟩
  all_goals
    (try rw [hm]); (try rw [he])
    rw [bayesian_real_object _ _ (fun _ ↦ by simp)]
    simp only [measureReal_def, Measure.finsetSum_smul_dirac_singleton, weights,
      ENNReal.toReal_natCast, ENNReal.toReal_one, RoundsTo, objectReference,
      Data.Statistics.Decimal.toRat, abs_le]
    norm_num

/-- The Bayesian prediction is the closest of the three to the observed rate of reference to the
object in both conditions, and it fits best over participants and over items. -/
theorem bayesian_closest :
    (∀ c, |(objectReference c).actual.toRat - (objectReference c).bayesian.toRat| <
        |(objectReference c).actual.toRat - (objectReference c).mirror.toRat| ∧
      |(objectReference c).actual.toRat - (objectReference c).bayesian.toRat| <
        |(objectReference c).actual.toRat - (objectReference c).expectancy.toRat|) ∧
    ∀ m, m ≠ .bayesian → (fit m).participants.toRat < (fit .bayesian).participants.toRat ∧
      (fit m).items.toRat < (fit .bayesian).items.toRat := by
  refine ⟨fun c ↦ ?_, fun m hm ↦ ?_⟩
  · cases c <;> norm_num [objectReference, Data.Statistics.Decimal.toRat, abs_of_nonneg,
      abs_of_nonpos]
  · cases m <;> first
      | exact absurd rfl hm
      | norm_num [fit, Data.Statistics.Decimal.toRat]

end KehlerRohde2019
