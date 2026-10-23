module

public import Linglib.Core.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Moments.Basic

/-!
# The Gibbs variational principle  [UPSTREAM]

For a probability measure `μ` and a function `f`, the free energy `𝔼_q[f] - KL(q ‖ μ)` of a
probability measure `q ≪ μ` is at most the cumulant generating function `cgf f μ 1`, with
equality exactly at the tilted measure `μ.tilted f`. This is the Gibbs, or Donsker–Varadhan,
variational principle, which the module docstring of `Mathlib/MeasureTheory/Measure/Tilted.lean`
anticipates.

## Main definitions

* `MeasureTheory.Measure.freeEnergy`: the free energy `𝔼_q[f] - KL(q ‖ μ)`.

## Main statements

* `InformationTheory.toReal_klDiv_tilted_right`: the decomposition
  `KL(q ‖ μ.tilted f) = KL(q ‖ μ) - 𝔼_q[f] + cgf f μ 1`.
* `InformationTheory.freeEnergy_le_cgf`, `InformationTheory.freeEnergy_tilted`,
  `InformationTheory.eq_tilted_of_freeEnergy_eq_cgf`: the free energy is at most `cgf f μ 1`,
  with equality exactly at `μ.tilted f`.
* `InformationTheory.isGreatest_cgf`: `cgf f μ 1` is the greatest free energy.

## Implementation notes

The decomposition repackages `MeasureTheory.integral_llr_tilted_right` at the `klDiv` level:
`μ.tilted f` is a probability measure, so both `klDiv` terms collapse to their `llr`-integrals
via `toReal_klDiv_of_measure_eq`. The candidate `q` is pinned to `[IsProbabilityMeasure]` by
`integral_llr_tilted_right`, which requires it on its left measure, so relaxing it is a separate
upstream concern in `LogLikelihoodRatio`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The free energy `𝔼_q[f] - KL(q ‖ μ)` of a measure `q`, relative to `μ` and `f`. -/
noncomputable def Measure.freeEnergy (μ : Measure α) (f : α → ℝ) (q : Measure α) : ℝ :=
  (∫ a, f a ∂q) - (klDiv q μ).toReal

end MeasureTheory

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

theorem toReal_klDiv_tilted_right (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x ↦ Real.exp (f x)) μ) :
    (klDiv q (μ.tilted f)).toReal = (klDiv q μ).toReal - (∫ x, f x ∂q) + cgf f μ 1 := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have hq_tilt : q ≪ μ.tilted f := hqμ.trans (absolutelyContinuous_tilted h_exp)
  rw [toReal_klDiv_of_measure_eq hq_tilt (by simp only [measure_univ]),
      toReal_klDiv_of_measure_eq hqμ (by simp only [measure_univ]),
      integral_llr_tilted_right hqμ h_int_f h_exp h_int_llr]
  simp only [cgf, mgf, one_mul]

theorem freeEnergy_le_cgf (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x ↦ Real.exp (f x)) μ) :
    μ.freeEnergy f q ≤ cgf f μ 1 := by
  have h := toReal_klDiv_tilted_right μ q hqμ h_int_llr h_int_f h_exp
  have hnn : 0 ≤ (klDiv q (μ.tilted f)).toReal := ENNReal.toReal_nonneg
  rw [Measure.freeEnergy]
  linarith

theorem freeEnergy_tilted (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x ↦ Real.exp (f x)) μ) :
    μ.freeEnergy f (μ.tilted f) = cgf f μ 1 := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have h := toReal_klDiv_tilted_right μ (μ.tilted f) (tilted_absolutelyContinuous μ f)
    h_int_llr h_int_f h_exp
  rw [klDiv_self, ENNReal.toReal_zero] at h
  rw [Measure.freeEnergy]
  linarith

theorem eq_tilted_of_freeEnergy_eq_cgf (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x ↦ Real.exp (f x)) μ)
    (h : μ.freeEnergy f q = cgf f μ 1) : q = μ.tilted f := by
  have : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have hkl : (klDiv q (μ.tilted f)).toReal = 0 := by
    rw [toReal_klDiv_tilted_right μ q hqμ h_int_llr h_int_f h_exp]
    rw [Measure.freeEnergy] at h
    linarith
  have hne : klDiv q (μ.tilted f) ≠ ⊤ := klDiv_ne_top_iff.2
    ⟨hqμ.trans (absolutelyContinuous_tilted h_exp),
      integrable_llr_tilted_right hqμ h_int_f h_int_llr h_exp⟩
  exact klDiv_eq_zero_iff.1 (((ENNReal.toReal_eq_zero_iff _).1 hkl).resolve_right hne)

theorem isGreatest_cgf (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x ↦ Real.exp (f x)) μ) :
    IsGreatest (μ.freeEnergy f '' {q | IsProbabilityMeasure q ∧ q ≪ μ ∧
        Integrable (llr q μ) q ∧ Integrable f q}) (cgf f μ 1) := by
  refine ⟨⟨μ.tilted f, ⟨isProbabilityMeasure_tilted h_exp, tilted_absolutelyContinuous μ f,
      h_int_llr, h_int_f⟩, freeEnergy_tilted μ h_int_f h_int_llr h_exp⟩, ?_⟩
  rintro x ⟨q, ⟨hq_prob, hqμ, hq_llr, hq_f⟩, rfl⟩
  exact freeEnergy_le_cgf μ q hqμ hq_llr hq_f h_exp

end InformationTheory
