module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.UniformOn

/-!
# Tilted measures

Tilting is invariant under scaling the measure, `(c • μ).tilted f = μ.tilted f` for a finite
nonzero `c`, since the normalization absorbs the factor. On a finite type the tilt reweights each
atom by the exponential of `f` and renormalizes, so tilting the counting measure, or the uniform
measure, gives `Real.softmax f`.

## Main results

* `MeasureTheory.tilted_smul`: tilting is invariant under scaling the measure.
* `MeasureTheory.tilted_real_singleton`, `MeasureTheory.count_tilted_real_singleton`: the tilted
  measure of an atom on a finite type.
* `MeasureTheory.uniformOn_univ_tilted`: tilting the uniform measure on a finite type is tilting
  the counting measure.
* `MeasureTheory.eq_tilted_iff`: a measure on a finite type is a tilt exactly when its atoms are
  proportional to the reweighted ones.
-/

@[expose] public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

section Smul

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

theorem tilted_smul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) : (c • μ).tilted f = μ.tilted f := by
  rw [Measure.tilted, Measure.tilted, integral_smul_measure, withDensity_smul_measure]
  by_cases hz : ∫ x, Real.exp (f x) ∂μ = 0
  · simp [hz]
  ext s hs
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  rw [Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ hc]
  refine lintegral_congr fun x ↦ ?_
  rw [smul_eq_mul, ← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_mul hc'.le,
    ENNReal.toReal_ofReal hc'.le]
  congr 1
  field_simp

theorem uniformOn_univ_tilted [Fintype α] [Nonempty α] :
    (uniformOn Set.univ).tilted f = Measure.count.tilted f := by
  rw [uniformOn, ProbabilityTheory.cond, Measure.restrict_univ, tilted_smul (by simp) (by simp)]

end Smul

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

theorem tilted_real_singleton (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (a : α) :
    (μ.tilted f).real {a} = μ.real {a} * Real.exp (f a) / ∑ b, μ.real {b} * Real.exp (f b) := by
  have hZ : 0 ≤ ∫ x, Real.exp (f x) ∂μ := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  rw [measureReal_def, tilted_apply, lintegral_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ), ← measureReal_def,
    integral_fintype .of_finite]
  simp only [smul_eq_mul]
  ring

theorem eq_tilted_iff (μ ν : Measure α) [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [NeZero ν]
    (f : α → ℝ) : μ = ν.tilted f ↔ ∃ Z > 0, ∀ a, μ.real {a} = ν.real {a} * Real.exp (f a) / Z := by
  have hZ : 0 < ∑ b, ν.real {b} * Real.exp (f b) := by
    obtain ⟨a, ha⟩ : ∃ a, ν {a} ≠ 0 := by
      by_contra! h
      exact NeZero.ne ν (Measure.ext_iff_singleton.2 fun a ↦ by simp [h a])
    exact (mul_pos (ENNReal.toReal_pos ha (measure_ne_top _ _)) (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun b _ ↦ mul_nonneg measureReal_nonneg (Real.exp_pos _).le)
        (Finset.mem_univ a))
  constructor
  · rintro rfl
    exact ⟨_, hZ, tilted_real_singleton ν f⟩
  · rintro ⟨Z, hZ0, h⟩
    have hZeq : Z = ∑ b, ν.real {b} * Real.exp (f b) := by
      have := sum_measureReal_singleton_eq_one μ
      simp_rw [h, ← Finset.sum_div] at this
      exact ((div_eq_one_iff_eq hZ0.ne').1 this).symm
    have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted .of_finite
    refine Measure.ext_iff_singleton.2 fun a ↦ ?_
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
      ← measureReal_def, ← measureReal_def, h, tilted_real_singleton, hZeq]

theorem count_tilted_real_singleton (f : α → ℝ) (a : α) :
    (Measure.count.tilted f).real {a} = Real.softmax f a := by
  simp [tilted_real_singleton, Real.softmax_apply]


end MeasureTheory
