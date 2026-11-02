/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Moments of a convolution  `[UPSTREAM]`

The convolution `μ ∗ ν` of two probability measures on `ℝ` is the law of the sum of independent
draws from `μ` and `ν`, so its mean is the sum of the means and its variance the sum of the
variances. The second moment of a law about any point is its variance plus the squared distance
of its mean from the point.

## Main statements

* `ProbabilityTheory.integral_id_conv`: the mean of a convolution.
* `ProbabilityTheory.variance_id_conv`: the variance of a convolution.
* `ProbabilityTheory.integral_sub_sq`: the second moment about a point.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem memLp_id_conv {p : ENNReal} (hμ : MemLp id p μ) (hν : MemLp id p ν) :
    MemLp id p (μ ∗ ν) := by
  rw [Measure.conv, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

theorem integral_id_conv (hμ : Integrable id μ) (hν : Integrable id ν) :
    ∫ x, x ∂(μ ∗ ν) = ∫ x, x ∂μ + ∫ x, x ∂ν := by
  have h1 : Integrable (fun p : ℝ × ℝ ↦ p.1) (μ.prod ν) := hμ.comp_fst ν
  have h2 : Integrable (fun p : ℝ × ℝ ↦ p.2) (μ.prod ν) := hν.comp_snd μ
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop), integral_add h1 h2,
    integral_fun_fst (fun t : ℝ ↦ t), integral_fun_snd (fun t : ℝ ↦ t)]
  simp

theorem variance_id_conv (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    Var[id; μ ∗ ν] = Var[id; μ] + Var[id; ν] := by
  have := (indepFun_prod (μ := μ) (ν := ν) measurable_id measurable_id).variance_add
    (hμ.comp_fst ν) (hν.comp_snd μ)
  simp only [id] at this
  rw [Measure.conv, variance_id_map (by fun_prop),
    show (fun x : ℝ × ℝ ↦ x.1 + x.2) = (fun ω ↦ ω.1) + fun ω ↦ ω.2 from rfl, this,
    ← variance_id_map measurable_fst.aemeasurable, ← variance_id_map measurable_snd.aemeasurable,
    Measure.map_fst_prod, Measure.map_snd_prod]
  simp

theorem integral_sub_sq (hμ : MemLp id 2 μ) (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂μ = Var[id; μ] + (∫ x, x ∂μ - c) ^ 2 := by
  have h1 : Integrable (fun x : ℝ ↦ x) μ := hμ.integrable one_le_two
  have h2 : Integrable (fun x : ℝ ↦ x ^ 2) μ := hμ.integrable_sq
  have h3 : Integrable (fun x : ℝ ↦ 2 * c * x) μ := h1.const_mul _
  have h4 : Integrable (fun x : ℝ ↦ x ^ 2 - 2 * c * x) μ := h2.sub h3
  rw [variance_eq_sub hμ]
  calc ∫ x, (x - c) ^ 2 ∂μ = ∫ x, (x ^ 2 - 2 * c * x + c ^ 2) ∂μ :=
        integral_congr_ae (.of_forall fun x ↦ by ring)
    _ = _ := by
      rw [integral_add h4 (integrable_const _), integral_sub h2 h3, integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul, id, Pi.pow_apply]
      ring

end ProbabilityTheory
