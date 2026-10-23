/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Regularity of the cdf of a real probability measure

Each regularity property of `ProbabilityTheory.cdf μ` is the image of a property of `μ`, read off
the Stieltjes function `cdf μ` whose measure is `μ`. The cdf is continuous exactly at the points
that are not atoms, strictly monotone when `μ` charges every nonempty open set, and, when `μ` has no
atoms, satisfies the reflection formula `cdf μ (-x) = 1 - cdf μ x` exactly when `μ` is invariant
under negation. A measure with the first two properties has a cdf that is an order isomorphism from
`ℝ` onto `(0, 1)`, whose inverse is the quantile function. `[UPSTREAM]` candidate for
`Mathlib/Probability/CDF.lean`.

## Main definitions

* `ProbabilityTheory.cdfOrderIso`: the cdf as an order isomorphism `ℝ ≃o Ioo 0 1`.

## Main results

* `ProbabilityTheory.continuousAt_cdf_iff`: the cdf is continuous at `x` iff `μ {x} = 0`.
* `ProbabilityTheory.strictMono_cdf`: the cdf of an open-positive measure is strictly monotone.
* `ProbabilityTheory.measureReal_Ioi_eq_cdf_neg`: the upper tail of a negation-invariant measure
  is the cdf at the reflected point.
* `ProbabilityTheory.cdf_neg`: the reflection formula for a negation-invariant measure.
* `ProbabilityTheory.isNegInvariant_iff_cdf_neg`: a measure without atoms is negation-invariant iff
  its cdf satisfies the reflection formula.
* `ProbabilityTheory.range_cdf`: the cdf of an atomless open-positive measure has range `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Pointwise

namespace ProbabilityTheory

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}

/-! ### Continuity -/

theorem continuousAt_cdf_iff : ContinuousAt (cdf μ) x ↔ μ {x} = 0 := by
  rw [StieltjesFunction.continuousAt_iff_measure_singleton_eq_zero, measure_cdf]

theorem continuous_cdf [NullSingletonClass μ] : Continuous (cdf μ) :=
  (cdf μ).continuous_iff_nullSingletonClass.2 (by rw [measure_cdf]; infer_instance)

/-! ### Reflection -/

theorem measureReal_Ioi_eq_cdf_neg [μ.IsNegInvariant] (hx : μ {x} = 0) :
    μ.real (Ioi x) = cdf μ (-x) := by
  rw [cdf_eq_real, ← neg_Ici, measureReal_congr (Ioi_ae_eq_Ici' hx), measureReal_def,
    measureReal_def, μ.measure_neg]

theorem cdf_neg [μ.IsNegInvariant] (hx : μ {x} = 0) : cdf μ (-x) = 1 - cdf μ x := by
  rw [← measureReal_Ioi_eq_cdf_neg μ hx, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    cdf_eq_real]

theorem cdf_zero [μ.IsNegInvariant] (h : μ {0} = 0) : cdf μ 0 = 2⁻¹ := by
  linarith [cdf_neg μ h, congrArg (cdf μ) neg_zero]

theorem isNegInvariant_iff_cdf_neg [NullSingletonClass μ] :
    μ.IsNegInvariant ↔ ∀ x, cdf μ (-x) = 1 - cdf μ x := by
  refine ⟨fun _ x ↦ cdf_neg μ (measure_singleton x), fun h ↦ ⟨?_⟩⟩
  have : IsProbabilityMeasure μ.neg := inferInstanceAs (IsProbabilityMeasure (μ.map Neg.neg))
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun x ↦ ?_)
  rw [cdf_eq_real, measureReal_def, Measure.neg_apply, neg_Iic, ← measureReal_def,
    ← measureReal_congr (Ioi_ae_eq_Ici' (measure_singleton _)), ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, h, sub_sub_cancel]

/-! ### Strict monotonicity -/

section IsOpenPosMeasure

variable [μ.IsOpenPosMeasure]

theorem strictMono_cdf : StrictMono (cdf μ) :=
  (cdf μ).strictMono_iff_isOpenPosMeasure.2 (by rw [measure_cdf]; infer_instance)

theorem cdf_pos (x : ℝ) : 0 < cdf μ x :=
  (cdf_nonneg μ (x - 1)).trans_lt (strictMono_cdf μ (sub_one_lt x))

theorem cdf_lt_one (x : ℝ) : cdf μ x < 1 :=
  (strictMono_cdf μ (lt_add_one x)).trans_le (cdf_le_one μ _)

/-! ### The cdf as an order isomorphism -/

variable [NullSingletonClass μ]

/-- The cdf of an atomless open-positive probability measure as an order isomorphism between `ℝ`
and `(0, 1)`. Its inverse is the quantile function of `μ`. -/
noncomputable def cdfOrderIso : ℝ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective _
    ((strictMono_cdf μ).codRestrict fun x ↦ mem_Ioo.2 ⟨cdf_pos μ x, cdf_lt_one μ x⟩) <|
    ((continuous_cdf μ).subtype_mk _).surjective
      (by rw [tendsto_Ioo_atTop]
          exact tendsto_nhdsWithin_iff.2 ⟨tendsto_cdf_atTop μ, .of_forall (cdf_lt_one μ)⟩)
      (by rw [tendsto_Ioo_atBot]
          exact tendsto_nhdsWithin_iff.2 ⟨tendsto_cdf_atBot μ, .of_forall (cdf_pos μ)⟩)

@[simp]
theorem coe_cdfOrderIso_apply (x : ℝ) : (cdfOrderIso μ x : ℝ) = cdf μ x :=
  rfl

@[simp]
theorem coe_comp_cdfOrderIso : (↑) ∘ cdfOrderIso μ = cdf μ :=
  rfl

theorem range_cdf : range (cdf μ) = Ioo 0 1 := by
  rw [← coe_comp_cdfOrderIso μ, range_comp, (cdfOrderIso μ).range_eq, image_univ, Subtype.range_coe]

end IsOpenPosMeasure

end ProbabilityTheory
