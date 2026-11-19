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
# Regularity of the cdf of a real probability measure, and the quantile function

Each regularity property of `ProbabilityTheory.cdf μ` is the image of a property of `μ`, read off
the Stieltjes function `cdf μ` whose measure is `μ`. The cdf is [continuous exactly at the points
that are not atoms](##ProbabilityTheory.continuousAt_cdf_iff), [strictly monotone exactly when `μ`
charges every nonempty open set](##ProbabilityTheory.strictMono_cdf_iff), and, when `μ` has no
atoms, satisfies the reflection formula `cdf μ (-x) = 1 - cdf μ x` [exactly when `μ` is invariant under
negation](##ProbabilityTheory.isNegInvariant_iff_cdf_neg). The quantile function
`quantile μ p = sInf {x | p ≤ cdf μ x}` is [the lower adjoint of the cdf on
`(0, 1)`](##ProbabilityTheory.quantile_le_iff). For a measure with the first two properties the cdf
is an order isomorphism from `ℝ` onto `(0, 1)` whose [inverse is the quantile
function](##ProbabilityTheory.coe_cdfOrderIso_symm_apply). `[UPSTREAM]` candidate for
`Mathlib/Probability/CDF.lean`.

## Implementation notes

`quantile μ p` is `0` for `p ≤ 0`, where the set is everything, and for `1 ≤ p` when `μ` charges
every nonempty open set, where the set is empty. So `quantile_one_sub` holds for every real `p`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Pointwise

namespace ProbabilityTheory

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}

/-- The quantile function of a real probability measure, the least `x` at which the cdf reaches
`p`. On `(0, 1)` it is the lower adjoint of the cdf (`quantile_le_iff`), and its inverse when the
cdf is continuous and strictly monotone. -/
noncomputable def quantile (p : ℝ) : ℝ :=
  sInf {x | p ≤ cdf μ x}

/-! ### Continuity -/

/-- The cdf is continuous at `x` iff `x` is not an atom. -/
theorem continuousAt_cdf_iff : ContinuousAt (cdf μ) x ↔ μ {x} = 0 := by
  rw [StieltjesFunction.continuousAt_iff_measure_singleton_eq_zero, measure_cdf]

/-- The cdf is continuous iff the measure has no atoms. -/
theorem continuous_cdf_iff : Continuous (cdf μ) ↔ NullSingletonClass μ := by
  rw [(cdf μ).continuous_iff_nullSingletonClass, measure_cdf]

theorem continuous_cdf [NullSingletonClass μ] : Continuous (cdf μ) :=
  (continuous_cdf_iff μ).2 inferInstance

/-! ### Reflection -/

/-- The upper tail of a negation-invariant measure at a point that is not an atom is the cdf at
the reflected point. -/
theorem measureReal_Ioi_eq_cdf_neg [μ.IsNegInvariant] (hx : μ {x} = 0) :
    μ.real (Ioi x) = cdf μ (-x) := by
  rw [cdf_eq_real, ← neg_Ici, measureReal_congr (Ioi_ae_eq_Ici' hx), measureReal_def,
    measureReal_def, μ.measure_neg]

/-- The reflection formula for the cdf of a negation-invariant measure, away from atoms. -/
theorem cdf_neg [μ.IsNegInvariant] (hx : μ {x} = 0) : cdf μ (-x) = 1 - cdf μ x := by
  rw [← measureReal_Ioi_eq_cdf_neg μ hx, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    cdf_eq_real]

theorem cdf_zero [μ.IsNegInvariant] (h : μ {0} = 0) : cdf μ 0 = 2⁻¹ := by
  linarith [cdf_neg μ h, congrArg (cdf μ) neg_zero]

/-- A measure without atoms is invariant under negation iff its cdf satisfies the reflection
formula. -/
theorem isNegInvariant_iff_cdf_neg [NullSingletonClass μ] :
    μ.IsNegInvariant ↔ ∀ x, cdf μ (-x) = 1 - cdf μ x := by
  refine ⟨fun _ x ↦ cdf_neg μ (measure_singleton x), fun h ↦ ⟨?_⟩⟩
  have : IsProbabilityMeasure μ.neg := inferInstanceAs (IsProbabilityMeasure (μ.map Neg.neg))
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun x ↦ ?_)
  rw [cdf_eq_real, measureReal_def, Measure.neg_apply, neg_Iic, ← measureReal_def,
    ← measureReal_congr (Ioi_ae_eq_Ici' (measure_singleton _)), ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, h, sub_sub_cancel]

/-! ### Strict monotonicity -/

/-- The cdf is strictly monotone iff the measure charges every nonempty open set. -/
theorem strictMono_cdf_iff : StrictMono (cdf μ) ↔ μ.IsOpenPosMeasure := by
  rw [(cdf μ).strictMono_iff_isOpenPosMeasure, measure_cdf]

section IsOpenPosMeasure

variable [μ.IsOpenPosMeasure]

theorem strictMono_cdf : StrictMono (cdf μ) :=
  (strictMono_cdf_iff μ).2 inferInstance

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

/-! ### The quantile function -/

omit [IsProbabilityMeasure μ] [NullSingletonClass μ] [μ.IsOpenPosMeasure] in
variable {μ} in
/-- The quantile function is the lower adjoint of the cdf: `quantile μ p ≤ x` iff the mass up to
`x` is at least `p`. -/
theorem quantile_le_iff {p : ℝ} (hp : p ∈ Ioo 0 1) : quantile μ p ≤ x ↔ p ≤ cdf μ x := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hp.1).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt hp.2).exists
  have hbdd : BddBelow {y | p ≤ cdf μ y} :=
    ⟨a, fun y hy ↦ le_of_not_gt fun h ↦ (hy.trans (monotone_cdf μ h.le)).not_gt ha⟩
  refine ⟨fun h ↦ ?_, fun h ↦ csInf_le hbdd h⟩
  refine ge_of_tendsto (((cdf μ).right_continuous x).mono Ioi_subset_Ici_self) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt ⟨b, hb.le⟩ (h.trans_lt hy)
  exact hz.trans (monotone_cdf μ hzy.le)

omit [NullSingletonClass μ] in
@[simp]
theorem quantile_cdf (x : ℝ) : quantile μ (cdf μ x) = x := by
  simp only [quantile, (strictMono_cdf μ).le_iff_le]
  exact csInf_Ici

omit [NullSingletonClass μ] in
theorem quantile_of_notMem {p : ℝ} (hp : p ∉ Ioo 0 1) : quantile μ p = 0 := by
  rcases le_or_gt p 0 with h | h
  · have : {x | p ≤ cdf μ x} = univ := eq_univ_of_forall fun x ↦ h.trans (cdf_nonneg μ x)
    rw [quantile, this, Real.sInf_univ]
  · have : {x | p ≤ cdf μ x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hp ⟨h, hx.trans_lt (cdf_lt_one μ x)⟩
    rw [quantile, this, Real.sInf_empty]

variable {p q : ℝ}

theorem cdf_quantile (hp : p ∈ Ioo 0 1) : cdf μ (quantile μ p) = p := by
  obtain ⟨x, rfl⟩ : p ∈ range (cdf μ) := range_cdf μ ▸ hp
  rw [quantile_cdf]

/-- The inverse of the cdf is the quantile function. -/
@[simp]
theorem coe_cdfOrderIso_symm_apply (p : Ioo (0 : ℝ) 1) :
    ((cdfOrderIso μ).symm p : ℝ) = quantile μ p := by
  obtain ⟨x, rfl⟩ := (cdfOrderIso μ).surjective p
  rw [OrderIso.symm_apply_apply, coe_cdfOrderIso_apply, quantile_cdf]

theorem quantile_lt_quantile_iff (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) :
    quantile μ p < quantile μ q ↔ p < q := by
  rw [← (strictMono_cdf μ).lt_iff_lt, cdf_quantile μ hp, cdf_quantile μ hq]

theorem quantile_le_quantile_iff (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) :
    quantile μ p ≤ quantile μ q ↔ p ≤ q := by
  rw [← (strictMono_cdf μ).le_iff_le, cdf_quantile μ hp, cdf_quantile μ hq]

/-- The median of a symmetric measure is `0`. -/
@[simp]
theorem quantile_inv_two [μ.IsNegInvariant] : quantile μ 2⁻¹ = 0 := by
  rw [← cdf_zero μ (measure_singleton 0), quantile_cdf]

/-- The quantile function of a symmetric measure is odd about `1 / 2`. Outside `(0, 1)` both sides
are `0`. -/
theorem quantile_one_sub [μ.IsNegInvariant] (p : ℝ) : quantile μ (1 - p) = -quantile μ p := by
  by_cases hp : p ∈ Ioo 0 1
  · obtain ⟨x, rfl⟩ : p ∈ range (cdf μ) := range_cdf μ ▸ hp
    rw [← cdf_neg μ (measure_singleton x), quantile_cdf, quantile_cdf]
  · have hp' : 1 - p ∉ Ioo 0 1 := fun h ↦ hp ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [quantile_of_notMem μ hp, quantile_of_notMem μ hp', neg_zero]

end IsOpenPosMeasure

end ProbabilityTheory
