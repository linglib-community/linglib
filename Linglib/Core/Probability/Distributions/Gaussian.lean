/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Variance

/-!
# The standard normal distribution function and the probit

The standard normal distribution function `Φ` is the cdf of mathlib's `gaussianReal 0 1`, and
everything about it here is an instance of a general fact about cdfs from
`Linglib/Core/Probability/CDF.lean`. A nondegenerate Gaussian has no atoms, charges every nonempty
open set, and is invariant under negation when centred, so `Φ` is continuous, strictly monotone and
satisfies `Φ (-x) = 1 - Φ x`. It is therefore an order isomorphism from `ℝ` onto `(0, 1)`, and the
probit is its inverse, extended by `0` outside `(0, 1)` as `Real.log` is extended outside `(0, ∞)`.

## Main definitions

* `ProbabilityTheory.normalCDF`: the standard normal distribution function `Φ`.
* `ProbabilityTheory.probit`: the standard normal quantile function `Φ⁻¹`.

## Main results

* `ProbabilityTheory.cdf_gaussianReal_eq`: standardization,
  `cdf (gaussianReal μ v) x = Φ ((x - μ) / √v)`.
* `ProbabilityTheory.gaussianReal_real_Ioi`: the upper tail of a Gaussian is `Φ ((μ - x) / √v)`.
* `ProbabilityTheory.probit_one_sub`: `Φ⁻¹ (1 - p) = -Φ⁻¹ p`, for every real `p`.
* `ProbabilityTheory.gaussianPDFReal_div_gaussianPDFReal`: the ratio of two Gaussian densities of a
  common variance is the exponential of an affine function.
* `ProbabilityTheory.map_pi_gaussianReal_sum_mul`, `variance_pi_gaussianReal_sum_mul`,
  `covariance_pi_gaussianReal_sum_mul`: a linear combination of independent Gaussians is Gaussian,
  with the variance and covariances read off the coefficients.

## Implementation notes

Mathlib states the atomlessness of a Gaussian as a lemma with hypothesis `v ≠ 0`. The instances here
take `[NeZero v]` instead, so that they fire for the standard normal `gaussianReal 0 1`.
`[UPSTREAM]` candidates for `Mathlib/Probability/Distributions/Gaussian/Real.lean`, and the linear
combination lemmas for
`Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {μ : ℝ} {v : ℝ≥0}

instance [NeZero v] : NullSingletonClass (gaussianReal μ v) :=
  nullSingletonClass_gaussianReal (NeZero.ne v)

lemma isOpenPosMeasure_gaussianReal (hv : v ≠ 0) : (gaussianReal μ v).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' μ hv).isOpenPosMeasure

instance [NeZero v] : (gaussianReal μ v).IsOpenPosMeasure :=
  isOpenPosMeasure_gaussianReal (NeZero.ne v)

instance : (gaussianReal 0 v).IsNegInvariant :=
  ⟨by simpa [Measure.neg_def] using gaussianReal_map_neg (μ := 0) (v := v)⟩

variable {x p q : ℝ}

/-! ### The standard normal distribution function -/

/-- The standard normal distribution function `Φ`, the cdf of `gaussianReal 0 1`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

theorem normalCDF_nonneg (x : ℝ) : 0 ≤ normalCDF x := cdf_nonneg _ x

theorem normalCDF_le_one (x : ℝ) : normalCDF x ≤ 1 := cdf_le_one _ x

theorem normalCDF_pos (x : ℝ) : 0 < normalCDF x := cdf_pos _ x

theorem normalCDF_lt_one (x : ℝ) : normalCDF x < 1 := cdf_lt_one _ x

theorem normalCDF_mem_Ioo (x : ℝ) : normalCDF x ∈ Ioo (0 : ℝ) 1 :=
  ⟨normalCDF_pos x, normalCDF_lt_one x⟩

theorem normalCDF_strictMono : StrictMono normalCDF := strictMono_cdf _

theorem normalCDF_monotone : Monotone normalCDF := normalCDF_strictMono.monotone

theorem normalCDF_injective : Function.Injective normalCDF := normalCDF_strictMono.injective

theorem continuous_normalCDF : Continuous normalCDF := continuous_cdf _

@[simp]
theorem range_normalCDF : range normalCDF = Ioo 0 1 := range_cdf _

theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x :=
  cdf_neg _ (measure_singleton x)

@[simp]
theorem normalCDF_zero : normalCDF 0 = 2⁻¹ := cdf_zero _ (measure_singleton 0)

theorem inv_two_lt_normalCDF_iff : 2⁻¹ < normalCDF x ↔ 0 < x := by
  rw [← normalCDF_zero, normalCDF_strictMono.lt_iff_lt]

theorem normalCDF_lt_inv_two_iff : normalCDF x < 2⁻¹ ↔ x < 0 := by
  rw [← normalCDF_zero, normalCDF_strictMono.lt_iff_lt]

/-! ### Standardization -/

/-- The cdf of a nondegenerate Gaussian is `Φ` at the standard score. -/
theorem cdf_gaussianReal_eq (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal μ v) x = normalCDF ((x - μ) / √v) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 hv.bot_lt)
  have h : (gaussianReal μ v).map (fun y ↦ (y - μ) / √v) = gaussianReal 0 1 := by
    rw [show (fun y ↦ (y - μ) / √(v : ℝ)) = (· / √(v : ℝ)) ∘ (· - μ) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_div_const, sub_self, zero_div]
    congr
    ext
    simp [Real.sq_sqrt, hv]
  rw [normalCDF, cdf_eq_real, cdf_eq_real, ← h,
    map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext y
  simp [div_le_div_iff_of_pos_right hs]

/-- The upper tail of a nondegenerate Gaussian `X ~ N(μ, v)` is `P(X > x) = Φ ((μ - x) / √v)`. -/
theorem gaussianReal_real_Ioi (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal μ v).real (Ioi x) = normalCDF ((μ - x) / √v) := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_gaussianReal_eq μ hv, ← normalCDF_neg, ← neg_div, neg_sub]

/-! ### The probit -/

/-- The probit, the quantile function `Φ⁻¹` of the standard normal, equal to the inverse of
`normalCDF` on `(0, 1)` and to `0` elsewhere. The extension by `0` makes `probit_one_sub` hold for
every real argument. -/
noncomputable def probit (p : ℝ) : ℝ :=
  if hp : p ∈ Ioo 0 1 then (cdfOrderIso (gaussianReal 0 1)).symm ⟨p, hp⟩ else 0

theorem probit_of_mem (hp : p ∈ Ioo 0 1) :
    probit p = (cdfOrderIso (gaussianReal 0 1)).symm ⟨p, hp⟩ :=
  dite_eq_left hp

theorem probit_of_notMem (hp : p ∉ Ioo 0 1) : probit p = 0 :=
  dite_eq_right hp

theorem normalCDF_probit (hp : p ∈ Ioo 0 1) : normalCDF (probit p) = p := by
  rw [probit_of_mem hp, normalCDF, ← coe_cdfOrderIso_apply _, OrderIso.apply_symm_apply]

@[simp]
theorem probit_normalCDF (x : ℝ) : probit (normalCDF x) = x := by
  rw [probit_of_mem (normalCDF_mem_Ioo x)]
  exact (cdfOrderIso (gaussianReal 0 1)).symm_apply_apply x

theorem probit_lt_probit_iff (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) :
    probit p < probit q ↔ p < q := by
  rw [probit_of_mem hp, probit_of_mem hq, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

theorem probit_le_probit_iff (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) :
    probit p ≤ probit q ↔ p ≤ q := by
  rw [probit_of_mem hp, probit_of_mem hq, OrderIso.le_iff_le, Subtype.mk_le_mk]

@[simp]
theorem probit_inv_two : probit 2⁻¹ = 0 := by
  rw [← normalCDF_zero, probit_normalCDF]

/-- The probit is odd about `1 / 2`. Outside `(0, 1)` both sides are the junk value `0`. -/
theorem probit_one_sub (p : ℝ) : probit (1 - p) = -probit p := by
  by_cases hp : p ∈ Ioo 0 1
  · have hp' : 1 - p ∈ Ioo 0 1 := ⟨sub_pos.2 hp.2, sub_lt_self 1 hp.1⟩
    apply normalCDF_injective
    rw [normalCDF_probit hp', normalCDF_neg, normalCDF_probit hp]
  · have hp' : 1 - p ∉ Ioo 0 1 := fun h ↦ hp ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [probit_of_notMem hp, probit_of_notMem hp', neg_zero]

/-! ### Densities -/

/-- The ratio of two Gaussian densities of a common nonzero variance is the exponential of an affine
function, zero midway between the means. -/
theorem gaussianPDFReal_div_gaussianPDFReal (μ₁ μ₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal μ₁ v x / gaussianPDFReal μ₀ v x =
      Real.exp ((μ₁ - μ₀) * (x - (μ₀ + μ₁) / 2) / v) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  rw [gaussianPDFReal, gaussianPDFReal, mul_div_mul_left _ _ (by positivity), ← Real.exp_sub]
  congr 1
  field_simp
  ring

/-! ### Linear combinations of independent Gaussians -/

section LinearCombination

variable {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ι → ℝ≥0)

/-- A linear combination of independent Gaussians is Gaussian. -/
theorem map_pi_gaussianReal_sum_mul (d : ι → ℝ) :
    (Measure.pi fun i ↦ gaussianReal (m i) (v i)).map (fun η ↦ ∑ i, d i * η i) =
      gaussianReal (∑ i, d i * m i) (∑ i, .mk (d i ^ 2) (sq_nonneg _) * v i) := by
  set P := Measure.pi fun i ↦ gaussianReal (m i) (v i)
  have hlaw : ∀ i, HasLaw (fun η : ι → ℝ ↦ d i * η i)
      (gaussianReal (d i * m i) (.mk (d i ^ 2) (sq_nonneg _) * v i)) P := fun i ↦ by
    refine ⟨(measurable_const.mul (measurable_pi_apply i)).aemeasurable, ?_⟩
    rw [← gaussianReal_map_const_mul,
      ← (measurePreserving_eval (fun i ↦ gaussianReal (m i) (v i)) i).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hind : iIndepFun (fun i (η : ι → ℝ) ↦ d i * η i) P :=
    iIndepFun_pi (X := fun i x ↦ d i * x) fun i ↦ by fun_prop
  rw [(hind.hasGaussianLaw_fun_sum fun i ↦ (hlaw i).hasGaussianLaw).map_eq_gaussianReal]
  congr 1
  · rw [integral_finsetSum _ fun i _ ↦ (hlaw i).integrable
      ((memLp_id_gaussianReal' 1 ENNReal.one_ne_top).integrable le_rfl)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [(hlaw i).integral_eq, integral_id_gaussianReal]
  · rw [← Real.toNNReal_coe (r := ∑ i, _), ← Finset.sum_fn]
    congr 1
    rw [variance_sum_pi (X := fun i x ↦ d i * x) fun i ↦ (memLp_id_gaussianReal 2).const_mul _]
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ by rw [variance_const_mul, variance_fun_id_gaussianReal]

/-- The variance of a linear combination of independent Gaussians. -/
theorem variance_pi_gaussianReal_sum_mul (d : ι → ℝ) :
    Var[fun η ↦ ∑ i, d i * η i; Measure.pi fun i ↦ gaussianReal (m i) (v i)] =
      ∑ i, d i ^ 2 * v i := by
  rw [← Finset.sum_fn,
    variance_sum_pi (X := fun i x ↦ d i * x) fun i ↦ (memLp_id_gaussianReal 2).const_mul _]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [variance_const_mul, variance_fun_id_gaussianReal]

/-- The covariance of two linear combinations of independent Gaussians. -/
theorem covariance_pi_gaussianReal_sum_mul (d e : ι → ℝ) :
    cov[fun η ↦ ∑ i, d i * η i, fun η ↦ ∑ i, e i * η i;
      Measure.pi fun i ↦ gaussianReal (m i) (v i)] = ∑ i, d i * e i * v i := by
  have hL (d : ι → ℝ) : MemLp (fun η : ι → ℝ ↦ ∑ i, d i * η i) 2
      (Measure.pi fun i ↦ gaussianReal (m i) (v i)) := by
    rw [← Finset.sum_fn]
    exact memLp_finsetSum' _ fun i _ ↦
      ((memLp_id_gaussianReal 2).const_mul (d i)).comp_measurePreserving
        (measurePreserving_eval _ i)
  have h := variance_fun_add (hL d) (hL e)
  simp only [← Finset.sum_add_distrib, ← add_mul] at h
  rw [variance_pi_gaussianReal_sum_mul, variance_pi_gaussianReal_sum_mul,
    variance_pi_gaussianReal_sum_mul] at h
  have : ∑ i, (d i + e i) ^ 2 * (v i : ℝ) =
      ∑ i, d i ^ 2 * v i + 2 * ∑ i, d i * e i * v i + ∑ i, e i ^ 2 * v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  linarith

end LinearCombination

end ProbabilityTheory
