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
satisfies `Φ (-x) = 1 - Φ x`, and the probit, its quantile function, inverts it on `(0, 1)`. The
cdf of any nondegenerate Gaussian is [`Φ` at the standard
score](##ProbabilityTheory.cdf_gaussianReal_eq), and [a linear combination of independent Gaussians
is Gaussian](##ProbabilityTheory.map_pi_gaussianReal_sum_mul).

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

/-! ### The standard normal distribution function -/

/-- The standard normal distribution function `Φ`, the cdf of `gaussianReal 0 1`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

theorem normalCDF_nonneg (x : ℝ) : 0 ≤ normalCDF x := cdf_nonneg _ x

theorem normalCDF_pos (x : ℝ) : 0 < normalCDF x := cdf_pos _ x

theorem normalCDF_strictMono : StrictMono normalCDF := strictMono_cdf _

theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x :=
  cdf_neg _ (measure_singleton x)

@[simp]
theorem normalCDF_zero : normalCDF 0 = 2⁻¹ := cdf_zero _ (measure_singleton 0)

/-! ### Standardization -/

/-- The cdf of a nondegenerate Gaussian is `Φ` at the standard score. -/
theorem cdf_gaussianReal_eq (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal μ v) x = normalCDF ((x - μ) / √v) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 hv.bot_lt)
  have h : gaussianReal μ v = (gaussianReal 0 1).map
      ((OrderIso.mulRight₀ _ hs).trans (OrderIso.addRight μ)) := by
    rw [show ⇑((OrderIso.mulRight₀ _ hs).trans (OrderIso.addRight μ)) =
        (· + μ) ∘ (· * √(v : ℝ)) from rfl, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_mul_const, gaussianReal_map_add_const]
    congr
    · simp
    · ext
      simp [Real.sq_sqrt]
  rw [h, cdf_map_orderIso]
  rfl

/-- The upper tail of a nondegenerate Gaussian `X ~ N(μ, v)` is `P(X > x) = Φ ((μ - x) / √v)`. -/
theorem gaussianReal_real_Ioi (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal μ v).real (Ioi x) = normalCDF ((μ - x) / √v) := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_gaussianReal_eq μ hv, ← normalCDF_neg, ← neg_div, neg_sub]

/-! ### The probit -/

/-- The probit `Φ⁻¹`, the quantile function of the standard normal. It is `0` outside `(0, 1)`. -/
noncomputable def probit (p : ℝ) : ℝ :=
  quantile (gaussianReal 0 1) p

@[simp]
theorem probit_normalCDF (x : ℝ) : probit (normalCDF x) = x :=
  quantile_cdf _ x

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
