/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.MeasureTheory.Constructions.Pi
public import Linglib.Core.Probability.Distributions.Gaussian
public import Linglib.Core.Probability.Distributions.Gumbel
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Random utility models

In a random utility model the alternatives `j : ι` have real-valued utilities with a joint law `μ`
on `ι → ℝ`, and the alternative with the highest utility is chosen. The choice probability of `i` is
the mass `μ` gives to the event that coordinate `i` is the strict maximum. Most models take the
utilities independent, `μ = Measure.pi ν`; noise on parameters shared by the alternatives
correlates them, and such a law is a pushforward (`choiceProb_map`). The additive model, with
utility `u j + ε j` for a systematic part `u j` and noise `ε j`, is the case where `ν` is a location
family.

For independent utilities the theory is independent of the noise family. Splitting coordinate `i`
off the product measure (`measurePreserving_piSplitAt`) writes the choice probability as the
integral against `ν i` of the product of the other coordinates' distribution functions. For
atomless noise ties are null, so the choice probabilities of the alternatives sum to one.
Independent Gumbel noise gives the softmax rule. This direction is due to Marschak and, in
constructive form, to Holman and Marley as reported by Luce and Suppes; McFadden proves it as his
Lemma 1, and his Lemma 2 is the converse for choice sets of size at least three, since Yellott
shows that binary logistic choice does not pin down Gumbel noise. Gaussian noise gives the probit
rule, whose binary case is computed here from the convolution of two Gaussians.

## Main definitions

* `ProbabilityTheory.choiceProb`: the probability that alternative `i` has the highest utility under
  a joint law of the utilities.

## Main results

* `ProbabilityTheory.choiceProb_map`: the choice probabilities of a pushforward law.
* `ProbabilityTheory.choiceProb_pi_eq_lintegral`: for independent utilities, the choice
  probability as an integral against
  `ν i`.
* `ProbabilityTheory.sum_choiceProb`: when ties are null the choice probabilities sum to one.
* `ProbabilityTheory.choiceProb_pi_gumbelMeasure`: under independent Gumbel utilities the choice
  probabilities are softmax.
* `ProbabilityTheory.choiceProb_pi_gaussianReal`: two alternatives with independent Gaussian
  utilities of common variance `v` have choice probability `Φ ((u 0 - u 1) / √(2 * v))`.

## References

* [L. L. Thurstone, *A law of comparative judgment* (1927)][thurstone-1927]
* [D. McFadden, *Conditional logit analysis of qualitative choice behavior* (1974)][mcfadden-1974]
* [marschak-1960]
* [luce-suppes-1965]
* [luce-1959]
* [yellott-1977]
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### Choice probabilities -/

section ChoiceProb

variable {ι : Type*} [Fintype ι]

/-- The choice probability of alternative `i` in the random utility model whose utilities have
the joint law `μ` is the probability that coordinate `i` is the strict maximum. -/
noncomputable def choiceProb (μ : Measure (ι → ℝ)) (i : ι) : ℝ≥0∞ :=
  μ {x | ∀ j, j ≠ i → x j < x i}

theorem measurableSet_setOf_forall_ne_lt (i : ι) :
    MeasurableSet {x : ι → ℝ | ∀ j, j ≠ i → x j < x i} := by
  simp only [ofPred_forall]
  exact .iInter fun j ↦ .iInter fun _ ↦
    measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

/-- The choice probabilities of a pushforward law are the masses of the preimage events. -/
theorem choiceProb_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {U : Ω → ι → ℝ}
    (hU : Measurable U) (i : ι) :
    choiceProb (P.map U) i = P {ω | ∀ j, j ≠ i → U ω j < U ω i} := by
  rw [choiceProb, Measure.map_apply hU (measurableSet_setOf_forall_ne_lt i)]
  rfl

/-- When ties have probability zero the choice probabilities of the alternatives sum to one, as for
independent atomless noise (`Measure.pi_setOf_apply_eq_apply`). -/
theorem sum_choiceProb [Nonempty ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ j k, j ≠ k → μ {x | x j = x k} = 0) : ∑ i, choiceProb μ i = 1 := by
  have hdisj : Pairwise (Function.onFun Disjoint fun i ↦ {x : ι → ℝ | ∀ j, j ≠ i → x j < x i}) :=
    fun i k hik ↦ Set.disjoint_left.2 fun x hi hk ↦ lt_asymm (hi k hik.symm) (hk i hik)
  simp only [choiceProb]
  rw [← measure_biUnion_finset (fun i _ k _ hik ↦ hdisj hik) fun i _ ↦
      measurableSet_setOf_forall_ne_lt i, ← measure_univ (μ := μ)]
  refine measure_congr (ae_eq_univ.2 (measure_mono_null (t := ⋃ j, ⋃ k, ⋃ (_ : j ≠ k),
    {x : ι → ℝ | x j = x k}) (fun x hx ↦ ?_) ?_))
  · by_contra hinj
    simp only [mem_iUnion, not_exists] at hinj
    obtain ⟨i, hi⟩ := Finite.exists_max x
    exact hx (mem_iUnion₂.2 ⟨i, mem_univ i, fun j hj ↦ (hi j).lt_of_ne fun h ↦ hinj j i hj h⟩)
  · exact measure_iUnion_null fun j ↦ measure_iUnion_null fun k ↦ measure_iUnion_null (hμ j k)

variable [DecidableEq ι]

/-- The choice probability of `i` is the integral, against the law of the `i`-th utility, of the
probability that every other utility falls below it. -/
theorem choiceProb_pi_eq_lintegral (ν : ι → Measure ℝ) [∀ j, SigmaFinite (ν j)] (i : ι) :
    choiceProb (Measure.pi ν) i = ∫⁻ x, ∏ j ∈ univ.erase i, ν j (Iio x) ∂ν i := by
  have hS : {x : ι → ℝ | ∀ j, j ≠ i → x j < x i} = MeasurableEquiv.piSplitAt (fun _ ↦ ℝ) i ⁻¹'
      {p | ∀ j, p.2 j < p.1} := by ext; simp
  have hT : MeasurableSet {p : ℝ × ({j // j ≠ i} → ℝ) | ∀ j, p.2 j < p.1} := by
    simp only [ofPred_forall]
    exact .iInter fun j ↦ measurableSet_lt (by fun_prop) measurable_fst
  rw [choiceProb, hS, (measurePreserving_piSplitAt ν i).measure_preimage_equiv,
    Measure.prod_apply hT]
  refine lintegral_congr fun x ↦ ?_
  rw [show Prod.mk x ⁻¹' {p : ℝ × ({j // j ≠ i} → ℝ) | ∀ j, p.2 j < p.1} =
    Set.pi univ fun _ ↦ Iio x by ext; simp, Measure.pi_pi]
  exact (prod_subtype (univ.erase i) (by simp) fun j ↦ ν j (Iio x)).symm

theorem choiceProb_pi_eq_lintegral_cdf (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    [∀ j, NullSingletonClass (ν j)] (i : ι) :
    choiceProb (Measure.pi ν) i = ∫⁻ x, ENNReal.ofReal (∏ j ∈ univ.erase i, cdf (ν j) x) ∂ν i := by
  rw [choiceProb_pi_eq_lintegral]
  refine lintegral_congr fun x ↦ ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun j _ ↦ cdf_nonneg _ _]
  exact prod_congr rfl fun j _ ↦ by rw [ofReal_cdf, measure_congr Iio_ae_eq_Iic]

end ChoiceProb

/-! ### Gaussian noise: the probit rule -/

/-- Two alternatives with independent Gaussian utilities of means `u 0`, `u 1` and common variance
`v` follow the binary probit rule, since the difference of the utilities is Gaussian with variance
`2 * v`. -/
theorem choiceProb_pi_gaussianReal (u : Fin 2 → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    choiceProb (Measure.pi fun j ↦ gaussianReal (u j) v) 0 =
      ENNReal.ofReal (normalCDF ((u 0 - u 1) / √(2 * v))) := by
  have hS : {x : Fin 2 → ℝ | ∀ j, j ≠ 0 → x j < x 0} =
      MeasurableEquiv.piFinTwo (fun _ ↦ ℝ) ⁻¹' ((fun p : ℝ × ℝ ↦ p.1 + -p.2) ⁻¹' Ioi 0) := by
    ext x; simp [Fin.forall_fin_two]
  have hmap : ((gaussianReal (u 0) v).prod (gaussianReal (u 1) v)).map (fun p ↦ p.1 + -p.2) =
      gaussianReal (u 0 - u 1) (v + v) := by
    have h : (gaussianReal (u 0) v).prod ((gaussianReal (u 1) v).map fun x ↦ -x) =
        ((gaussianReal (u 0) v).prod (gaussianReal (u 1) v)).map (Prod.map id fun x ↦ -x) := by
      simpa using Measure.map_prod_map (gaussianReal (u 0) v) (gaussianReal (u 1) v)
        measurable_id measurable_neg
    rw [sub_eq_add_neg, ← gaussianReal_conv_gaussianReal, ← gaussianReal_map_neg, Measure.conv, h,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hv2 : v + v ≠ 0 := by simpa using hv
  rw [choiceProb, hS,
    (measurePreserving_piFinTwo fun j ↦ gaussianReal (u j) v).measure_preimage_equiv,
    ← Measure.map_apply (by fun_prop) measurableSet_Ioi, hmap, ← ofReal_measureReal,
    gaussianReal_real_Ioi _ hv2, sub_zero, NNReal.coe_add, two_mul]

variable {σ : ℝ}

open Real

theorem gaussianReal_real_Ioi_zero (Δ : ℝ) (hσ : 0 < σ) :
    (gaussianReal Δ (.mk (σ ^ 2) (sq_nonneg σ))).real (Set.Ioi 0) = normalCDF (Δ / σ) := by
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) ≠ 0 := by simp [← NNReal.coe_eq_zero, hσ.ne']
  simp only [gaussianReal_real_Ioi Δ hv, NNReal.coe_mk, sqrt_sq hσ.le, sub_zero]

theorem choiceProb_pi_gaussianReal_sq (u : Fin 2 → ℝ) (hσ : 0 < σ) :
    choiceProb (Measure.pi fun j ↦ gaussianReal (u j) (.mk (σ ^ 2) (sq_nonneg σ))) 0 =
      ENNReal.ofReal (normalCDF ((u 0 - u 1) / (σ * √2))) := by
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) ≠ 0 := by simp [← NNReal.coe_eq_zero, hσ.ne']
  rw [choiceProb_pi_gaussianReal u hv, NNReal.coe_mk, mul_comm (2 : ℝ),
    sqrt_mul (sq_nonneg σ), sqrt_sq hσ.le]

/-! ### Gumbel noise: the softmax rule -/

section GumbelRUM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {β : ℝ≥0}

/-- When the utilities are independent with `Gumbel(uⱼ, β)` laws, alternative `i` has the highest
utility with probability `softmax (β⁻¹ • u) i`. The density of the `i`-th utility times the other
utilities' cdfs is `softmax (β⁻¹ • u) i` times the density of the maximum utility, which is Gumbel
with location `β * log (∑ j, exp (u j / β))` by max-stability. McFadden states the unit-scale case;
the scale of the noise is not separately identified from that of `u`. -/
theorem choiceProb_pi_gumbelMeasure (u : ι → ℝ) (hβ : β ≠ 0) (i : ι) :
    choiceProb (Measure.pi fun j ↦ gumbelMeasure (u j) β) i =
      ENNReal.ofReal (softmax ((β : ℝ)⁻¹ • u) i) := by
  have := fun j ↦ nullSingletonClass_gumbelMeasure (u j) hβ
  set m := β * log (∑ j, exp (u j / β)) with hm
  have key (x : ℝ) : gumbelPDF (u i) β x *
      ENNReal.ofReal (∏ j ∈ univ.erase i, cdf (gumbelMeasure (u j) β) x) =
        ENNReal.ofReal (softmax ((β : ℝ)⁻¹ • u) i) * gumbelPDF m β x := by
    have h : exp (u i / β - log (∑ j, exp (u j / β))) * exp (-((x - m) / β)) =
        exp (-((x - u i) / β)) := by
      rw [← exp_add]; congr 1; field_simp; ring
    rw [gumbelPDF, gumbelPDF, ← ENNReal.ofReal_mul (gumbelPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_mul (softmax_nonneg _ _), gumbelPDFReal_eq_mul_cdf _ hβ,
      gumbelPDFReal_eq_mul_cdf _ hβ, mul_assoc,
      mul_prod_erase _ (fun j ↦ cdf (gumbelMeasure (u j) β) x) (mem_univ i),
      prod_cdf_gumbelMeasure univ_nonempty u hβ, ← hm, softmax_eq_exp_sub, ← h]
    simp only [Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    congr 1; ring
  rw [choiceProb_pi_eq_lintegral_cdf, gumbelMeasure_of_scale_ne_zero (u i) hβ,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_gumbelPDF _ _)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [Pi.mul_apply, key]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gumbelPDF_eq_one m hβ, mul_one]

/-! ### Binary case: the logistic function -/

theorem choiceProb_pi_gumbelMeasure_fin_two (u : Fin 2 → ℝ) (hβ : β ≠ 0) :
    choiceProb (Measure.pi fun j ↦ gumbelMeasure (u j) β) 0 =
      ENNReal.ofReal (sigmoid ((u 0 - u 1) / β)) := by
  rw [choiceProb_pi_gumbelMeasure u hβ 0, softmax_fin_two]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 2; ring

end GumbelRUM

end ProbabilityTheory
