module

public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.Moments.Covariance
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Exact Bayes for the posterior kernel at atoms

Mathlib characterizes the posterior kernel `κ†μ` almost everywhere. On discrete spaces an
ae-fact holds at every atom of positive mass, which gives Bayes' rule pointwise at any
positive-mass observation, with no Radon–Nikodym derivative. Drawing a state from the posterior
given an observation of a state drawn from the prior leaves the prior invariant.

## Main results

* `ProbabilityTheory.posterior_apply_singleton`: `(κ†μ) x {ω} = μ {ω} * κ ω {x} / (κ ∘ₘ μ) {x}`;
  and `comp_real_mul_posterior_real`, the same with the denominator cleared, at every observation.
* `ProbabilityTheory.posterior_deterministic_eq_cond`: a deterministic observation's posterior
  is the prior conditioned on the observation's fibre.
* `ProbabilityTheory.ae_eq_posterior_of_eq_of_ne_zero`: when each observation is equally likely
  at every state that can emit it, the posterior renormalizes the prior over those states.
* `ProbabilityTheory.invariant_posterior_comp`, `ProbabilityTheory.invariant_comp_posterior`,
  `ProbabilityTheory.invariant_id_prod_comp_prodMkLeft_posterior`: the chains that alternate the
  likelihood and the posterior leave the prior, the prior predictive and the joint invariant.
* `ProbabilityTheory.posterior_real_singleton_lt_posterior_of_pair`: under priors carried by
  two atoms, the posterior at an atom is strictly increasing in its prior mass.
* `ProbabilityTheory.integral_le_integral_posterior`: conditioning on an observation raises
  the expectation of a statistic that monovaries with the observation's likelihood.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass 𝓧]

/-! ### Priors carried by two atoms

The `_of_pair` lemmas assume the prior's support lies in a pair `{ω, ω'}`, so that the
observation's marginal has two terms and the comparison of the posterior with the prior at
one atom is the comparison of the two likelihoods. -/

section PairMarginal

variable [Fintype Ω] (κ : Kernel Ω 𝓧) (μ : Measure Ω) {ω ω' : Ω} (hne : ω ≠ ω')
  (hsupp : ∀ ω'', μ {ω''} ≠ 0 → ω'' = ω ∨ ω'' = ω')
include hne hsupp

theorem _root_.MeasureTheory.Measure.comp_real_singleton_of_pair [IsFiniteMeasure μ]
    [IsFiniteKernel κ] (x : 𝓧) :
    (κ ∘ₘ μ).real {x} = μ.real {ω} * (κ ω).real {x} + μ.real {ω'} * (κ ω').real {x} := by
  rw [Measure.comp_real_singleton]
  exact Fintype.sum_eq_add ω ω' hne fun c hc ↦ by
    rw [measureReal_def, of_not_not (mt (hsupp c) (not_or.mpr hc)), ENNReal.toReal_zero, zero_mul]

theorem _root_.MeasureTheory.measureReal_singleton_add_singleton_of_pair
    [IsProbabilityMeasure μ] : μ.real {ω} + μ.real {ω'} = 1 := by
  have h := measure_univ (μ := μ)
  rw [← Finset.coe_univ, ← sum_measure_singleton,
    Fintype.sum_eq_add ω ω' hne (fun c hc ↦ of_not_not (mt (hsupp c) (not_or.mpr hc)))] at h
  rw [measureReal_def, measureReal_def,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h, ENNReal.toReal_one]

theorem _root_.MeasureTheory.Measure.comp_apply_singleton_ne_zero_of_pair
    [IsProbabilityMeasure μ] {x : 𝓧} (hκω : κ ω {x} ≠ 0) (hκω' : κ ω' {x} ≠ 0) :
    (κ ∘ₘ μ) {x} ≠ 0 := by
  obtain hω | hω := eq_or_ne (μ {ω}) 0
  · refine Measure.comp_apply_singleton_ne_zero κ μ (fun hω' ↦ ?_) hκω'
    have h1 := measureReal_singleton_add_singleton_of_pair μ hne hsupp
    rw [measureReal_def, measureReal_def, hω, hω'] at h1
    simp at h1
  · exact Measure.comp_apply_singleton_ne_zero κ μ hω hκω

end PairMarginal

variable [StandardBorelSpace Ω] [Nonempty Ω]
  (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ]

/-- At an observation of positive mass, the posterior mass of a state is given exactly by Bayes'
rule. -/
theorem posterior_apply_singleton {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    (κ†μ) x {ω} = μ {ω} * κ ω {x} / (κ ∘ₘ μ) {x} := by
  have hrect := congrArg (fun m => m ({x} ×ˢ {ω}))
    (compProd_posterior_eq_map_swap (κ := κ) (μ := μ))
  beta_reduce at hrect
  rw [Measure.compProd_apply_prod (.singleton x) (.singleton ω),
    Measure.map_apply measurable_swap ((MeasurableSet.singleton x).prod (.singleton ω)),
    Set.preimage_swap_prod,
    Measure.compProd_apply_prod (.singleton ω) (.singleton x),
    lintegral_singleton, lintegral_singleton] at hrect
  rw [ENNReal.eq_div_iff hx (measure_ne_top _ _), mul_comm]
  rw [hrect]
  ring

theorem posterior_apply_singleton_ne_zero_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    (κ†μ) x {ω} ≠ 0 ↔ μ {ω} ≠ 0 ∧ κ ω {x} ≠ 0 := by
  rw [posterior_apply_singleton κ μ hx, ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, not_or,
    not_or]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, measure_ne_top _ _⟩⟩

/-- A deterministic observation's posterior is the prior conditioned on the observation's
fibre. -/
theorem posterior_deterministic_eq_cond [Countable Ω] {f : Ω → 𝓧} (hf : Measurable f) {x : 𝓧}
    (hx : μ (f ⁻¹' {x}) ≠ 0) : ((Kernel.deterministic f hf)†μ) x = μ[|f ⁻¹' {x}] := by
  have hx' : (Kernel.deterministic f hf ∘ₘ μ) {x} ≠ 0 := by
    rwa [Measure.deterministic_comp_eq_map, Measure.map_apply hf (measurableSet_singleton x)]
  refine Measure.ext_of_singleton fun ω => ?_
  rw [posterior_apply_singleton _ _ hx', cond_apply (hf (measurableSet_singleton x)),
    Measure.deterministic_comp_eq_map, Measure.map_apply hf (measurableSet_singleton x),
    Kernel.deterministic_apply' hf ω (measurableSet_singleton x)]
  by_cases h : f ω = x
  · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr h), mul_one, div_eq_mul_inv, mul_comm,
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (show ω ∈ f ⁻¹' {x} from h))]
  · rw [Set.indicator_of_notMem (by simpa using h), mul_zero, ENNReal.zero_div,
      Set.inter_singleton_eq_empty.mpr (by simpa using h), measure_empty, mul_zero]

theorem posterior_real_singleton {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (ω : Ω) :
    ((κ†μ) x).real {ω} = μ.real {ω} * (κ ω).real {x} / (κ ∘ₘ μ).real {x} := by
  rw [measureReal_def, posterior_apply_singleton κ μ hx, ENNReal.toReal_div, ENNReal.toReal_mul,
    measureReal_def, measureReal_def, measureReal_def]

/-- If each observation is equally likely at every state that can emit it, a kernel that weighs the
states that can emit `x` by `w` is the posterior under any prior proportional to `w`, on the
observations the prior predicts. -/
theorem ae_eq_posterior_of_eq_of_ne_zero [Fintype Ω] [Countable 𝓧]
    (hκ : ∀ x ω ω', κ ω {x} ≠ 0 → κ ω' {x} ≠ 0 → κ ω {x} = κ ω' {x}) {η : Kernel 𝓧 Ω}
    (w : Ω → ℝ≥0∞) {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) (hμ : ∀ ω, μ {ω} = c * w ω)
    (hη : ∀ x, (κ ∘ₘ μ) {x} ≠ 0 → ∀ ω,
      η x {ω} = (if κ ω {x} = 0 then 0 else w ω) / ∑ ω', if κ ω' {x} = 0 then 0 else w ω') :
    η =ᵐ[κ ∘ₘ μ] κ†μ := by
  refine ae_iff_of_countable.2 fun x hx ↦ Measure.ext_of_singleton fun ω ↦ ?_
  obtain ⟨ω₀, -, h₀⟩ := (Measure.comp_apply_singleton_ne_zero_iff κ μ).1 hx
  have key (ω : Ω) : μ {ω} * κ ω {x} = (c * κ ω₀ {x}) * if κ ω {x} = 0 then 0 else w ω := by
    by_cases h₁ : κ ω {x} = 0
    · simp [h₁]
    · simp only [h₁, ↓reduceIte]
      rw [hμ, hκ x ω ω₀ h₁ h₀]
      ring
  have hsum : (κ ∘ₘ μ) {x} = (c * κ ω₀ {x}) * ∑ ω', if κ ω' {x} = 0 then 0 else w ω' := by
    rw [Measure.comp_apply_singleton, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω _ ↦ key ω
  rw [hη x hx ω, posterior_apply_singleton κ μ hx ω, key, hsum,
    ENNReal.mul_div_mul_left _ _ (mul_ne_zero hc₀ h₀) (ENNReal.mul_ne_top hc (measure_ne_top _ _))]

/-- At every state and observation, the observation marginal times the posterior is the prior
times the likelihood, Bayes' rule on reals with the denominator cleared. -/
theorem comp_real_mul_posterior_real [Fintype Ω] (ω : Ω) (x : 𝓧) :
    (κ ∘ₘ μ).real {x} * ((κ†μ) x).real {ω} = μ.real {ω} * (κ ω).real {x} := by
  obtain hx | hx := eq_or_ne ((κ ∘ₘ μ) {x}) 0
  · have h0 : μ {ω} * κ ω {x} = 0 := by
      rw [Measure.comp_apply_singleton, Finset.sum_eq_zero_iff] at hx
      exact hx ω (Finset.mem_univ ω)
    rw [measureReal_def, hx, ENNReal.toReal_zero, zero_mul, measureReal_def, measureReal_def,
      ← ENNReal.toReal_mul, h0, ENNReal.toReal_zero]
  · rw [posterior_real_singleton κ μ hx, mul_div_cancel₀]
    rwa [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)]

theorem real_lt_posterior_real_singleton_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) {ω : Ω}
    (hω : μ {ω} ≠ 0) :
    μ.real {ω} < ((κ†μ) x).real {ω} ↔ (κ ∘ₘ μ).real {x} < (κ ω).real {x} := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hμ : 0 < μ.real {ω} := ENNReal.toReal_pos hω (measure_ne_top _ _)
  rw [posterior_real_singleton κ μ hx, lt_div_iff₀ hm, mul_lt_mul_iff_of_pos_left hμ]

theorem posterior_real_singleton_lt_iff {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) {ω : Ω}
    (hω : μ {ω} ≠ 0) :
    ((κ†μ) x).real {ω} < μ.real {ω} ↔ (κ ω).real {x} < (κ ∘ₘ μ).real {x} := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hμ : 0 < μ.real {ω} := ENNReal.toReal_pos hω (measure_ne_top _ _)
  rw [posterior_real_singleton κ μ hx, div_lt_iff₀ hm, mul_lt_mul_iff_of_pos_left hμ]

/-! ### Expectations under the posterior

Bayes' rule reweights the prior by the likelihood, so the posterior expectation of a statistic
compares with its prior expectation as the statistic's covariance with the likelihood:
Chebyshev's integral inequality. -/

section Expectation

variable [Fintype Ω] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0)
include hx

theorem integral_posterior (f : Ω → ℝ) :
    ∫ ω, f ω ∂((κ†μ) x) = (∫ ω, f ω * (κ ω).real {x} ∂μ) / (κ ∘ₘ μ).real {x} := by
  rw [integral_fintype .of_finite, integral_fintype .of_finite, Finset.sum_div]
  exact Finset.sum_congr rfl fun ω _ ↦ by
    rw [posterior_real_singleton κ μ hx, smul_eq_mul, smul_eq_mul]; ring

variable [IsProbabilityMeasure μ] {f : Ω → ℝ}

/-- Conditioning on an observation raises the expectation of a statistic that monovaries with
the observation's likelihood. -/
theorem integral_le_integral_posterior (hf : Monovary f fun ω ↦ (κ ω).real {x}) :
    ∫ ω, f ω ∂μ ≤ ∫ ω, f ω ∂((κ†μ) x) := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  rw [integral_posterior κ μ hx, le_div_iff₀ hm, Measure.comp_real_singleton_eq_integral]
  simpa [probReal_univ] using
    hf.integral_mul_integral_le_measureReal_univ_mul_integral (μ := μ) .of_finite .of_finite
      .of_finite

theorem integral_posterior_le_integral (hf : Antivary f fun ω ↦ (κ ω).real {x}) :
    ∫ ω, f ω ∂((κ†μ) x) ≤ ∫ ω, f ω ∂μ := by
  have hm : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  rw [integral_posterior κ μ hx, div_le_iff₀ hm, Measure.comp_real_singleton_eq_integral]
  simpa [probReal_univ] using
    hf.measureReal_univ_mul_integral_le_integral_mul_integral (μ := μ) .of_finite .of_finite
      .of_finite

end Expectation

section Pair

variable [Fintype Ω] {ω ω' : Ω} (hne : ω ≠ ω') (hsupp : ∀ ω'', μ {ω''} ≠ 0 → ω'' = ω ∨ ω'' = ω')
include hne hsupp

/-- Under two priors carried by the same two atoms, at an observation both atoms emit with
positive likelihood, the posterior mass of an atom is strictly increasing in its prior mass, so
Bayes' rule is prior-sensitive. -/
theorem posterior_real_singleton_lt_posterior_of_pair {ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hν : ∀ ω'', ν {ω''} ≠ 0 → ω'' = ω ∨ ω'' = ω') {x : 𝓧}
    (hκω : κ ω {x} ≠ 0) (hκω' : κ ω' {x} ≠ 0) (hμν : μ.real {ω} < ν.real {ω}) :
    ((κ†μ) x).real {ω} < ((κ†ν) x).real {ω} := by
  have hμm := Measure.comp_apply_singleton_ne_zero_of_pair κ μ hne hsupp hκω hκω'
  have hνm := Measure.comp_apply_singleton_ne_zero_of_pair κ ν hne hν hκω hκω'
  have hμ1 := measureReal_singleton_add_singleton_of_pair μ hne hsupp
  have hν1 := measureReal_singleton_add_singleton_of_pair ν hne hν
  have ha : 0 < (κ ω).real {x} := ENNReal.toReal_pos hκω (measure_ne_top _ _)
  have hb : 0 < (κ ω').real {x} := ENNReal.toReal_pos hκω' (measure_ne_top _ _)
  have hμr : 0 < (κ ∘ₘ μ).real {x} := ENNReal.toReal_pos hμm (measure_ne_top _ _)
  have hνr : 0 < (κ ∘ₘ ν).real {x} := ENNReal.toReal_pos hνm (measure_ne_top _ _)
  rw [posterior_real_singleton κ μ hμm, posterior_real_singleton κ ν hνm,
    div_lt_div_iff₀ hμr hνr, Measure.comp_real_singleton_of_pair κ μ hne hsupp,
    Measure.comp_real_singleton_of_pair κ ν hne hν,
    show μ.real {ω'} = 1 - μ.real {ω} by linarith,
    show ν.real {ω'} = 1 - ν.real {ω} by linarith]
  nlinarith [mul_pos (mul_pos ha hb) (sub_pos.2 hμν)]

variable [IsProbabilityMeasure μ] {x : 𝓧} (hx : (κ ∘ₘ μ) {x} ≠ 0) (hω : μ {ω} ≠ 0)
  (hω' : μ {ω'} ≠ 0)
include hx hω hω'

theorem real_lt_posterior_real_singleton_iff_of_pair :
    μ.real {ω} < ((κ†μ) x).real {ω} ↔ (κ ω').real {x} < (κ ω).real {x} := by
  have h1 := measureReal_singleton_add_singleton_of_pair μ hne hsupp
  have h2 : 0 < μ.real {ω'} := ENNReal.toReal_pos hω' (measure_ne_top _ _)
  rw [real_lt_posterior_real_singleton_iff κ μ hx hω,
    Measure.comp_real_singleton_of_pair κ μ hne hsupp,
    show μ.real {ω} = 1 - μ.real {ω'} by linarith]
  constructor <;> intro h <;> nlinarith

theorem posterior_real_singleton_lt_iff_of_pair :
    ((κ†μ) x).real {ω} < μ.real {ω} ↔ (κ ω).real {x} < (κ ω').real {x} := by
  have h1 := measureReal_singleton_add_singleton_of_pair μ hne hsupp
  have h2 : 0 < μ.real {ω'} := ENNReal.toReal_pos hω' (measure_ne_top _ _)
  rw [posterior_real_singleton_lt_iff κ μ hx hω,
    Measure.comp_real_singleton_of_pair κ μ hne hsupp,
    show μ.real {ω} = 1 - μ.real {ω'} by linarith]
  constructor <;> intro h <;> nlinarith

end Pair

/-! ### Stationarity

A state drawn from the posterior given an observation of a state drawn from the prior is
distributed as the prior. The chains that alternate the likelihood and the posterior therefore
leave the prior, the prior predictive and their joint invariant; the last is the Gibbs sampler for
the joint. -/

section Invariant

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} [StandardBorelSpace Ω]
  [Nonempty Ω] {κ : Kernel Ω 𝓧} [IsMarkovKernel κ] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A kernel equal to the posterior on the observations the prior predicts, composed after the
likelihood, leaves the prior invariant. -/
theorem invariant_comp_of_ae_eq_posterior {η : Kernel 𝓧 Ω} (hη : η =ᵐ[κ ∘ₘ μ] κ†μ) :
    (η ∘ₖ κ).Invariant μ := by
  rw [Kernel.Invariant, ← Measure.comp_assoc, Measure.comp_congr hη, posterior_comp_self]

theorem invariant_posterior_comp : (κ†μ ∘ₖ κ).Invariant μ :=
  invariant_comp_of_ae_eq_posterior (Filter.EventuallyEq.refl _ _)

theorem invariant_comp_posterior : (κ ∘ₖ κ†μ).Invariant (κ ∘ₘ μ) := by
  rw [Kernel.Invariant, ← Measure.comp_assoc, posterior_comp_self]

/-- The Gibbs sampler for the joint law of a state and its observation, which redraws the state
from the posterior given the observation and then the observation from the state, leaves the joint
invariant. -/
theorem invariant_id_prod_comp_prodMkLeft_posterior :
    ((Kernel.id ×ₖ κ) ∘ₖ (κ†μ).prodMkLeft Ω).Invariant (μ ⊗ₘ κ) := by
  rw [Kernel.Invariant, ← Measure.comp_assoc, Measure.prodMkLeft_comp_compProd, posterior_comp_self,
    Measure.compProd_eq_comp_prod]

end Invariant

section Const

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} [StandardBorelSpace Ω]
  [Nonempty Ω]

theorem posterior_const (ν : Measure 𝓧) [IsFiniteMeasure ν] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (Kernel.const Ω ν)†μ =ᵐ[ν] Kernel.const 𝓧 μ := by
  have h := ae_eq_posterior_of_compProd_eq (κ := Kernel.const Ω ν) (μ := μ)
    (η := Kernel.const 𝓧 μ) (by
      rw [Measure.const_comp, measure_univ, one_smul, Measure.compProd_const,
        Measure.compProd_const, Measure.prod_swap])
  rw [Measure.const_comp, measure_univ, one_smul] at h
  exact h.symm

end Const

end ProbabilityTheory
