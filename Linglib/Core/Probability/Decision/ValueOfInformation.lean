/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Decision.Blackwell
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Decision.Risk.RiskIncrease

/-!
# The value of information of an experiment

An experiment is a Markov kernel `κ : Kernel Θ 𝓧` that draws an observation from a parameter.
An agent with prior `π` who values a belief `μ` at `V μ` expects, before observing, the value
of the posterior `κ†π`; the value of information `valueOfInformation V κ π` is that expectation
less the value of the prior. DeGroot calls it the information in the experiment when `V` is the
negative of an uncertainty function, and Lindley's measure of information is the case of
Shannon entropy.

The decision value `decisionValue U μ` of a belief is the best expected utility of an action.
For it, the value of information is the risk increase of mathlib's decision theory at the
regret loss `C − U`, so information never has negative value, and garbling an experiment never
raises its value, the forward direction of Blackwell's comparison of experiments. For an
experiment that observes a classifier `f`, the value of information is the probability-weighted
value of the prior conditioned on each fibre of `f`; a fixed statistic gains nothing, which is the
law of total expectation over the fibres, and the converse of Blackwell's theorem says that a
classifier never worth more than `f` factors through `f`. Observing the parameter itself leaves a
point-mass belief, so its value is the expected value of perfect information, and no experiment
is worth more.

## Main definitions

* `valueOfInformation V κ π`: the expected value of the posterior less the value of the prior.
* `decisionValue U μ`: the best expected utility of an action under the belief `μ`.

## Main statements

* `hasArgminEstimator_of_finite`: with countably many observations and finitely many actions,
  a pointwise minimizer of the posterior expected loss is an argmin estimator.
* `riskIncrease_ofReal_sub`: at the regret loss, the risk increase is the value of information
  of the decision value.
* `valueOfInformation_decisionValue_nonneg`: information has nonnegative value.
* `valueOfInformation_decisionValue_comp_le`: a garbled experiment is worth no more.
* `valueOfInformation_const`: an experiment whose law does not depend on the parameter is
  worth nothing.
* `valueOfInformation_deterministic`, `sum_measureReal_mul_integral_cond`: the value of observing
  a classifier sums over its fibres, and the law of total expectation over them.
* `exists_eq_comp_of_forall_valueOfInformation_le`: a classifier never worth more than `f`
  factors through `f`.
* `valueOfInformation_id`, `valueOfInformation_decisionValue_le_id`: observing the parameter is
  worth the expected value of its point-mass beliefs, and no experiment is worth more.

## Implementation notes

The decision value is a supremum over the action type, `0` when there is no action. The
theorems about it assume finitely many parameters, observations and actions, and the regret
bound `C` stays inside the proofs of the inequalities.

## References

* [degroot-1962]
* [lindley-1956]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}

section ArgminEstimator

variable {m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace Θ] [Nonempty Θ] [Countable 𝓧]
  [MeasurableSingletonClass 𝓧] [Finite 𝓨] [Nonempty 𝓨]

theorem hasArgminEstimator_of_finite (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] : HasArgminEstimator ℓ P π := by
  choose f hf using fun x ↦ Finite.exists_min fun y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x
  exact ⟨f, ⟨measurable_of_countable f, ae_of_all _ fun x ↦
    le_antisymm (le_iInf (hf x)) (iInf_le _ _)⟩⟩

end ArgminEstimator

theorem _root_.MeasureTheory.Measure.integral_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure 𝓧} {κ : Kernel 𝓧 Θ} {f : Θ → E} (hf : Integrable f (κ ∘ₘ μ)) :
    ∫ θ, f θ ∂(κ ∘ₘ μ) = ∫ x, ∫ θ, f θ ∂(κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- The value of information of the experiment `κ` to an agent with prior `π` who values a
belief by `V` is the expected value of the posterior less the value of the prior. -/
noncomputable def valueOfInformation [StandardBorelSpace Θ] [Nonempty Θ] (V : Measure Θ → ℝ)
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] : ℝ :=
  ∫ x, V ((κ†π) x) ∂(κ ∘ₘ π) - V π

/-- The decision value of a belief `μ` is the best expected utility of an action under `μ`. -/
noncomputable def decisionValue (U : Θ → 𝓨 → ℝ) (μ : Measure Θ) : ℝ := ⨆ a, ∫ θ, U θ a ∂μ

section Basic

variable [StandardBorelSpace Θ] [Nonempty Θ] (κ : Kernel Θ 𝓧) [IsFiniteKernel κ]
  (π : Measure Θ) [IsFiniteMeasure π]

theorem valueOfInformation_smul (V : Measure Θ → ℝ) (c : ℝ) :
    valueOfInformation (c • V) κ π = c * valueOfInformation V κ π := by
  simp only [valueOfInformation, Pi.smul_apply, smul_eq_mul, integral_const_mul, mul_sub]

omit [IsFiniteKernel κ] in
theorem valueOfInformation_const (V : Measure Θ → ℝ) (ν : Measure 𝓧) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] : valueOfInformation V (Kernel.const Θ ν) π = 0 := by
  rw [valueOfInformation, Measure.const_comp, measure_univ, one_smul, sub_eq_zero,
    integral_congr_ae ((posterior_const ν π).mono fun x hx ↦ congrArg V hx)]
  simp

theorem valueOfInformation_id (V : Measure Θ → ℝ) :
    valueOfInformation V Kernel.id π = ∫ θ, V (Measure.dirac θ) ∂π - V π := by
  rw [valueOfInformation, Measure.id_comp]
  congr 1
  exact integral_congr_ae
    ((posterior_id π).mono fun θ hθ ↦ congrArg V (hθ.trans (Kernel.id_apply θ)))

theorem valueOfInformation_integral [Finite Θ] [MeasurableSingletonClass Θ] [Finite 𝓧]
    [MeasurableSingletonClass 𝓧] (g : Θ → ℝ) (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
    (π : Measure Θ) [IsProbabilityMeasure π] :
    valueOfInformation (fun ν ↦ ∫ θ, g θ ∂ν) κ π = 0 := by
  rw [valueOfInformation, sub_eq_zero, ← Measure.integral_comp .of_finite, posterior_comp_self]

end Basic

section DecisionValue

variable {U : Θ → 𝓨 → ℝ}

theorem decisionValue_smul {c : ℝ} (hc : 0 ≤ c) (μ : Measure Θ) :
    decisionValue (c • U) μ = c * decisionValue U μ := by
  simp only [decisionValue, Pi.smul_apply, smul_eq_mul, integral_const_mul,
    Real.mul_iSup_of_nonneg hc]

@[simp]
theorem decisionValue_dirac [MeasurableSingletonClass Θ] (θ : Θ) :
    decisionValue U (Measure.dirac θ) = ⨆ a, U θ a := by
  simp [decisionValue]

variable [Finite 𝓨]

theorem integral_le_decisionValue (μ : Measure Θ) (a : 𝓨) : ∫ θ, U θ a ∂μ ≤ decisionValue U μ :=
  le_ciSup (f := fun a ↦ ∫ θ, U θ a ∂μ) (Set.finite_range _).bddAbove a

end DecisionValue

/-! ### The decision value and the risk increase -/

section Regret

variable [Finite Θ] [MeasurableSingletonClass Θ] [Finite 𝓨] [Nonempty 𝓨] {U : Θ → 𝓨 → ℝ}
  {C : ℝ} (hC : ∀ θ a, U θ a ≤ C)
include hC

omit [Finite 𝓨] in
theorem decisionValue_le (μ : Measure Θ) [IsProbabilityMeasure μ] : decisionValue U μ ≤ C :=
  ciSup_le fun a ↦ (integral_mono .of_finite (integrable_const C) (hC · a)).trans (by simp)

theorem iInf_lintegral_ofReal_sub (μ : Measure Θ) [IsProbabilityMeasure μ] :
    ⨅ a, ∫⁻ θ, ENNReal.ofReal (C - U θ a) ∂μ = ENNReal.ofReal (C - decisionValue U μ) := by
  have h a : ∫⁻ θ, ENNReal.ofReal (C - U θ a) ∂μ = ENNReal.ofReal (C - ∫ θ, U θ a ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal .of_finite
        (ae_of_all _ fun θ ↦ sub_nonneg.2 (hC θ a)),
      integral_sub (integrable_const C) .of_finite, integral_const, probReal_univ, one_smul]
  simp_rw [h]
  obtain ⟨a, ha⟩ := Finite.exists_max fun a ↦ ∫ θ, U θ a ∂μ
  have hv : decisionValue U μ = ∫ θ, U θ a ∂μ :=
    le_antisymm (ciSup_le ha) (integral_le_decisionValue μ a)
  rw [hv]
  exact le_antisymm (iInf_le _ a) (le_iInf fun b ↦ ENNReal.ofReal_le_ofReal (by linarith [ha b]))

variable [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓧] [MeasurableSingletonClass 𝓧]
  (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (π : Measure Θ) [IsProbabilityMeasure π]

omit [Finite 𝓨] in
private theorem integral_decisionValue_posterior_le :
    ∫ x, decisionValue U ((κ†π) x) ∂(κ ∘ₘ π) ≤ C :=
  (integral_mono .of_finite (integrable_const C) fun _ ↦ decisionValue_le hC _).trans (by simp)

variable [MeasurableSpace 𝓨] [MeasurableSingletonClass 𝓨]

theorem bayesRisk_ofReal_sub :
    bayesRisk (fun θ a ↦ ENNReal.ofReal (C - U θ a)) κ π =
      ENNReal.ofReal (C - ∫ x, decisionValue U ((κ†π) x) ∂(κ ∘ₘ π)) := by
  rw [(hasArgminEstimator_of_finite _ κ π).bayesRisk_eq (measurable_of_countable _)]
  simp_rw [iInf_lintegral_ofReal_sub hC]
  rw [← ofReal_integral_eq_lintegral_ofReal .of_finite
      (ae_of_all _ fun x ↦ sub_nonneg.2 (decisionValue_le hC _)),
    integral_sub (integrable_const C) .of_finite, integral_const, probReal_univ, one_smul]

theorem riskIncrease_ofReal_sub :
    riskIncrease (fun θ a ↦ ENNReal.ofReal (C - U θ a)) κ π =
      ENNReal.ofReal (valueOfInformation (decisionValue U) κ π) := by
  rw [riskIncrease_eq_iInf_sub (measurable_of_countable _), bayesRisk_ofReal_sub hC,
    iInf_lintegral_ofReal_sub hC,
    ← ENNReal.ofReal_sub _ (sub_nonneg.2 (integral_decisionValue_posterior_le hC κ π)),
    valueOfInformation]
  congr 1
  ring

end Regret

section Inequalities

variable [Finite Θ] [MeasurableSingletonClass Θ] [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓧]
  [MeasurableSingletonClass 𝓧] [Finite 𝓨] (U : Θ → 𝓨 → ℝ) (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
  (π : Measure Θ) [IsProbabilityMeasure π]

theorem valueOfInformation_decisionValue_nonneg : 0 ≤ valueOfInformation (decisionValue U) κ π := by
  rcases isEmpty_or_nonempty 𝓨 with h𝓨 | h𝓨
  · simp [valueOfInformation, decisionValue]
  let _ : MeasurableSpace 𝓨 := ⊤
  have : MeasurableSingletonClass 𝓨 := ⟨fun _ ↦ trivial⟩
  obtain ⟨C, hC⟩ := Finite.exists_le (Function.uncurry U)
  replace hC : ∀ θ a, U θ a ≤ C := fun θ a ↦ hC (θ, a)
  have h := bayesRisk_le_iInf (m𝓨 := inferInstance)
    (measurable_of_countable (Function.uncurry fun θ a ↦ ENNReal.ofReal (C - U θ a))) κ π
  rw [bayesRisk_ofReal_sub hC, iInf_lintegral_ofReal_sub hC,
    ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 (decisionValue_le hC π))] at h
  rw [valueOfInformation]
  linarith

theorem valueOfInformation_decisionValue_comp_le {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'}
    [Finite 𝓧'] [MeasurableSingletonClass 𝓧'] (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    valueOfInformation (decisionValue U) (η ∘ₖ κ) π ≤ valueOfInformation (decisionValue U) κ π := by
  rcases isEmpty_or_nonempty 𝓨 with h𝓨 | h𝓨
  · simp [valueOfInformation, decisionValue]
  let _ : MeasurableSpace 𝓨 := ⊤
  have : MeasurableSingletonClass 𝓨 := ⟨fun _ ↦ trivial⟩
  obtain ⟨C, hC⟩ := Finite.exists_le (Function.uncurry U)
  replace hC : ∀ θ a, U θ a ≤ C := fun θ a ↦ hC (θ, a)
  have h := riskIncrease_comp_le (fun θ a ↦ ENNReal.ofReal (C - U θ a)) κ π η
  rwa [riskIncrease_ofReal_sub hC, riskIncrease_ofReal_sub hC,
    ENNReal.ofReal_le_ofReal_iff (valueOfInformation_decisionValue_nonneg U κ π)] at h

theorem valueOfInformation_decisionValue_le_id :
    valueOfInformation (decisionValue U) κ π ≤
      valueOfInformation (decisionValue U) Kernel.id π := by
  simpa only [Kernel.comp_id] using valueOfInformation_decisionValue_comp_le U Kernel.id π κ

end Inequalities

/-! ### Deterministic experiments -/

section Deterministic

variable [Finite Θ] [MeasurableSingletonClass Θ] [StandardBorelSpace Θ] [Nonempty Θ]
  [Fintype 𝓧] [MeasurableSingletonClass 𝓧]

theorem valueOfInformation_deterministic (V : Measure Θ → ℝ) {f : Θ → 𝓧} (hf : Measurable f)
    (π : Measure Θ) [IsFiniteMeasure π] :
    valueOfInformation V (Kernel.deterministic f hf) π =
      ∑ x, π.real (f ⁻¹' {x}) * V π[|f ⁻¹' {x}] - V π := by
  rw [valueOfInformation, integral_fintype .of_finite, Measure.deterministic_comp_eq_map]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul, map_measureReal_apply hf (measurableSet_singleton x)]
  rcases eq_or_ne (π (f ⁻¹' {x})) 0 with h | h
  · simp [measureReal_def, h]
  · rw [posterior_deterministic_eq_cond _ hf h]

theorem valueOfInformation_decisionValue_le_of_factorsThrough [Finite 𝓨] (U : Θ → 𝓨 → ℝ)
    {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'} [Finite 𝓧'] [MeasurableSingletonClass 𝓧']
    {f : Θ → 𝓧} {g : Θ → 𝓧'} (hf : Measurable f) (hg : Measurable g) (h : g.FactorsThrough f)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    valueOfInformation (decisionValue U) (Kernel.deterministic g hg) π ≤
      valueOfInformation (decisionValue U) (Kernel.deterministic f hf) π := by
  obtain ⟨θ₀⟩ := ‹Nonempty Θ›
  have hψ := h.extend_comp (e' := fun _ ↦ g θ₀)
  have := valueOfInformation_decisionValue_comp_le U (Kernel.deterministic f hf) π
    (Kernel.deterministic (Function.extend f g fun _ ↦ g θ₀) (measurable_of_countable _))
  simp only [Kernel.deterministic_comp_deterministic, hψ] at this
  exact this

omit [MeasurableSingletonClass 𝓧] in
theorem sum_measureReal_mul_integral_cond (g : Θ → ℝ) (f : Θ → 𝓧) (π : Measure Θ)
    [IsProbabilityMeasure π] :
    ∑ x, π.real (f ⁻¹' {x}) * ∫ θ, g θ ∂π[|f ⁻¹' {x}] = ∫ θ, g θ ∂π := by
  let _ : MeasurableSpace 𝓧 := ⊤
  have : MeasurableSingletonClass 𝓧 := ⟨fun _ ↦ trivial⟩
  have h := valueOfInformation_integral g (Kernel.deterministic f (measurable_of_countable f)) π
  rwa [valueOfInformation_deterministic, sub_eq_zero] at h

variable {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'} [Fintype 𝓧'] [MeasurableSingletonClass 𝓧']
  [Nonempty 𝓧']

theorem exists_eq_comp_of_forall_valueOfInformation_le [Fintype Θ] (f : Θ → 𝓧) (g : Θ → 𝓧')
    (h : ∀ U : Θ → 𝓧' → ℝ,
      valueOfInformation (decisionValue U) (Kernel.deterministic g (measurable_of_countable g))
          (uniformOn Set.univ) ≤
        valueOfInformation (decisionValue U) (Kernel.deterministic f (measurable_of_countable f))
          (uniformOn Set.univ)) :
    ∃ ψ : 𝓧 → 𝓧', g = ψ ∘ f := by
  refine (Kernel.deterministic_isGarblingOf_deterministic_iff (measurable_of_countable f)
    (measurable_of_countable g)).1 (isGarblingOf_of_bayesRisk_uniform_le fun ℓ hℓ ↦ ?_)
  have hπ : ((Fintype.card Θ : ℝ≥0∞)⁻¹ • Measure.count : Measure Θ) = uniformOn Set.univ :=
    Measure.ext fun s _ ↦ by
      rw [uniformOn_univ, Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul]
  have hU : ∀ θ x', -(ℓ θ x').toReal ≤ 0 := fun _ _ ↦ neg_nonpos.2 ENNReal.toReal_nonneg
  have hℓ' : ℓ = fun θ x' ↦ ENNReal.ofReal (0 - -(ℓ θ x').toReal) := by
    ext θ x'
    simp [ENNReal.ofReal_toReal (hℓ θ x')]
  rw [hπ, hℓ', bayesRisk_ofReal_sub hU, bayesRisk_ofReal_sub hU]
  refine ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ 0)
  have := h fun θ x' ↦ -(ℓ θ x').toReal
  rw [valueOfInformation, valueOfInformation] at this
  linarith

end Deterministic

end ProbabilityTheory
