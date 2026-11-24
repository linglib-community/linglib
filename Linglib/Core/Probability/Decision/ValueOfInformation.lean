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
public import Linglib.Core.Analysis.Convex.Bregman
public import Linglib.Core.Analysis.Convex.Jensen

/-!
# The value of information of an experiment

An experiment is a Markov kernel `κ : Kernel Θ 𝓧`: for each value of a parameter, it gives the
distribution of an observation. Consider an agent with prior `π` who assigns the value `V μ` to
holding the belief `μ`. After observing, the agent holds the posterior `κ†π`. We define the value of
information `valueOfInformation V κ π` as the expected value of the posterior minus the value of the
prior.

The basic facts hold for every `V` that is convex on beliefs. Information cannot hurt: the prior is
a mixture of the posteriors, so this is Jensen's inequality. And garbling an experiment cannot
raise its value, because the posteriors of the garbled experiment are mixtures of the original
ones. See `valueOfInformation_nonneg_of_convexOn` and `valueOfInformation_comp_le_of_convexOn`.

The main example is the decision value `decisionValue U μ`, the best expected utility that an agent
with belief `μ` can obtain. For it we also prove Blackwell's theorem comparing experiments.

## Main definitions

* `valueOfInformation V κ π`: the expected value of the posterior less the value of the prior.
* `decisionValue U μ`: the best expected utility of an action under the belief `μ`.

## Main statements

* `hasArgminEstimator_of_finite`: with countably many observations and finitely many actions,
  a pointwise minimizer of the posterior expected loss is an argmin estimator.
* `riskIncrease_ofReal_sub`: at the regret loss, the risk increase is the value of information
  of the decision value.
* `valueOfInformation_nonneg_of_convexOn`: information has nonnegative value for a value
  function convex on beliefs, and so for the decision value
  (`valueOfInformation_decisionValue_nonneg`).
* `valueOfInformation_eq_integral_bregmanDiv`: the value of information is the expected Bregman
  divergence from the prior to the posterior.
* `valueOfInformation_comp_le_of_convexOn`: a garbled experiment is worth no more, for a value
  function convex on beliefs.
* `valueOfInformation_const`: an experiment whose law does not depend on the parameter is
  worth nothing.
* `valueOfInformation_deterministic`, `sum_measureReal_mul_integral_cond`,
  `integral_integral_cond_preimage`: the value of observing a classifier sums over its fibres,
  and the law of total expectation over them, as a sum and as an integral.
* `exists_eq_comp_of_forall_valueOfInformation_le`: a classifier never worth more than `f`
  factors through `f`.
* `valueOfInformation_id`, `valueOfInformation_decisionValue_le_id`: observing the parameter is
  worth the expected value of its point-mass beliefs, and no experiment is worth more.
* `valueOfInformation_decisionValue_eq_id_iff`: an experiment is worth that much exactly when,
  at each observation, one action is best at every parameter still possible.

## Implementation notes

The decision value is a supremum over the action type, `0` when there is no action. The
theorems about it assume finitely many parameters, observations and actions, and the regret
bound `C` stays inside the proofs of the inequalities.

## TODO

* The value functions here are on finitely many parameters and observations. In general Jensen's
  inequality needs a topology on beliefs.
* Negative entropy as a value function, whose value of information is mutual information and
  whose Bregman divergence is the Kullback–Leibler divergence.

## References

* [degroot-1962]
* [lindley-1956]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}

section ArgminEstimator

variable {m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace Θ] [Nonempty Θ] [Countable 𝓧]
  [MeasurableSingletonClass 𝓧] [Finite 𝓨] [Nonempty 𝓨]

/-- With countably many observations and finitely many estimates, choosing a minimizer of the
posterior expected loss at each observation gives an argmin estimator. -/
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
/-- An experiment whose law does not depend on the parameter is worth nothing. -/
theorem valueOfInformation_const (V : Measure Θ → ℝ) (ν : Measure 𝓧) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] : valueOfInformation V (Kernel.const Θ ν) π = 0 := by
  rw [valueOfInformation, Measure.const_comp, measure_univ, one_smul, sub_eq_zero,
    integral_congr_ae ((posterior_const ν π).mono fun x hx ↦ congrArg V hx)]
  simp

/-- Observing the parameter itself leaves a point-mass belief at each value. -/
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

/-! ### Convex value functions -/

/-- A mixture of two probability measures is a probability measure. -/
theorem convex_setOf_isProbabilityMeasure :
    Convex ℝ≥0 {μ : Measure Θ | IsProbabilityMeasure μ} := by
  intro μ hμ ν hν a b _ _ hab
  have : IsProbabilityMeasure μ := hμ
  have : IsProbabilityMeasure ν := hν
  refine ⟨?_⟩
  simp only [FunLike.coe_add, Measure.coe_nnreal_smul_apply, Pi.add_apply, measure_univ, mul_one]
  exact_mod_cast hab

/-- The decision value is convex on beliefs: a mixture of beliefs is worth at most the mixture
of their values, since one action has to serve both. -/
theorem convexOn_decisionValue [Finite Θ] [MeasurableSingletonClass Θ] [Finite 𝓨]
    (U : Θ → 𝓨 → ℝ) : ConvexOn ℝ≥0 {μ : Measure Θ | IsProbabilityMeasure μ} (decisionValue U) := by
  refine ⟨convex_setOf_isProbabilityMeasure, fun μ hμ ν hν a b _ _ _ ↦ ?_⟩
  have : IsProbabilityMeasure μ := hμ
  have : IsProbabilityMeasure ν := hν
  rcases isEmpty_or_nonempty 𝓨 with h | h
  · simp [decisionValue]
  refine ciSup_le fun y ↦ ?_
  rw [integral_add_measure .of_finite .of_finite, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, NNReal.smul_def,
    NNReal.smul_def]
  exact add_le_add (mul_le_mul_of_nonneg_left (integral_le_decisionValue μ y) a.2)
    (mul_le_mul_of_nonneg_left (integral_le_decisionValue ν y) b.2)

/-- The posterior of a garbled experiment at an observation, weighted by the probability of the
observation, is the mixture of the posteriors of the original experiment weighted by the joint
probabilities. -/
theorem smul_posterior_comp [Fintype Θ] [MeasurableSingletonClass Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [Fintype 𝓧] [MeasurableSingletonClass 𝓧] {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'}
    [MeasurableSingletonClass 𝓧'] (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (π : Measure Θ)
    [IsProbabilityMeasure π] (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] (x' : 𝓧') :
    ((η ∘ₖ κ) ∘ₘ π) {x'} • ((η ∘ₖ κ)†π) x' = ∑ x, ((κ ∘ₘ π) {x} * η x {x'}) • (κ†π) x := by
  refine Measure.ext_of_singleton fun θ ↦ ?_
  rw [smul_apply, smul_eq_mul, comp_mul_posterior_singleton, Kernel.comp_apply_singleton,
    FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [smul_apply, smul_eq_mul, mul_right_comm, comp_mul_posterior_singleton]
  ring

section Convex

variable [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓧] [MeasurableSingletonClass 𝓧]
  (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (π : Measure Θ) [IsProbabilityMeasure π]

/-- Information has nonnegative value for a value function that is convex on beliefs, since the
prior is the mixture of the posteriors. -/
theorem valueOfInformation_nonneg_of_convexOn {V : Measure Θ → ℝ}
    (hV : ConvexOn ℝ≥0 {μ : Measure Θ | IsProbabilityMeasure μ} V) :
    0 ≤ valueOfInformation V κ π := by
  cases nonempty_fintype 𝓧
  have hne (x : 𝓧) : (κ ∘ₘ π) {x} ≠ ∞ := measure_ne_top _ _
  have hw : ∑ x, ((κ ∘ₘ π) {x}).toNNReal = 1 := by
    apply ENNReal.coe_injective
    simp [ENNReal.coe_toNNReal (hne _)]
  have hp : ∑ x, ((κ ∘ₘ π) {x}).toNNReal • (κ†π) x = π :=
    (Finset.sum_congr rfl fun x _ ↦ by
      rw [ENNReal.smul_def, ENNReal.coe_toNNReal (hne x)]).trans <| by
      rw [← Measure.sum_fintype, ← Measure.comp_eq_sum_of_countable, posterior_comp_self]
  have h := hV.map_sum_smul_le (t := Finset.univ) (w := fun x ↦ ((κ ∘ₘ π) {x}).toNNReal)
    (p := fun x ↦ (κ†π) x) (fun _ _ ↦ bot_le) hw
    fun x _ ↦ (inferInstance : IsProbabilityMeasure ((κ†π) x))
  rw [hp] at h
  rw [valueOfInformation, integral_fintype .of_finite, sub_nonneg]
  exact h.trans_eq (Finset.sum_congr rfl fun x _ ↦ by
    rw [NNReal.smul_def, measureReal_def, ENNReal.coe_toNNReal_eq_toReal])

/-- The value of information is the expected Bregman divergence of the value function from the
prior to the posterior, along any `g` whose expectation over the posteriors is its value at the
prior. -/
theorem valueOfInformation_eq_integral_bregmanDiv (V g : Measure Θ → ℝ)
    (hg : ∫ x, g ((κ†π) x) ∂(κ ∘ₘ π) = g π) :
    valueOfInformation V κ π = ∫ x, bregmanDiv V g π ((κ†π) x) ∂(κ ∘ₘ π) := by
  simp only [bregmanDiv, valueOfInformation]
  rw [integral_sub .of_finite .of_finite, integral_sub .of_finite .of_finite,
    integral_sub .of_finite .of_finite, hg]
  simp

/-- The value of information is the expected Bregman divergence of the value function from the
prior to the posterior, along the expectation of any function of the parameter. -/
theorem valueOfInformation_eq_integral_bregmanDiv_integral [Finite Θ] [MeasurableSingletonClass Θ]
    (V : Measure Θ → ℝ) (g : Θ → ℝ) :
    valueOfInformation V κ π =
      ∫ x, bregmanDiv V (fun μ ↦ ∫ θ, g θ ∂μ) π ((κ†π) x) ∂(κ ∘ₘ π) :=
  valueOfInformation_eq_integral_bregmanDiv κ π V _ <| by
    have h := valueOfInformation_integral g κ π
    rwa [valueOfInformation, sub_eq_zero] at h

/-- Garbling an experiment cannot raise its value for a value function that is convex on
beliefs. -/
theorem valueOfInformation_comp_le_of_convexOn [Finite Θ] [MeasurableSingletonClass Θ]
    {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'} [Finite 𝓧'] [MeasurableSingletonClass 𝓧']
    {V : Measure Θ → ℝ} (hV : ConvexOn ℝ≥0 {μ : Measure Θ | IsProbabilityMeasure μ} V)
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    valueOfInformation V (η ∘ₖ κ) π ≤ valueOfInformation V κ π := by
  cases nonempty_fintype Θ
  cases nonempty_fintype 𝓧
  cases nonempty_fintype 𝓧'
  rw [valueOfInformation, valueOfInformation, sub_le_sub_iff_right, integral_fintype .of_finite,
    integral_fintype .of_finite]
  simp only [smul_eq_mul, measureReal_def]
  have hm' (x' : 𝓧') : ((η ∘ₖ κ) ∘ₘ π) {x'} = ∑ x, (κ ∘ₘ π) {x} * η x {x'} := by
    rw [← Measure.comp_assoc, Measure.comp_apply_singleton]
  have hfin (x : 𝓧) (x' : 𝓧') : (κ ∘ₘ π) {x} * η x {x'} ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have key (x' : 𝓧') : (((η ∘ₖ κ) ∘ₘ π) {x'}).toReal * V (((η ∘ₖ κ)†π) x') ≤
      ∑ x, ((κ ∘ₘ π) {x} * η x {x'}).toReal * V ((κ†π) x) := by
    rcases eq_or_ne (((η ∘ₖ κ) ∘ₘ π) {x'}) 0 with h0 | h0
    · have hz (x : 𝓧) : (κ ∘ₘ π) {x} * η x {x'} = 0 :=
        Finset.sum_eq_zero_iff.1 ((hm' x').symm.trans h0) x (Finset.mem_univ x)
      simp [h0, hz]
    · have hc : ((η ∘ₖ κ) ∘ₘ π) {x'} ≠ ∞ := measure_ne_top _ _
      have hwt (x : 𝓧) : (κ ∘ₘ π) {x} * η x {x'} * (((η ∘ₖ κ) ∘ₘ π) {x'})⁻¹ ≠ ∞ :=
        ENNReal.mul_ne_top (hfin x x') (ENNReal.inv_ne_top.2 h0)
      have hw : ∑ x, ((κ ∘ₘ π) {x} * η x {x'} * (((η ∘ₖ κ) ∘ₘ π) {x'})⁻¹).toNNReal = 1 := by
        apply ENNReal.coe_injective
        push_cast
        simp_rw [ENNReal.coe_toNNReal (hwt _)]
        rw [← Finset.sum_mul, ← hm' x', ENNReal.mul_inv_cancel h0 hc]
      have hp : ∑ x, ((κ ∘ₘ π) {x} * η x {x'} * (((η ∘ₖ κ) ∘ₘ π) {x'})⁻¹).toNNReal • (κ†π) x =
          ((η ∘ₖ κ)†π) x' := by
        calc _ = ∑ x, (((η ∘ₖ κ) ∘ₘ π) {x'})⁻¹ • ((κ ∘ₘ π) {x} * η x {x'}) • (κ†π) x :=
              Finset.sum_congr rfl fun x _ ↦ by
                rw [ENNReal.smul_def, ENNReal.coe_toNNReal (hwt x), smul_smul, mul_comm]
          _ = (((η ∘ₖ κ) ∘ₘ π) {x'})⁻¹ • (((η ∘ₖ κ) ∘ₘ π) {x'} • ((η ∘ₖ κ)†π) x') := by
              rw [← Finset.smul_sum, smul_posterior_comp κ π η x']
          _ = ((η ∘ₖ κ)†π) x' := by rw [smul_smul, ENNReal.inv_mul_cancel h0 hc, one_smul]
      have hJ := hV.map_sum_smul_le (t := Finset.univ)
        (w := fun x ↦ ((κ ∘ₘ π) {x} * η x {x'} * (((η ∘ₖ κ) ∘ₘ π) {x'})⁻¹).toNNReal)
        (p := fun x ↦ (κ†π) x) (fun _ _ ↦ bot_le) hw
        fun x _ ↦ (inferInstance : IsProbabilityMeasure ((κ†π) x))
      rw [hp] at hJ
      refine (mul_le_mul_of_nonneg_left hJ ENNReal.toReal_nonneg).trans_eq ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [NNReal.smul_def, smul_eq_mul, ← mul_assoc, ENNReal.coe_toNNReal_eq_toReal,
        ← ENNReal.toReal_mul, mul_comm (((η ∘ₖ κ) ∘ₘ π) {x'}), mul_assoc,
        ENNReal.inv_mul_cancel h0 hc, mul_one]
  refine (Finset.sum_le_sum fun x' _ ↦ key x').trans_eq ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [ENNReal.toReal_mul]
  rw [← Finset.mul_sum, ← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _]
  simp

end Convex

/-- Along an action that is best at the prior, the Bregman divergence of the decision value to a
belief is what re-optimizing there gains over keeping that action. -/
theorem bregmanDiv_decisionValue {U : Θ → 𝓨 → ℝ} {a : 𝓨} {π : Measure Θ}
    (ha : ∫ θ, U θ a ∂π = decisionValue U π) (μ : Measure Θ) :
    bregmanDiv (decisionValue U) (fun ν ↦ ∫ θ, U θ a ∂ν) π μ =
      decisionValue U μ - ∫ θ, U θ a ∂μ := by
  rw [bregmanDiv, ha]
  ring

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

/-- At the regret loss `C − U`, the risk increase of an experiment is the value of information
of the decision value. -/
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

section Perfect

variable [Finite Θ] [MeasurableSingletonClass Θ] [Finite 𝓨] [Nonempty 𝓨] (U : Θ → 𝓨 → ℝ)
  (μ : Measure Θ) [IsFiniteMeasure μ]

/-- No belief is worth more than choosing the best action at each parameter. -/
theorem decisionValue_le_integral_iSup : decisionValue U μ ≤ ∫ θ, ⨆ a, U θ a ∂μ :=
  ciSup_le fun a ↦ integral_mono .of_finite .of_finite fun θ ↦
    le_ciSup (Set.finite_range (U θ)).bddAbove a

/-- A belief is worth as much as knowing the parameter exactly when one action is best at every
parameter it gives weight to. -/
theorem decisionValue_eq_integral_iSup_iff :
    decisionValue U μ = ∫ θ, ⨆ a, U θ a ∂μ ↔ ∃ a, ∀ θ, μ {θ} ≠ 0 → ∀ b, U θ b ≤ U θ a := by
  have hsup (θ : Θ) (a : 𝓨) : U θ a ≤ ⨆ b, U θ b := le_ciSup (Set.finite_range (U θ)).bddAbove a
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finite.exists_max fun a ↦ ∫ θ, U θ a ∂μ
    have hDV : decisionValue U μ = ∫ θ, U θ a ∂μ :=
      le_antisymm (ciSup_le ha) (integral_le_decisionValue μ a)
    have h0 : ∫ θ, ((⨆ b, U θ b) - U θ a) ∂μ = 0 := by
      rw [integral_sub .of_finite .of_finite, ← h, hDV, sub_self]
    have hae := (integral_eq_zero_iff_of_nonneg (fun θ ↦ sub_nonneg.2 (hsup θ a)) .of_finite).1 h0
    exact ⟨a, fun θ hθ b ↦ (hsup θ b).trans_eq (sub_eq_zero.1 (ae_iff_of_countable.1 hae θ hθ))⟩
  · rintro ⟨a, ha⟩
    refine le_antisymm (decisionValue_le_integral_iSup U μ)
      (le_trans (le_of_eq ?_) (integral_le_decisionValue μ a))
    exact integral_congr_ae (ae_iff_of_countable.2 fun θ hθ ↦
      le_antisymm (ciSup_le (ha θ hθ)) (hsup θ a))

end Perfect

section Inequalities

variable [Finite Θ] [MeasurableSingletonClass Θ] [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓧]
  [MeasurableSingletonClass 𝓧] [Finite 𝓨] (U : Θ → 𝓨 → ℝ) (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
  (π : Measure Θ) [IsProbabilityMeasure π]

/-- Information has nonnegative value to an expected-utility maximizer. -/
theorem valueOfInformation_decisionValue_nonneg :
    0 ≤ valueOfInformation (decisionValue U) κ π :=
  valueOfInformation_nonneg_of_convexOn κ π (convexOn_decisionValue U)

/-- Garbling an experiment cannot raise its value to an expected-utility maximizer. -/
theorem valueOfInformation_decisionValue_comp_le {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'}
    [Finite 𝓧'] [MeasurableSingletonClass 𝓧'] (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    valueOfInformation (decisionValue U) (η ∘ₖ κ) π ≤ valueOfInformation (decisionValue U) κ π :=
  valueOfInformation_comp_le_of_convexOn κ π (convexOn_decisionValue U) η

/-- No experiment is worth more than observing the parameter itself, the expected value of
perfect information. -/
theorem valueOfInformation_decisionValue_le_id :
    valueOfInformation (decisionValue U) κ π ≤
      valueOfInformation (decisionValue U) Kernel.id π := by
  simpa only [Kernel.comp_id] using valueOfInformation_decisionValue_comp_le U Kernel.id π κ

/-- An experiment is worth the value of perfect information exactly when, at each observation,
one action is best at every parameter that the prior and the experiment leave possible. -/
theorem valueOfInformation_decisionValue_eq_id_iff [Nonempty 𝓨] :
    valueOfInformation (decisionValue U) κ π = valueOfInformation (decisionValue U) Kernel.id π ↔
      ∀ x, ∃ a, ∀ θ, π {θ} ≠ 0 → κ θ {x} ≠ 0 → ∀ b, U θ b ≤ U θ a := by
  have htot : ∫ x, ∫ θ, ⨆ a, U θ a ∂(κ†π) x ∂(κ ∘ₘ π) = ∫ θ, ⨆ a, U θ a ∂π := by
    conv_rhs => rw [← posterior_comp_self (κ := κ) (μ := π)]
    exact (Measure.integral_comp .of_finite).symm
  rw [valueOfInformation, valueOfInformation_id]
  simp only [decisionValue_dirac]
  rw [sub_left_inj, ← htot,
    integral_eq_iff_of_ae_le .of_finite .of_finite
      (ae_of_all _ fun x ↦ decisionValue_le_integral_iSup U ((κ†π) x)),
    Filter.EventuallyEq, ae_iff_of_countable]
  refine forall_congr' fun x ↦ ?_
  by_cases hx : (κ ∘ₘ π) {x} = 0
  · refine iff_of_true (fun h ↦ (h hx).elim) ⟨Classical.arbitrary 𝓨, fun θ hθ hκ ↦ ?_⟩
    rw [Measure.bind_apply (.singleton x) κ.aemeasurable,
      lintegral_eq_zero_iff (κ.measurable_coe (.singleton x))] at hx
    exact (hκ (ae_iff_of_countable.1 hx θ hθ)).elim
  · rw [imp_iff_right hx, decisionValue_eq_integral_iSup_iff]
    exact exists_congr fun a ↦ forall_congr' fun θ ↦ by
      rw [posterior_apply_singleton_ne_zero_iff κ π hx, and_imp]

end Inequalities

/-! ### Deterministic experiments -/

/-- The integral of a function of the fibre of `f` through the parameter is its sum over the
fibres of `f`, weighted by their probabilities. -/
theorem integral_preimage_singleton [Fintype 𝓧] [MeasurableSingletonClass 𝓧] (F : Set Θ → ℝ)
    {f : Θ → 𝓧} (hf : Measurable f) (π : Measure Θ) [IsFiniteMeasure π] :
    ∫ θ, F (f ⁻¹' {f θ}) ∂π = ∑ x, π.real (f ⁻¹' {x}) * F (f ⁻¹' {x}) := by
  rw [← integral_map hf.aemeasurable (f := fun x ↦ F (f ⁻¹' {x}))
      Integrable.of_finite.aestronglyMeasurable, integral_fintype .of_finite]
  exact Finset.sum_congr rfl fun x _ ↦ by
    rw [smul_eq_mul, map_measureReal_apply hf (measurableSet_singleton x)]

section Deterministic

variable [Finite Θ] [MeasurableSingletonClass Θ] [StandardBorelSpace Θ] [Nonempty Θ]
  [Fintype 𝓧] [MeasurableSingletonClass 𝓧]

/-- The value of information of observing `f` is the decision value of the prior conditioned on
each fibre of `f`, weighted by the fibre's probability, less the decision value of the prior. -/
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
/-- Averaging the expectations conditional on the fibres of `f` recovers the expectation, the law
of total expectation. -/
theorem sum_measureReal_mul_integral_cond (g : Θ → ℝ) (f : Θ → 𝓧) (π : Measure Θ)
    [IsProbabilityMeasure π] :
    ∑ x, π.real (f ⁻¹' {x}) * ∫ θ, g θ ∂π[|f ⁻¹' {x}] = ∫ θ, g θ ∂π := by
  let _ : MeasurableSpace 𝓧 := ⊤
  have : MeasurableSingletonClass 𝓧 := ⟨fun _ ↦ trivial⟩
  have h := valueOfInformation_integral g (Kernel.deterministic f (measurable_of_countable f)) π
  rwa [valueOfInformation_deterministic, sub_eq_zero] at h

omit [MeasurableSingletonClass 𝓧] in
/-- The expectation of the expectation conditional on the fibre of `f` through the parameter is
the expectation, the law of total expectation as an integral. -/
theorem integral_integral_cond_preimage (g : Θ → ℝ) (f : Θ → 𝓧) (π : Measure Θ)
    [IsProbabilityMeasure π] : ∫ θ, ∫ ω, g ω ∂π[|f ⁻¹' {f θ}] ∂π = ∫ θ, g θ ∂π := by
  let _ : MeasurableSpace 𝓧 := ⊤
  have : MeasurableSingletonClass 𝓧 := ⟨fun _ ↦ trivial⟩
  rw [integral_preimage_singleton (fun s ↦ ∫ ω, g ω ∂π[|s]) (measurable_of_countable f),
    sum_measureReal_mul_integral_cond]

variable {𝓧' : Type*} {m𝓧' : MeasurableSpace 𝓧'} [Fintype 𝓧'] [MeasurableSingletonClass 𝓧']
  [Nonempty 𝓧']

/-- If observing `g` is never worth more than observing `f` to an expected-utility maximizer
with actions `𝓧'` and a uniform prior, then `g` factors through `f`. -/
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
      rw [uniformOn_univ, smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul]
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
