/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Pragmatics.Agent.Basic

/-!
# Inverse planning

An observer who does not know an agent's reasons holds a prior `μ` over a population of agents
`p : Ω → Agent O S A`. The forward model `Agent.plan p β o` is the kernel that sends each member
of the population to its policy at the observation `o`, and what the observer believes after
seeing an action `x` is the posterior `(Agent.plan p β o)†μ` at `x`.

When the agents choose between two actions, seeing one of them raises the observer's expectation
of every statistic of the agents that monovaries with the value advantage of that action over the
other, since the share a policy gives an action is increasing in that advantage.

## Main definitions

* `Agent.plan`: the forward model of a population of agents at an observation.

## Main results

* `Agent.integral_le_integral_posterior_plan`: seeing an action raises the expectation of a
  statistic that monovaries with the action's value advantage on the agents of positive prior
  mass.
* `Agent.integral_posterior_plan_le_integral`: and lowers that of one that antivaries with it.

## References

* [baker-jara-ettinger-saxe-tenenbaum-2017]
* [houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Agent

variable {Ω O S A : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
  [MeasurableSpace O] [Countable O] [MeasurableSingletonClass O] [MeasurableSpace S]
  [Fintype A] [MeasurableSpace A]

/-- The forward model of a population of agents: each member's policy at the observation `o`. -/
noncomputable def plan (p : Ω → Agent O S A) (β : ℝ) (o : O) : Kernel Ω A :=
  Kernel.ofFunOfCountable fun ω ↦ (p ω).policy β o

variable (p : Ω → Agent O S A) (β : ℝ) (o : O)

@[simp] theorem plan_apply (ω : Ω) : plan p β o ω = (p ω).policy β o := rfl

instance (ω : Ω) : IsZeroOrProbabilityMeasure (plan p β o ω) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure ((p ω).policy β o))

instance : IsFiniteKernel (plan p β o) := ⟨1, ENNReal.one_lt_top, fun _ ↦ prob_le_one⟩

instance [Nonempty A] : IsMarkovKernel (plan p β o) :=
  ⟨fun ω ↦ inferInstanceAs (IsProbabilityMeasure ((p ω).policy β o))⟩

variable [MeasurableSingletonClass A]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] {β} {x x' : A} {f : Ω → ℝ}

/-- Every action has positive probability under the prior predictive. -/
theorem comp_plan_apply_singleton_ne_zero (x : A) : (plan p β o ∘ₘ μ) {x} ≠ 0 := by
  rw [Measure.comp_apply_singleton]
  intro h
  have hμ : ∀ ω, μ {ω} = 0 := fun ω ↦
    (mul_eq_zero.1 (Finset.sum_eq_zero_iff.1 h ω (Finset.mem_univ ω))).resolve_right
      ((p ω).policy_apply_singleton_ne_zero β o x)
  have := measure_univ (μ := μ)
  rw [← Finset.coe_univ, ← sum_measure_singleton, Finset.sum_eq_zero fun ω _ ↦ hμ ω] at this
  exact zero_ne_one this

variable [Nonempty Ω]

/-- Seeing an agent choose `x` over `x'` raises the observer's expectation of a statistic that
monovaries with the value advantage of `x` over `x'`. -/
theorem integral_le_integral_posterior_plan (hβ : 0 < β) (hxx' : x ≠ x')
    (hall : ∀ c, c = x ∨ c = x')
    (hf : MonovaryOn f (fun ω ↦ (p ω).value o x - (p ω).value o x') {ω | μ {ω} ≠ 0}) :
    ∫ ω, f ω ∂μ ≤ ∫ ω, f ω ∂((plan p β o)†μ) x := by
  refine integral_le_integral_posterior _ μ (comp_plan_apply_singleton_ne_zero p o μ x)
    fun i hi j hj hij ↦ ?_
  simp only [plan_apply, policy_real_of_pair hxx' hall] at hij
  exact hf hi hj ((mul_lt_mul_iff_of_pos_left hβ).1 (Real.sigmoid_lt_iff.1 hij))

/-- Seeing an agent choose `x` over `x'` lowers the observer's expectation of a statistic that
antivaries with the value advantage of `x` over `x'`. -/
theorem integral_posterior_plan_le_integral (hβ : 0 < β) (hxx' : x ≠ x')
    (hall : ∀ c, c = x ∨ c = x')
    (hf : AntivaryOn f (fun ω ↦ (p ω).value o x - (p ω).value o x') {ω | μ {ω} ≠ 0}) :
    ∫ ω, f ω ∂((plan p β o)†μ) x ≤ ∫ ω, f ω ∂μ := by
  refine integral_posterior_le_integral _ μ (comp_plan_apply_singleton_ne_zero p o μ x)
    fun i hi j hj hij ↦ ?_
  simp only [plan_apply, policy_real_of_pair hxx' hall] at hij
  exact hf hi hj ((mul_lt_mul_iff_of_pos_left hβ).1 (Real.sigmoid_lt_iff.1 hij))

end Agent
