/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.Kernel.Softmax

/-!
# Agents

An agent observes in `O`, acts in `A`, and has reasons that concern a state in `S`: a belief, the
measure on states it holds at each observation, and a utility, what each action is worth to it at
each state. The value of an action at an observation is its expected utility under the belief
there, and the agent's policy at rationality `β` is the kernel from observations to actions that
soft-maximizes the value, the softmax of `β` times the value.

The value is a Bochner integral, so it is the expected utility when the utility of the action is
integrable against the belief and `0` otherwise, and the policy is defined for a countable type
of observations, as `Kernel.softmax` is.

Agents with different reasons may have the same policy, so the policy is the agent's behaviour
and the agent is what an observer of the behaviour infers. Language use is one kind of rational
action: a listener who acts on what she has understood is an agent whose belief is her
interpretation.

## Main definitions

* `Agent`: a belief and a utility.
* `Agent.value`: the expected utility of an action at an observation.
* `Agent.policy`: the soft-maximizing kernel from observations to actions.

## Main results

* `Agent.policy_real_singleton`: the policy's share of an action is the real
  softmax of the scaled values.
* `Agent.policy_real_lt_iff`: at positive rationality the policy prefers the
  action of greater value.

## References

* [baker-jara-ettinger-saxe-tenenbaum-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- An agent observes in `O`, acts in `A`, and has reasons that concern a state in `S`: what it
believes the state to be at each observation, and what each action is worth to it at each
state. -/
@[ext]
structure Agent (O S A : Type*) [MeasurableSpace O] [MeasurableSpace S] where
  /-- What the agent believes the state to be at each observation. -/
  belief : Kernel O S
  /-- What an action is worth to the agent at a state. -/
  utility : S → A → ℝ

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] (ag : Agent O S A)

/-- The value of an action at an observation is its expected utility under the agent's belief
there. -/
noncomputable def value (o : O) (x : A) : ℝ := ∫ s, ag.utility s x ∂(ag.belief o)

@[simp] theorem value_mk (b : Kernel O S) (U : S → A → ℝ) (o : O) (x : A) :
    (mk b U).value o x = ∫ s, U s x ∂(b o) := rfl

variable [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]

/-- The agent's policy at rationality `β` soft-maximizes the value of its actions: the row at an
observation is proportional to the exponential of `β` times the value. -/
noncomputable def policy (β : ℝ) : Kernel O A :=
  Kernel.softmax fun o x ↦ ((β * ag.value o x : ℝ) : EReal)

variable (β : ℝ)

instance : IsFiniteKernel (ag.policy β) := inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance (o : O) : IsZeroOrProbabilityMeasure (ag.policy β o) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.softmax _ o))

instance [Nonempty A] : IsMarkovKernel (ag.policy β) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

theorem policy_apply_singleton_ne_zero [MeasurableSingletonClass A] (o : O) (x : A) :
    ag.policy β o {x} ≠ 0 :=
  Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _

variable {ag β} {o : O} {x x' : A} [MeasurableSingletonClass A]

/-- The policy's share of an action is the real softmax of the scaled values. -/
theorem policy_real_singleton :
    (ag.policy β o).real {x} = Real.softmax (fun x ↦ β * ag.value o x) x :=
  Kernel.softmax_coe_real_singleton (fun o x ↦ β * ag.value o x) o x

/-- The policy gives every action positive probability. -/
theorem policy_real_singleton_pos : 0 < (ag.policy β o).real {x} := by
  have : Nonempty A := ⟨x⟩
  rw [policy_real_singleton]; exact Real.softmax_pos _ x

/-- At positive rationality the policy prefers the action of greater value. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (ag.policy β o).real {x} < (ag.policy β o).real {x'} ↔ ag.value o x < ag.value o x' :=
  (Kernel.softmax_coe_real_singleton_lt_iff (fun o x ↦ β * ag.value o x) o).trans
    (mul_lt_mul_iff_right₀ hβ)

/-- With two actions, the policy's share of one is the logistic function of the scaled difference
in value. -/
theorem policy_real_of_pair (hxx' : x ≠ x') (hall : ∀ c, c = x ∨ c = x') :
    (ag.policy β o).real {x} = Real.sigmoid (β * (ag.value o x - ag.value o x')) := by
  rw [policy, Kernel.softmax_real_singleton_of_pair hxx' (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
    (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

end Agent
