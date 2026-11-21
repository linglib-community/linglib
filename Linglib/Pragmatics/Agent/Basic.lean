/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Core.Probability.Kernel.Softmax

/-!
# Agents

An agent observes in `O`, acts in `A`, and has reasons that concern a state in `S`: a belief, the
measure on states it holds at each observation, and a utility, what each action is worth to it at
each state. The value of an action at an observation is its expected utility under the belief
there, and the agent's policy at rationality `β` is the kernel from observations to actions that
soft-maximizes the value, the softmax of `β` times the value.

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
* `Agent.value_le_decisionValue`: no action is worth more than the decision
  value of the belief.

## References

* [baker-jara-ettinger-saxe-tenenbaum-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- An agent observes in `O`, acts in `A`, and has reasons that concern a state in `S`: what it
believes the state to be at each observation, and what each action is worth to it at each
state. -/
structure Agent (O S A : Type*) [MeasurableSpace O] [MeasurableSpace S] where
  /-- What the agent believes the state to be at each observation. -/
  belief : Kernel O S
  /-- What an action is worth to the agent at a state. -/
  utility : S → A → ℝ

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] (a : Agent O S A)

/-- The value of an action at an observation is its expected utility under the agent's belief
there. -/
noncomputable def value (o : O) (x : A) : ℝ := ∫ s, a.utility s x ∂(a.belief o)

@[simp] theorem value_mk (b : Kernel O S) (U : S → A → ℝ) (o : O) (x : A) :
    (mk b U).value o x = ∫ s, U s x ∂(b o) := rfl

theorem value_le_decisionValue (o : O) (x : A)
    (h : BddAbove (Set.range fun x ↦ a.value o x)) :
    a.value o x ≤ decisionValue a.utility (a.belief o) :=
  le_ciSup h x

variable [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]

/-- The agent's policy at rationality `β` soft-maximizes the value of its actions: the row at an
observation is proportional to the exponential of `β` times the value. -/
noncomputable def policy (β : ℝ) : Kernel O A :=
  Kernel.softmax fun o x ↦ ((β * a.value o x : ℝ) : EReal)

variable (β : ℝ)

instance : IsFiniteKernel (a.policy β) := inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty A] : IsMarkovKernel (a.policy β) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

variable {a β} {o : O} {x x' : A} [MeasurableSingletonClass A]

/-- The policy's share of an action is the real softmax of the scaled values. -/
theorem policy_real_singleton :
    (a.policy β o).real {x} = Real.softmax (fun x ↦ β * a.value o x) x :=
  Kernel.softmax_coe_real_singleton (fun o x ↦ β * a.value o x) o x

/-- At positive rationality the policy prefers the action of greater value. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (a.policy β o).real {x} < (a.policy β o).real {x'} ↔ a.value o x < a.value o x' :=
  (Kernel.softmax_coe_real_singleton_lt_iff (fun o x ↦ β * a.value o x) o).trans
    (mul_lt_mul_iff_right₀ hβ)

/-- With two actions, the policy's share of one is the logistic function of the scaled difference
in value. -/
theorem policy_real_of_pair (hxx' : x ≠ x') (hall : ∀ c, c = x ∨ c = x') :
    (a.policy β o).real {x} = Real.sigmoid (β * (a.value o x - a.value o x')) := by
  rw [policy, Kernel.softmax_real_singleton_of_pair hxx' (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
    (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

end Agent
