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
each state, which is `⊥` where the state rules the action out. The value of an action at an
observation is its expected utility under the belief there. An action is feasible there,
`Agent.Feasible`, when the belief gives no weight to a state that rules it out. The agent's policy
at rationality `β` is the kernel from observations to actions that soft-maximizes the value among
the feasible actions: the softmax of `β` times the value, with score `⊥` for an action that is not
feasible.

At a positive rationality the policy takes exactly the feasible actions with positive probability
(`Agent.policy_apply_singleton_ne_zero_iff`). An unconstrained agent, `Agent.IsUnconstrained`, for
whom every action is feasible, as for every agent with a real utility, has a policy that is the
softmax of the scaled values (`Agent.policy_real_singleton`) and prefers the action of greater
value (`Agent.policy_real_lt_iff`).

The value is a Bochner integral, so it is the expected utility when the utility of the action is
integrable against the belief and `0` otherwise, and the policy is defined for a countable type
of observations, as `Kernel.softmax` is.

Agents with different reasons may have the same policy, so the policy is the agent's behaviour
and the agent is what an observer of the behaviour infers. Language use is one kind of rational
action: a listener who acts on what she has understood is an agent whose belief is her
interpretation, and a speaker an agent whose utility is the logarithm of her listener's
probability of the state.

## Implementation notes

The value is real and feasibility is a separate predicate, so that an agent with a real utility is
used as before and only the policy mentions `⊥`. At rationality zero the score of an action that
is not feasible is `0 * ⊥ = 0`, and the policy is uniform over all the actions.

## References

* [baker-jara-ettinger-saxe-tenenbaum-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- An agent observes in `O`, acts in `A`, and has reasons that concern a state in `S`: what it
believes the state to be at each observation, and what each action is worth to it at each state,
`⊥` where the state rules the action out. -/
@[ext]
structure Agent (O S A : Type*) [MeasurableSpace O] [MeasurableSpace S] where
  /-- What the agent believes the state to be at each observation. -/
  belief : Kernel O S
  /-- What an action is worth to the agent at a state, `⊥` where the state rules it out. -/
  utility : S → A → EReal

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] (a : Agent O S A)

/-- The value of an action at an observation is its expected utility under the agent's belief
there. -/
noncomputable def value (o : O) (x : A) : ℝ := ∫ s, (a.utility s x).toReal ∂(a.belief o)

@[simp] theorem value_mk (b : Kernel O S) (U : S → A → EReal) (o : O) (x : A) :
    (mk b U).value o x = ∫ s, (U s x).toReal ∂(b o) := rfl

/-- A real utility has its expectation as value. -/
theorem value_coe (b : Kernel O S) (U : S → A → ℝ) (o : O) (x : A) :
    (mk b fun s x ↦ (U s x : EReal)).value o x = ∫ s, U s x ∂(b o) := by
  simp only [value_mk, EReal.toReal_coe]

/-- An action is feasible at an observation when the belief there gives no weight to a state that
rules it out. -/
def Feasible (o : O) (x : A) : Prop := a.belief o {s | a.utility s x = ⊥} = 0

/-- An agent is unconstrained when every action is feasible at every observation. -/
class IsUnconstrained (a : Agent O S A) : Prop where
  /-- Every action is feasible at every observation. -/
  feasible (o : O) (x : A) : a.Feasible o x

instance (b : Kernel O S) (U : S → A → ℝ) : (mk b fun s x ↦ (U s x : EReal)).IsUnconstrained :=
  ⟨fun o x ↦ by simp [Feasible]⟩

variable [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]

open Classical in
/-- The agent's policy at rationality `β` soft-maximizes the value among the feasible actions: the
row at an observation is proportional to the exponential of `β` times the value, and an action
that is not feasible has score `⊥`. -/
noncomputable def policy (β : ℝ) : Kernel O A :=
  Kernel.softmax fun o x ↦ β * if a.Feasible o x then (a.value o x : EReal) else ⊥

variable (β : ℝ)

instance : IsFiniteKernel (a.policy β) := inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance (o : O) : IsZeroOrProbabilityMeasure (a.policy β o) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.softmax _ o))

/-- At a positive rationality the policy takes exactly the feasible actions with positive
probability. -/
theorem policy_apply_singleton_ne_zero_iff [MeasurableSingletonClass A] {β : ℝ} (hβ : 0 < β)
    (o : O) (x : A) : a.policy β o {x} ≠ 0 ↔ a.Feasible o x := by
  classical
  have htop (y : A) : (β : EReal) * (if a.Feasible o y then (a.value o y : EReal) else ⊥) ≠ ⊤ := by
    split_ifs
    · rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    · rw [EReal.coe_mul_bot_of_pos hβ]; exact bot_ne_top
  refine ⟨fun h ↦ by_contra fun hx ↦ h ?_, fun hx ↦ ?_⟩
  · refine Kernel.softmax_apply_singleton_eq_zero ?_
    simp only [hx, ite_false, EReal.coe_mul_bot_of_pos hβ]
  · refine Kernel.softmax_apply_singleton_ne_zero ?_ htop
    simp only [hx, ite_true, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _

/-- The policy of an unconstrained agent is the softmax of its scaled values. -/
theorem policy_eq_softmax [a.IsUnconstrained] :
    a.policy β = Kernel.softmax fun o x ↦ ((β * a.value o x : ℝ) : EReal) := by
  unfold policy
  congr 1
  funext o x
  simp only [IsUnconstrained.feasible o x, ite_true, EReal.coe_mul]

instance [a.IsUnconstrained] [Nonempty A] : IsMarkovKernel (a.policy β) := by
  rw [policy_eq_softmax]
  exact Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

theorem policy_apply_singleton_ne_zero [a.IsUnconstrained] [MeasurableSingletonClass A] (o : O)
    (x : A) : a.policy β o {x} ≠ 0 := by
  rw [policy_eq_softmax]
  exact Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _

variable {a β} {o : O} {x x' : A} [MeasurableSingletonClass A] [a.IsUnconstrained]

/-- The policy's share of an action is the real softmax of the scaled values. -/
theorem policy_real_singleton :
    (a.policy β o).real {x} = Real.softmax (fun x ↦ β * a.value o x) x := by
  rw [policy_eq_softmax]
  exact Kernel.softmax_coe_real_singleton (fun o x ↦ β * a.value o x) o x

/-- The policy gives every action positive probability. -/
theorem policy_real_singleton_pos : 0 < (a.policy β o).real {x} := by
  have : Nonempty A := ⟨x⟩
  rw [policy_real_singleton]; exact Real.softmax_pos _ x

/-- At positive rationality the policy prefers the action of greater value. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (a.policy β o).real {x} < (a.policy β o).real {x'} ↔ a.value o x < a.value o x' := by
  rw [policy_eq_softmax]
  exact (Kernel.softmax_coe_real_singleton_lt_iff (fun o x ↦ β * a.value o x) o).trans
    (mul_lt_mul_iff_right₀ hβ)

/-- With two actions, the policy's share of one is the logistic function of the scaled difference
in value. -/
theorem policy_real_of_pair (hxx' : x ≠ x') (hall : ∀ c, c = x ∨ c = x') :
    (a.policy β o).real {x} = Real.sigmoid (β * (a.value o x - a.value o x')) := by
  rw [policy_eq_softmax, Kernel.softmax_real_singleton_of_pair hxx' (EReal.coe_ne_bot _)
    (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe,
    EReal.toReal_coe]
  ring_nf

end Agent
