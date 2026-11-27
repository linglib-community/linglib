module

public import Linglib.Core.Order.Argmax
public import Linglib.Pragmatics.Agent.Basic
public import Mathlib.Order.Filter.Extr

/-!
# Best responses

The best responses of an agent at an observation are the actions of greatest value there,
`Agent.bestResponses`. With finitely many actions there is one, and they are the `Finset.argmax`
of the value (`Agent.coe_argmax_value`). The agent's policy soft-maximizes
the same value, and as the rationality grows the policy of an unconstrained agent
leaves every action that is not a best response
(`Agent.tendsto_policy_real_singleton_atTop`).

## TODO

* The limit of the policy as the rationality grows is uniform on the best responses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] (a : Agent O S A)

/-- The best responses of an agent at an observation are the actions of greatest value there. -/
def bestResponses (o : O) : Set A := {x | ∀ y, a.value o y ≤ a.value o x}

variable {a} {o : O} {x : A}

theorem mem_bestResponses_iff : x ∈ a.bestResponses o ↔ IsMaxOn (a.value o) Set.univ x := by
  simp [bestResponses, isMaxOn_iff]

theorem bestResponses_nonempty [Finite A] [Nonempty A] (a : Agent O S A) (o : O) :
    (a.bestResponses o).Nonempty :=
  let ⟨x, hx⟩ := Finite.exists_max (a.value o)
  ⟨x, hx⟩

/-- With finitely many actions the best responses are the `Finset.argmax` of the value. -/
theorem coe_argmax_value [Fintype A] (a : Agent O S A) (o : O) :
    (Finset.univ.argmax (a.value o) : Set A) = a.bestResponses o := by
  ext x
  simp [Finset.mem_argmax, bestResponses]

variable [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A]

/-- As the rationality grows the policy leaves every action that is not a best response. -/
theorem tendsto_policy_real_singleton_atTop [a.IsUnconstrained] (hx : x ∉ a.bestResponses o) :
    Tendsto (fun β ↦ (a.policy β o).real {x}) atTop (𝓝 0) := by
  obtain ⟨y, hy⟩ : ∃ y, a.value o x < a.value o y := by
    simpa [bestResponses, not_forall, not_le] using hx
  have hlim : Tendsto (fun β : ℝ ↦ Real.exp (β * (a.value o x - a.value o y))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 hy))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun β ↦ measureReal_nonneg) fun β ↦ ?_
  rw [policy_real_singleton, Real.softmax_apply, mul_sub, Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _)
    (Finset.single_le_sum (f := fun j ↦ Real.exp (β * a.value o j))
      (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ y))

end Agent
