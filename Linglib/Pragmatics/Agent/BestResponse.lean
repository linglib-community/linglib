module

public import Linglib.Pragmatics.Agent.Basic
public import Mathlib.Order.Filter.Extr

/-!
# Best responses

The best responses of an agent at an observation are the actions of greatest value there,
`Agent.bestResponses`. With finitely many actions there is one. The agent's policy soft-maximizes
the same value, and as the rationality grows it leaves every action that is not a best response
(`Agent.tendsto_policy_real_singleton_atTop`).

## TODO

* The limit of the policy as the rationality grows is uniform on the best responses.
* Best responses as `Finset.argmax` for finitely many actions and a decidable order.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] (ag : Agent O S A)

/-- The best responses of an agent at an observation are the actions of greatest value there. -/
def bestResponses (o : O) : Set A := {x | ∀ y, ag.value o y ≤ ag.value o x}

variable {ag} {o : O} {x : A}

theorem mem_bestResponses_iff : x ∈ ag.bestResponses o ↔ IsMaxOn (ag.value o) Set.univ x := by
  simp [bestResponses, isMaxOn_iff]

theorem bestResponses_nonempty [Finite A] [Nonempty A] (ag : Agent O S A) (o : O) :
    (ag.bestResponses o).Nonempty :=
  let ⟨x, hx⟩ := Finite.exists_max (ag.value o)
  ⟨x, hx⟩

variable [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A]

/-- As the rationality grows the policy leaves every action that is not a best response. -/
theorem tendsto_policy_real_singleton_atTop (hx : x ∉ ag.bestResponses o) :
    Tendsto (fun β ↦ (ag.policy β o).real {x}) atTop (𝓝 0) := by
  obtain ⟨y, hy⟩ : ∃ y, ag.value o x < ag.value o y := by
    simpa [bestResponses, not_forall, not_le] using hx
  have hlim : Tendsto (fun β : ℝ ↦ Real.exp (β * (ag.value o x - ag.value o y))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 hy))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun β ↦ measureReal_nonneg) fun β ↦ ?_
  rw [policy_real_singleton, Real.softmax_apply, mul_sub, Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _)
    (Finset.single_le_sum (f := fun j ↦ Real.exp (β * ag.value o j))
      (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ y))

end Agent
