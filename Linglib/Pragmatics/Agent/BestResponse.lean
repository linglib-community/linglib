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
  -- TODO: some `y` has greater value, and the share of `x` is at most
  -- `exp (β * (value x - value y))`; see `Kernel.tendsto_softmax_mul_real_singleton_atTop`.
  sorry

end Agent
