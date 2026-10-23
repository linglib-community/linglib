module

public import Mathlib.Data.Set.Basic

/-!
# Clausal distributivity

A clause-embedding predicate relates an agent to a set of propositions: the answers of a question,
or the singleton of a declarative's proposition. The predicate is clausally distributive when it
relates an agent to a question exactly when it relates her to some answer. Most responsive
predicates are distributive, such as *know*. A predicate that relates an agent to a question while
relating her to none of its answers is not; this is the diagnostic Elliott and colleagues apply to
*care* and Qing and colleagues to *worry*.

## Main definitions

* `Distributivity.IsDistributive`: the predicate relates an agent to a question exactly when it
  relates her to some answer.

## Main statements

* `Distributivity.not_isDistributive_of_forall_not`: a predicate that holds of a question but of
  none of its answers is not distributive.

## References

* [spector-egre-2015]
* [uegaki-sudo-2019]
* [uegaki-2022]
* [elliott-etal-2017]
* [qing-uegaki-2025]
-/

@[expose] public section

namespace Distributivity

variable {W E : Type*}

/-- A clause-embedding predicate `V` is clausally distributive when it relates an agent to a set
of propositions exactly when it relates her to the singleton of one of them. -/
def IsDistributive (V : E → Set (Set W) → W → Prop) : Prop :=
  ∀ x Q w, V x Q w ↔ ∃ p ∈ Q, V x {p} w

/-- A predicate that holds of a question but of none of its answers is not distributive. -/
theorem not_isDistributive_of_forall_not {V : E → Set (Set W) → W → Prop} {x : E}
    {Q : Set (Set W)} {w : W} (hQ : V x Q w) (h : ∀ p ∈ Q, ¬ V x {p} w) : ¬ IsDistributive V :=
  fun hV ↦ let ⟨p, hp, hxp⟩ := (hV x Q w).1 hQ; h p hp hxp

end Distributivity
