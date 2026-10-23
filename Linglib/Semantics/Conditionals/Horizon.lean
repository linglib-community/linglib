module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Logic.Trivalent.Pointwise

/-!
# The modal-horizon counterfactual

On von Fintel's dynamic strict analysis, a counterfactual quantifies over a modal horizon, a set
of worlds accessible from each evaluation point that the context widens as needed. *If p, would
q* presupposes that the horizon admits `p` and asserts that every `p`-world of the horizon is a
`q`-world, the strict conditional `Conditional.strictImp` over the horizon. Strengthening the
antecedent is then not classically valid, since the strengthened antecedent may fall outside the
horizon, but it is valid wherever the conclusion's presupposition holds.

## Main definitions

* `Conditional.horizonCounterfactual`: the counterfactual over a modal horizon, a trivalent
  proposition.

## Main results

* `Conditional.exists_mem_of_horizonCounterfactual_eq_one`: a true counterfactual has a
  horizon-world where antecedent and consequent hold together.

## Implementation notes

The admissibility of the horizon with respect to an ordering source, a condition on the context
that does not mention the antecedent, is left to the caller. Von Fintel's page prints the
consequent as evaluated at `w`; it is evaluated at the horizon-world `w'`, as here.

## References

* [von-fintel-1999]
* [von-fintel-2000]
-/

@[expose] public section

namespace Conditional

variable {I W : Type*} (horizon : I → Set W) (p q : Set W)

open Classical in
/-- *If p, would q* over a modal horizon presupposes that the horizon admits `p` and asserts the
strict conditional over the horizon ([von-fintel-1999]'s (82) and (83)). -/
noncomputable def horizonCounterfactual : I → SignType :=
  {i | (horizon i ∩ p).Nonempty}.indicator fun i ↦ SignType.ofProp (i ∈ strictImp horizon p q)

variable {horizon p q} {i : I}

@[simp] theorem horizonCounterfactual_eq_zero_iff :
    horizonCounterfactual horizon p q i = 0 ↔ ¬ (horizon i ∩ p).Nonempty := by
  simp [horizonCounterfactual]

@[simp] theorem horizonCounterfactual_eq_one_iff :
    horizonCounterfactual horizon p q i = 1 ↔ (horizon i ∩ p).Nonempty ∧ horizon i ∩ p ⊆ q := by
  simp [horizonCounterfactual]

@[simp] theorem horizonCounterfactual_eq_neg_one_iff :
    horizonCounterfactual horizon p q i = -1 ↔
      (horizon i ∩ p).Nonempty ∧ ¬ horizon i ∩ p ⊆ q := by
  simp [horizonCounterfactual]

theorem exists_mem_of_horizonCounterfactual_eq_one (h : horizonCounterfactual horizon p q i = 1) :
    ∃ w ∈ horizon i, w ∈ p ∧ w ∈ q :=
  let ⟨⟨w, hw⟩, hs⟩ := horizonCounterfactual_eq_one_iff.1 h
  ⟨w, hw.1, hw.2, hs hw⟩

end Conditional
