/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.Deployment
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Universal inferences of trivalent quantifiers

A trivalent quantifier has a universal entailment over a domain when it is true of a predicate only
if the predicate is defined throughout the domain, a universal anti-entailment when it is false only
then, and a universal presupposition when it has both. Under Peters-Kleene deployment these turn on
[single steps](##Presupposition.universalEntailment_deployQuantifier_iff): a quantifier has a
universal entailment when it never holds of both a set and the set with one more element. So over
the whole universe a universal entailment is [an independent set of the Hasse diagram of
`Set α`](##Presupposition.universalEntailment_univ_deployQuantifier_iff_isIndepSet), and a universal
presupposition is [a proper 2-colouring of that
diagram](##Presupposition.universalPresupposition_univ_deployQuantifier_iff_exists_coloring).

## Implementation notes

The definitions take any `(α → SignType) → SignType`, so they apply to the other trivalent
quantifiers of `Linglib.Logic.Trivalent.Pointwise` as well as to deployed ones. The domain lets one
notion cover quantifiers, over the whole universe, and determiners, over the restrictor. The graph
reading is not George's, who argues by counting.

## References

* [george-2014]
-/

@[expose] public section

namespace Presupposition

open SignType Trivalent SimpleGraph

variable {α : Type*}

/-- `T` has a universal entailment over `R` when it is true of a predicate only if the predicate is
defined throughout `R`. -/
def UniversalEntailment (R : Set α) (T : (α → SignType) → SignType) : Prop :=
  ∀ A, T A = 1 → ∀ a ∈ R, A a ≠ 0

/-- `T` has a universal anti-entailment over `R` when it is false of a predicate only if the
predicate is defined throughout `R`. -/
def UniversalAntiEntailment (R : Set α) (T : (α → SignType) → SignType) : Prop :=
  ∀ A, T A = -1 → ∀ a ∈ R, A a ≠ 0

/-- `T` has a universal presupposition over `R` when it has a universal entailment and a universal
anti-entailment there. -/
def UniversalPresupposition (R : Set α) (T : (α → SignType) → SignType) : Prop :=
  UniversalEntailment R T ∧ UniversalAntiEntailment R T

variable {Q : Set α → Prop} {R : Set α}

/-! ### Deployed quantifiers: single steps -/

/-- A deployed quantifier has a universal entailment over `R` when it never holds of both a set and
the set with one more element of `R`. -/
theorem universalEntailment_deployQuantifier_iff :
    UniversalEntailment R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (Q B ∧ Q (insert a B)) := by
  rw [← forall_repairs_imp_iff]
  simp [UniversalEntailment, deployQuantifier_eq_supervaluationOn, supervaluationOn_eq_one_iff]

/-- A deployed quantifier has a universal anti-entailment over `R` when it never fails of both a set
and the set with one more element of `R`. -/
theorem universalAntiEntailment_deployQuantifier_iff :
    UniversalAntiEntailment R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (¬ Q B ∧ ¬ Q (insert a B)) := by
  rw [← forall_repairs_imp_iff (fun B ↦ ¬ Q B)]
  simp [UniversalAntiEntailment, deployQuantifier_eq_supervaluationOn,
    supervaluationOn_eq_neg_one_iff, repairs_nonempty]

/-- A deployed quantifier has a universal anti-entailment exactly when its complement has a
universal entailment. -/
theorem universalAntiEntailment_deployQuantifier_iff_compl :
    UniversalAntiEntailment R (deployQuantifier Q) ↔
      UniversalEntailment R (deployQuantifier Qᶜ) := by
  rw [universalAntiEntailment_deployQuantifier_iff, universalEntailment_deployQuantifier_iff]; rfl

/-- A deployed quantifier has a universal presupposition over `R` when it flips at every step in
`R`. -/
theorem universalPresupposition_deployQuantifier_iff :
    UniversalPresupposition R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → (Q (insert a B) ↔ ¬ Q B) := by
  rw [UniversalPresupposition, universalEntailment_deployQuantifier_iff,
    universalAntiEntailment_deployQuantifier_iff]
  refine ⟨fun h B a haR ha ↦ ?_, fun h ↦ ⟨fun B a haR ha ↦ ?_, fun B a haR ha ↦ ?_⟩⟩
  · have := h.1 B a haR ha; have := h.2 B a haR ha; tauto
  · have := h B a haR ha; tauto
  · have := h B a haR ha; tauto

/-! ### Deployed quantifiers: the Hasse diagram of `Set α` -/

/-- Over the whole universe, a deployed quantifier has a universal entailment exactly when it is an
independent set of the Hasse diagram of `Set α`. -/
theorem universalEntailment_univ_deployQuantifier_iff_isIndepSet :
    UniversalEntailment Set.univ (deployQuantifier Q) ↔ (hasse (Set α)).IsIndepSet Q := by
  rw [universalEntailment_deployQuantifier_iff]
  constructor
  · intro h B hB C hC _ hadj
    rcases hasse_adj.1 hadj with e | e
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e
      exact h B a trivial ha ⟨hB, hC⟩
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e
      exact h C a trivial ha ⟨hC, hB⟩
  · rintro h B a - ha ⟨hB, hC⟩
    have e := Set.covBy_insert ha
    exact h hB hC e.ne (hasse_adj.2 (.inl e))

/-- Over the whole universe, a deployed quantifier has a universal presupposition exactly when it is
a proper 2-colouring of the Hasse diagram of `Set α`. -/
theorem universalPresupposition_univ_deployQuantifier_iff_exists_coloring :
    UniversalPresupposition Set.univ (deployQuantifier Q) ↔
      ∃ c : (hasse (Set α)).Coloring Prop, ⇑c = Q := by
  rw [universalPresupposition_deployQuantifier_iff]
  constructor
  · intro h
    refine ⟨Coloring.mk Q fun {B C} hadj e ↦ ?_, rfl⟩
    rcases hasse_adj.1 hadj with e' | e'
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e'
      have := h B a trivial ha
      simp_all
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e'
      have := h C a trivial ha
      simp_all
  · rintro ⟨c, rfl⟩ B a - ha
    have h := c.valid (hasse_adj.2 (.inl (Set.covBy_insert ha)))
    by_cases hB : c B <;> by_cases hC : c (insert a B) <;> simp_all

end Presupposition
