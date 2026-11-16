/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Basic

/-!
# Control and raising

On the analysis of Montague, Bach, Dowty and Chierchia the complement of *try*, *persuade* or
*seem* denotes a property, and the predicate denotes a relation `R : (E → Φ) → X → Φ` between a
property and its other arguments `X`, with `Φ` the propositions. What is called control and
raising are then two answers to how much of the property the relation reads. Given the argument
`c : X → E` the property is understood of, the relation is *raising* at `c` when it reads only the
proposition `P (c x)`, and *controlled* at `c` when it reads that proposition and the arguments
`x`. A raising relation is controlled, and a controlled one is [exactly a relation to a
proposition](##ArgumentStructure.isControlledAt_iff) with the property applied to `c x`, so an
analysis on which the complement denotes a proposition describes the controlled relations and no
others. A raising relation [entails nothing about `c x`](##ArgumentStructure.IsRaisingAt.le_of_le)
that it does not entail of everything: the argument is not a semantic argument of the relation, as
no participant of a raising verb fills the slot it raises into (`Diathesis.IsRaising`).

## Implementation notes

`IsRaisingAt` and `IsControlledAt` are predicates on the bare relation, as `Monotone` is on a
function, and a relation that reads the whole property satisfies neither. Being controlled is
`Function.FactorsThrough` evaluation at `c x`, for each `x`. The argument `c` is any function of
the other arguments, the bearer of a thematic role in Chierchia's sense; the participant in a
slot is the case of a projection. Equality in `Φ` is logical equivalence when propositions are
sets of worlds.

## References

* [dowty-1985]
* [bach-1979]
* [stiebels-2007]
-/

@[expose] public section

open Function

namespace ArgumentStructure

variable {E Φ X Y : Type*} {R : (E → Φ) → X → Φ} {c : X → E}

/-- A relation to a property is raising at `c` when it depends only on the proposition the
property forms with `c x`: two properties forming one proposition with two arguments are related
alike. -/
def IsRaisingAt (R : (E → Φ) → X → Φ) (c : X → E) : Prop :=
  ∀ ⦃P Q : E → Φ⦄ ⦃x y : X⦄, P (c x) = Q (c y) → R P x = R Q y

/-- A relation to a property is controlled at `c` when it depends on the property only through
the proposition it forms with `c x`. -/
def IsControlledAt (R : (E → Φ) → X → Φ) (c : X → E) : Prop :=
  ∀ ⦃P Q : E → Φ⦄ ⦃x : X⦄, P (c x) = Q (c x) → R P x = R Q x

theorem IsRaisingAt.isControlledAt (h : IsRaisingAt R c) : IsControlledAt R c :=
  fun _ _ _ hPQ ↦ h hPQ

theorem isControlledAt_iff_forall_factorsThrough :
    IsControlledAt R c ↔ ∀ x, FactorsThrough (R · x) (eval (c x)) :=
  ⟨fun h _ _ _ hPQ ↦ h hPQ, fun h _ _ x hPQ ↦ h x hPQ⟩

/-- A relation is controlled at `c` exactly when it is a relation to a proposition, taken at the
proposition the property forms with `c x`. -/
theorem isControlledAt_iff :
    IsControlledAt R c ↔ ∃ R' : Φ → X → Φ, ∀ P x, R P x = R' (P (c x)) x :=
  ⟨fun h ↦ ⟨fun φ x ↦ R (fun _ ↦ φ) x, fun _ _ ↦ h rfl⟩,
    fun ⟨R', h⟩ P Q x hPQ ↦ by rw [h, h, hPQ]⟩

open Classical in
/-- A relation is raising at `c` exactly when it is a property of propositions, taken at the
proposition the property forms with `c x`. -/
theorem isRaisingAt_iff : IsRaisingAt R c ↔ ∃ S : Φ → Φ, ∀ P x, R P x = S (P (c x)) :=
  ⟨fun h ↦ ⟨fun φ ↦ if hX : Nonempty X then R (fun _ ↦ φ) hX.some else φ, fun P x ↦ by
      simp only [(⟨x⟩ : Nonempty X), ↓reduceDIte]; exact h rfl⟩,
    fun ⟨S, h⟩ P Q x y hPQ ↦ by rw [h, h, hPQ]⟩

/-- The controlling argument is followed along a map of the other arguments, as across the
diatheses of a verb. -/
theorem IsControlledAt.comp (h : IsControlledAt R c) (σ : Y → X) :
    IsControlledAt (fun P y ↦ R P (σ y)) (c ∘ σ) :=
  fun _ _ _ hPQ ↦ h hPQ

theorem IsRaisingAt.comp (h : IsRaisingAt R c) (σ : Y → X) :
    IsRaisingAt (fun P y ↦ R P (σ y)) (c ∘ σ) :=
  fun _ _ _ _ hPQ ↦ h hPQ

/-- What a raising relation entails of the argument it is raising at, it entails of every entity
some argument takes there: its meaning does not depend on that argument as such. -/
theorem IsRaisingAt.le_of_le [LE Φ] (h : IsRaisingAt R c) {α : E → Φ}
    (hα : ∀ P x, R P x ≤ α (c x)) (P : E → Φ) (x y : X) : R P x ≤ α (c y) :=
  h (Q := fun _ ↦ P (c x)) (y := y) rfl ▸ hα _ y

end ArgumentStructure
