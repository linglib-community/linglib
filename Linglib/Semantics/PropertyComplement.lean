/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Basic

/-!
# Predicates with a property complement

On the analysis of Montague, Bach, Dowty and Chierchia the complement of *try*, *persuade* or
*seem* denotes a property, and the predicate denotes a relation `R : (E → Φ) → X → Φ` between a
property and its other arguments `X`, with `Φ` the propositions. What is called control and
raising are then two answers to how much of the property the relation reads. Given the argument
`c : X → E` the property is understood of, the relation is *raising* at `c` when it reads only the
proposition `P (c x)`, and *controlled* at `c` when it reads that proposition and the arguments
`x`. A raising relation is controlled, and a controlled one is [exactly a relation to a
proposition](##PropertyComplement.isControlledAt_iff) with the property applied to `c x`, so an
analysis on which the complement denotes a proposition describes the controlled relations and no
others. A raising relation [entails nothing about `c x`](##PropertyComplement.IsRaisingAt.le_of_le)
that it does not entail of everything.

## Implementation notes

`IsRaisingAt` and `IsControlledAt` are `Function.FactorsThrough` at two maps, so they are
predicates on the bare relation, as `Monotone` is on a function, and a relation that reads the
whole property satisfies neither. The argument `c` is any function of the other arguments, the
bearer of a thematic role in Chierchia's sense; the participant in a slot is the case of a
projection. Equality in `Φ` is logical equivalence when propositions are sets of worlds.

## References

* [dowty-1985]
* [bach-1979]
* [stiebels-2007]
-/

@[expose] public section

open Function

namespace PropertyComplement

variable {E Φ X Y : Type*} {R : (E → Φ) → X → Φ} {c : X → E}

/-- A relation to a property is raising at `c` when it depends only on the proposition the
property forms with `c x`. -/
def IsRaisingAt (R : (E → Φ) → X → Φ) (c : X → E) : Prop :=
  FactorsThrough (uncurry R) fun a ↦ a.1 (c a.2)

/-- A relation to a property is controlled at `c` when it depends on the property only through
the proposition it forms with `c x`. -/
def IsControlledAt (R : (E → Φ) → X → Φ) (c : X → E) : Prop :=
  FactorsThrough (uncurry R) fun a ↦ (a.1 (c a.2), a.2)

theorem IsRaisingAt.isControlledAt (h : IsRaisingAt R c) : IsControlledAt R c :=
  fun _ _ hab ↦ h (congrArg Prod.fst hab)

theorem IsControlledAt.of_eq {R' : Φ → X → Φ} (h : ∀ P x, R P x = R' (P (c x)) x) :
    IsControlledAt R c := by
  rintro ⟨P, x⟩ ⟨Q, y⟩ hab
  obtain ⟨hφ, rfl⟩ := Prod.mk.inj hab
  simp only [uncurry, h]
  exact congrArg (R' · x) hφ

theorem IsRaisingAt.of_eq {S : Φ → Φ} (h : ∀ P x, R P x = S (P (c x))) : IsRaisingAt R c :=
  fun ⟨P, x⟩ ⟨Q, y⟩ hab ↦ by simp only [uncurry, h]; exact congrArg S hab

/-- A relation is controlled at `c` exactly when it is a relation to a proposition, taken at the
proposition the property forms with `c x`. -/
theorem isControlledAt_iff [Nonempty Φ] :
    IsControlledAt R c ↔ ∃ R' : Φ → X → Φ, ∀ P x, R P x = R' (P (c x)) x := by
  rw [IsControlledAt, factorsThrough_iff]
  exact ⟨fun ⟨e, he⟩ ↦ ⟨fun φ x ↦ e (φ, x), fun P x ↦ congrFun he (P, x)⟩,
    fun ⟨R', h⟩ ↦ ⟨fun a ↦ R' a.1 a.2, funext fun ⟨P, x⟩ ↦ h P x⟩⟩

/-- A relation is raising at `c` exactly when it is a property of propositions, taken at the
proposition the property forms with `c x`. -/
theorem isRaisingAt_iff [Nonempty Φ] :
    IsRaisingAt R c ↔ ∃ S : Φ → Φ, ∀ P x, R P x = S (P (c x)) := by
  rw [IsRaisingAt, factorsThrough_iff]
  exact ⟨fun ⟨e, he⟩ ↦ ⟨e, fun P x ↦ congrFun he (P, x)⟩,
    fun ⟨S, h⟩ ↦ ⟨S, funext fun ⟨P, x⟩ ↦ h P x⟩⟩

/-- The controlling argument is followed along a map of the other arguments, as across the
diatheses of a verb. -/
theorem IsControlledAt.comp (h : IsControlledAt R c) (σ : Y → X) :
    IsControlledAt (fun P y ↦ R P (σ y)) (c ∘ σ) := by
  rintro ⟨P, y⟩ ⟨Q, z⟩ hab
  obtain ⟨hφ, rfl⟩ := Prod.mk.inj hab
  exact h (a := (P, σ y)) (b := (Q, σ y)) (Prod.ext hφ rfl)

theorem IsRaisingAt.comp (h : IsRaisingAt R c) (σ : Y → X) :
    IsRaisingAt (fun P y ↦ R P (σ y)) (c ∘ σ) :=
  fun ⟨P, y⟩ ⟨Q, z⟩ hab ↦ h (a := (P, σ y)) (b := (Q, σ z)) hab

/-- What a raising relation entails of the argument it is raising at, it entails of every entity
some argument takes there: its meaning does not depend on that argument as such. -/
theorem IsRaisingAt.le_of_le [LE Φ] (h : IsRaisingAt R c) {α : E → Φ}
    (hα : ∀ P x, R P x ≤ α (c x)) (P : E → Φ) (x y : X) : R P x ≤ α (c y) := by
  have : R P x = R (fun _ ↦ P (c x)) y := h (a := (P, x)) (b := (fun _ ↦ P (c x), y)) rfl
  exact this ▸ hα _ y

end PropertyComplement
