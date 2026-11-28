/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Max

/-!
# Situations

A situation is a part of a world. Situations are ordered by parthood, the worlds are the maximal
situations, and a proposition is a set of situations, true in the situations that belong to it. A
proposition is persistent when it is true in every situation that a situation in which it is true
is part of, that is, when it is an upper set.

This file defines the worlds of an order of situations and the classical logical relations
between propositions, which depend only on the worlds in which the propositions are true. A set
`A` of propositions implies `q` when `q` is true in every world in which every member of `A` is
true, and is consistent when some world makes every member true.

The other files of the directory build on this one. `Lumping.lean` has the lumping of one
proposition by another in a situation, and `Exemplification.lean` the situations that exemplify a
proposition, those that contain nothing that does not contribute to its truth. `World.lean` has
the world of a situation, where each situation is part of exactly one world, and truth at a world
for worlds given from outside the order. `Index.lean` has the world and the time of a situation
as an index of evaluation.

## Main definitions

* `Situation.worlds`: the maximal situations.
* `Situation.Follows`, `Situation.IsConsistent`, `Situation.IsCompatible`: logical consequence,
  consistency and compatibility.

## Implementation notes

The situations are any preorder, and a persistent proposition is an `IsUpperSet`. That every
situation is part of a world, or of exactly one, is not assumed here; the sum of two situations of
a world is the join of the order where it has one. A state space of truthmaker semantics is an
order of situations whose possible states form a lower set, and the propositions that its states
inexactly verify are the persistent ones.

## References

* [kratzer-1989]
* [kratzer-2012]
* [elbourne-2005]
-/

@[expose] public section

namespace Situation

open Set

variable {S : Type*} [Preorder S] {A B : Set (Set S)} {p q : Set S} {w : S}

variable (S) in
/-- The worlds, the maximal situations. -/
def worlds : Set S := {s | IsMax s}

@[simp] theorem mem_worlds {s : S} : s ∈ worlds S ↔ IsMax s := Iff.rfl

/-- `A` logically implies `q` when `q` is true in every world in which all of `A` is. -/
def Follows (A : Set (Set S)) (q : Set S) : Prop := worlds S ∩ ⋂₀ A ⊆ q

/-- `A` is consistent when all of it is true in some world. -/
def IsConsistent (A : Set (Set S)) : Prop := (worlds S ∩ ⋂₀ A).Nonempty

/-- `p` is compatible with `A` when adding it to `A` preserves consistency. -/
def IsCompatible (p : Set S) (A : Set (Set S)) : Prop := IsConsistent (insert p A)

theorem Follows.mono (h : Follows B q) (hBA : B ⊆ A) : Follows A q :=
  (inter_subset_inter_right _ (sInter_subset_sInter hBA)).trans h

theorem isCompatible_iff_not_follows_compl : IsCompatible p A ↔ ¬ Follows A pᶜ := by
  simp only [IsCompatible, IsConsistent, Follows, sInter_insert, not_subset, Set.Nonempty,
    mem_inter_iff, mem_compl_iff, not_not]
  exact ⟨fun ⟨s, hw, hp, hA⟩ ↦ ⟨s, ⟨hw, hA⟩, hp⟩, fun ⟨s, ⟨hw, hA⟩, hp⟩ ↦ ⟨s, hw, hp, hA⟩⟩

end Situation
