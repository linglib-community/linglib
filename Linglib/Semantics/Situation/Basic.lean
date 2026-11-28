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
situations, and a proposition is a set of situations, true in the situations that belong to it.
This file defines the worlds of an order of situations, the classical logical relations between
propositions, which depend only on the worlds in which the propositions are true, and lumping,
which depends on the parts of a world.

A set `A` of propositions implies `q` when `q` is true in every world in which every member of `A`
is true, and is consistent when some world makes every member true. A proposition `p` lumps `q` in
a situation `w` when `p` is true in `w` and `q` is true in every part of `w` in which `p` is true.
In a situation without proper parts lumping is joint truth.

## Main definitions

* `Situation.worlds`: the maximal situations.
* `Situation.Follows`, `Situation.IsConsistent`, `Situation.IsCompatible`: logical consequence,
  consistency and compatibility.
* `Situation.Lumps`: lumping.

## Implementation notes

The situations are any preorder. That every situation is part of exactly one world is not assumed
here. Exemplification of a proposition by a situation is in
`Linglib/Semantics/Situation/Exemplification.lean`.

## References

* [kratzer-1989]
* [kratzer-2012]
-/

@[expose] public section

namespace Situation

open Set

variable {S : Type*} [Preorder S] {A B : Set (Set S)} {p q : Set S} {w : S}

/-- `p` lumps `q` in `w` when `p` is true in `w` and `q` is true in every part of `w` in which `p`
is true. -/
structure Lumps (p q : Set S) (w : S) : Prop where
  /-- `p` is true in `w`. -/
  holds : w ∈ p
  /-- `q` is true in every part of `w` in which `p` is true. -/
  localImpl : ∀ ⦃s⦄, s ≤ w → s ∈ p → s ∈ q

/-- At a minimal situation lumping is joint truth, so a possible-worlds semantics cannot separate it
from material implication. -/
theorem Lumps.iff_of_isMin {S : Type*} [PartialOrder S] {p q : Set S} {w : S} (hw : IsMin w) :
    Lumps p q w ↔ w ∈ p ∧ w ∈ q :=
  ⟨fun h ↦ ⟨h.holds, h.localImpl le_rfl h.holds⟩,
    fun ⟨hp, hq⟩ ↦ ⟨hp, fun _ hs _ ↦ hw.eq_of_ge hs ▸ hq⟩⟩

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
