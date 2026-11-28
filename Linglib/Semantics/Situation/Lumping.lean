/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Situation.Basic

/-!
# Lumping

A proposition `p` lumps a proposition `q` in a situation `w` when `p` is true in `w` and `q` is
true in every part of `w` in which `p` is true. Lumping depends on the parts of a situation: in a
situation without proper parts it is joint truth, so a semantics whose only situations are worlds
does not distinguish it from material implication.

## Main definitions

* `Situation.Lumps`: lumping.

## References

* [kratzer-1989]
* [kratzer-2012]
-/

@[expose] public section

namespace Situation

variable {S : Type*} [Preorder S] {p q : Set S} {w : S}

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

end Situation
