/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Minimal elements of well-founded images

`Set.IsWF.exists_forall_not_lt`: if the image of a nonempty set under `f` is well-founded, some
element of the set has no element below it. This needs no order on the codomain beyond `<`, where
mathlib's `Set.IsPWO.exists_minimalFor` assumes a preorder.
-/

public section

namespace Set

variable {ι β : Type*} [LT β] {f : ι → β} {s : Set ι}

theorem IsWF.exists_forall_not_lt (h : (f '' s).IsWF) (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, ¬ f j < f i := by
  obtain ⟨i, hi, hmin⟩ := (wellFoundedOn_iff.1 (wellFoundedOn_image.1 h)).has_min s hs
  exact ⟨i, hi, fun j hj hlt ↦ hmin j hj ⟨hlt, hj, hi⟩⟩

end Set
