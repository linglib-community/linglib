/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Minimal elements of well-founded images

`Set.IsWF.exists_minimalFor`, the well-founded companion of mathlib's
`Set.IsPWO.exists_minimalFor`: if the image of a nonempty set under `f` is well-founded, some
element of the set is minimal for `f`.
-/

public section

namespace Set

variable {ι β : Type*} [Preorder β]

theorem IsWF.exists_minimalFor (f : ι → β) (s : Set ι) (h : (f '' s).IsWF) (hs : s.Nonempty) :
    ∃ i, MinimalFor (· ∈ s) f i := by
  obtain ⟨i, hi, hfi⟩ := h.min_mem (hs.image f)
  refine ⟨i, hi, fun j hj hle ↦ not_lt_iff_le_imp_ge.1 ?_ hle⟩
  exact hfi ▸ h.not_lt_min (hs.image f) (mem_image_of_mem f hj)

end Set
