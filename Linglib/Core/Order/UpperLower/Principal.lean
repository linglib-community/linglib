module

public import Mathlib.Order.Cover
public import Mathlib.Order.UpperLower.Principal

/-!
# Principal upper sets at two points

The principal upper sets `UpperSet.Ici a` and `UpperSet.Ioi a` compared across points: the upper
set strictly above a point is weaker than the one from any greater point, and the upper set from
a point is covered by the one strictly above it, the two differing only in the point itself. The
lemmas restate `Set.Ici_subset_Ioi` and the cover of `Set.Ioi a` by `Set.Ici a` for upper sets,
and are `[UPSTREAM]` additions to `Mathlib.Order.UpperLower.Principal`.
-/

@[expose] public section

namespace UpperSet

variable {α : Type*}

theorem Ioi_le_Ici [Preorder α] {a b : α} (h : a < b) : Ioi a ≤ Ici b :=
  fun _ hx ↦ h.trans_le hx

theorem Ici_covBy_Ioi [PartialOrder α] (a : α) : Ici a ⋖ Ioi a := by
  refine ⟨(Ici_le_Ioi a).lt_of_ne fun h ↦ ?_, fun U h₁ h₂ ↦ ?_⟩
  · simpa using congrArg (a ∈ ·) h
  by_cases ha : a ∈ U
  · exact h₁.not_ge (le_Ici.2 ha)
  · exact h₂.not_ge fun x hx ↦ lt_of_le_of_ne (h₁.le hx) fun h ↦ ha (h ▸ hx)

end UpperSet
