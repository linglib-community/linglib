module

public import Mathlib.Order.UpperLower.Basic

/-!
# Lower sets inside upper sets of a linear order

In a linear order a nonempty lower set meets every point from below or contains it, so an upper
set that includes a nonempty lower set is the whole order, and dually a lower set that includes
a nonempty upper set is. The lemmas sit beside `IsUpperSet.total` and are `[UPSTREAM]` candidates
for `Mathlib.Order.UpperLower.Basic`.
-/

public section

variable {α : Type*} [LinearOrder α] {s t : Set α}

theorem IsLowerSet.eq_univ_of_subset_isUpperSet (hs : IsLowerSet s) (ht : IsUpperSet t)
    (hne : s.Nonempty) (h : s ⊆ t) : t = Set.univ :=
  let ⟨a, ha⟩ := hne
  Set.eq_univ_of_forall fun b ↦ (le_total b a).elim (fun hb ↦ h (hs hb ha)) fun hb ↦ ht hb (h ha)

theorem IsUpperSet.eq_univ_of_subset_isLowerSet (hs : IsUpperSet s) (ht : IsLowerSet t)
    (hne : s.Nonempty) (h : s ⊆ t) : t = Set.univ :=
  let ⟨a, ha⟩ := hne
  Set.eq_univ_of_forall fun b ↦ (le_total b a).elim (fun hb ↦ ht hb (h ha)) fun hb ↦ h (hs hb ha)
