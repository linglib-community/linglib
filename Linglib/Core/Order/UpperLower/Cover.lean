/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Cover
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Covers of lower sets

In a well-founded partial order, a lower set covers another exactly when it adds a single element,
and that element is maximal in it. This is the lower-set counterpart of mathlib's
`Set.covBy_iff_exists_insert`. `[UPSTREAM]` candidate for `Mathlib/Order/UpperLower/`.

## Main results

* `LowerSet.covBy_iff_exists_insert`: `s ⋖ t` iff `t` is `s` with one element added.
* `LowerSet.maximal_of_coe_eq_insert`: the element added is maximal in `t`.
-/

@[expose] public section

namespace LowerSet

variable {α : Type*} [PartialOrder α] {s t : LowerSet α} {a : α}

/-- An element added to a lower set to give a lower set is maximal in it. -/
theorem maximal_of_coe_eq_insert (ha : a ∉ s) (ht : (t : Set α) = insert a (s : Set α)) :
    Maximal (· ∈ t) a := by
  refine ⟨show a ∈ (t : Set α) by simp [ht], fun b (hb : b ∈ (t : Set α)) hab ↦ ?_⟩
  rw [ht] at hb
  rcases hb with rfl | hb
  · exact le_rfl
  · exact absurd (s.lower hab hb) ha

theorem covBy_iff_exists_insert [WellFoundedLT α] :
    s ⋖ t ↔ ∃ a ∉ s, (t : Set α) = insert a (s : Set α) := by
  refine ⟨fun h ↦ ?_, fun ⟨a, ha, ht⟩ ↦ ?_⟩
  · obtain ⟨x, hxt, hxs⟩ := IsConcreteLE.exists_of_lt h.lt
    obtain ⟨a, ⟨hat, has⟩, hmin⟩ := wellFounded_lt.has_min ((t : Set α) \ s) ⟨x, hxt, hxs⟩
    have hlow : IsLowerSet (insert a (s : Set α)) := by
      rintro c d hdc (rfl | hc)
      · by_cases hds : d ∈ s
        · exact Or.inr hds
        · rcases hdc.lt_or_eq with hlt | rfl
          · exact absurd hlt (hmin d ⟨t.lower hdc hat, hds⟩)
          · exact Or.inl rfl
      · exact Or.inr (s.lower hdc hc)
    let u : LowerSet α := ⟨_, hlow⟩
    have hsu : s < u := IsConcreteLE.lt_iff_le_and_exists.2
      ⟨fun _ hb ↦ Or.inr hb, a, Or.inl rfl, has⟩
    have hut : u ≤ t := fun b hb ↦ by
      rcases hb with rfl | hb
      · exact hat
      · exact h.le hb
    refine ⟨a, has, ?_⟩
    rw [← hut.eq_of_not_lt (h.2 hsu)]
    rfl
  · have hst : (s : Set α) ⋖ t := ht ▸ Set.covBy_insert ha
    exact ⟨SetLike.coe_ssubset_coe.1 hst.lt, fun u hsu hut ↦
      hst.2 (SetLike.coe_ssubset_coe.2 hsu) (SetLike.coe_ssubset_coe.2 hut)⟩

end LowerSet
