/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Comparable
public import Mathlib.Order.Minimal

/-!
# Minimality under a key and along a map

Among elements none of which lies below another, minimality under a key depends only on the key's
strict order between incomparable elements: when that order is an irreflexive relation `r`, the
minimal elements are those that nothing is `r`-related to. A strictly monotone map along which
lower elements lift carries the minimal elements of a preimage to the minimal elements of the
set, whether or not the map is injective.

A point whose value under a map is least among the values on a set is minimal for the map on the
set, for any relation `≤` on the values. When the values have a least one and `≤` is transitive,
the minimal points are exactly the points of the set whose value is least.

## Main statements

* `IsLeast.minimalFor`
* `minimalFor_iff_of_isLeast`
* `minimalFor_iff_of_isAntichain`
* `minimal_comp_iff_of_strictMono`
-/

public section

section Least

variable {α β : Type*} {f : α → β} {s : Set α} {a b : α}

/-- A point of a set whose value is least among the values on the set is minimal for the map on
the set. -/
theorem IsLeast.minimalFor [LE β] (ha : a ∈ s) (h : IsLeast (f '' s) (f a)) :
    MinimalFor (· ∈ s) f a :=
  ⟨ha, fun _ hb _ ↦ h.2 (Set.mem_image_of_mem f hb)⟩

/-- When the values of a map on a set have a least one, the points minimal for the map are the
points of the set whose value is least. -/
theorem minimalFor_iff_of_isLeast [Preorder β] (h : IsLeast (f '' s) (f a)) :
    MinimalFor (· ∈ s) f b ↔ b ∈ s ∧ IsLeast (f '' s) (f b) := by
  obtain ⟨a', ha', hfa⟩ := h.1
  refine ⟨fun hb ↦ ⟨hb.1, Set.mem_image_of_mem f hb.1, fun c hc ↦ ?_⟩,
    fun hb ↦ hb.2.minimalFor hb.1⟩
  exact (hb.2 ha' (hfa ▸ h.2 (Set.mem_image_of_mem f hb.1))).trans (hfa ▸ h.2 hc)

end Least

variable {ι β : Type*} [Preorder ι] [Preorder β] {P : ι → Prop} {f : ι → β} {r : ι → ι → Prop}
  {i : ι}

/-- Among elements of `P` none of which lies below another, an element is minimal under a key
whose strict order between incomparable elements is the irreflexive relation `r` exactly when no
element of `P` is `r`-related to it. -/
theorem minimalFor_iff_of_isAntichain (hP : IsAntichain (· ≤ ·) {j | P j}) (hr : ∀ j, ¬ r j j)
    (h : ∀ ⦃j k⦄, IncompRel (· ≤ ·) j k → (f j < f k ↔ r j k)) :
    MinimalFor P f i ↔ P i ∧ ∀ ⦃j⦄, P j → ¬ r j i := by
  rw [minimalFor_iff_forall_lt]
  refine and_congr_right fun hi ↦ forall_congr' fun j ↦ ?_
  by_cases hj : P j
  · obtain rfl | hne := eq_or_ne j i
    · simp [hj, hr]
    · simp [hj, h ⟨hP hj hi hne, hP hi hj hne.symm⟩]
  · simp [hj]

/-- A strictly monotone map `g` such that every element below `g a` is the image of one below
`a` reflects and preserves minimality: `a` is minimal among the elements whose image satisfies
`Q` exactly when `g a` is minimal in `Q`. -/
theorem minimal_comp_iff_of_strictMono {α : Type*} [PartialOrder α] {g : α → β} {Q : β → Prop}
    {a : α} (hg : StrictMono g) (hlift : ∀ ⦃a b⦄, b ≤ g a → ∃ c ≤ a, g c = b) :
    Minimal (fun c ↦ Q (g c)) a ↔ Minimal Q (g a) := by
  refine ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, fun b hb hle ↦ ?_⟩, fun ⟨ha, hmin⟩ ↦ ⟨ha, fun c hc hca ↦ ?_⟩⟩
  · obtain ⟨c, hca, rfl⟩ := hlift hle
    exact hg.monotone (hmin hb hca)
  · exact (hca.lt_or_eq.resolve_left fun hlt ↦ (hg hlt).not_ge (hmin hc (hg.monotone hca))).ge
