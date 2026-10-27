module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite set families as families of sets

A finite set family `F : Finset (Finset α)`, the representation of mathlib's
`Combinatorics/SetFamily`, read as a family of sets: the image of `F` under the coercion
`Finset α → Set α`. Finite alternative sets and finite Hamblin sets enter the `Set (Set α)` API
this way.

## Main definitions

* `Finset.toSetFamily F`: the sets of the finsets in `F`.

## Main results

* `Finset.toSetFamily_subset_toSetFamily`: the coercion reflects and preserves inclusion.
* `Finset.exists_toSetFamily_eq_of_subset`: every subfamily of `F.toSetFamily` comes from a
  subfamily of `F`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} {F G : Finset (Finset α)} {s : Set α} {a : Finset α}

/-- A finite set family as a family of sets. -/
def toSetFamily (F : Finset (Finset α)) : Set (Set α) := (↑) '' (↑F : Set (Finset α))

@[simp] theorem mem_toSetFamily : s ∈ F.toSetFamily ↔ ∃ a ∈ F, (↑a : Set α) = s := by
  simp [toSetFamily]

theorem coe_mem_toSetFamily : (↑a : Set α) ∈ F.toSetFamily ↔ a ∈ F := by
  simp only [mem_toSetFamily, coe_inj, exists_eq_right]

theorem finite_toSetFamily (F : Finset (Finset α)) : F.toSetFamily.Finite :=
  (finite_toSet F).image _

theorem toSetFamily_subset_toSetFamily : F.toSetFamily ⊆ G.toSetFamily ↔ F ⊆ G :=
  ⟨fun h a ha ↦ by
    obtain ⟨b, hb, hba⟩ := mem_toSetFamily.1 (h (mem_toSetFamily.2 ⟨a, ha, rfl⟩))
    exact coe_inj.1 hba ▸ hb,
   fun h s hs ↦ let ⟨a, ha, has⟩ := mem_toSetFamily.1 hs; mem_toSetFamily.2 ⟨a, h ha, has⟩⟩

theorem exists_toSetFamily_eq_of_subset {X : Set (Set α)} (h : X ⊆ F.toSetFamily) :
    ∃ M ⊆ F, M.toSetFamily = X := by
  classical
  refine ⟨F.filter fun a : Finset α ↦ (a : Set α) ∈ X, filter_subset _ _, ?_⟩
  ext s
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := mem_toSetFamily.1 hs
    exact (mem_filter.1 ha).2
  · obtain ⟨a, ha, rfl⟩ := mem_toSetFamily.1 (h hs)
    exact mem_toSetFamily.2 ⟨a, mem_filter.2 ⟨ha, hs⟩, rfl⟩

end Finset
