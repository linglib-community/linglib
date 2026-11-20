module

public import Linglib.Core.Order.SupIndep
public import Linglib.Semantics.Mereology.Basic

/-!
# Counting relative to a set

The cardinality of an element relative to a set `Z` is the number of its parts in `Z`
([landman-2020]). It grows with the element and with `Z`, and when `Z` is independent, as a
disjoint set of a frame is, a sum of elements of `Z` counts as many as the elements summed
(`Mereology.count_sSup`).

## References

* [landman-2020]
-/

@[expose] public section

namespace Mereology

open Set

variable {α : Type*}

section PartialOrder

variable [PartialOrder α] {Z Z' : Set α} {x y : α}

theorem count_mono_left (hy : (Iic y ∩ Z).Finite) (h : x ≤ y) : count Z x ≤ count Z y :=
  ncard_le_ncard (inter_subset_inter_left Z (Iic_subset_Iic.2 h)) hy

theorem count_mono_right (hx : (Iic x ∩ Z').Finite) (h : Z ⊆ Z') : count Z x ≤ count Z' x :=
  ncard_le_ncard (inter_subset_inter_right _ h) hx

end PartialOrder

section CompleteLattice

variable [CompleteLattice α] {Y Z : Set α} {z : α} (hZ : sSupIndep Z) (hbot : ⊥ ∉ Z)
include hZ hbot

/-- Over an independent set without `⊥`, a sum counts as many as the elements it sums. -/
theorem count_sSup (hY : Y ⊆ Z) : count Z (sSup Y) = Y.ncard := by
  rw [count, hZ.Iic_sSup_inter hbot hY]

theorem count_of_mem (hz : z ∈ Z) : count Z z = 1 := by
  simpa using count_sSup hZ hbot (singleton_subset_iff.2 hz)

end CompleteLattice

end Mereology
