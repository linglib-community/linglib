/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Group.Multiset

/-!
# `Multiset.filterMap` as an additive monoid hom

`Multiset.filterMapAddMonoidHom` bundles `Multiset.filterMap f` as an additive monoid hom, as
`Multiset.mapAddMonoidHom` bundles `Multiset.map f`, so that `map_sum`, `map_list_sum` and
`map_nsmul` apply to it. A multiple of a nonzero multiset has no duplicates only once
(`Multiset.Nodup.le_one_of_nsmul`). `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Algebra.Order.Group.Multiset`.
-/

@[expose] public section

namespace Multiset

variable {α β : Type*}

/-- `Multiset.filterMap` as an `AddMonoidHom`. -/
@[simps]
def filterMapAddMonoidHom (f : α → Option β) : Multiset α →+ Multiset β where
  toFun := filterMap f
  map_zero' := filterMap_zero f
  map_add' := filterMap_add f

@[simp] theorem coe_filterMapAddMonoidHom (f : α → Option β) :
    ⇑(filterMapAddMonoidHom f) = filterMap f := rfl

/-- A multiple of a nonzero multiset without duplicates is at most a single copy. -/
theorem Nodup.le_one_of_nsmul [DecidableEq α] {n : ℕ} {s : Multiset α} (h : (n • s).Nodup)
    (hs : s ≠ 0) : n ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_mem_of_ne_zero hs
  have h1 := nodup_iff_count_le_one.1 h a
  rw [count_nsmul] at h1
  exact (Nat.le_mul_of_pos_right n (count_pos.2 ha)).trans h1

end Multiset
