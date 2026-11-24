/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Topology.Order.UpperLowerSetTopology`.
-/
module

public import Linglib.Core.Order.UpperLower.Closure
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Interior and derived set in the lower set topology

In the lower set topology the open sets are the lower sets, the least neighbourhood of a point
`x` is `Set.Iic x`, and mathlib shows that the closure of a set is its upper closure. This file
adds the interior and the derived set. A point is interior to `s` when everything below it is in
`s`, and is an accumulation point of `s` when some other point of `s` lies below it. In a partial
order the isolated points of `s` are therefore its minimal elements, and in a well-founded one
every set lies in the closure of its isolated points.

## Main results

* `Topology.IsLowerSet.mem_interior_iff`: `x ∈ interior s ↔ Set.Iic x ⊆ s`.
* `Topology.IsLowerSet.mem_derivedSet_iff`: `x ∈ derivedSet s ↔ ∃ y ∈ s, y < x`.
* `Topology.IsLowerSet.mem_sdiff_derivedSet_iff`: the isolated points of a set are its minimal
  elements.
* `Topology.IsLowerSet.closure_sdiff_derivedSet`: in a well-founded order the closure of the
  isolated points of a set is the closure of the set.
-/

public section

open Set Filter Topology

namespace Topology.IsLowerSet

variable {α : Type*} [TopologicalSpace α]

section Preorder

variable [Preorder α] [Topology.IsLowerSet α] {s : Set α} {x : α}

theorem Iic_mem_nhds (x : α) : Iic x ∈ 𝓝 x := by
  rw [nhds_eq_principal_Iic]
  exact mem_principal_self _

theorem mem_interior_iff : x ∈ interior s ↔ Iic x ⊆ s := by
  rw [mem_interior_iff_mem_nhds, nhds_eq_principal_Iic, mem_principal]

end Preorder

section PartialOrder

variable [PartialOrder α] [Topology.IsLowerSet α] {s : Set α} {x : α}

theorem mem_derivedSet_iff : x ∈ derivedSet s ↔ ∃ y ∈ s, y < x := by
  rw [mem_derivedSet, accPt_iff_frequently, nhds_eq_principal_Iic, frequently_principal]
  exact ⟨fun ⟨y, hyx, hne, hy⟩ ↦ ⟨y, hy, lt_of_le_of_ne hyx hne⟩,
    fun ⟨y, hy, hyx⟩ ↦ ⟨y, hyx.le, hyx.ne, hy⟩⟩

/-- The isolated points of a set in the lower set topology are its minimal elements. -/
theorem mem_sdiff_derivedSet_iff : x ∈ s \ derivedSet s ↔ Minimal (· ∈ s) x := by
  rw [Set.mem_sdiff, mem_derivedSet_iff, minimal_iff_forall_lt]
  exact and_congr_right fun _ ↦ ⟨fun h y hy hys ↦ h ⟨y, hys, hy⟩, fun h ⟨y, hys, hy⟩ ↦ h hy hys⟩

/-- In a well-founded order with the lower set topology, a set lies in the closure of its
isolated points. -/
theorem closure_sdiff_derivedSet [WellFoundedLT α] (s : Set α) :
    closure (s \ derivedSet s) = closure s := by
  rw [closure_eq_upperClosure, closure_eq_upperClosure, ← upperClosure_setOf_minimal s]
  congr 2
  exact Set.ext fun _ ↦ mem_sdiff_derivedSet_iff

end PartialOrder

end Topology.IsLowerSet
