/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Modality.OrderingSemantics
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Ordering semantics in the lower-set topology

In the lower-set topology of a preorder the open sets are the lower sets, so the interior of `t`
is the set of worlds all of whose predecessors are `t`-worlds, and a set is dense when every world
has one of its worlds below it. Necessity in ordering semantics is then truth on a dense open set
and good possibility truth on a nonempty open set. Two dense open sets meet in a dense open set,
which is why necessities are closed under intersection, while two nonempty open sets can be
disjoint, which is why good possibilities are not.

The forces over a domain are the forces over the domain as a preordered type in its own right,
so the characterization holds over any domain in the lower-set topology of its restricted order.

## Main statements

* `OrderingSemantics.isNecessity_iff_dense_interior`: necessity is truth on a dense open set.
* `OrderingSemantics.isGoodPossibility_iff_nonempty_interior`: good possibility is truth on a
  nonempty open set.

## References

* [lewis-1981]
-/

@[expose] public section

namespace OrderingSemantics

open Set Topology

/-! ### Over a whole preordered type -/

section Univ

variable {α : Type*} [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] {t : Set α}

theorem interior_eq_setOf_forall_le : interior t = {a | ∀ b ≤ a, b ∈ t} := by
  ext a
  conv_lhs => rw [← compl_compl t, interior_compl, Topology.IsLowerSet.closure_eq_upperClosure]
  simp only [mem_compl_iff, SetLike.mem_coe, mem_upperClosure, not_exists, not_and, mem_ofPred_eq]
  exact ⟨fun h b hb ↦ by_contra fun hbt ↦ h b hbt hb, fun h b hbt hb ↦ hbt (h b hb)⟩

theorem dense_iff_forall_exists_le {D : Set α} : Dense D ↔ ∀ a, ∃ d ∈ D, d ≤ a := by
  rw [dense_iff_closure_eq, Topology.IsLowerSet.closure_eq_upperClosure, eq_univ_iff_forall]
  simp only [SetLike.mem_coe, mem_upperClosure]

theorem isNecessity_univ_iff_dense_interior :
    IsNecessity ‹Preorder α› univ t ↔ Dense (interior t) := by
  simp only [dense_iff_forall_exists_le, interior_eq_setOf_forall_le, IsNecessity, mem_univ,
    true_and, mem_ofPred_eq, forall_const]
  exact forall_congr' fun _ ↦ exists_congr fun _ ↦ and_comm

theorem isGoodPossibility_univ_iff_nonempty_interior :
    IsGoodPossibility ‹Preorder α› univ t ↔ (interior t).Nonempty := by
  simp only [interior_eq_setOf_forall_le, IsGoodPossibility, mem_univ, true_and, forall_const,
    Set.Nonempty, mem_ofPred_eq]

end Univ

/-! ### Over a domain -/

section Domain

variable {W : Type*} (p : Preorder W) (s t : Set W)

theorem isNecessity_iff_subtype :
    IsNecessity p s t ↔ IsNecessity (@Preorder.lift s W p Subtype.val) univ (Subtype.val ⁻¹' t) :=
  ⟨fun h ⟨u, hu⟩ _ ↦
      let ⟨v, hv, hvu, hvt⟩ := h u hu
      ⟨⟨v, hv⟩, trivial, hvu, fun ⟨w, hw⟩ _ hwv ↦ hvt w hw hwv⟩,
    fun h u hu ↦
      let ⟨⟨v, hv⟩, _, hvu, hvt⟩ := h ⟨u, hu⟩ trivial
      ⟨v, hv, hvu, fun w hw hwv ↦ hvt ⟨w, hw⟩ trivial hwv⟩⟩

theorem isGoodPossibility_iff_subtype :
    IsGoodPossibility p s t ↔
      IsGoodPossibility (@Preorder.lift s W p Subtype.val) univ (Subtype.val ⁻¹' t) :=
  ⟨fun ⟨v, hv, hvt⟩ ↦ ⟨⟨v, hv⟩, trivial, fun ⟨w, hw⟩ _ hwv ↦ hvt w hw hwv⟩,
    fun ⟨⟨v, hv⟩, _, hvt⟩ ↦ ⟨v, hv, fun w hw hwv ↦ hvt ⟨w, hw⟩ trivial hwv⟩⟩

theorem isNecessity_iff_dense_interior :
    letI : Preorder s := @Preorder.lift s W p Subtype.val
    IsNecessity p s t ↔ Dense (interior (Subtype.val ⁻¹' t : Set (WithLowerSet s))) := by
  let : Preorder s := @Preorder.lift s W p Subtype.val
  exact (isNecessity_iff_subtype p s t).trans
    (isNecessity_univ_iff_dense_interior (α := WithLowerSet s))

theorem isGoodPossibility_iff_nonempty_interior :
    letI : Preorder s := @Preorder.lift s W p Subtype.val
    IsGoodPossibility p s t ↔ (interior (Subtype.val ⁻¹' t : Set (WithLowerSet s))).Nonempty := by
  let : Preorder s := @Preorder.lift s W p Subtype.val
  exact (isGoodPossibility_iff_subtype p s t).trans
    (isGoodPossibility_univ_iff_nonempty_interior (α := WithLowerSet s))

end Domain

end OrderingSemantics
