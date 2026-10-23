/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Well-quasi-orders: finite bases and Higman's lemma

The finite-basis property of well-quasi-orders, that every upward-closed set is the union of
finitely many principal filters, and Higman's lemma: over a finite alphabet the sublist order on
`List α` is a well-quasi-order, the case of mathlib's
`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` at equality.

## References

* [higman-1952]
-/

@[expose] public section

variable {α : Type*}

theorem WellQuasiOrdered.exists_finset_eq_biUnion {r : α → α → Prop} [IsPartialOrder α r]
    (hr : WellQuasiOrdered r) {s : Set α} (hs : ∀ ⦃a b⦄, r a b → a ∈ s → b ∈ s) :
    ∃ F : Finset α, s = ⋃ a ∈ F, {b | r a b} := by
  have hfin : {a | a ∈ s ∧ ∀ b ∈ s, r b a → b = a}.Finite :=
    IsAntichain.finite_of_wellQuasiOrdered (fun _ ha _ hb hne hab ↦ hne (hb.2 _ ha.1 hab)) hr
  refine ⟨hfin.toFinset, Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, exists_prop]
  refine ⟨fun hx ↦ ?_, fun ⟨m, ⟨hm, _⟩, hmx⟩ ↦ hs hmx hm⟩
  obtain ⟨m, ⟨hm, hmx⟩, hmin⟩ := hr.wellFounded.has_min {a | a ∈ s ∧ r a x} ⟨x, hx, refl_of r x⟩
  exact ⟨m, ⟨hm, fun b hb hbm ↦
    antisymm hbm (not_not.mp fun h ↦ hmin b ⟨hb, trans_of r hbm hmx⟩ ⟨hbm, h⟩)⟩, hmx⟩

theorem List.wellQuasiOrdered_sublist [Finite α] :
    WellQuasiOrdered (List.Sublist : List α → List α → Prop) := fun f ↦ by
  obtain ⟨m, n, hmn, h⟩ := Set.PartiallyWellOrderedOn.exists_lt
    (Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (Eq : α → α → Prop)
      Set.finite_univ.partiallyWellOrderedOn) (f := f) fun _ _ _ ↦ Set.mem_univ _
  exact ⟨m, n, hmn, by simpa [sublistForall₂_iff, forall₂_eq_eq_eq] using h⟩
