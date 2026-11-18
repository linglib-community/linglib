/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Locally finite linear orders embed in the integers

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/LinearLocallyFinite.lean`. A locally finite
linear order embeds in `ℤ` by numbering its elements from a base point, `toZ`, once it is given
the successor and predecessor structure of a locally finite order. An interval of a linear order
is finite exactly when finitely many covering steps lead from one end to the other, the converse
of `transGen_covBy_of_lt`.
-/

public section

theorem nonempty_orderEmbedding_int (ι : Type*) [LinearOrder ι] [LocallyFiniteOrder ι] :
    Nonempty (ι ↪o ℤ) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨OrderEmbedding.ofIsEmpty⟩
  | inr hι =>
    let := LinearLocallyFiniteOrder.succOrder ι
    let := LinearLocallyFiniteOrder.predOrder ι
    exact ⟨OrderEmbedding.ofStrictMono (toZ hι.some) toZ_strictMono⟩

variable {α : Type*} {a b : α}

theorem Set.Finite.transGen_covBy [PartialOrder α] (h : (Set.Icc a b).Finite) (hab : a < b) :
    Relation.TransGen (· ⋖ ·) a b := by
  have := h.to_subtype
  let := LocallyFiniteOrder.ofFiniteIcc fun x y : Set.Icc a b ↦ Set.toFinite (Set.Icc x y)
  have hr : (Set.range (OrderEmbedding.subtype (· ∈ Set.Icc a b))).OrdConnected := by
    simpa [Set.Icc] using Set.ordConnected_Icc (a := a) (b := b)
  exact (transGen_covBy_of_lt (x := (⟨a, Set.left_mem_Icc.2 hab.le⟩ : Set.Icc a b))
    (y := ⟨b, Set.right_mem_Icc.2 hab.le⟩) hab).lift Subtype.val fun _ _ ↦
      (hr.apply_covBy_apply_iff _).2

theorem Relation.TransGen.finite_Icc [LinearOrder α] (h : Relation.TransGen (· ⋖ ·) a b) :
    (Set.Icc a b).Finite := by
  induction h with
  | single h => exact h.Icc_eq ▸ Set.toFinite _
  | tail _ h ih =>
    exact (ih.union (h.Icc_eq ▸ Set.toFinite _)).subset Set.Icc_subset_Icc_union_Icc
