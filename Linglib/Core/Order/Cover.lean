/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Cover
public import Mathlib.Order.WellFounded
public import Mathlib.Order.UpperLower.Basic

/-!
# Covers

`[UPSTREAM]` In a linear order the greatest element strictly below `b` is the one `b` covers, and a
lower set has greatest element `a` exactly when it contains `a` and not the element covering it.
When `>` is well-founded, an order with a non-maximal element has one whose strict successors are
all maximal (`exists_not_isMax_and_forall_gt_isMax`).
-/

public section

variable {α : Type*}

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

/-- The greatest element strictly below `b` is the one that `b` covers. -/
theorem isGreatest_Iio_iff_covBy : IsGreatest (Set.Iio b) a ↔ a ⋖ b :=
  ⟨fun h ↦ ⟨h.1, fun _ hac hcb ↦ hac.not_ge (h.2 hcb)⟩, fun h ↦ ⟨h.lt, fun _ hc ↦ h.le_of_lt hc⟩⟩

/-- The least element strictly above `a` is the one that covers `a`. -/
theorem isLeast_Ioi_iff_covBy : IsLeast (Set.Ioi a) b ↔ a ⋖ b :=
  ⟨fun h ↦ ⟨h.1, fun _ hac hcb ↦ hcb.not_ge (h.2 hac)⟩, fun h ↦ ⟨h.lt, fun _ hc ↦ h.ge_of_gt hc⟩⟩

/-- A lower set has greatest element `a` exactly when it contains `a` and not the element
covering `a`. -/
theorem IsLowerSet.isGreatest_iff_of_covBy (hs : IsLowerSet s) (h : a ⋖ b) :
    IsGreatest s a ↔ a ∈ s ∧ b ∉ s :=
  ⟨fun hg ↦ ⟨hg.1, fun hb ↦ h.lt.not_ge (hg.2 hb)⟩,
    fun ⟨ha, hb⟩ ↦ ⟨ha, fun _ hc ↦ not_lt.1 fun hac ↦ hb (hs (h.ge_of_gt hac) hc)⟩⟩

end LinearOrder

/-- Two distinct elements covering the same element are incomparable. -/
theorem CovBy.not_le_of_ne [PartialOrder α] {a b c : α} (hab : a ⋖ b) (hac : a ⋖ c)
    (hbc : b ≠ c) : ¬ b ≤ c :=
  fun h ↦ hbc ((hac.eq_or_eq hab.le h).resolve_left hab.ne')

/-- When `>` is well-founded, as on a finite order, an order with a non-maximal element has one
all of whose strict successors are maximal. -/
theorem exists_not_isMax_and_forall_gt_isMax [Preorder α] [WellFoundedGT α] {a : α}
    (ha : ¬ IsMax a) : ∃ b : α, ¬ IsMax b ∧ ∀ c, b < c → IsMax c :=
  let ⟨b, hb, hmax⟩ := (wellFounded_gt (α := α)).has_min {b | ¬ IsMax b} ⟨a, ha⟩
  ⟨b, hb, fun c hbc ↦ of_not_not fun hc ↦ hmax c hc hbc⟩

/-- An element is branching when at least two elements cover it. -/
@[expose] def IsBranching [Preorder α] (a : α) : Prop := {b | a ⋖ b}.Nontrivial
