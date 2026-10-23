/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Fixed blocks of pretransitive actions

A set fixed by every element of a group acting pretransitively is empty or the whole space:
any point of the set reaches every point of the space inside the set. This is the triviality
lemma for `MulAction.IsFixedBlock` missing next to mathlib's `MulAction.IsBlock` API.

## Main results

* `MulAction.IsFixedBlock.eq_empty_or_univ`: a fixed block of a pretransitive action is `∅` or
  `Set.univ`.
-/

@[expose] public section

namespace MulAction

open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- A fixed block of a pretransitive action is empty or the whole space. -/
theorem IsFixedBlock.eq_empty_or_univ [IsPretransitive G X] {B : Set X}
    (hB : IsFixedBlock G B) : B = ∅ ∨ B = Set.univ := by
  rcases B.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · exact Or.inl h
  · refine Or.inr (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨g, hg⟩ := exists_smul_eq G a x
    exact hg ▸ hB g ▸ Set.smul_mem_smul_set ha

end MulAction
