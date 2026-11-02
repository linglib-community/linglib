/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Chain

/-!
# Lemmas about `List.IsChain`

The `List.IsChain` counterparts of three `List.Pairwise` facts in core that mathlib lacks: a
relation holding everywhere makes every list a chain, `List.pairwise_of_forall`, and a chain for a
conjunction of relations is exactly a chain for each conjunct, `List.pairwise_and_iff` and
`List.Pairwise.and`. [UPSTREAM] candidates for `Mathlib/Data/List/Chain.lean`.
-/

public section

namespace List

variable {α : Type*} {R S T : α → α → Prop} {l : List α}

theorem isChain_of_forall (H : ∀ x y, R x y) : IsChain R l := (pairwise_of_forall H).isChain

theorem isChain_and_iff :
    l.IsChain (fun a b ↦ S a b ∧ T a b) ↔ l.IsChain S ∧ l.IsChain T := by
  simp [isChain_iff_getElem, forall_and]

theorem IsChain.and (hS : l.IsChain S) (hT : l.IsChain T) : l.IsChain fun a b ↦ S a b ∧ T a b :=
  isChain_and_iff.2 ⟨hS, hT⟩

end List
