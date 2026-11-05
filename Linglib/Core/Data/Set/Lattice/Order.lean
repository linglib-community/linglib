/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Lattice.Order

/-!
# Maps out of a powerset that preserve suprema

A powerset is the free complete lattice on its members: a map out of it preserves suprema exactly
when it is the supremum of its values on singletons. `[UPSTREAM]` candidate for
`Mathlib/Data/Set/Lattice/Order.lean`, beside `iSup_sUnion`.
-/

public section

namespace Set

variable {α β : Type*} [CompleteLattice β] {f : Set α → β}

theorem forall_map_sSup_iff :
    (∀ T : Set (Set α), f (sSup T) = ⨆ t ∈ T, f t) ↔ ∀ s, f s = ⨆ a ∈ s, f {a} := by
  refine ⟨fun h s ↦ ?_, fun h T ↦ ?_⟩
  · conv_lhs => rw [← biUnion_of_singleton s, ← sUnion_image, ← sSup_eq_sUnion, h, iSup_image]
  · rw [h (sSup T), sSup_eq_sUnion, iSup_sUnion]
    exact iSup_congr fun t ↦ iSup_congr fun _ ↦ (h t).symm

end Set
