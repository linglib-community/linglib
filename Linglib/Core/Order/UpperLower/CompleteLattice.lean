module

public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# Heyting implication of lower sets

[UPSTREAM] Lower sets of a preorder form a completely distributive lattice, hence a Heyting
algebra. This file characterizes membership in the Heyting implication: `a` lies in `P ⇨ Q` when
every element below `a` that lies in `P` lies in `Q`.

## Main results

* `LowerSet.mem_himp`: membership in `P ⇨ Q`.
-/

@[expose] public section

namespace LowerSet

variable {α : Type*} [Preorder α] {P Q : LowerSet α} {a : α}

theorem mem_himp : a ∈ P ⇨ Q ↔ ∀ b ≤ a, b ∈ P → b ∈ Q := by
  rw [← Iic_le, le_himp_iff, ← coe_subset_coe, coe_inf, Set.subset_def]
  simp [and_imp]

end LowerSet
