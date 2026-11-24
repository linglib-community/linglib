module

public import Linglib.Core.Order.SupClosed
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# Heyting implication of lower sets

[UPSTREAM] Lower sets of a preorder form a completely distributive lattice, hence a Heyting
algebra. This file characterizes membership in the Heyting implication: `a` lies in `P ⇨ Q` when
every element below `a` that lies in `P` lies in `Q`. Implication from a lower set closed under
joins distributes over the join of lower sets.

## Main results

* `LowerSet.mem_himp`: membership in `P ⇨ Q`.
* `LowerSet.himp_sup_of_supClosed`: if `P` is closed under joins, then
  `P ⇨ Q ⊔ R = (P ⇨ Q) ⊔ (P ⇨ R)`.
-/

public section

namespace LowerSet

variable {α : Type*} [Preorder α] {P Q : LowerSet α} {a : α}

theorem mem_himp : a ∈ P ⇨ Q ↔ ∀ b ≤ a, b ∈ P → b ∈ Q := by
  rw [← Iic_le, le_himp_iff, ← coe_subset_coe, coe_inf, Set.subset_def]
  simp [and_imp]

theorem mem_himp_iff_inter_Iic_subset :
    a ∈ P ⇨ Q ↔ (P : Set α) ∩ Set.Iic a ⊆ Q :=
  mem_himp.trans ⟨fun h _ hb ↦ h _ hb.2 hb.1, fun h _ hba hb ↦ h ⟨hb, hba⟩⟩

/-- If `P` is closed under joins, then implication from `P` distributes over joins. -/
theorem himp_sup_of_supClosed {α : Type*} [SemilatticeSup α] {P : LowerSet α}
    (hP : SupClosed (P : Set α)) (Q R : LowerSet α) : P ⇨ Q ⊔ R = (P ⇨ Q) ⊔ (P ⇨ R) := by
  refine SetLike.ext fun a ↦ ?_
  rw [mem_sup_iff, mem_himp_iff_inter_Iic_subset, mem_himp_iff_inter_Iic_subset,
    mem_himp_iff_inter_Iic_subset, coe_sup]
  exact (hP.inter (show SupClosed (Set.Iic a) from fun _ hb _ hc ↦ sup_le hb hc)).subset_union_iff
    Q.lower R.lower

end LowerSet
