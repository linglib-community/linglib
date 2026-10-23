module

public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Interval inclusions in a linear order

Over a dense order, a nonempty open interval lies inside a closed interval exactly when its
endpoints do, the missing sibling of `Set.Ioo_subset_Ioo_iff` and `Set.Icc_subset_Ioo_iff`. And
in any linear order a ray closed above is never inside a ray open below. Both are `[UPSTREAM]`
additions to `Mathlib.Order.Interval.Set.LinearOrder`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [LinearOrder α]

theorem not_Iic_subset_Ioi (a b : α) : ¬ Iic a ⊆ Ioi b :=
  fun h ↦ lt_irrefl b ((h (min_le_left a b)).trans_le (min_le_right a b))

variable [DenselyOrdered α] {a₁ a₂ b₁ b₂ : α}

theorem Ioo_subset_Icc_iff (h₁ : a₁ < b₁) : Ioo a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  refine ⟨fun h ↦ ⟨le_of_not_gt fun h' ↦ ?_, le_of_not_gt fun h' ↦ ?_⟩,
    fun h ↦ Ioo_subset_Icc_self.trans (Icc_subset_Icc h.1 h.2)⟩
  · obtain ⟨x, hx₁, hx₂⟩ := exists_between (lt_min h' h₁)
    exact (lt_min_iff.1 hx₂).1.not_ge (h ⟨hx₁, (lt_min_iff.1 hx₂).2⟩).1
  · obtain ⟨x, hx₁, hx₂⟩ := exists_between (max_lt h' h₁)
    exact (max_lt_iff.1 hx₁).1.not_ge (h ⟨(max_lt_iff.1 hx₁).2, hx₂⟩).2

end Set
