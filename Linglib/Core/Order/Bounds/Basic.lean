module

public import Mathlib.Order.Bounds.Basic

/-!
# Bounds of open intervals

In a densely ordered lattice the endpoints of a nonempty open interval are its greatest lower and
least upper bounds, so the interval lies inside a closed interval exactly when its endpoints do:
the missing sibling of `Set.Ioo_subset_Ioo_iff` and `Set.Icc_subset_Icc_iff`.

`[UPSTREAM]` candidate for `Mathlib/Order/Bounds/Basic.lean`, beside `isGLB_Ioo`.
-/

public section

namespace Set

variable {α : Type*} [Lattice α] [DenselyOrdered α] {a₁ a₂ b₁ b₂ : α}

theorem Ioo_subset_Icc_iff (h₁ : a₁ < b₁) : Ioo a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  subset_inter_iff.trans <|
    and_congr (le_isGLB_iff (isGLB_Ioo h₁)).symm (isLUB_le_iff (isLUB_Ioo h₁)).symm

end Set
