module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Order.LatticeIntervals

/-!
# Projection onto a ray and the ray's endpoints

This file describes when `Set.projIci a` reaches the endpoints of the ray `Set.Ici a`, whose least
element is `a` and whose greatest element is the ambient `⊤`. A point goes to the least element
exactly when it lies at or below `a`, and to the greatest exactly when `a` or the point is `⊤`.
The lemmas restate `Set.projIci_eq_self`, `lt_max_iff` and `max_eq_top` through the endpoints of
the ray, and are `[UPSTREAM]` additions to `Mathlib.Order.Interval.Set.ProjIcc`.
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {a x : α}

theorem projIci_eq_bot : projIci a x = ⊥ ↔ x ≤ a := projIci_eq_self

theorem bot_lt_projIci : ⊥ < projIci a x ↔ a < x := by
  rw [bot_lt_iff_ne_bot, Ne, projIci_eq_bot, not_le]

theorem projIci_eq_top [OrderTop α] : projIci a x = ⊤ ↔ a = ⊤ ∨ x = ⊤ := by
  rw [Subtype.ext_iff, coe_projIci, Ici.coe_top, max_eq_top]

end Set
