module

public import Mathlib.Order.Closure

/-!
# Principal closure operators

[UPSTREAM] candidate for `Mathlib/Order/Closure.lean`.

On a join-semilattice, joining with a fixed element `a` is a closure operator whose closed
elements are those above `a`. On a join-semilattice with a bottom element, these principal
closure operators are exactly the closure operators whose closed elements form an upper set:
such an operator joins its argument with the closure of `⊥`.

## Main definitions

* `ClosureOperator.supRight`: the closure operator `(· ⊔ a)`.

## Main results

* `ClosureOperator.isClosed_supRight_iff`: the closed elements of `(· ⊔ a)` are those above `a`.
* `ClosureOperator.eq_supRight_iff`: a closure operator is `(· ⊔ c ⊥)` exactly when its closed
  elements form an upper set.
-/

@[expose] public section

namespace ClosureOperator

variable {α : Type*} [SemilatticeSup α] {a x : α}

/-- The principal closure operator `(· ⊔ a)`, whose closed elements are those above `a`. -/
@[simps! apply]
def supRight (a : α) : ClosureOperator α :=
  .mk' (· ⊔ a) (fun _ _ h ↦ sup_le_sup_right h a) (fun _ ↦ le_sup_left)
    fun _ ↦ by rw [sup_assoc, sup_idem]

theorem isClosed_supRight_iff : (supRight a).IsClosed x ↔ a ≤ x :=
  (supRight a).isClosed_iff.trans sup_eq_left

theorem isUpperSet_setOf_isClosed_supRight (a : α) :
    IsUpperSet {x | (supRight a).IsClosed x} := fun _ _ hxy hx ↦
  isClosed_supRight_iff.2 ((isClosed_supRight_iff.1 hx).trans hxy)

/-- A closure operator joins its argument with the closure of `⊥` exactly when its closed
elements form an upper set. -/
theorem eq_supRight_iff [OrderBot α] (c : ClosureOperator α) :
    c = supRight (c ⊥) ↔ IsUpperSet {x | c.IsClosed x} := by
  refine ⟨fun h ↦ h ▸ isUpperSet_setOf_isClosed_supRight _, fun h ↦ ext _ _ fun x ↦ ?_⟩
  refine le_antisymm (c.closure_min le_sup_left ?_) (sup_le (c.le_closure x) (c.monotone bot_le))
  exact h le_sup_right (c.isClosed_closure ⊥)

end ClosureOperator
