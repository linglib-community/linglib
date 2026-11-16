module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Group.End

/-!
# The action of order endomorphisms

The order embeddings of an order into itself form a monoid under composition, and act on the
order by application, as `Function.End` and `Equiv.Perm` do on a type.
-/

@[expose] public section

variable {α : Type*} [LE α]

/-- The tautological action of the order embeddings `α ↪o α` on `α`, by application. -/
instance OrderEmbedding.applyMulAction : MulAction (α ↪o α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem OrderEmbedding.smul_def (f : α ↪o α) (a : α) : f • a = f a :=
  rfl
