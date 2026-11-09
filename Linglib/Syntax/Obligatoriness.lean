module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Obligatoriness

This file defines `Obligatoriness`, whether an element or process is obligatory, optional or
excluded in a context: a particle in a sentence type, verb second in an embedding context, overt
case on an object of a given prominence, a Case a language's verbs assign. The values are ordered by
how far the element is required, and each is determined by the presence values it allows, a
nonempty set of booleans.

## Main definitions

* `Obligatoriness`, with its linear order from `excluded` to `obligatory`.
* `Obligatoriness.allowed`, `Obligatoriness.ofAllowed`: the presence values a value allows, and
  the value allowing a set of them.

## References

* [aissen-2003]
-/

@[expose] public section

/-- Whether an element or process is obligatory, optional or excluded in a context, the three
classes of objects that differential object marking distinguishes, in [aissen-2003]'s words. -/
inductive Obligatoriness where
  | excluded
  | optional
  | obligatory
  deriving DecidableEq, Repr, Fintype

namespace Obligatoriness

/-- Ordered by how far the element is required. -/
instance : LinearOrder Obligatoriness := .lift' (·.ctorIdx) (by decide)

instance : BoundedOrder Obligatoriness where
  bot := .excluded
  bot_le o := by cases o <;> decide
  top := .obligatory
  le_top o := by cases o <;> decide

/-- The values the presence of the element may take: presence where it is obligatory, absence
where it is excluded, either where it is optional. -/
def allowed : Obligatoriness → Finset Bool
  | .obligatory => {true}
  | .excluded => {false}
  | .optional => .univ

theorem allowed_injective : Function.Injective allowed := by decide

/-- The value allowing exactly the presence values in `a`: obligatory for presence alone, excluded
for absence alone, optional for both, and excluded for the empty set. -/
def ofAllowed (a : Finset Bool) : Obligatoriness :=
  if true ∈ a then if false ∈ a then .optional else .obligatory else .excluded

@[simp] theorem ofAllowed_allowed (o : Obligatoriness) : ofAllowed o.allowed = o := by
  decide +revert

theorem allowed_ofAllowed {a : Finset Bool} (h : a.Nonempty) : (ofAllowed a).allowed = a := by
  obtain ⟨b, hb⟩ := h
  ext x
  by_cases ht : true ∈ a <;> by_cases hf : false ∈ a <;> cases x <;> cases b <;>
    simp_all [ofAllowed, allowed]

end Obligatoriness
