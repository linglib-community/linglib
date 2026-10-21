module

public import Mathlib.Order.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Logophoric roles

Sells replaces a single notion of logophoricity with three discourse roles, each defined with
respect to a proposition: the source, the intentional agent of the communication; the self, whose
mental state or attitude the proposition describes; and the pivot, with respect to whose location
the proposition is evaluated. A report predicates each role of the external speaker or of a
referent inside the sentence, and the roles form a hierarchy: where the source is internal so is
the self, and where the self is internal so is the pivot. The order here is that hierarchy, the
pivot least.

## Main definitions

* `LogophoricRole`: the three roles, a bounded linear order.

## Implementation notes

* The discourse environments the hierarchy sorts, and the forms oriented to each role, are in
  `Studies/Sells1987.lean`.

## References

* [sells-1987]
-/

@[expose] public section

/-- The discourse roles of [sells-1987], ordered by his hierarchy with the pivot least. -/
inductive LogophoricRole where
  /-- The one with respect to whose location the content of the report is evaluated. -/
  | pivot
  /-- The one whose mental state or attitude the content of the report describes. -/
  | self
  /-- The intentional agent of the communication. -/
  | source
  deriving DecidableEq, Fintype, Repr

namespace LogophoricRole

/-- The rank of a role in the hierarchy. -/
def toNat : LogophoricRole → ℕ
  | .pivot => 0
  | .self => 1
  | .source => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [toNat]

instance : LinearOrder LogophoricRole := LinearOrder.lift' toNat toNat_injective

instance : BoundedOrder LogophoricRole where
  bot := .pivot
  bot_le r := by cases r <;> decide
  top := .source
  le_top r := by cases r <;> decide

end LogophoricRole

