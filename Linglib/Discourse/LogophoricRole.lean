module

public import Mathlib.Order.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Logophoric roles

A report has three discourse roles, each defined with respect to the proposition reported
([sells-1987]). The *source* is the intentional agent of the communication, the *self* is the one
whose mental state or attitude the proposition describes, and the *pivot* is the one with respect
to whose location in space and time the proposition is evaluated. A role is held either by the
external speaker or by a referent inside the sentence, and in the second case it is *internal*.

We define the type `LogophoricRole` of the three roles as a bounded linear order with
`pivot < self < source`. This is the hierarchy of [sells-1987], on which an internal source
implies an internal self and an internal self an internal pivot, so that the roles internal to a
report form a lower set.

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

instance : LinearOrder LogophoricRole := LinearOrder.lift' (·.ctorIdx) (by decide)

instance : BoundedOrder LogophoricRole where
  bot := pivot
  bot_le := by decide
  top := source
  le_top := by decide

end LogophoricRole
