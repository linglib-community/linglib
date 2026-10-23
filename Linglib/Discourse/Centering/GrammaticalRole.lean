module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Centering theory: ranking by grammatical role

The ranking of forward-looking centers that centering theory assumes for English: the subject
outranks the object, which outranks every other role. Kameyama argued for grammatical role over
Sidner's focus-based ranking, Grosz, Joshi, and Weinstein adopt it in their examples, and Gordon,
Grosz, and Gilliom's repeated-name penalty experiments support it.

## Main declarations

* `Discourse.Centering.GrammaticalRole`: subject, object, and other, linearly ordered in that
  order of prominence.
* `GrammaticalRole.ofArgumentRole`: the role of a comparative coding slot under an accusative
  alignment, the hom from `ArgumentRole` that connects the ranking to the clause
  vocabulary.

## References

* [kameyama-1986]
* [grosz-joshi-weinstein-1995]
* [gordon-grosz-gilliom-1993]
-/

@[expose] public section

namespace Discourse.Centering

/-- A grammatical role ranking the forward-looking centers: subject over object over the rest. -/
inductive GrammaticalRole where
  | subject
  | object
  | other
  deriving DecidableEq, Repr, Fintype

namespace GrammaticalRole

/-- The prominence of a role, the subject the most prominent. -/
def rank : GrammaticalRole → ℕ
  | .subject => 2
  | .object => 1
  | .other => 0

instance : LinearOrder GrammaticalRole := LinearOrder.lift' rank (by decide)

theorem object_lt_subject : object < subject := by decide

theorem other_lt_object : other < object := by decide

/-- The role of a comparative coding slot under the accusative alignment the ranking was stated
for: the S and A slots are the subject and the P, R, and T slots are objects. Obliques lie
outside the coding slots and are the other roles. -/
def ofArgumentRole : ArgumentRole → GrammaticalRole
  | .S | .A => .subject
  | .P | .R | .T => .object

theorem ofArgumentRole_ne_other (r : ArgumentRole) : ofArgumentRole r ≠ other := by
  cases r <;> decide

end GrammaticalRole

end Discourse.Centering
