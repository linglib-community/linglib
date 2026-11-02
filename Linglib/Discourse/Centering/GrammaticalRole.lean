module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Case.Alignment

/-!
# Centering theory: ranking by grammatical role

This file defines the grammatical roles by which Grosz, Joshi, and Weinstein rank the
forward-looking centers of an English utterance: the subject above the objects, and the objects
above every other role. Sidner's focusing theory had ordered its potential foci by thematic role
instead. Grosz, Joshi, and Weinstein call grammatical role a major factor in the ranking, not the
only one, and Gordon, Grosz, and Gilliom found that surface-initial position also raises an
entity's prominence, whether or not it is the subject. Read as a marking of the comparative
coding slots, the ranking [groups S with A](##isAccusative_ofArgumentRole) and
[P with R and T](##isNeutral_ofArgumentRole_comp_ditransitive).

## Implementation notes

The coding-slot map reads a ditransitive as a double-object construction, whose recipient and
theme are both objects. A recipient in a prepositional phrase is an other role, so no map from
the coding slots fits both English ditransitive constructions.

## References

* [grosz-joshi-weinstein-1995]
* [sidner-1979]
* [gordon-grosz-gilliom-1993]
-/

@[expose] public section

namespace Discourse.Centering

/-- The grammatical roles by which [grosz-joshi-weinstein-1995] rank forward-looking centers,
SUBJECT > OBJECT(S) > OTHER (p. 214): the subject, an object, and every other role. -/
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

/-- The role of a comparative coding slot in an English clause: S and A are subjects, and P, R,
and T are objects, R and T as the two objects of a double-object construction. -/
def ofArgumentRole : ArgumentRole → GrammaticalRole
  | .S | .A => .subject
  | .P | .R | .T => .object

theorem ofArgumentRole_ne_other (r : ArgumentRole) : ofArgumentRole r ≠ other := by
  cases r <;> nofun

theorem isAccusative_ofArgumentRole : Alignment.IsAccusative ofArgumentRole := ⟨rfl, nofun⟩

theorem isNeutral_ofArgumentRole_comp_ditransitive :
    Alignment.IsNeutral (ofArgumentRole ∘ Alignment.ditransitive) :=
  ⟨rfl, rfl⟩

end GrammaticalRole

end Discourse.Centering
