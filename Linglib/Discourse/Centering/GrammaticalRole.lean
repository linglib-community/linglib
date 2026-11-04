module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.Alignment
public import Linglib.Syntax.Voice.TermRole

/-!
# Centering theory: ranking by grammatical role

This file defines the grammatical roles by which Grosz, Joshi, and Weinstein rank the
forward-looking centers of an English utterance: the subject above the objects, and the objects
above every other role. Sidner's focusing theory had ordered its potential foci by thematic role
instead. Grosz, Joshi, and Weinstein call grammatical role a major factor in the ranking, not the
only one, and Gordon, Grosz, and Gilliom found that surface-initial position also raises an
entity's prominence, whether or not it is the subject. A term of a construction takes its role
from its transitivity-related role, so that the ranking, read through the comparative coding
slots, [groups S with A](##isAccusative_ofTermRole_comp_ofArgumentRole).

## Implementation notes

Roles are read off the terms of a construction rather than the coding slots, since one coding
slot can be a core term in one construction and an oblique in another: the recipient of *gave
her a book* is an object and that of *gave a book to her* an oblique, as is the initial A of a
long passive.

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

/-- The role of a term in an English clause by its transitivity-related role: an S or A term is
the subject, a P term an object, and an oblique an other role. -/
def ofTermRole : Voice.TermRole → GrammaticalRole
  | .S | .A => .subject
  | .P => .object
  | .X => .other

theorem isAccusative_ofTermRole_comp_ofArgumentRole :
    Alignment.IsAccusative (ofTermRole ∘ Voice.TermRole.ofArgumentRole) :=
  ⟨rfl, nofun⟩

end GrammaticalRole

end Discourse.Centering
