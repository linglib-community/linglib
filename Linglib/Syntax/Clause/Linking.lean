module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Clause linking

Two linked clauses stand in one of sixteen semantic relations, the subtypes of Dixon's six types
of clause linking. Temporal linking is succession ('and then'), relative time ('after', 'before',
'while') or condition; consequence is cause, result or purpose; possible consequence ('lest')
stands alone; addition is unordered, of two aspects of one event, elaboration or contrast;
alternatives are disjunction, rejection ('instead of') or suggestion ('rather than'); and manner
is real ('like') or hypothetical ('as if'). In most kinds one clause is the focal clause, the
central activity or state, and the other a supporting clause that sets out its temporal milieu,
a condition or a presupposition for it.

## Main definitions

* `Clause.Linking`: the sixteen kinds of clause linking.
* `Clause.LinkingType`: the six types, with `Clause.Linking.type` the type of a kind.

## References

* [dixon-2009]
-/

@[expose] public section

namespace Clause

/-- The six semantic types of clause linking. -/
inductive LinkingType where
  | temporal
  | consequence
  | possibleConsequence
  | addition
  | alternatives
  | manner
  deriving DecidableEq, Repr, Fintype

/-- The kinds of clause linking, the semantic relations in which a supporting clause stands to
its focal clause. -/
inductive Linking where
  /-- Temporal succession: one event and then the other. -/
  | succession
  /-- Relative time: the time of one event located by the other, as with 'after', 'before',
  'when', 'since', 'until' and 'while'. -/
  | relativeTime
  /-- The supporting clause is a condition on the focal clause. -/
  | conditional
  /-- The supporting clause gives the reason for the focal clause. -/
  | cause
  /-- The focal clause is a natural consequence of the supporting clause. -/
  | result
  /-- The focal clause is done so that the event of the other will come about. -/
  | purpose
  /-- The supporting clause is a consequence to be guarded against, as with 'lest' and
  'in case'. -/
  | possibleConsequence
  /-- Two pieces of information are added, in no order. -/
  | unorderedAddition
  /-- The clauses describe two aspects of one event. -/
  | sameEventAddition
  /-- The second clause elaborates on the first. -/
  | elaboration
  /-- The focal clause holds against what the supporting clause would lead one to expect, as
  with 'but' and 'although'. -/
  | contrast
  /-- The clauses are alternatives, as with 'or'. -/
  | disjunction
  /-- One alternative is rejected for the other, as with 'instead of'. -/
  | rejection
  /-- One alternative is preferred to the other, as with 'rather than'. -/
  | suggestion
  /-- The supporting clause says how the event of the focal clause is done. -/
  | realManner
  /-- The supporting clause says how the event of the focal clause appears to be done, as with
  'as if'. -/
  | hypotheticalManner
  deriving DecidableEq, Repr, Fintype

/-- The type of a kind of linking. -/
def Linking.type : Linking → LinkingType
  | .succession | .relativeTime | .conditional => .temporal
  | .cause | .result | .purpose => .consequence
  | .possibleConsequence => .possibleConsequence
  | .unorderedAddition | .sameEventAddition | .elaboration | .contrast => .addition
  | .disjunction | .rejection | .suggestion => .alternatives
  | .realManner | .hypotheticalManner => .manner

end Clause
