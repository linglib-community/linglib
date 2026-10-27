module

public import Linglib.Syntax.Clause.Basic

/-!
# German word order

German is a verb-second language in main clauses: the finite verb follows exactly one constituent
in a declarative or a wh-question, *Die Kinder haben diesen Film gesehen* 'The children have seen
this film', *Was haben die Kinder gesehen?* 'What have the children seen?', and comes first in a
yes/no-question and in an imperative, *Tritt bitte von der Bahnsteigkante zurück!* 'Please step
back from the edge of the track!'. In a subordinate clause it comes last, *Er sagt, daß die Kinder
diesen Film gesehen haben* 'He says that the children have seen this film'. Exclamatives are not
verb second.

Verb second in a subordinate clause depends on the matrix verb: the complement of a *bridge verb*
such as *behaupten* 'claim' or *sagen* 'say' may be verb second, that of *beweisen* 'prove' or
*bedauern* 'regret' may not, and embedded questions never are. In a bridge complement verb second
and the complementizer *dass* exclude each other, and one of them must be present, so the clause is
verb second exactly when it lacks a complementizer: *Sie sagte, sie würde kommen* beside *Sie
sagte, daß sie kommen würde* 'She said (that) she would come'.

A subordinate form used as a root utterance keeps the verb last: the *dass*-clause in isolation,
which Durrell records as a command, wish or exclamation, and the deliberative *ob*- or wh-question
of Gutzmann's minimal pairs.

## Implementation notes

Each cell records the left edges the language admits, written `⟨complementizer, verbSecond⟩` as a
`Clause.LeftEdge`, and verb second is read off them. The complement of a bridge verb is the
quasi-subordinated context, and a subordinate form used as a root utterance is insubordinated. The
comments locate each cell: V cites Vikner by numbered example or page, W cites Westergaard by
second-chapter example or table, G cites Gutzmann by example or page.

## References

* [westergaard-2009]
* [vikner-1995]
* [durrell-2011]
* [gutzmann-2015]
-/

@[expose] public section

namespace German

open Clause

/-- The left edges of German clauses, written `⟨complementizer, verbSecond⟩`. -/
def leftEdges : LeftEdge.Table
  | .declarative, .matrix => some {⟨false, true⟩}  -- V (36a)
  | .polar, .matrix => some {⟨false, true⟩}  -- V (42c)
  | .constituent, .matrix => some {⟨false, true⟩}  -- V (37d)
  | .exclamative, .matrix => some {⟨false, false⟩}  -- W Table 3.1
  | .imperative, .matrix => some {⟨false, true⟩}  -- G (5.53), pp. 193–194
  | .declarative, .quasiSubordinated => some {⟨true, false⟩, ⟨false, true⟩}  -- W (17); V (52)
  | .declarative, .subordinated => some {⟨true, false⟩}  -- V (15b), (16b)
  | .polar, .subordinated => some {⟨true, false⟩}  -- V (45c)
  | .constituent, .subordinated => some {⟨false, false⟩}  -- V (43c), (44c)
  | .declarative, .insubordinated => some {⟨true, false⟩}  -- G (5.44)
  | .polar, .insubordinated => some {⟨true, false⟩}  -- G (5.36b)
  | .constituent, .insubordinated => some {⟨false, false⟩}  -- G (5.48)
  | _, _ => none

/-- Verb second in German: required in root declaratives, questions and imperatives, optional after
a bridge verb, and excluded in the other clauses recorded. -/
def verbSecond : Distribution := leftEdges.verbSecond

end German
