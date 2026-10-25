module

public import Linglib.Syntax.Clause.Basic

/-!
# Danish word order

This file records where the finite verb of Danish moves to the left periphery, as a
distribution over sentence types and embedding contexts. A main clause is verb second: the
finite verb follows one constituent in a declarative or a wh-question, begins a
yes/no-question, and precedes the sentence adverbials. Danish has no verb movement to I, so a
subordinate clause has the finite verb after the sentence adverbials, *Vi ved at Peter ofte
drikker kaffe*. An embedded declarative may still be verb second after a bridge verb such as
*vide* 'know' or *påstå* 'claim', though not after *bevise* 'prove' or *beklage* 'regret', and
then keeps the complementizer *at*, without which it is marginal. An embedded question is never
verb second, and an *at*-clause used as an exclamation, *At du ikke kan holde din mund!*, keeps
the subordinate order. Some types of exclamative are verb second, *Hvor er han sød!*, though not
all, and imperatives are not, by Westergaard's description.

## References

* [vikner-1995]
* [westergaard-2009]
-/

@[expose] public section

namespace Danish

open Clause

/-- Danish has obligatory verb second in the three root clause types, optional verb second in
exclamatives and in an embedded declarative with *at*, and none in imperatives, embedded
questions, an embedded declarative without *at*, or an *at*-clause used as a root utterance. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .optional
  | .imperative, .matrix => some .excluded
  | .declarative, .subordinated => some .optional
  | .declarative, .quasiSubordinated => some .excluded
  | .polar, .subordinated => some .excluded
  | .constituent, .subordinated => some .excluded
  | .declarative, .insubordinated => some .excluded
  | _, _ => none

end Danish
