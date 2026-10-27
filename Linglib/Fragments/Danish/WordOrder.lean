module

public import Linglib.Syntax.Clause.Basic

/-!
# Danish word order

This file records where the finite verb of Danish moves to the left periphery, as
distributions over sentence types and embedding contexts. A main clause is verb second: the
finite verb follows one constituent in a declarative or a wh-question, begins a
yes/no-question, and precedes the sentence adverbials. Danish has no verb movement to I, so a
subordinate clause has the finite verb after the sentence adverbials, *Vi ved at Peter ofte
drikker kaffe*. Embedded verb second is limited by the matrix verb: the complement of a bridge
verb such as *påstå* 'claim', *sige* 'say' or *vide* 'know' may be verb second or not, while that
of *bevise* 'prove' or *beklage* 'regret' may not, so that verb second is optional in the
complement of a bridge verb and excluded under subordination elsewhere. Embedded verb second
also needs the complementizer *at*, without which it is marginal, although *at* is optional in
an embedded clause that is not verb second. An embedded question is never verb second, and an
*at*-clause used as an exclamation, *At du da ikke kan holde din mund!*, keeps the subordinate
order. Some types of exclamative are verb second, *Hvor er han sød!*, though not all, and
imperatives are not, by Westergaard's description.

## Implementation notes

The comments locate each cell: V cites Vikner by numbered example or page, W cites the third
chapter of Westergaard by example, note or table.

## References

* [vikner-1995]
* [westergaard-2009]
-/

@[expose] public section

namespace Danish

open Clause

/-- Danish requires verb second in the three root clause types and allows it in exclamatives and
in the complement of a bridge verb; it excludes it in imperatives, embedded questions, other
subordinate declaratives, and an *at*-clause used as an exclamation. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory  -- V (33c)–(33e)
  | .polar, .matrix => some .obligatory  -- V (33b)
  | .constituent, .matrix => some .obligatory  -- V (37c), (38c)
  | .exclamative, .matrix => some .optional  -- W (17), note 1
  | .imperative, .matrix => some .excluded  -- W Table 3.1
  | .declarative, .quasiSubordinated => some .optional  -- V (13a), (14a), list (17)
  | .declarative, .subordinated => some .excluded  -- V (15a), (16a), list (18)
  | .polar, .subordinated => some .excluded  -- V p. 85
  | .constituent, .subordinated => some .excluded  -- V p. 85
  | .declarative, .insubordinated => some .excluded  -- V (79a)
  | _, _ => none

/-- Without *at* the complement of a bridge verb is not verb second,
*??Hun sagde vi skulle ikke købe denne bog*. -/
def verbSecondWithoutComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .excluded  -- V (54b), (81b)
  | _, _ => none

end Danish
