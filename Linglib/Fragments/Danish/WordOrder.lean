module

public import Linglib.Syntax.Clause.Basic

/-!
# Danish word order

Danish is a verb-second language: in a main clause the finite verb follows exactly one constituent,
*Kaffe drikker Peter ofte om morgenen* 'Coffee Peter often drinks in the morning', and begins a
yes/no-question, *Drikker Peter ofte kaffe om morgenen?* 'Does Peter often drink coffee in the
morning?'. Since the verb does not otherwise leave the verb phrase, a subordinate clause places it
after the sentence adverbials, *Vi ved at Peter ofte drikker kaffe* 'We know that Peter often
drinks coffee'. Some types of exclamative are verb second, *Hvor er han sød!* 'How nice he is!',
though not all.

Verb second in a subordinate clause is what Vikner calls *limited embedded V2*: it depends on the
matrix verb. The complement of a *bridge verb* such as *påstå* 'claim', *sige* 'say' or *vide*
'know' may be verb second, *Watson påstod at disse penge havde Moriarty stjålet* 'Watson claimed
that this money Moriarty had stolen', while that of *bevise* 'prove' or *beklage* 'regret' may not.
Embedded verb second also needs the complementizer *at*, which is otherwise optional: *Hun sagde at
vi skulle ikke købe denne bog* 'She said that we should not buy this book' is verb second, and
without *at* the same order is marginal. Embedded questions are never verb second, nor is an
*at*-clause used as an exclamation, *At du da ikke kan holde din mund!* 'I wish you hadn't said
that!'.

## Implementation notes

Each cell records the left edges the language admits, written `⟨complementizer, verbSecond⟩` as a
`Clause.LeftEdge`, and verb second is read off them. The complement of a bridge verb is the
quasi-subordinated context; other subordinate clauses are subordinated. The comments locate each
cell: V cites Vikner by numbered example or page, W cites the third chapter of Westergaard by
example or note.

## TODO

The imperative cell is unrecorded: Westergaard sets no verb movement to the imperative head, which
concerns the verb's position relative to an overt subject, and Vikner does not describe the order
of Danish imperatives. The embedded constituent question records Vikner's object and adjunct
questions; subject questions, which add a complementizer, are not recorded.

## References

* [vikner-1995]
* [westergaard-2009]
-/

@[expose] public section

namespace Danish

open Clause

/-- The left edges of Danish clauses, written `⟨complementizer, verbSecond⟩`. -/
def leftEdges : LeftEdge.Table
  | .declarative, .matrix => some {⟨false, true⟩}  -- V (33c)–(33e)
  | .polar, .matrix => some {⟨false, true⟩}  -- V (33b), (42b)
  | .constituent, .matrix => some {⟨false, true⟩}  -- V (37c), (38c)
  | .exclamative, .matrix => some {⟨false, true⟩, ⟨false, false⟩}  -- W (17), note 1
  | .declarative, .quasiSubordinated =>  -- V (13a), (14a), (54), list (17)
    some {⟨true, true⟩, ⟨true, false⟩, ⟨false, false⟩}
  | .declarative, .subordinated => some {⟨true, false⟩, ⟨false, false⟩}  -- V (15a), (16a), p. 84
  | .polar, .subordinated => some {⟨true, false⟩}  -- V (45b)
  | .constituent, .subordinated => some {⟨false, false⟩}  -- V (43b), (44b)
  | .declarative, .insubordinated => some {⟨true, false⟩}  -- V (79a)
  | _, _ => none

/-- Verb second in Danish: required in root declaratives and questions, optional in exclamatives
and after a bridge verb, and excluded in the other clauses recorded. -/
def verbSecond : Distribution := leftEdges.verbSecond

end Danish
