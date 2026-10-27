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
though not all, and imperatives are not, by Westergaard's description.

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

Verb second is a `Clause.Distribution` over sentence types and embedding contexts. The complement
of a bridge verb is the quasi-subordinated context, whose cell combines the clauses with and
without *at*; other subordinate clauses are subordinated. The comments locate each cell: V cites
Vikner by numbered example or page, W cites the third chapter of Westergaard by example, note or
table.

## References

* [vikner-1995]
* [westergaard-2009]
-/

@[expose] public section

namespace Danish

open Clause

/-- Verb second in a subordinate clause introduced by *at*: optional after a bridge verb. -/
def verbSecondWithComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .optional  -- V (13a), (14a), (54a), (54c)
  | _, _ => none

/-- Verb second in a subordinate clause without a complementizer: excluded after a bridge verb,
where it needs *at*. -/
def verbSecondWithoutComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .excluded  -- V (54b), (81b)
  | _, _ => none

/-- Verb second in Danish: required in root declaratives and questions, optional in exclamatives
and after a bridge verb, and excluded in the other clauses recorded. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory  -- V (33c)–(33e)
  | .polar, .matrix => some .obligatory  -- V (33b)
  | .constituent, .matrix => some .obligatory  -- V (37c), (38c)
  | .exclamative, .matrix => some .optional  -- W (17), note 1
  | .imperative, .matrix => some .excluded  -- W Table 3.1
  | t, .quasiSubordinated =>  -- V list (17)
    verbSecondWithComplementizer.union verbSecondWithoutComplementizer t .quasiSubordinated
  | .declarative, .subordinated => some .excluded  -- V (15a), (16a), list (18)
  | .polar, .subordinated => some .excluded  -- V p. 85
  | .constituent, .subordinated => some .excluded  -- V p. 85
  | .declarative, .insubordinated => some .excluded  -- V (79a)
  | _, _ => none

end Danish
