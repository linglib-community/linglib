module

public import Linglib.Syntax.Clause.Basic

/-!
# Norwegian word order

Norwegian is a verb-second language: in a main clause the finite verb is preceded by exactly one
constituent, *Da snakker han engelsk* 'Then he speaks English'. Faarlund, Lie and Vannebo describe
the clause by two schemas. Schema A, the schema of main clauses, places the finite verb after the
forefield, which holds at most one constituent, and before the sentence adverbials. A declarative
or a wh-question fills the forefield; a yes/no-question leaves it empty, so that the verb comes
first, *Liker du jordbær?* 'Do you like strawberries?', as does an imperative, *Kom hit!* 'Come
here!'. Schema B, the schema of most subordinate clauses, places the finite verb after the subject
and the sentence adverbials, *da han ikkje hadde eti middag den dagen* 'when he had not eaten
dinner that day'. Exclamatives are not verb second, *Så fin du er!* 'How nice you look!'.

Among subordinate clauses, schema A is found above all in an *at*-clause that reports a statement,
the complement of a *bridge verb* such as *si* 'say', and even there schema B is possible: *Han sa
at nå kunne de komme inn* beside *Han sa at de nå kunne komme inn* 'He said that now they could
come in'. Whether the complementizer *at* is present does not matter, as Westergaard notes, *Han sa
(at) han kommer ikke* 'He said (that) he isn't coming'. A conditional clause without a subjunction
also takes schema A, *Kjem dei, går ikkje eg* 'If they come, I'm not going'. Embedded questions
take schema B, as does an *at*-clause used on its own as an exclamation, *At du vil gjøre det!*
'That you would do that!'.

The Nordmøre dialect differs from Standard Norwegian in its wh-questions, where verb second is
optional with short and long wh-phrases alike, *Kåles bil du kjøpte?* beside *Kåles bil kjøpte
du?* 'Which car did you buy?'; its declaratives are strictly verb second.

## Implementation notes

Each cell records the left edges the language admits, written `⟨complementizer, verbSecond⟩` as a
`Clause.LeftEdge`, and verb second is read off them. The complement of a bridge verb is the
quasi-subordinated context, which admits every left edge; other subordinate clauses are
subordinated, an embedded subject question takes the subjunction *som*, and conditional clauses
have no cell. The comments locate each cell: FLV cites Faarlund, Lie and Vannebo by page, W cites
the second chapter of Westergaard by example.

## References

* [faarlund-lie-vannebo-1997]
* [westergaard-2009]
-/

@[expose] public section

namespace Norwegian

open Clause

/-- The left edges of Standard Norwegian clauses, written `⟨complementizer, verbSecond⟩`. -/
def leftEdges : LeftEdge.Table
  | .declarative, .matrix => some {⟨false, true⟩}  -- FLV p. 859, W (5)–(7)
  | .polar, .matrix => some {⟨false, true⟩}  -- FLV p. 863, W (8)
  | .constituent, .matrix => some {⟨false, true⟩}  -- FLV p. 863, W (9), (10)
  | .exclamative, .matrix => some {⟨false, false⟩}  -- W (13)
  | .imperative, .matrix => some {⟨false, true⟩}  -- FLV p. 863
  | .declarative, .quasiSubordinated => some .univ  -- FLV pp. 866–867, W (36)
  | .declarative, .subordinated => some {⟨true, false⟩, ⟨false, false⟩}  -- FLV p. 866
  | .polar, .subordinated => some {⟨true, false⟩}  -- FLV p. 865
  | .constituent, .subordinated => some {⟨false, false⟩, ⟨true, false⟩}  -- FLV pp. 864–866
  | .declarative, .insubordinated => some {⟨true, false⟩}  -- FLV p. 864
  | _, _ => none

/-- Verb second in Standard Norwegian: required in root declaratives, questions and imperatives,
optional after a bridge verb, and excluded in the other clauses recorded. -/
def verbSecond : Distribution := leftEdges.verbSecond

/-- The left edges of Nordmøre clauses: as in Standard Norwegian in root clauses, except that a
wh-question may leave its verb unfronted. Subordinate clauses are not described. -/
def Nordmore.leftEdges : LeftEdge.Table
  | .constituent, .matrix => some {⟨false, true⟩, ⟨false, false⟩}  -- W (37), (38)
  | t, .matrix => Norwegian.leftEdges t .matrix
  | _, _ => none

/-- Verb second in the Nordmøre dialect. -/
def Nordmore.verbSecond : Distribution := Nordmore.leftEdges.verbSecond

end Norwegian
