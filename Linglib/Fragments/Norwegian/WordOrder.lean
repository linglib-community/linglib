module

public import Linglib.Syntax.Clause.Basic

/-!
# Norwegian word order

Norwegian is a verb-second language: in a main clause the finite verb is preceded by exactly one
constituent, *Da snakker han engelsk* 'Then he speaks English'. Faarlund, Lie and Vannebo describe
the clause by two schemas. Schema A, the schema of main clauses, places the finite verb after the
forefield, which holds at most one constituent, and before the sentence adverbials. A declarative
or a wh-question fills the forefield; a yes/no-question leaves it empty, so that the verb comes
first, *Liker du jordbær?* 'Do you like strawberries?'. Schema B, the schema of most subordinate
clauses, places the finite verb after the subject and the sentence adverbials, *da han ikkje hadde
eti middag den dagen* 'when he had not eaten dinner that day'. Exclamatives are not verb second,
*Så fin du er!* 'How nice you look!'.

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

Verb second is a `Clause.Distribution` over sentence types and embedding contexts. The complement
of a bridge verb is the quasi-subordinated context, whose cell combines the clauses with and
without *at*; other subordinate clauses are subordinated, and conditional clauses have no cell. The
comments locate each cell: FLV cites Faarlund, Lie and Vannebo by page, W cites the second chapter
of Westergaard by example or the third by table.

## TODO

Faarlund, Lie and Vannebo give an imperative the order of a yes/no-question, an empty forefield
and the verb before the negation, *Ta ikkje boka mi!* (p. 863), while the imperative cell records
Westergaard's setting of no verb movement to the imperative head; the German and Danish files
record their imperatives the same way.

## References

* [faarlund-lie-vannebo-1997]
* [westergaard-2009]
-/

@[expose] public section

namespace Norwegian

open Clause

/-- Verb second in a subordinate clause introduced by *at*: optional after a bridge verb. -/
def verbSecondWithComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .optional  -- FLV pp. 866–867, W (36)
  | _, _ => none

/-- Verb second in a subordinate clause without a complementizer: optional after a bridge verb,
as with *at*. -/
def verbSecondWithoutComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .optional  -- W (36)
  | _, _ => none

/-- Verb second in Standard Norwegian: required in root declaratives and questions, optional
after a bridge verb, and excluded in the other clauses recorded. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory  -- FLV p. 859, W (5)–(7)
  | .polar, .matrix => some .obligatory  -- FLV p. 863, W (8)
  | .constituent, .matrix => some .obligatory  -- FLV p. 863, W (9), (10)
  | .exclamative, .matrix => some .excluded  -- W (13)
  | .imperative, .matrix => some .excluded  -- W Table 3.1
  | t, .quasiSubordinated =>
    verbSecondWithComplementizer.union verbSecondWithoutComplementizer t .quasiSubordinated
  | .declarative, .subordinated => some .excluded  -- FLV p. 866
  | .polar, .subordinated => some .excluded  -- FLV p. 865
  | .constituent, .subordinated => some .excluded  -- FLV p. 864, W (12)
  | .declarative, .insubordinated => some .excluded  -- FLV p. 864
  | _, _ => none

/-- Verb second in the Nordmøre dialect: as in Standard Norwegian in root clauses, except that it
is optional in wh-questions. Subordinate clauses are not described. -/
def Nordmore.verbSecond : Distribution
  | .constituent, .matrix => some .optional  -- W (37), (38)
  | t, .matrix => Norwegian.verbSecond t .matrix
  | _, _ => none

end Norwegian
