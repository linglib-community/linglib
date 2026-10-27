module

public import Linglib.Syntax.Clause.Basic

/-!
# Norwegian word order

This file records where the finite verb of Standard Norwegian and of the Nordmøre dialect
stands, as distributions over sentence types and embedding contexts. Faarlund, Lie and Vannebo
describe the Norwegian clause by two schemas. In schema A, the schema of main clauses, the finite
verb follows a forefield of at most one constituent and precedes the sentence adverbials: a
declarative or a wh-question fills the forefield and a yes/no-question leaves it empty, so that
its verb comes first. In schema B, the schema of most subordinate clauses, the finite verb
follows the subject and the sentence adverbials. Embedded questions take schema B, and so does
an *at*-clause used as an exclamation, *At du vil gjøre det!*. An *at*-clause that reports a
statement may take either schema, *Han sa at nå kunne de komme inn* beside *Han sa at de nå
kunne komme inn*, so that verb second is optional in the complement of a bridge verb such as
*si* 'say' and excluded under subordination elsewhere. Whether the complement keeps its
complementizer does not matter: Westergaard gives both orders with and without *at*.
Exclamatives are not verb second. Nordmøre Norwegian is strictly verb second in declaratives but
lets the verb stay low in every wh-question, with short and long wh-phrases alike, the
verb-second order remaining grammatical.

## Implementation notes

The comments locate each cell: FLV cites Faarlund, Lie and Vannebo by page, W cites
Westergaard by chapter-2 example number or table.

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

/-- Standard Norwegian requires verb second in root declaratives, yes/no-questions and
wh-questions and allows it in the complement of a bridge verb; it excludes it in exclamatives,
imperatives, embedded questions, other subordinate declaratives, and an *at*-clause used as an
exclamation. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory  -- FLV p. 859, W (5)–(7)
  | .polar, .matrix => some .obligatory  -- FLV p. 863, W (8)
  | .constituent, .matrix => some .obligatory  -- FLV p. 863, W (9), (10)
  | .exclamative, .matrix => some .excluded  -- W (13)
  | .imperative, .matrix => some .excluded  -- W Table 3.1
  | .declarative, .quasiSubordinated => some .optional  -- FLV pp. 866–867, W (36)
  | .declarative, .subordinated => some .excluded  -- FLV p. 866
  | .polar, .subordinated => some .excluded  -- FLV p. 865
  | .constituent, .subordinated => some .excluded  -- FLV p. 864, W (12)
  | .declarative, .insubordinated => some .excluded  -- FLV p. 864
  | _, _ => none

/-- Without its complementizer the complement of a bridge verb is still optionally verb second,
*Han sa han ikke kommer* beside *Han sa han kommer ikke*. -/
def verbSecondWithoutComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .optional  -- W (36)
  | _, _ => none

/-- Nordmøre Norwegian differs from Standard Norwegian in root clauses only in its wh-questions,
where verb second is optional; its embedded clauses are not described. -/
def Nordmore.verbSecond : Distribution
  | .constituent, .matrix => some .optional  -- W (37), (38)
  | t, .matrix => Norwegian.verbSecond t .matrix
  | _, _ => none

end Norwegian
