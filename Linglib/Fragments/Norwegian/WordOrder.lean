module

public import Linglib.Syntax.Clause.Basic

/-!
# Norwegian word order

This file records where the finite verb of Standard Norwegian and of the Nordmøre dialect moves
to the left periphery, as a distribution over sentence types and embedding contexts. Standard
Norwegian is verb second in declarative main clauses, where one constituent precedes the finite
verb, in yes/no-questions, which begin with the finite verb, and in wh-questions, where the
wh-phrase fills the forefield and the finite verb follows, the three main-clause schemas of
Faarlund, Lie and Vannebo's reference grammar; a subordinate clause follows the grammar's
schema B, with the finite verb after the sentence adverbials, though an embedded declarative
may be verb second after a bridge verb, with or without the complementizer, as Westergaard
notes. Exclamatives and imperatives are not verb second. Nordmøre Norwegian is strictly verb
second in declaratives but lets the verb stay low in every wh-question, with short and long
wh-phrases alike, the verb-second order remaining grammatical.

## References

* [faarlund-lie-vannebo-1997]
* [westergaard-2009]
-/

@[expose] public section

namespace Norwegian

open Clause

/-- Standard Norwegian has obligatory verb second in root declaratives, yes/no-questions and
wh-questions, none in exclamatives, imperatives and subordinate questions, and optional verb
second in an embedded declarative with or without its complementizer. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .excluded
  | .imperative, .matrix => some .excluded
  | .declarative, .subordinated => some .optional
  | .declarative, .quasiSubordinated => some .optional
  | .polar, .subordinated => some .excluded
  | .constituent, .subordinated => some .excluded
  | _, _ => none

/-- Nordmøre Norwegian differs from Standard Norwegian in root clauses only in its wh-questions,
where verb second is optional; its embedded clauses are not described. -/
def Nordmore.verbSecond : Distribution
  | .constituent, .matrix => some .optional
  | t, .matrix => Norwegian.verbSecond t .matrix
  | _, _ => none

end Norwegian
