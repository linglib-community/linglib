module

public import Linglib.Syntax.Reciprocal

/-!
# Portuguese reciprocals

Brazilian Portuguese marks reciprocity with the clitic *se*, which is also the reflexive and
yields a monovalent predicate, and with the bipartite *um o outro* 'one the other'. Beside these
a class of transitive verbs has a lexical reciprocal entry: with *abraçar* 'hug' and its
siblings the reciprocal reading also arises without *se*, in Brazilian Portuguese both in finite
clauses, *X e Y abraçaram*, and in analytic causatives, *eu fiz X e Y abraçarem*, the two
environments of Palmieri's table where the clitic may be omitted. The lexical reciprocals are
entries of `Portuguese.Verbs`, and Palmieri's list of them and their two-entry analysis are
`Studies/Palmieri2024.lean`.

## Main definitions

* `Portuguese.Reciprocals.seClitic`, `Portuguese.Reciprocals.bipartite`,
  `Portuguese.Reciprocals.markers`: the reciprocal markers.

## References

* [palmieri-2024]
-/

@[expose] public section

namespace Portuguese.Reciprocals

open Reciprocal

/-- The clitic *se* in its reciprocal use, also the reflexive. -/
def seClitic : Marker :=
  { morphs := [.free "se"], strategy := .recipClitic, readings := {.reciprocal, .reflexive} }

/-- The bipartite *um o outro* 'one the other'. -/
def bipartite : Marker :=
  { morphs := [.free "um", .free "o", .free "outro"], strategy := .bipartiteNP }

/-- The reciprocal markers. -/
def markers : Finset Marker := {seClitic, bipartite}

end Portuguese.Reciprocals
