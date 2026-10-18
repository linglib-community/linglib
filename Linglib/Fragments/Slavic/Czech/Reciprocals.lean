module

public import Linglib.Syntax.Reciprocal

/-!
# Czech reciprocals

Czech marks reciprocity with the reflexive clitic *se*, which also carries the reflexive reading and
yields a monovalent predicate, and with the bipartite periphrasis *jeden druhého* 'one the-other'
([nordlinger-2023], [siloni-2012]).

## References

* [nordlinger-2023]
* [siloni-2012]
-/

@[expose] public section

namespace Czech.Reciprocals

open Reciprocal

/-- *se*, the reflexive clitic in its reciprocal use. -/
def se : Marker :=
  { morphs := [.free "se"], strategy := .recipClitic }

/-- *jeden druhého* 'one the-other', the bipartite periphrastic reciprocal. -/
def jedenDruheho : Marker :=
  { morphs := [.free "jeden", .free "druhého"], strategy := .bipartiteNP }

/-- The reciprocal markers. -/
def markers : Finset Marker := {se, jedenDruheho}

end Czech.Reciprocals
