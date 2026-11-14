module

public import Linglib.Syntax.Case.Basic

/-!
# Zürich German case

This file defines the cases of Shieber's Zürich German clauses: the nominative of a subject such
as *mer* 'we', and the accusative and the dative of the objects, which the article tells apart,
*de Hans* against *em Hans* (Shieber's (3)–(4)), as `articleCase` records.

## Implementation notes

The cases are those the clauses mark, and no other case of the dialect is recorded.

## References

* [shieber-1985]
-/

@[expose] public section

namespace German.Zurich

/-- The cases of the clauses. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The dative. -/
  | dat
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | dat => .dat

/-- The articles of the clauses' objects and the case each marks: *em* the dative, and *de*, *es*
and the clitic *d'* the accusative. -/
def articleCase : List (String × Case) :=
  [("em", .dat), ("de", .acc), ("es", .acc), ("d'", .acc)]

end German.Zurich
