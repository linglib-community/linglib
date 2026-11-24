module

public import Linglib.Syntax.Negation

/-!
# Russian negation

Russian negates a clause with the preverbal particle *ne* (не), and nothing else in the clause
changes: *ja govor-ju po-russkij* 'I speak Russian', *ja ne govor-ju po-russkij* 'I do not speak
Russian'. Negative concord is obligatory, every item of the *ni-* series co-occurring with *ne*; the
items are entered in `Languages/Slavic/Russian/PolarityItems.lean`. Miestamo's examples are rows of
`Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace Russian.Negation

/-- *ne* (не), the standard negator. -/
def ne : Marker := { pieces := [[.free "ne"]] }

/-- The standard negators. -/
def standard : List Marker := [ne]

end Russian.Negation
