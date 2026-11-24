module

public import Linglib.Syntax.Negation

/-!
# Spanish negation

Spanish negates a clause with the preverbal particle *no*, and nothing else in the clause changes:
*canta-s* 'you sing', *no canta-s* 'you do not sing'. A preverbal n-word excludes *no* and a
postverbal one requires it; the n-words are entered in
`Languages/Romance/Spanish/PolarityItems.lean`. Miestamo's examples are rows of
`Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace Spanish.Negation

/-- *no*, the standard negator. -/
def no : Marker := { pieces := [[.free "no"]] }

/-- The standard negators. -/
def standard : List Marker := [no]

end Spanish.Negation
