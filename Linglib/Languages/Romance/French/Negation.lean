module

public import Linglib.Syntax.Negation

/-!
# French negation

French negates a clause with the proclitic *ne* before the finite verb and *pas* after it: *jean
vient* 'Jean comes', *jean ne vient pas* 'Jean does not come'. Nothing else in the clause changes.
*Ne* is regularly dropped in colloquial speech, leaving *pas* as the only negator. On its own,
without *pas*, *ne* occurs expletively under *avoir peur* 'fear', *avant que* 'before', *à moins
que* 'unless' and other triggers; the examples of Jin and Koenig are the rows of
`Data.Examples.JinKoenig2021`. Miestamo's examples are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [jin-koenig-2021]
-/

@[expose] public section

open Negation

namespace French.Negation

/-- *ne … pas*, the standard negator. -/
def nePas : Marker := { pieces := [[.procl "ne"], [.free "pas"]] }

/-- *ne* alone, the expletive negator. -/
def ne : Marker := { pieces := [[.procl "ne"]] }

/-- The standard negators. -/
def standard : List Marker := [nePas]

end French.Negation
