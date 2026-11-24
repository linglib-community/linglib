module

public import Linglib.Syntax.Negation

/-!
# Burmese negation

Burmese negates a verb with a discontinuous marker: the prefix *ma-* and a suffix, *-bû* in
*ma-θwâ-bû* '(he) does not go', which stands in the slot of the postverbal markers of the
affirmative. Those markers distinguish the actual *θwâ-dé* '(he) goes, went', the potential *θwâ-mé*
'(he) will go' and the perfect *θwâ-bí* '(he) has gone', and the one negative form answers to all
three. Miestamo's examples, from Cornyn's grammar, are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [cornyn-1944]
-/

@[expose] public section

open Negation

namespace Burmese.Negation

/-- The discontinuous negator *ma-…-bû*, whose suffix Miestamo cites as *-phû*. -/
def maBu : Marker := { pieces := [[.pref "ma"], [.suff "bû"]] }

/-- The standard negators. -/
def standard : List Marker := [maBu]

end Burmese.Negation
