module

public import Linglib.Syntax.Negation

/-!
# Turkish negation

Turkish negates a verb with the suffix *-mA-*, *-ma-* or *-me-* by vowel harmony, between the
stem and the tense suffix: *gel-di* 'came', *gel-me-di* 'did not come'. The aorist is the one
tense whose marking changes under negation: the aorist suffix *-ir* of *gel-ir* 'comes' is *-z*
in the negative of the second and third persons, *gel-me-z*, and is absent in the first person,
*gel-me-m* beside *gel-ir-im*. Miestamo's examples are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace Turkish.Negation

/-- The negative suffix *-mA-*. -/
def mA : Marker := { pieces := [[.suff "mA"]] }

/-- The standard negators. -/
def standard : List Marker := [mA]

end Turkish.Negation
