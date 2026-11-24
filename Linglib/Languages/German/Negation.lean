module

public import Linglib.Syntax.Negation

/-!
# German negation

This file defines German standard negation, the particle *nicht*, which follows the finite verb of a
main clause: *ich singe* 'I sing', *ich singe nicht* 'I do not sing'. Nothing else in the clause
changes, in any person or tense. Miestamo's examples are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace German.Negation

/-- *Nicht* is the standard negator. -/
def nicht : Marker := { pieces := [[.free "nicht"]] }

/-- The standard negators. -/
def standard : List Marker := [nicht]

end German.Negation
