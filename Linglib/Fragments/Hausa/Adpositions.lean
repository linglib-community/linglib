module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Hausa prepositions

The prepositions of Hausa as `Adposition` entries: so far the comitative-instrumental *dà*
'with' ([jaggar-2001], p. 222), the same word as the coordinator *dà* 'and',
`Hausa.Coordination.da`.

## Main definitions

* `Hausa.Adpositions.da`: the comitative-instrumental preposition.

## References

* [jaggar-2001]
-/

@[expose] public section

namespace Hausa.Adpositions

/-- *dà* 'with', marking a companion or an instrument. -/
def da : Adposition :=
  { morphs := [.free "dà"], linearization := {.pre}, functions := {.comitative, .instrumental},
    complements := {some .np} }

end Hausa.Adpositions
