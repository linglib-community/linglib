module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Lango prepositions

The prepositions of Lango as `Adposition` entries: so far *kèdè* 'with', which marks
accompaniment and the instrument. Lango has no symmetric conjunction of noun phrases, and
*kèdè* is also the usual way of linking them, `Lango.Coordination.kede` ([noonan-1992], §8.7.5,
pp. 162–163).

## Main definitions

* `Lango.Adpositions.kede`: the comitative-instrumental preposition.

## Implementation notes

* Like other Lango prepositions, *kèdè* is conjugated for the person of its object, *kedi*
  'with you'; the entry records the third person singular form.

## References

* [noonan-1992]
-/

@[expose] public section

namespace Lango.Adpositions

/-- *kèdè* 'with', marking a companion or an instrument. -/
def kede : Adposition :=
  { morphs := [.free "kèdè"], linearization := {.pre}, functions := {.comitative, .instrumental},
    complements := {some .np} }

end Lango.Adpositions
