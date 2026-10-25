module

public import Linglib.Syntax.Reflex
public import Linglib.Fragments.Mayan.Extraction

/-!
# Yucatec Maya extraction marking

Yucatec focuses or questions a transitive subject with its Agent Focus construction, a verb stem
without Set A, optionally after *j-*, whose status suffix is *-ik* in the incompletive, *-ej* in
the completive and *-il* in the perfect: *Máax kíin-s-ik-∅?* 'Who is killing him?'. Unlike Agent
Focus elsewhere in the family, it has no morpheme of its own. The intransitive subject extracts
unmarked, *Máax k-u-b'in y-éet-el?* 'Who's going with him?', and so does the object of *ti'*
'for', *Máax ti' k-a-meyaj?* 'For whom do you work?'. Itzaj and Mopan, the other Yucatecan
languages Hofling compares, have no Agent Focus construction.

## Main declarations

* `Yukatek.Extraction.realize`: the Agent Focus reflex of subject extraction and the unmarked
  extraction of the intransitive subject and of a benefactive.

## Implementation notes

The Agent Focus reflex is the alternation of the verb's form, recorded with an empty marker
since no morpheme codes it. The status suffixes are Hofling's; Aissen describes the construction
as lacking the status suffix as well as Set A. Hofling glosses the optional *j-* with a query as
the masculine clitic, and it is not recorded. The extraction of an object is not exemplified and
is left undescribed.

## Errata

Hofling's example (24) labels its Yucatec questions a, b, b and its Southern Lacandon ones d, d,
e; the question with *ti'* is the second (24b).

## References

* [hofling-2017]
* [aissen-2017]
-/

@[expose] public section

namespace Yukatek.Extraction

/-- The extraction of a transitive subject takes the Agent Focus form, a verb without Set A that
no morpheme marks ([hofling-2017] p. 733, (24b) p. 740, [aissen-2017] fn. 9 p. 321); the
intransitive subject ((15a) p. 733, (24a) p. 740) and the object of *ti'* 'for' (the second (24b)
p. 740) extract unmarked. -/
def realize : Mayan.ExtractionSite → Option (Finset (Reflex Mayan.Host))
  | .argument .A => some {.morpheme .verb []}
  | .argument .S | .adjunct .benefactive => some ∅
  | _ => none

end Yukatek.Extraction
