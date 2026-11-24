module

public import Linglib.Languages.Chichewa.Voice
public import Linglib.Syntax.Reciprocal

/-!
# Chicheŵa reciprocals

Chicheŵa marks reciprocity with the verbal suffix *-an-*, the Bantu reciprocal extension
reconstructed for Proto-Bantu as \*-an: *Mbiǐdzi zi-ku-mény-an-a* 'The zebras are hitting each
other', Nordlinger's example from Dalrymple, Mchombo and Peters. The suffix derives an
intransitive verb whose subject names the reciprocants, so, as Hyman and Mchombo observe, it
does not combine with the passive *-idw-* in either order: a transitive verb such as *mang-*
'tie' is detransitivized only once. The reflexive, on Dalrymple, Mchombo and Peters's analysis
as Palmieri reports it, is instead an incorporated pronoun that leaves its clause transitive.
The reciprocants may also be split between the subject and a comitative *ndi* phrase, *Mtengo
u-na-gwer-ana ndi munthu* 'A tree and a person fell on each other', an example of Mchombo and
Ngalande's that Palmieri cites.

## Implementation notes

The reflexive is not entered: the sources at hand state the contrast but not its form.

## References

* [nordlinger-2023]
* [hyman-mchombo-1992]
* [palmieri-2024]
-/

@[expose] public section

namespace Chichewa.Reciprocals

open Reciprocal

/-- The reciprocal suffix *-an-*, the marker of the reciprocal voice. -/
def anSuffix : Marker :=
  { morphs := Chichewa.reciprocal.marker, strategy := .verbalAffix }

/-- The marker inventory. -/
def markers : Finset Marker := {anSuffix}

end Chichewa.Reciprocals
