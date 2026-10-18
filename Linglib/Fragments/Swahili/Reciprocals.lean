module

public import Linglib.Syntax.Reciprocal

/-!
# Swahili reciprocals

Swahili marks reciprocity with the verbal suffix *-an-*, which derives an intransitive verb whose
plural subject names the reciprocants, *Juma na Halima wa-li-tekeny-an-a* 'Juma and Halima tickled
each other'; with a singular subject and a comitative *na* phrase it forms the discontinuous
reciprocal, *Juma a-li-tekeny-an-a na Halima*, which Nordlinger reviews. The suffix is distinct
from the reflexive prefix *ji-*, which stands in the object slot, *a-li-ji-kata* 'she cut herself'
beside *a-li-m-kata* 'she cut him', and does not vary for person. In some verbs the suffix is
lexicalized as part of the stem; Palmieri's appendix of these is `Studies/Palmieri2024.lean`.

## Main definitions

* `Swahili.Reciprocals.anSuffix`, `markers`: the marker and the inventory
* `Swahili.Reciprocals.reflexivePrefix`: the reflexive *ji-*, for contrast

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [haspelmath-2023b]
* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

@[expose] public section

namespace Swahili.Reciprocals

open Reciprocal

/-- The reciprocal suffix *-an-*. -/
def anSuffix : Marker :=
  { morphs := [.suff "an"], strategy := .verbalAffix }

/-- The marker inventory. -/
def markers : Finset Marker := {anSuffix}

/-- The reflexive prefix *ji-*, an argument index in the object slot. -/
def reflexivePrefix : Morphology.Morph := .pref "ji"

end Swahili.Reciprocals
