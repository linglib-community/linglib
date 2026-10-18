module

public import Linglib.Syntax.Reciprocal

/-!
# Swahili reciprocals

Swahili marks reciprocity with the verbal suffix *-an-*, which derives an intransitive verb whose
plural subject names the reciprocants, *Juma na Halima wa-li-tekeny-an-a* 'Juma and Halima tickled
each other'; with a singular subject and a comitative *na* phrase it forms the discontinuous
reciprocal, *Juma a-li-tekeny-an-a na Halima*, which Nordlinger reviews. The suffix is distinct
from the reflexive prefix *ji-*. In some verbs the suffix is lexicalized as part of the stem;
Palmieri's appendix of these is `Studies/Palmieri2024.lean`.

## Main definitions

* `Swahili.Reciprocals.anSuffix`, `markers`: the marker and the inventory

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
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

end Swahili.Reciprocals
