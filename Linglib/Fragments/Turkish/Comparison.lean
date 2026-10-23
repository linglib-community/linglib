module

public import Linglib.Syntax.Comparative

/-!
# Turkish comparison

This file defines the Turkish comparative construction as Göksel and Kerslake describe it. The
standard of comparison takes the ablative and the adjective is preceded by the adverb *daha*
'more', which may be omitted when the ablative complement is present, *bu makine öbüründen
(daha) ucuz* 'this machine is cheaper than the other one'; the superlative is the adverb *en*
'most' before the adjective. Stassen's example is *sen gül-den güzel-sin* 'you are more
beautiful than a rose', with no *daha*, and the gerund in *-(y)ArAk* of the chains he holds the
comparative to be modelled on takes the same ablative, *ev-e gid-erek-ten* 'having gone
home'. The construction's type, read off its anatomy, is locational, and separative in
Stassen's finer typology.

## Main definitions

* `Turkish.Comparison.dan`: the comparative construction

## Main results

* `Turkish.Comparison.type_dan`: the construction is locational

## Implementation notes

* The superlative *en* is a free adverb that `SuperlativeStrategy` has no case for, so none is
  recorded.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [L. Stassen, *Comparison and Universal Grammar* (1985)][stassen-1985]
-/

@[expose] public section

namespace Turkish.Comparison

open Comparative

/-- The ablative comparative, whose standard takes *-DAn* and whose adjective is preceded by
the optional *daha* and carries no comparative morphology. -/
def dan : Comparative :=
  { standardMarker := [.suff "DAn"], caseAssignment := .fixed, fixedEncoding := some .adverbial,
    standardCase := some .abl, degreeMarkers := [.free "daha"] }

/-- The construction is locational. -/
theorem type_dan : dan.type = .locational := rfl

end Turkish.Comparison
