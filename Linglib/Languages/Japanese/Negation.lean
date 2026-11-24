module

public import Linglib.Syntax.Negation

/-!
# Japanese negation

Japanese negates a plain verb with the suffix *-na-* on its stem, and the negative inflects as an
adjective: *tabe-ru* 'eats' has the negative *tabe-na-i* and *tabe-ta* 'ate' the negative
*tabe-na-katta*, with the adjectival endings *-i* and *-katta*, not the verbal *-ru* and *-ta*. In
the polite style the negative *-en* stands in place of the nonpast ending, *tabe-mas-u* and
*tabe-mas-en*, and the past negative adds the past of the polite copula, *tabe-mas-en deshita*
beside *tabe-mashi-ta*, where *-mashi-* is the form of *-mas-* before *-ta*. A plain verb thus
becomes an adjective under negation, the adjectival tense endings replacing the verbal ones, while
each affirmative form keeps its own negative. Miestamo's examples, from Hinds's grammar, are rows of
`Data.Examples.Miestamo2005`.

## Main definitions

* `Japanese.Negation.na`, `Japanese.Negation.en`: the plain and the polite negative suffix
* `Japanese.Negation.adjectivalEndings`: the adjectival tense endings

## References

* [miestamo-2005]
* [hinds-1988]
-/

@[expose] public section

open Negation

namespace Japanese.Negation

open Morphology (Morph)

/-- The plain negative suffix *-na-*, inflected as an adjective. -/
def na : Marker := { pieces := [[.suff "na"]] }

/-- The polite negative suffix *-en*. -/
def en : Marker := { pieces := [[.suff "en"]] }

/-- The adjectival tense endings, the non-past *-i* and the past *-katta*. -/
def adjectivalEndings : List Morph := [.suff "i", .suff "katta"]

/-- The standard negators. -/
def standard : List Marker := [na, en]

end Japanese.Negation
