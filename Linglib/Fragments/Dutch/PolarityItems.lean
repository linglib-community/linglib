module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# Dutch polarity items

This file types the polarity items of Dutch as values of `PolarityItem`. *Pas* 'only then' is a
positive polarity item that serves as the punctual *until* and does not combine with negation, as
Giannakidou shows. Karttunen discusses the parallel German *erst*. *Ooit* 'ever' is
*bipolar*, as van der Wouden shows, since it is a weak negative polarity item and a weak positive
polarity item at once. `Studies/VanDerWouden1997.lean` checks the entry against his examples.
*Hoeven* 'need' and *kunnen velen* 'can abide' are weak negative polarity items in the same
classification, and *hoeven* is subject to further restrictions. *Ook maar iets* 'anything at all'
and *bijster* 'very' are strong negative polarity items, which require an anti-additive context,
as Zwarts shows. `Studies/Zwarts1998.lean` checks these four items against his examples.

## References

* [giannakidou-2002]
* [karttunen-1974]
* [vanderwouden-1997]
* [zwarts-1998]
-/

@[expose] public section

namespace Dutch.PolarityItems

open PolarityItem

/-- *pas*, the punctual *until* of a positive clause, as in *Marie kwam pas om 9 uur aan* 'Marie
only arrived at nine' ([giannakidou-2002]'s (47)). -/
def pas : PolarityItem :=
  { form := "pas"
  , antiLicensor := some .antiMorphic }

/-- *ooit* 'ever', a weak negative polarity item that is also a weak positive polarity item
([vanderwouden-1997]). -/
def ooit : PolarityItem :=
  { form := "ooit"
  , licensor := some .weak
  , antiLicensor := some .antiMorphic }

/-- *hoeven* 'need', a weak negative polarity item. It is acceptable under monotone decreasing
operators, anti-additive noun phrases, comparatives, superlatives, and *before*, but unacceptable
in questions, in conditionals, and in the restrictors of *alle* 'all' and *geen* 'no'
([vanderwouden-1997]'s table (235)). It is also acceptable under a negated *geloven* 'believe',
his (234c). -/
def hoeven : PolarityItem :=
  { form := "hoeven"
  , licensor := some .weak }

/-- *kunnen velen* 'can abide', a weak negative polarity item ([zwarts-1998]). -/
def kunnenVelen : PolarityItem :=
  { form := "kunnen velen"
  , licensor := some .weak }

/-- *ook maar iets* 'anything at all', a strong negative polarity item, which requires an
anti-additive context ([zwarts-1998]). -/
def ookMaarIets : PolarityItem :=
  { form := "ook maar iets"
  , licensor := some .antiAdditive }

/-- *bijster* 'very', a strong negative polarity item ([zwarts-1998]). -/
def bijster : PolarityItem :=
  { form := "bijster"
  , licensor := some .antiAdditive }

end Dutch.PolarityItems
