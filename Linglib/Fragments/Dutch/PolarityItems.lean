module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# Dutch polarity items

Polarity items of Dutch typed by `PolarityItem`: *pas* 'only then', the positive polarity item
that serves as the punctual *until* and does not combine with negation ([giannakidou-2002], the
paper's (47); [karttunen-1974] on the parallel German *erst*), *ooit* 'ever', which
[vanderwouden-1997] shows to be bipolar, a weak negative and a weak positive polarity item at once;
`Studies/VanDerWouden1997.lean` checks the entry against his examples; and *hoeven* 'need', a weak
negative polarity item in the same classification, with further restrictions.

## References

* [giannakidou-2002]
* [karttunen-1974]
* [vanderwouden-1997]
-/

@[expose] public section

namespace Dutch.PolarityItems

open PolarityItem

/-- *pas*, the punctual *until* of a positive clause, *Marie kwam pas om 9 uur aan* 'Marie only
arrived at nine'. -/
def pas : PolarityItem :=
  { form := "pas"
  , antiLicensor := some .antiMorphic }

/-- *ooit* 'ever', a weak negative polarity item that is also a weak positive polarity item
([vanderwouden-1997]). -/
def ooit : PolarityItem :=
  { form := "ooit"
  , licensor := some .weak
  , antiLicensor := some .antiMorphic }

/-- *hoeven* 'need', a weak negative polarity item, fine under monotone decreasing operators,
anti-additive noun phrases, comparatives, superlatives and *before*, but out in questions, in
conditionals and in the restrictors of *alle* 'all' and *geen* 'no' ([vanderwouden-1997]'s table
(235)); fine too under a negated *geloven* 'believe', (234c). -/
def hoeven : PolarityItem :=
  { form := "hoeven"
  , licensor := some .weak
  , licensingContexts :=
      [.negation, .few, .nobody, .clausalComparative, .superlative, .beforeClause,
        .superordinateNegation]
  , excludedContexts := [.question, .conditionalAntecedent, .universalRestrictor, .noRestrictor] }

end Dutch.PolarityItems
