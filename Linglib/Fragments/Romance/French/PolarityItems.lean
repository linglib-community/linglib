module

public import Linglib.Fragments.Romance.French.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# French polarity items

This file types the French negative words *personne* 'nobody', *rien* 'nothing', *jamais*
'never', and *plus* 'no more' as values of `PolarityItem`. They derive from the noun *personne*
'person', the Latin noun *rem* 'thing', Latin *iam* 'already' together with *magis* 'more', and
the comparative *plus* 'more'. The first three are members of the *personne*-series of
`French.Indefinites`. That series is used most often in direct negation with the preverbal
particle *ne*, as in *Je ne vois rien* 'I cannot see anything', and it is also used under indirect
negation, in comparatives, and in rhetorical questions and conditionals. French is a non-strict
negative concord language, and its negator *ne* is optional both before and after the negative
word, as van der Auwera and Van Alsenoy describe. The negative words therefore carry the weak
licensor that Spanish and Italian negative words carry. Clausal negation is treated in the sibling
file `Negation.lean`.

## References

* [haspelmath-1997]
* [van-der-auwera-van-alsenoy-2016]
-/

@[expose] public section

namespace French.PolarityItems

open PolarityItem

/-- *personne* 'nobody, anybody', a member of the *personne*-series of [haspelmath-1997]. -/
def personne : PolarityItem :=
  { form := Indefinites.personne.form
  , licensor := some .weak }

/-- *rien* 'nothing, anything', a member of the *personne*-series of [haspelmath-1997]. -/
def rien : PolarityItem :=
  { form := Indefinites.rien.form
  , licensor := some .weak }

/-- *jamais* 'never, ever', a member of the *personne*-series of [haspelmath-1997]. -/
def jamais : PolarityItem :=
  { form := Indefinites.jamais.form
  , licensor := some .weak }

/-- *plus* 'no more, no longer', which is the comparative *plus* 'more' with *ne*. -/
def plus : PolarityItem :=
  { form := "plus"
  , licensor := some .weak }

end French.PolarityItems
