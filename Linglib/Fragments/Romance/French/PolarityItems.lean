module

public import Linglib.Fragments.Romance.French.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# French polarity items

The French negative words *personne* 'nobody', *rien* 'nothing', *jamais* 'never' and *plus* 'no
more', typed by `PolarityItem`. They go back to the noun *personne* 'person', the Latin noun *rem*
'thing', Latin *iam* 'already' + *magis* 'more', and the comparative *plus* 'more'. The first three
are members of the *personne*-series of `French.Indefinites`, which is used most often in direct
negation with the preverbal particle *ne*, as in *Je ne vois rien* 'I cannot see anything', and
also under indirect negation, in comparatives, and in rhetorical questions and conditionals.
French is a non-strict negative concord language whose negator *ne* is optional before and after
the negative word (van der Auwera and Van Alsenoy), so the negative words carry the weak licensor
that Spanish and Italian negative words carry. Clausal negation is in the sibling `Negation.lean`.

## References

* [haspelmath-1997]
* [van-der-auwera-van-alsenoy-2016]
-/

@[expose] public section

namespace French.PolarityItems

open PolarityItem

/-- *personne* 'nobody, anybody', of the *personne*-series of [haspelmath-1997]. -/
def personne : PolarityItem :=
  { form := Indefinites.personne.form
  , licensor := some .weak }

/-- *rien* 'nothing, anything', of the *personne*-series of [haspelmath-1997]. -/
def rien : PolarityItem :=
  { form := Indefinites.rien.form
  , licensor := some .weak }

/-- *jamais* 'never, ever', of the *personne*-series of [haspelmath-1997]. -/
def jamais : PolarityItem :=
  { form := Indefinites.jamais.form
  , licensor := some .weak }

/-- *plus* 'no more, no longer', the comparative *plus* 'more' with *ne*. -/
def plus : PolarityItem :=
  { form := "plus"
  , licensor := some .weak }

end French.PolarityItems
