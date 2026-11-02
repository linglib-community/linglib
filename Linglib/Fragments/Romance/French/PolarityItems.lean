module

public import Linglib.Semantics.PolarityItem.Licensing

/-!
# French polarity items

The French negative words *personne* 'nobody', *rien* 'nothing', *jamais* 'never' and *plus* 'no
more', typed by `PolarityItem`. They go back to the noun *personne* 'person', the Latin noun *rem*
'thing', Latin *iam* 'already' + *magis* 'more', and the comparative *plus* 'more'
(Haspelmath A.9.2). The *personne*-series is used most often in direct negation with the
preverbal particle *ne*, as in *Je ne vois rien* 'I cannot see anything', and also under indirect
negation, *Je doute que personne y réussisse* 'I doubt that anybody will succeed in it', in
comparatives, and in rhetorical questions and conditionals, *si rien s'ébruite dans la presse*
'if anything transpires in the media' (Haspelmath A.9.3). French is a non-strict negative
concord language whose negator *ne* is optional before and after the negative word
(van der Auwera and Van Alsenoy (32)), so the negative words carry the weak licensor that
Spanish and Italian negative words carry. Clausal negation is in the sibling `Negation.lean`.

## References

* [haspelmath-1997]
* [van-der-auwera-van-alsenoy-2016]
-/

@[expose] public section

namespace French.PolarityItems

open PolarityItem

/-- *personne* 'nobody, anybody', as in *Personne n'a jamais dit rien* 'Nobody ever said
anything', *Je doute que personne y réussisse* ([haspelmath-1997] A68b, A69a). -/
def personne : PolarityItem :=
  { form := "personne"
  , licensor := some .weak
  , licensingContexts := [.negation, .doubtVerb] }

/-- *rien* 'nothing, anything', as in *Je ne vois rien*, under *personne* in *Personne n'a jamais
dit rien*, in a rhetorical question, *valait-il de lui rien sacrifier?* 'would it be worth
sacrificing anything for it?', and in a conditional ([haspelmath-1997] A68, A66b, A67a). -/
def rien : PolarityItem :=
  { form := "rien"
  , licensor := some .weak
  , licensingContexts := [.negation, .nobody, .question, .conditionalAntecedent] }

/-- *jamais* 'never, ever', under *personne* in *Personne n'a jamais dit rien*
([haspelmath-1997] A68b). -/
def jamais : PolarityItem :=
  { form := "jamais"
  , licensor := some .weak
  , licensingContexts := [.negation, .nobody] }

/-- *plus* 'no more, no longer', the comparative *plus* 'more' with *ne*. -/
def plus : PolarityItem :=
  { form := "plus"
  , licensor := some .weak
  , licensingContexts := [.negation] }

/-- The French polarity items. -/
def items : List PolarityItem :=
  [personne, rien, jamais, plus]

theorem french_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenser.Admits e := by
  decide

end French.PolarityItems
