module

public import Linglib.Languages.Slavic.Russian.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# Russian polarity items

This file gives the Russian indefinite polarity items, typed by `PolarityItem`, the person row
taking its forms from `Russian.Indefinites`, after
Haspelmath's map of the Russian series: the *-libo* series spans questions, conditionals,
comparatives and indirect negation; the *ni-*
series occupies direct negation as negative concord items, which co-occur with clausemate verbal
negation *ne*, as Zeijlstra and Giannakidou describe them; and *kto ugodno* is a free-choice
item.

## References

* [haspelmath-1997]
* [zeijlstra-2004]
* [giannakidou-1998]
-/

@[expose] public section

namespace Russian.PolarityItems

open PolarityItem

/-! ### The *-libo* series -/

/-- *kto-libo* (кто-либо) 'anyone', used in questions, conditionals, comparatives and under
indirect negation. -/
def ktoLibo : PolarityItem :=
  { form := Indefinites.ktoLibo.form }

/-! ### The *ni-* series -/

/-- *nikto* (никто) 'nobody', a negative concord item that requires clausemate negation, *nikto
ne prišël* 'nobody came'. -/
def nikto : PolarityItem :=
  { form := Indefinites.nikto.form }

/-- *ničego* (ничего) 'nothing', the non-human negative concord item, *ničego ne videl* '(he) saw
nothing'. -/
def nichego : PolarityItem :=
  { form := "ničego" }

/-- *nikogda* (никогда) 'never', the temporal negative concord item, *nikogda ne prixodil* '(he)
never came'. -/
def nikogda : PolarityItem :=
  { form := (Indefinites.ni Pronouns.kogda).form }

/-! ### Free choice -/

/-- *kto ugodno* (кто угодно) 'anyone at all', a free-choice item. -/
def ktoUgodno : PolarityItem :=
  { form := Indefinites.ktoUgodno.form
  , freeChoice := true }

/-! ### The entries -/

/-- The polarity items. -/
def items : List PolarityItem :=
  [ktoLibo, nikto, nichego, nikogda, ktoUgodno]

end Russian.PolarityItems
