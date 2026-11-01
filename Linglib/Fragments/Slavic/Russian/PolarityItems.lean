module

public import Linglib.Fragments.Slavic.Russian.Indefinites
public import Linglib.Semantics.PolarityItem.Licensing

/-!
# Russian polarity items

This file gives the Russian indefinite polarity items, typed by `PolarityItem`, the person row
taking its forms from `Russian.Indefinites`, after
Haspelmath's map of the Russian series: the *-libo* series spans the functions of a weak
negative polarity item, questions, conditionals, comparatives and indirect negation; the *ni-*
series occupies direct negation as negative concord items, which co-occur with clausemate verbal
negation *ne*, as Zeijlstra and Giannakidou describe them; and *kto ugodno* is a free-choice
item.

The concord items carry `licensor := some .antiMorphic`, so a context licenses them exactly when
its licenser is anti-morphic, which among the named contexts is clausemate *ne* alone
(`niSeries_licensing_characterized`).

## References

* [haspelmath-1997]
* [zeijlstra-2004]
* [giannakidou-1998]
-/

@[expose] public section

namespace Russian.PolarityItems

open PolarityItem

/-! ### The *-libo* series -/

/-- *kto-libo* (кто-либо) 'anyone', a weak negative polarity item, licensed in questions,
conditionals, comparatives and under indirect negation. -/
def ktoLibo : PolarityItem :=
  { form := Indefinites.ktoLibo.form
  , licensor := some .weak
  , licensingContexts := [.question, .conditionalAntecedent, .negation, .clausalComparative] }

/-! ### The *ni-* series -/

/-- *nikto* (никто) 'nobody', a negative concord item that requires clausemate negation, *nikto
ne prišël* 'nobody came'. -/
def nikto : PolarityItem :=
  { form := Indefinites.nikto.form
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *ničego* (ничего) 'nothing', the non-human negative concord item, *ničego ne videl* '(he) saw
nothing'. -/
def nichego : PolarityItem :=
  { form := "ničego"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nikogda* (никогда) 'never', the temporal negative concord item, *nikogda ne prixodil* '(he)
never came'. -/
def nikogda : PolarityItem :=
  { form := (Indefinites.ni Pronouns.kogda).form
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-! ### Free choice -/

/-- *kto ugodno* (кто угодно) 'anyone at all', a free-choice item. -/
def ktoUgodno : PolarityItem :=
  { form := Indefinites.ktoUgodno.form
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### The entries -/

/-- The polarity items. -/
def items : List PolarityItem :=
  [ktoLibo, nikto, nichego, nikogda, ktoUgodno]

/-! ### Verification -/

theorem niSeries_licensing_characterized :
    ∀ e ∈ [nikto, nichego, nikogda], ∀ c : LicensingContext,
      c.licenser.Licenses e ↔ c.licenser.Carries .antiMorphic := by
  intro e he c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;>
    exact Licenser.licenses_iff_carries rfl (by decide) (by decide)

theorem russian_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenser.Admits e := by
  decide

end Russian.PolarityItems
