module

public import Linglib.Fragments.Turkish.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Turkish indefinite pronouns

This file defines the Turkish indefinite series as Haspelmath tabulates them. All three are
built on generic nouns and the numeral *bir* 'one': the non-emphatic *bir*-series, *biri(si)*
'someone', *bir şey* 'something', *bir yerde* 'somewhere', *bir zaman* 'sometime', *bir şekilde*
'somehow' and the determiner *bir*; the negative *hiç*-series, which prefixes the Persian loan
*hiç* to a *bir*-member and has *hiçbiri* and *hiç kimse* for a person; and the free-choice
*herhangi*-series, which prefixes *herhangi*, from *her* 'every' and *hangi* 'which', to a
*bir*-member. The isolated *kimse* 'someone, anyone', from *kim* 'who' and the conditional
suffix, is used only non-specifically. The functions each series covers are the regions of
`Studies/Haspelmath1997.lean`.

## Main definitions

* `Turkish.Indefinites.bir`, `Turkish.Indefinites.birSeries`: the *bir*-series, a member of
  which is a generic noun with *bir*
* `Turkish.Indefinites.hiç`, `Turkish.Indefinites.herhangi`: the marked series, each a prefix
  on a member of the *bir*-series, with `hiçSeries` and `herhangiSeries`
* `Turkish.Indefinites.kimse`, `Turkish.Indefinites.hiçKimse`: the isolated indefinite and
  its negative

## Implementation notes

* The spacing is Haspelmath's, *hiçbiri* but *hiç bir şey*.

## References

* [M. Haspelmath, *Indefinite Pronouns* (1997)][haspelmath-1997]
-/

@[expose] public section

namespace Turkish.Indefinites

open ProForm (OntologicalCategory)

/-! ### The bir-series -/

/-- A member of the *bir*-series, a generic noun with *bir* 'one'. -/
def bir (form : String) (ontology : OntologicalCategory) : IndefinitePronoun :=
  { form, ontology }

/-- *biri(si)* 'someone'. -/
def biri : IndefinitePronoun := bir "biri" .person

/-- *bir şey* 'something'. -/
def birŞey : IndefinitePronoun := bir "bir şey" .thing

/-- *bir yerde* 'somewhere'. -/
def birYerde : IndefinitePronoun := bir "bir yerde" .place

/-- *bir zaman* 'sometime'. -/
def birZaman : IndefinitePronoun := bir "bir zaman" .time

/-- *bir şekilde* 'somehow'. -/
def birŞekilde : IndefinitePronoun := bir "bir şekilde" .manner

/-- The determiner *bir* 'some'. -/
def birDeterminer : IndefinitePronoun := bir "bir" .determiner

/-- The *bir*-series. -/
def birSeries : IndefinitePronoun.Series :=
  ⟨"bir-", {biri, birŞey, birYerde, birZaman, birŞekilde, birDeterminer}⟩

/-! ### The isolated indefinite -/

/-- *kimse* 'someone, anyone', used only non-specifically. -/
def kimse : IndefinitePronoun := { form := "kimse", ontology := .person }

/-! ### The hiç-series -/

/-- The *hiç*-series prefixes *hiç* to a member of the *bir*-series. -/
def hiç (p : IndefinitePronoun) : IndefinitePronoun := { p with form := "hiç " ++ p.form }

/-- *hiçbiri* 'nobody', written as one word. -/
def hiçbiri : IndefinitePronoun := { biri with form := "hiçbiri" }

/-- *hiç kimse* 'nobody', the negative of the isolated indefinite. -/
def hiçKimse : IndefinitePronoun := hiç kimse

/-- The *hiç*-series, with two person members. -/
def hiçSeries : IndefinitePronoun.Series :=
  ⟨"hiç", insert hiçbiri (insert hiçKimse ((birSeries.members.erase biri).image hiç))⟩

/-! ### The herhangi-series -/

/-- The *herhangi*-series prefixes *herhangi* to a member of the *bir*-series. -/
def herhangi (p : IndefinitePronoun) : IndefinitePronoun :=
  { p with form := "herhangi " ++ p.form }

/-- *herhangi biri* 'anyone'. -/
def herhangiBiri : IndefinitePronoun := herhangi biri

/-- The *herhangi*-series. -/
def herhangiSeries : IndefinitePronoun.Series := ⟨"herhangi", birSeries.members.image herhangi⟩

end Turkish.Indefinites
