module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Hindi-Urdu indefinite pronouns

Hindi-Urdu has two major series of indefinite pronouns: the *koii*-series (*koii* 'someone', *kuch*
'something'), morphologically similar to the interrogatives but not synchronically derivable from
them, and the *bhii*-series derived from it with the focus particle *bhii* 'also, even' (*koii bhii*
'anyone'). The members are those of Haspelmath's table.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace HindiUrdu.Indefinites

/-- *koii* 'someone'. -/
def koii : IndefinitePronoun := { form := "koii", ontology := .person }

/-- *kuch* 'something'. -/
def kuch : IndefinitePronoun := { form := "kuch", ontology := .thing }

/-- *kabhii*, of the time category. -/
def kabhii : IndefinitePronoun := { form := "kabhii", ontology := .time }

/-- The *bhii*-series follows a member of the *koii*-series with *bhii*. -/
def bhii (p : IndefinitePronoun) : IndefinitePronoun := { p with form := p.form ++ " bhii" }

/-- *koii bhii* 'anyone'. -/
def koiiBhii : IndefinitePronoun := bhii koii

/-! ### The series -/

/-- The *koii*-series. -/
def koiiSeries : IndefinitePronoun.Series :=
  ⟨"koii", {koii, kuch, { form := "kahĩ", ontology := .place }, kabhii}⟩

/-- The *bhii*-series. -/
def bhiiSeries : IndefinitePronoun.Series := ⟨"bhii", koiiSeries.members.image bhii⟩

end HindiUrdu.Indefinites
