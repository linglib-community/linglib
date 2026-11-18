module

public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Mandarin.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Mandarin indefinite pronouns

Mandarin uses its bare interrogatives, the quexistentials of `Mandarin.Pronouns`, as indefinites,
as *shéi* 'who' for 'someone, anyone', and
derives two series from them with *dōu* and *yě* 'even, also; every, all', *shéi dōu* and *shéi yě*.
Generic nouns such as *rén* 'person' are also used as indefinites, and the determiner *rènhé* 'any'
can be counted a series of its own. The members are those of Haspelmath's table, the bare
interrogatives being its interrogative column, and the generic-noun series is entered with *rén*,
the one generic noun he names; the series are named as he names them.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Mandarin.Indefinites

/-- The generic noun *rén* 'person' used as an indefinite. -/
def ren : IndefinitePronoun :=
  { form := Nouns.ren.form, script := some Nouns.ren.hanzi, ontology := .person }

/-- Bare *shéi* 'who' used as an indefinite. -/
def shei : IndefinitePronoun := ⟨Pronouns.shei⟩

/-- Bare *shénme* 'what' used as an indefinite. -/
def shenme : IndefinitePronoun := ⟨Pronouns.shenme⟩

/-- *shéi dōu*, the interrogative with *dōu*. -/
def sheiDou : IndefinitePronoun := { form := "shéi dōu", script := some "谁都", ontology := .person }

/-- *shéi yě*, the interrogative with *yě*. -/
def sheiYe : IndefinitePronoun := { form := "shéi yě", script := some "谁也", ontology := .person }

/-- The determiner *rènhé* 'any'. -/
def renhe : IndefinitePronoun := { form := "rènhé", script := some "任何", ontology := .determiner }

/-! ### The series -/

/-- The generic nouns used as indefinites. -/
def genericNounSeries : IndefinitePronoun.Series := ⟨"generic noun", {ren}⟩

/-- The bare interrogatives used as indefinites. -/
def interrogativeSeries : IndefinitePronoun.Series :=
  ⟨"bare interrogative", Pronouns.quexistentials.image (⟨·⟩)⟩

/-- The *dōu* series. -/
def douSeries : IndefinitePronoun.Series :=
  ⟨"dōu", {sheiDou, { form := "shénme dōu", ontology := .thing },
    { form := "shénme dìfang dōu", ontology := .place },
    { form := "něi … dōu", ontology := .determiner }}⟩

/-- The *yě* series. -/
def yeSeries : IndefinitePronoun.Series :=
  ⟨"yě", {sheiYe, { form := "shénme yě", ontology := .thing },
    { form := "shénme dìfang yě", ontology := .place }}⟩

/-- The series of the determiner *rènhé*. -/
def renheSeries : IndefinitePronoun.Series := ⟨"rènhé", {renhe}⟩

end Mandarin.Indefinites
