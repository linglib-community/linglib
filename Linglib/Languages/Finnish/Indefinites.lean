module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Finnish indefinite pronouns

Finnish has three main series of indefinite pronouns: the non-emphatic *-kin*-series, based on the
relative pronouns (*joku*), and two series derived from the interrogatives, the mainly negative
*-kaan*-series (*kukaan*) and the free-choice series with *hyvänsä* (*kuka hyvänsä*), which has the
equivalent *tahansa*. *Eräs* 'a certain' is counted a series of its own. The members are those of
Haspelmath's table, in their usual spelling where he hyphenates (*kuka-an*), with *mitenkään* for
his *miten-kaan*; his dual determiners (*jompikumpi*) are determiners here. *Kukaan* and *kuka
hyvänsä* are also `Finnish.PolarityItems.kukaan` and `Finnish.PolarityItems.kukaHyvänsä`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Finnish.Indefinites

/-- The determiner *eräs* 'a certain'. -/
def eräs : IndefinitePronoun := { form := "eräs", ontology := .determiner }

/-- *joku*, of the *-kin*-series, a compound of the roots *jo-* and *ku-* without the suffix. -/
def joku : IndefinitePronoun := { form := "joku", ontology := .person }

/-- *kukaan*, the interrogative *kuka* with *-kaan*. -/
def kukaan : IndefinitePronoun := { form := "kukaan", ontology := .person }

/-- *kuka hyvänsä*, the interrogative *kuka* with *hyvänsä*. -/
def kukaHyvänsä : IndefinitePronoun := { form := "kuka hyvänsä", ontology := .person }

/-! ### The series -/

/-- The series of *eräs*. -/
def eräsSeries : IndefinitePronoun.Series := ⟨"eräs", {eräs}⟩

/-- The *-kin*-series. -/
def kinSeries : IndefinitePronoun.Series :=
  ⟨"-kin", {joku, { form := "jokin", ontology := .thing },
    { form := "jotakin", ontology := .thing },
    { form := "jossakin", ontology := .place }, { form := "jolloinkin", ontology := .time },
    { form := "jotenkin", ontology := .manner }, { form := "jompikumpi", ontology := .determiner }}⟩

/-- The *-kaan*-series. -/
def kaanSeries : IndefinitePronoun.Series :=
  ⟨"-kaan", {kukaan, { form := "mikään", ontology := .thing },
    { form := "missään", ontology := .place },
    { form := "milloinkaan", ontology := .time }, { form := "mitenkään", ontology := .manner },
    { form := "kumpikaan", ontology := .determiner }}⟩

/-- The *hyvänsä*-series. -/
def hyvänsäSeries : IndefinitePronoun.Series :=
  ⟨"hyvänsä", {kukaHyvänsä, { form := "mikä hyvänsä", ontology := .thing },
    { form := "missä hyvänsä", ontology := .place },
    { form := "milloin hyvänsä", ontology := .time },
    { form := "miten hyvänsä", ontology := .manner },
    { form := "kumpi hyvänsä", ontology := .determiner }}⟩

end Finnish.Indefinites
