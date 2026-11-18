module

public import Linglib.Fragments.Swahili.Nouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Swahili indefinite pronouns

Swahili has two major series of indefinite pronouns: generic nouns used as indefinites, as *mtu*
'person', and the free-choice and negative *CL-o CL-ote*, a noun with its gender prefix on *-o* and
on *-ote*, as in *mtu ye yote*. Haspelmath counts the generic nouns as a series for comparability,
though they may not be grammaticalized as pronouns. The members are those of Haspelmath's table,
without the determiner of the *CL-o CL-ote* series, which it gives only as the schema.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Swahili.Indefinites

/-- The generic noun *mtu* 'person' used as an indefinite. -/
def mtu : IndefinitePronoun := { form := Swahili.mtu.form, ontology := .person }

/-- *mtu ye yote*, *mtu* with *ye* and *yote*, its gender's forms of *-o* and *-ote*. -/
def mtuYeYote : IndefinitePronoun := { mtu with form := mtu.form ++ " ye yote" }

/-! ### The series -/

/-- The generic nouns used as indefinites. -/
def genericNounSeries : IndefinitePronoun.Series :=
  ⟨"generic noun", {mtu, { form := "neno", ontology := .thing },
    { form := "kitu", ontology := .thing },
    { form := "mahali", ontology := .place }, { form := "wakati", ontology := .time },
    { form := "-moja", ontology := .determiner }}⟩

/-- The *CL-o CL-ote* series. -/
def oOteSeries : IndefinitePronoun.Series :=
  ⟨"CL-o CL-ote", {mtuYeYote, { form := "kitu cho chote", ontology := .thing },
    { form := "neno lo lote", ontology := .thing },
    { form := "mahali po pote", ontology := .place },
    { form := "wakati wo wote", ontology := .time },
    { form := "kwa njia yo yote", ontology := .manner },
    { form := "vyo vyote", ontology := .manner }}⟩

end Swahili.Indefinites
