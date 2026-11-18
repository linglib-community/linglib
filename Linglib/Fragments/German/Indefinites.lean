module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# German indefinite pronouns

German has indefinite pronouns of two morphological kinds. *Jemand* 'someone', *etwas* 'something'
and negative *niemand*, *nichts* are built on generic nouns (*jemand* from *je-man* 'ever-person');
the *irgend-* series, *irgendwer*, *irgendwas*, temporal *je* 'ever' and *jeder* 'any, every' are
built with dedicated markers. *Jemand* runs from the specific functions to indirect negation.
*Irgend-* is excluded where the speaker has the referent in mind and under direct negation and
covers the rest of the map, a distribution it reached from an earlier non-specific use, as Aloni and
Port describe; the two series overlap from specific unknown to indirect negation. The determiner
*irgendein* is `German.PolarityItems.irgendein`. The members are those of Haspelmath's table, in
their usual spelling where he hyphenates (*irgend-wer*), and the series are named as he names them.
He parenthesizes the determiner *ein* of the *etwas-* series and *auf keine Weise* of the *n-*
series as no members of them, and counts *je* and *jeder* in no series, though his figure draws a
region for each.

## References

* [aloni-port-2015]
* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

namespace German.Indefinites

/-- *jemand* 'someone', of the *etwas-* series. -/
def jemand : IndefinitePronoun := { form := "jemand", ontology := .person }

/-- *irgendwer*, of the *irgend-* series. -/
def irgendwer : IndefinitePronoun := { form := "irgendwer", ontology := .person }

/-- Temporal *je* 'ever'. -/
def je : IndefinitePronoun := { form := "je", ontology := .time }

/-- The determiner *jeder* 'any, every'. -/
def jeder : IndefinitePronoun := { form := "jeder", ontology := .determiner }

/-- *niemand* 'nobody', of the *n-* series. -/
def niemand : IndefinitePronoun := { form := "niemand", ontology := .person }

/-! ### The series -/

/-- The series of *jemand* and *etwas*, which Haspelmath names the *etwas-* series. -/
def etwasSeries : IndefinitePronoun.Series := ⟨"etwas-", {jemand,
    { form := "etwas", ontology := .thing }}⟩

/-- The *irgend-* series. -/
def irgendSeries : IndefinitePronoun.Series :=
  ⟨"irgend-", {irgendwer, { form := "irgendjemand", ontology := .person },
    { form := "irgendwas", ontology := .thing },
    { form := "irgendetwas", ontology := .thing }, { form := "irgendwo", ontology := .place },
    { form := "irgendwann", ontology := .time }, { form := "irgendwie", ontology := .manner },
    { form := "irgendein", ontology := .determiner },
    { form := "irgendwelche", ontology := .determiner }}⟩

/-- The series of temporal *je*. -/
def jeSeries : IndefinitePronoun.Series := ⟨"je", {je}⟩

/-- The series of *jeder*. -/
def jederSeries : IndefinitePronoun.Series := ⟨"jeder", {jeder}⟩

/-- The negative *n-* series. -/
def nSeries : IndefinitePronoun.Series :=
  ⟨"n-", {niemand, { form := "nichts", ontology := .thing },
    { form := "nirgends", ontology := .place },
    { form := "nie", ontology := .time }, { form := "kein", ontology := .determiner }}⟩

end German.Indefinites
