module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# French indefinite pronouns

French has five major series of indefinite pronouns. These are the non-emphatic *quelque*-series,
as in *quelqu'un*, the negative polarity series of *personne*, the free-choice series with
*n'importe*, as in *n'importe qui*, and the two emphatic series with *que ce soit*, as in *qui que
ce soit*, and with *-conque*, as in *quiconque*. The members are those of Haspelmath's table,
written in their usual spelling where he hyphenates (*qui-conque*). The forms that the table
parenthesizes, *en quelque temps* and *en quelque sorte*, are left out. The *n'importe*- and
*que ce soit*-series, which Haspelmath derives regularly from the interrogatives, have the members
he prints. The negative words are also typed as polarity items, as `French.PolarityItems.personne`,
`French.PolarityItems.rien`, and `French.PolarityItems.jamais`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace French.Indefinites

/-- *quelqu'un* 'someone', a member of the *quelque*-series. -/
def quelquUn : IndefinitePronoun := { form := "quelqu'un", ontology := .person }

/-- *personne* 'nobody, anybody', from the noun *personne* 'person'. -/
def personne : IndefinitePronoun := { form := "personne", ontology := .person }

/-- *rien* 'nothing, anything', from Latin *rem* 'thing'. -/
def rien : IndefinitePronoun := { form := "rien", ontology := .thing }

/-- *jamais* 'never, ever', from Latin *iam* 'already' together with *magis* 'more'. -/
def jamais : IndefinitePronoun := { form := "jamais", ontology := .time }

/-- *n'importe qui* 'anyone at all', which is the interrogative *qui* with *n'importe* 'it does
not matter'. -/
def nImporteQui : IndefinitePronoun := { form := "n'importe qui", ontology := .person }

/-- *qui que ce soit* 'anyone', which is the interrogative *qui* with *que ce soit* 'that it
be'. -/
def quiQueCeSoit : IndefinitePronoun := { form := "qui que ce soit", ontology := .person }

/-- *quiconque* 'anyone', which is the interrogative *qui* with *-conque*. -/
def quiconque : IndefinitePronoun := { form := "quiconque", ontology := .person }

/-! ### The series -/

/-- The *quelque*-series. -/
def quelqueSeries : IndefinitePronoun.Series :=
  ⟨"quelque-", {quelquUn, { form := "quelque chose", ontology := .thing },
    { form := "quelque part", ontology := .place }, { form := "quelque", ontology := .determiner }}⟩

/-- The *personne*-series. -/
def personneSeries : IndefinitePronoun.Series :=
  ⟨"personne", {personne, rien, { form := "nulle part", ontology := .place }, jamais,
    { form := "aucunement", ontology := .manner }, { form := "aucun", ontology := .determiner }}⟩

/-- The *n'importe*-series. -/
def nImporteSeries : IndefinitePronoun.Series :=
  ⟨"n'importe", {nImporteQui, { form := "n'importe quoi", ontology := .thing },
    { form := "n'importe quel", ontology := .determiner }}⟩

/-- The *que ce soit*-series, whose determiner is the discontinuous *quelque … que ce soit*. -/
def queCeSoitSeries : IndefinitePronoun.Series :=
  ⟨"que ce soit", {quiQueCeSoit, { form := "quoi que ce soit", ontology := .thing },
    { form := "quelque … que ce soit", ontology := .determiner }}⟩

/-- The *-conque*-series. -/
def conqueSeries : IndefinitePronoun.Series :=
  ⟨"-conque", {quiconque, { form := "quelconque", ontology := .determiner }}⟩

end French.Indefinites
