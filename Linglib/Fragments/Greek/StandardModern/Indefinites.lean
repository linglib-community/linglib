module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Greek indefinite pronouns

Modern Greek has three main series of indefinite pronouns: the specific *ka*-series (*kapjos*),
built on the interrogatives; the non-specific *tipota*-series (*kanenas*, *tipota*), formally
heterogeneous; and the free-choice series in *-dhipote* (*opjosdhipote*), built on the relatives.
The members are those of Haspelmath's table, which parenthesizes *me kanenan tropo* 'in any way'
as no member of the *tipota*-series. The *tipota*-series serves questions, conditionals,
imperatives and complements of *want*, and both functions of negation, where it co-occurs with
verbal negation. Under emphatic accent its members are the n-words of
`Greek.StandardModern.PolarityItems`.

## Implementation notes

* Forms are romanized without stress, as elsewhere in the fragment, so *pote* 'ever' of the
  *tipota*-series is written as the interrogative *póte* 'when' is.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Greek.StandardModern.Indefinites

/-- *kapjos* 'someone', the interrogative *pjos* 'who' with *ka-*. -/
def kapjos : IndefinitePronoun := { form := "kapjos", ontology := .person }

/-- *kati* 'something', the interrogative *ti* 'what' with *ka-*. -/
def kati : IndefinitePronoun := { form := "kati", ontology := .thing }

/-- *kanenas* 'anyone', from *kan* 'even' and *enas* 'one'. -/
def kanenas : IndefinitePronoun := { form := "kanenas", ontology := .person }

/-- *tipota* 'anything', built on *ti* 'what'. -/
def tipota : IndefinitePronoun := { form := "tipota", ontology := .thing }

/-- *opjosdhipote* 'anyone', the relative *opjos* with *-dhipote*. -/
def opjosdhipote : IndefinitePronoun := { form := "opjosdhipote", ontology := .person }

/-! ### The series -/

/-- The *ka*-series. -/
def kaSeries : IndefinitePronoun.Series :=
  ⟨"ka-", {kapjos, kati, ⟨{ form := "kapu" }, .place⟩, ⟨{ form := "kapote" }, .time⟩,
    ⟨{ form := "kapos" }, .manner⟩}⟩

/-- The *tipota*-series, which has two forms for a person and none for a manner. -/
def tipotaSeries : IndefinitePronoun.Series :=
  ⟨"tipota", {kanenas, ⟨{ form := "kanis" }, .person⟩, tipota, ⟨{ form := "puthena" }, .place⟩,
    ⟨{ form := "pote" }, .time⟩}⟩

/-- The *-dhipote* series, which has no member for a manner. -/
def dhipoteSeries : IndefinitePronoun.Series :=
  ⟨"-dhipote", {opjosdhipote, ⟨{ form := "otidhipote" }, .thing⟩,
    ⟨{ form := "opudhipote" }, .place⟩, ⟨{ form := "opotedhipote" }, .time⟩}⟩

end Greek.StandardModern.Indefinites
