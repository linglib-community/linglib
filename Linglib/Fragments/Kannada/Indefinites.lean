module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Kannada indefinite pronouns

Kannada builds its indefinite pronouns by suffixing a particle to an interrogative pronoun, three
series on *yaaru* 'who': *yaar-oo* 'someone', with *-oo* 'or', for a referent the speaker
presupposes but cannot identify; *yaar-aadaruu* 'anyone', with *-aadaruu* 'even if it be', for
irrealis non-specific reference and in questions and conditionals; and *yaar-uu*, with *-uu* 'also,
even', under negation, in comparatives and for free choice. No series is used for a referent the
speaker has in mind. The members are those of Haspelmath's table, as he segments them; both the
masculine and the feminine determiner of the *-oo* series are entered, and the determiner of the
*-uu* series is cited with its noun as *X*, as he cites it.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

@[expose] public section

namespace Kannada.Indefinites

/-- *yaar-oo* 'someone'. -/
def yaarOo : IndefinitePronoun := { form := "yaar-oo", ontology := .person }

/-- *yaar-aadaruu* 'anyone'. -/
def yaarAadaruu : IndefinitePronoun := { form := "yaar-aadaruu", ontology := .person }

/-- *yaar-uu* 'anyone, no one'. -/
def yaarUu : IndefinitePronoun := { form := "yaar-uu", ontology := .person }

/-! ### The series -/

/-- The *-oo* series. -/
def ooSeries : IndefinitePronoun.Series :=
  ⟨"-oo", {yaarOo, { form := "een-oo", ontology := .thing },
    { form := "elliy-oo", ontology := .place },
    { form := "yaavaagal-oo", ontology := .time }, { form := "heeg-oo", ontology := .manner },
    { form := "eṣṭ-oo", ontology := .amount }, { form := "yaava-n-oo", ontology := .determiner },
    { form := "yaava-ḷ-oo", ontology := .determiner }}⟩

/-- The *-aadaruu* series. -/
def aadaruuSeries : IndefinitePronoun.Series :=
  ⟨"-aadaruu", {yaarAadaruu, { form := "een-aadaruu", ontology := .thing },
    { form := "elliy-aadaruu", ontology := .place },
    { form := "yaavaagal-aadaruu", ontology := .time },
    { form := "heeg-aadaruu", ontology := .manner }, { form := "eṣṭ-aadaruu", ontology := .amount },
    { form := "yaavanaadaruu", ontology := .determiner }}⟩

/-- The *-uu* series. -/
def uuSeries : IndefinitePronoun.Series :=
  ⟨"-uu", {yaarUu, { form := "een-uu", ontology := .thing },
    { form := "elliy-uu", ontology := .place },
    { form := "yaavaagal-uu", ontology := .time }, { form := "heeg-uu", ontology := .manner },
    { form := "eṣṭ-uu", ontology := .amount }, { form := "yaava X-uu", ontology := .determiner }}⟩

end Kannada.Indefinites
