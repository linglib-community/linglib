module

public import Linglib.Languages.Latvian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Latvian indefinite pronouns

Latvian builds its three indefinite series on the interrogative pronouns: the general
*kaut*-series with the particle *kaut* 'at least, even' (*kaut kas* 'something'), the negative
*ne*-series with the prefix *ne-*, apparently that of verbal negation, with which the series
co-occurs (*Viņu nekas neinteresē* 'Nothing interests him'), and the free-choice *jeb*-series
with *jeb* 'or' (*jebkas* 'anything'). The person row departs from the pattern:
*neviens* 'nobody' is built on the numeral *viens* 'one' and *jebkāds* 'anybody' on the
determiner *kāds*, which is also used bare for 'somebody'. The manner row has no member of the
*jeb*-series in Haspelmath's table, and the determiner row of the *kaut*-series has
*kaut kurš* beside *kaut kāds* (Kalnača and Lokmane, §2.4.7).

## Implementation notes

Forms are orthographic: the prefixes are written together with the interrogative (*nekas*), *kaut*
apart from it (*kaut kas*), as Kalnača and Lokmane prescribe; Haspelmath hyphenates the prefixes
(*ne-kas*). A member is its series' marker applied to an interrogative of `Latvian.Pronouns`, which
derives its form and category. In the person row *kāds* and *jebkāds* take the person category over
the determiner they are built on, and *neviens*, built on no interrogative, is stated whole.

## References

* [haspelmath-1997]
* [kalnaca-lokmane-2021]
-/

@[expose] public section

namespace Latvian.Indefinites

/-! ### The markers -/

/-- The *kaut* marker puts the particle *kaut* before the interrogative. -/
def kaut : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("kaut " ++ ·)

/-- The *ne-* marker attaches the negative prefix *ne-* to the interrogative. -/
def ne : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("ne" ++ ·)

/-- The *jeb-* marker attaches the prefix *jeb-* to the interrogative. -/
def jeb : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("jeb" ++ ·)

/-! ### The person row -/

/-- *kaut kas* 'someone' is the *kaut*-member of *kas* 'who'. -/
def kautKas : IndefinitePronoun := kaut Pronouns.kasPerson

/-- *kāds* 'somebody' is the interrogative determiner used bare as a person indefinite. -/
def kāds : IndefinitePronoun :=
  { IndefinitePronoun.ofInterrogative id Pronouns.kāds with ontology := .person }

/-- *neviens* 'nobody' is *ne-* on the numeral *viens* 'one', in a series otherwise built on
the interrogatives ([haspelmath-1997], §7.5.2). -/
def neviens : IndefinitePronoun :=
  { form := "neviens", ontology := .person }

/-- *jebkāds* 'anybody' is the *jeb*-member of the determiner *kāds*, the person member of
[haspelmath-1997]'s table. [kalnaca-lokmane-2021] gloss *jebkāds* 'any, any kind' and
*jebkurš* 'any, anyone'. -/
def jebkāds : IndefinitePronoun := { jeb Pronouns.kāds with ontology := .person }

/-! ### The series -/

/-- The *kaut*-series. -/
def kautSeries : IndefinitePronoun.Series :=
  ⟨"kaut", {kautKas, kāds, kaut Pronouns.kasThing, kaut Pronouns.kur, kaut Pronouns.kad,
    kaut Pronouns.kā, kaut Pronouns.kāds, kaut Pronouns.kurš}⟩

/-- The *ne*-series. -/
def neSeries : IndefinitePronoun.Series :=
  ⟨"ne-", {neviens, ne Pronouns.kasThing, ne Pronouns.kur, ne Pronouns.kad, ne Pronouns.kā,
    ne Pronouns.kāds}⟩

/-- The *jeb*-series. -/
def jebSeries : IndefinitePronoun.Series :=
  ⟨"jeb-", {jebkāds, jeb Pronouns.kasThing, jeb Pronouns.kur, jeb Pronouns.kad, jeb Pronouns.kāds,
    jeb Pronouns.kurš}⟩

end Latvian.Indefinites
