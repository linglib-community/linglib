module

public import Linglib.Languages.Slavic.Russian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Russian indefinite pronouns

Russian builds its indefinite series on the interrogative pronouns *kto* 'who' and *čto* 'what' of
`Russian.Pronouns`: a marker maps each interrogative to an indefinite, and a series collects the
indefinites one marker builds. A series marks the interrogative with a prefix, *koe-* or *ni-*, with
a suffix, *-to*, *-nibud'* or *-libo*, or with a following phrase, *by to ni bylo* or *ugodno*. The
free-choice determiner *ljuboj* 'any' forms a series of its own. The members are those of
Haspelmath's table, which omits the *by to ni bylo* and *ugodno* series; these are entered with
their person and thing members.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Russian.Indefinites

open Pronouns

/-! ### The markers -/

/-- The *koe-* marker attaches the prefix *koe-* to the interrogative. -/
def koe : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("koe-" ++ ·)

/-- The *-to* marker attaches the suffix *-to* to the interrogative. -/
def to_ : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-to")

/-- The *-nibud'* marker attaches the suffix *-nibud'* to the interrogative. -/
def nibud : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-nibud'")

/-- The *-libo* marker attaches the suffix *-libo* to the interrogative. -/
def libo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-libo")

/-- The *by to ni bylo* marker follows the interrogative with *by to ni bylo*. -/
def byToNiBylo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " by to ni bylo")

/-- The negative marker attaches the prefix *ni-* to the interrogative. -/
def ni : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("ni" ++ ·)

/-- The *ugodno* marker follows the interrogative with *ugodno* 'pleasing'. -/
def ugodno : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " ugodno")

/-! ### The person row -/

/-- *koe-kto* 'someone'. -/
def koeKto : IndefinitePronoun := koe kto

/-- *kto-to* 'someone'. -/
def ktoTo : IndefinitePronoun := to_ kto

/-- *kto-nibud'* 'someone, anyone'. -/
def ktoNibud : IndefinitePronoun := nibud kto

/-- *kto-libo* 'anyone'. -/
def ktoLibo : IndefinitePronoun := libo kto

/-- *kto by to ni bylo* 'anyone at all'. -/
def ktoByToNiBylo : IndefinitePronoun := byToNiBylo kto

/-- *nikto* 'nobody'. -/
def nikto : IndefinitePronoun := ni kto

/-- *kto ugodno* 'anyone'. -/
def ktoUgodno : IndefinitePronoun := ugodno kto

/-- *ljuboj* 'any', a free-choice determiner. -/
def ljuboj : IndefinitePronoun := { form := "ljuboj", ontology := .determiner }

/-! ### The series -/

/-- The *koe-* series, which has no member for an amount. -/
def koeSeries : IndefinitePronoun.Series := ⟨"koe-", (interrogatives.erase skol'ko).image koe⟩

/-- The *-to* series. -/
def toSeries : IndefinitePronoun.Series := ⟨"-to", interrogatives.image to_⟩

/-- The *-nibud'* series. -/
def nibudSeries : IndefinitePronoun.Series := ⟨"-nibud'", interrogatives.image nibud⟩

/-- The *-libo* series, which has no member for an amount. -/
def liboSeries : IndefinitePronoun.Series := ⟨"-libo", (interrogatives.erase skol'ko).image libo⟩

/-- The *by to ni bylo* series, entered with its person and thing members. -/
def byToNiByloSeries : IndefinitePronoun.Series :=
  ⟨"by to ni bylo", ({kto, čto} : Finset _).image byToNiBylo⟩

/-- The negative series. -/
def niSeries : IndefinitePronoun.Series := ⟨"ni-", interrogatives.image ni⟩

/-- The *ugodno* series, entered with its person and thing members. -/
def ugodnoSeries : IndefinitePronoun.Series := ⟨"ugodno", ({kto, čto} : Finset _).image ugodno⟩

/-- The series of the determiner *ljuboj*. -/
def ljubojSeries : IndefinitePronoun.Series := ⟨"ljuboj", {ljuboj}⟩

end Russian.Indefinites
