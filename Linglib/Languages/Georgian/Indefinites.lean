module

public import Linglib.Languages.Georgian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Georgian indefinite pronouns

This file defines the five Georgian indefinite series, all built on the interrogatives of
`Georgian.Pronouns`. The specific *-γac*-series has *vi-γac* 'someone', the non-specific
*-me*-series *vin-me* 'anyone', and the three negative series *ara-vin*, *vera-vin* and
*nura-vin* 'nobody'. The negative prefixes come from the negators *ar*, *ver* and *nu*, and a
clause takes the series of its negator. A negative indefinite normally co-occurs with verbal
negation, which may be omitted; Haspelmath knows of no rule for the omission (§8.2.4). Free
choice has no series and is expressed by the adjective *nebismieri* 'arbitrary, any'.

## Main definitions

* `Georgian.Indefinites.γac`, `Georgian.Indefinites.me`: the markers of the two non-negative
  series.
* `Georgian.Indefinites.negative`: the marker of a negative series with a given prefix.
* `Georgian.Indefinites.γacSeries`, `meSeries`, `araSeries`, `veraSeries`, `nuraSeries`: the
  series.

## Implementation notes

Forms follow Haspelmath's transliteration and hyphenation, with *γ* where Hewitt writes *ġ*. A
member that departs from its interrogative, such as *vi-γac* or *ara-sodes* 'never', keeps the
interrogative's category under its own form. Haspelmath tabulates only the *ara*-series (A.34);
the *vera*- and *nura*-members are Hewitt's (§3.2.8, §3.5.4).

## References

* [haspelmath-1997]
* [hewitt-1995]
-/

@[expose] public section

namespace Georgian.Indefinites

open Pronouns

/-! ### The markers -/

/-- The *-γac*-series attaches the specific suffix *-γac* to the interrogative. -/
def γac : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-γac")

/-- The *-me*-series attaches the non-specific suffix *-me* to the interrogative. -/
def me : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-me")

/-- The negative series with prefix `neg` attaches `neg` to the interrogative; the prefix is
*ara* in the neutral series, *vera* in the potential and *nura* in the prohibitive. -/
def negative (neg : String) : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (neg ++ "-" ++ ·)

/-- The thing member of a negative series is built on *peri* in place of *ra*, as in *ara-peri*
'nothing'. -/
def peri (neg : String) : IndefinitePronoun := { negative neg ra with form := neg ++ "-peri" }

/-- The determiner member of a negative series is built on *vitari* in place of *romeli*, as in
*ara-vitari* 'no'. -/
def vitari (neg : String) : IndefinitePronoun :=
  { negative neg romeli with form := neg ++ "-vitari" }

/-! ### The person row -/

/-- *vi-γac* 'someone' is the *-γac*-member of *vin* 'who', built on its stem *vi-*. -/
def viγac : IndefinitePronoun := { γac vin with form := "vi-γac" }

/-- *vin-me* 'anyone' is the *-me*-member of *vin* 'who'. -/
def vinMe : IndefinitePronoun := me vin

/-- *ara-vin* 'nobody' is the neutral negative member of *vin* 'who'. -/
def araVin : IndefinitePronoun := negative "ara" vin

/-! ### The series -/

/-- The *-γac*-series has a member for each interrogative. -/
def γacSeries : IndefinitePronoun.Series :=
  ⟨"-γac", {viγac, γac ra, γac sad, γac rodis, γac rogor, γac romeli}⟩

/-- The *-me*-series has a member for each interrogative. -/
def meSeries : IndefinitePronoun.Series :=
  ⟨"-me", {vinMe, me ra, me sad, me rodis, me rogor, me romeli}⟩

/-- The *ara*-series has two thing members, *ara-peri* and the older *ara-ra*, and no manner
member; *ar-sad* 'nowhere' takes the short prefix and *ara-sodes* 'never' is built on *sodes*. -/
def araSeries : IndefinitePronoun.Series :=
  ⟨"ara-", {araVin, peri "ara", negative "ara" ra, negative "ar" sad,
    { negative "ara" rodis with form := "ara-sodes" }, vitari "ara"}⟩

/-- The potential series has the members *vera-vin* 'nobody', *vera-peri* 'nothing' and
*vera-vitari* 'no'. -/
def veraSeries : IndefinitePronoun.Series :=
  ⟨"vera-", {negative "vera" vin, peri "vera", vitari "vera"}⟩

/-- The prohibitive series has the members *nura-vin* 'nobody', *nura-peri* 'nothing' and
*nura-vitari* 'no'. -/
def nuraSeries : IndefinitePronoun.Series :=
  ⟨"nura-", {negative "nura" vin, peri "nura", vitari "nura"}⟩

end Georgian.Indefinites
