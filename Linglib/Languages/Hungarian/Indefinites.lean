module

public import Linglib.Languages.Hungarian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Hungarian indefinite pronouns

This file defines the Hungarian indefinite series, all built on the interrogatives of
`Hungarian.Pronouns`. The general *vala*-series has *valaki* 'someone', the negative
*sem*-series *senki* 'nobody', the free-choice *akár*- and *bár*-series *akárki* and *bárki*
'anyone', and the marginal *né*-series *néhány* 'some, a few'. A negative pronoun requires
clausemate negation, *nem* or, after a preverbal negative pronoun, *sem*, as in *Itt senki sem
beszél magyarul* 'No one speaks Hungarian here'.

## Main definitions

* `Hungarian.Indefinites.vala`, `Hungarian.Indefinites.akár`, `Hungarian.Indefinites.bár`,
  `Hungarian.Indefinites.né`: the markers that attach a single prefix.
* `Hungarian.Indefinites.sem`: the negative marker, given the form of its prefix.
* `Hungarian.Indefinites.valaSeries`, `semSeries`, `akárSeries`, `bárSeries`, `néSeries`: the
  series.

## Implementation notes

Forms are orthographic, with the prefix written together with the interrogative, where
Haspelmath hyphenates it (*vala-ki*). The negative prefix is *sen-* in *senki*, *sem-* before
*mi*, *milyen* and *mikor*, and *se-* elsewhere. Haspelmath's table (A.26) has no *vala*-member
for the amounts, the bare *mely(ik)* for its determiner, no *sem*-member for the determiner and
no directional rows: *valahány*, *valamennyi*, *valamelyik* and *semelyik* are from Rounds
(§7.10, §7.11) and Kenesei et al. (§2.1.6.6), the *hova*- and *honnan*-members from Kenesei et
al. (§2.1.6.6.1).

## References

* [haspelmath-1997]
* [kenesei-vago-fenyvesi-1998]
* [rounds-2001]
-/

@[expose] public section

namespace Hungarian.Indefinites

open Pronouns

/-! ### The markers -/

/-- The *vala*-series attaches the prefix *vala-* to the interrogative. -/
def vala : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("vala" ++ ·)

/-- The negative series attaches its prefix to the interrogative in the form `pre`, one of
*sem-*, *se-* and *sen-*. -/
def sem (pre : String) : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (pre ++ ·)

/-- The *akár*-series attaches the prefix *akár-* to the interrogative. -/
def akár : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("akár" ++ ·)

/-- The *bár*-series attaches the prefix *bár-* to the interrogative. -/
def bár : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("bár" ++ ·)

/-- The marginal *né*-series attaches the prefix *né-* to the interrogative. -/
def né : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("né" ++ ·)

/-! ### The person row -/

/-- *valaki* 'someone' is the *vala*-member of *ki* 'who'. -/
def valaki : IndefinitePronoun := vala ki

/-- *senki* 'nobody' is the negative member of *ki* 'who', with the prefix *sen-*. -/
def senki : IndefinitePronoun := sem "sen" ki

/-- *akárki* 'anyone' is the *akár*-member of *ki* 'who'. -/
def akárki : IndefinitePronoun := akár ki

/-- *bárki* 'anyone' is the *bár*-member of *ki* 'who'. -/
def bárki : IndefinitePronoun := bár ki

/-! ### The series -/

/-- The *vala*-series has a member for each interrogative. -/
def valaSeries : IndefinitePronoun.Series :=
  ⟨"vala-", {valaki, vala mi, vala milyen, vala hol, vala hova, vala honnan, vala mikor, vala hogy,
    vala hány, vala mennyi, vala melyik}⟩

/-- The negative series has a member for each interrogative. -/
def semSeries : IndefinitePronoun.Series :=
  ⟨"sem-", {senki, sem "sem" mi, sem "sem" milyen, sem "se" hol, sem "se" hova, sem "se" honnan,
    sem "sem" mikor, sem "se" hogy, sem "se" hány, sem "se" mennyi, sem "se" melyik}⟩

/-- The *akár*-series has a member for each interrogative. -/
def akárSeries : IndefinitePronoun.Series :=
  ⟨"akár-", {akárki, akár mi, akár milyen, akár hol, akár hova, akár honnan, akár mikor, akár hogy,
    akár hány, akár mennyi, akár melyik}⟩

/-- The *bár*-series has a member for each interrogative but *hány*. -/
def bárSeries : IndefinitePronoun.Series :=
  ⟨"bár-", {bárki, bár mi, bár milyen, bár hol, bár hova, bár honnan, bár mikor, bár hogy,
    bár mennyi, bár melyik}⟩

/-- The *né*-series has the members *némi* 'something, a little', *néhol* 'in some places',
*néhány* 'some, a few' and *némelyik* 'some'. -/
def néSeries : IndefinitePronoun.Series :=
  ⟨"né-", {né mi, né hol, né hány, né melyik}⟩

end Hungarian.Indefinites
