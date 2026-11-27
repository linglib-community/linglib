module

public import Linglib.Languages.Yakut.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Yakut (Sakha) indefinite pronouns

Yakut builds its indefinite pronouns from an interrogative pronoun and an enclitic particle, four
series on *kim* 'who': *kim ere* 'somebody' for a referent the speaker has in mind or presupposes;
*kim eme* 'somebody, anybody' for irrealis non-specific reference and in questions and conditionals;
*kim da* 'anybody', with the variant *kim dayanï*, in affirmative and negative sentences alike,
under negation, in comparatives and for free choice; and the generalising *kim bayarar* 'whoever',
on *bayar* 'want', for free choice. The members are those of Haspelmath's table, each the
interrogative followed by the particle; a seventh row of his table, on *xaja*, has no category and
is left out.

## References

* [haspelmath-1997]
* [stachowski-menz-1998]
-/

@[expose] public section

namespace Yakut.Indefinites

open Pronouns

/-! ### The markers -/

/-- The *ere* marker follows the interrogative with the particle *ere*. -/
def ere : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " ere")

/-- The *eme* marker follows the interrogative with the particle *eme*. -/
def eme : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " eme")

/-- The *da* marker follows the interrogative with the particle *da*. -/
def da : InterrogativePronoun → IndefinitePronoun := IndefinitePronoun.ofInterrogative (· ++ " da")

/-- The *bayarar* marker follows the interrogative with *bayarar*. -/
def bayarar : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " bayarar")

/-! ### The person row -/

/-- *kim ere* 'somebody'. -/
def kimEre : IndefinitePronoun := ere kim

/-- *kim eme* 'somebody, anybody'. -/
def kimEme : IndefinitePronoun := eme kim

/-- *kim da* 'anybody', with the variant *kim dayanï*. -/
def kimDa : IndefinitePronoun := da kim

/-- *kim bayarar* 'whoever'. -/
def kimBayarar : IndefinitePronoun := bayarar kim

/-! ### The series -/

/-- The *ere* series. -/
def ereSeries : IndefinitePronoun.Series := ⟨"ere", interrogatives.image ere⟩

/-- The *eme* series, which has no member for a manner or a determiner. -/
def emeSeries : IndefinitePronoun.Series :=
  ⟨"eme", ({kim, tuox, xanna, xahan} : Finset _).image eme⟩

/-- The *da* series. -/
def daSeries : IndefinitePronoun.Series := ⟨"da", interrogatives.image da⟩

/-- The *bayarar* series. -/
def bayararSeries : IndefinitePronoun.Series := ⟨"bayarar", interrogatives.image bayarar⟩

end Yakut.Indefinites
