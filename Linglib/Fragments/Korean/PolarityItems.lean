module

public import Linglib.Fragments.Korean.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# Korean polarity items

Korean builds its indefinites on the interrogative pronouns, as Japanese does. Bare *nwukwu* 'who'
is a general indefinite, used from the specific functions through indirect negation, and is not a
polarity item. *Nwukwu-to*, with the additive particle *-to*, is used under indirect and direct
negation, with verbal negation in the latter, *Ku sonye-nun nwukwu-to an po-ass-ta* 'The girl did
not see anybody', and in the standard of comparison; *nwukwu-na*, whose *-na* is the adversative
mood of the copula and also means 'or', is the free-choice item of *Nwukwu-na i muncey-lul phul
swu-iss-ta* 'Anybody can solve this problem' (Haspelmath, Appendix A.39).

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Korean.PolarityItems

open PolarityItem

/-- *nwukwu-to* 'anybody', 'nobody', the interrogative with the additive particle, used under
indirect and direct negation and in comparatives ([haspelmath-1997] Fig. A.39, (A292)–(A294)), so
needing an anti-additive context. -/
def nwukwuTo : PolarityItem :=
  { form := Indefinites.nwukwuTo.form
  , licensor := some .antiAdditive }

/-- *nwukwu-na* 'anybody', the free-choice item ([haspelmath-1997] (A291)); *-na* is not an
additive particle. -/
def nwukwuNa : PolarityItem :=
  { form := Indefinites.nwukwuNa.form
  , freeChoice := true }

/-- *Nwukwu-to* is licensed exactly by the contexts carrying anti-additive strength. -/
theorem nwukwuTo_licensing_characterized (c : LicensingContext) :
    c.licenser.Licenses nwukwuTo ↔ c.licenser.Carries .antiAdditive :=
  Licenser.licenses_iff_carries rfl (by decide) (by decide)

end Korean.PolarityItems
