module

public import Linglib.Fragments.Quechua.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Ancash Quechua indefinite pronouns

Ancash Quechua uses its bare interrogatives as indefinites, as *pi* 'who', and derives one series
from them, the non-specific *-pis*-series (*pi-pis*), with *-pis* 'also, even'. The members are
those of Haspelmath's table. *Pi-pis* is also `Quechua.PolarityItems.piPis`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Quechua.Indefinites

/-- The *-pis* marker attaches *-pis* to the interrogative. -/
def pis : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-pis")

/-- Bare *pi* 'who' used as an indefinite. -/
def pi : IndefinitePronoun := ⟨Pronouns.pi.toProForm⟩

/-- *pi-pis*, the interrogative *pi* with *-pis*. -/
def piPis : IndefinitePronoun := pis Pronouns.pi

/-! ### The series -/

/-- The bare interrogatives used as indefinites. -/
def interrogativeSeries : IndefinitePronoun.Series :=
  ⟨"bare interrogative", Pronouns.interrogatives.image (⟨·.toProForm⟩)⟩

/-- The *-pis*-series. -/
def pisSeries : IndefinitePronoun.Series := ⟨"-pis", Pronouns.interrogatives.image pis⟩

end Quechua.Indefinites
