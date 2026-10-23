module

public import Linglib.Fragments.Quechua.Indefinites
public import Linglib.Semantics.Polarity.Licensing

/-!
# Quechua (Ancash) Polarity-Sensitive Items

The Ancash Quechua *-pis* series (Haspelmath's appendix A.37), interrogative + *-pis* ('also,
even'), is used in all non-specific functions: questions, conditionals, both negation functions
(direct negation with the discontinuous negator *mana … -tsu*, A279), comparatives (A277), and
free choice (A278). It is a dual NPI/FCI on Lahiri's indefinite-plus-even pattern.

## References

* [haspelmath-1997]
* [lahiri-1998]
-/

@[expose] public section

namespace Quechua.PolarityItems

open PolarityItem

/-- *pi-pis*, wh + 'also/even', is a dual NPI/FCI covering the map's whole
    non-specific span (A.37). -/
def piPis : PolarityItem :=
  { form := Indefinites.piPis.form
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.negation, .question, .conditionalAntecedent, .clausalComparative,
       .modalPossibility, .imperative, .generic] }

/-! ### Verification -/

theorem piPis_licensing_sound :
    ∀ c ∈ piPis.licensingContexts, c.licenser.Admits piPis := by
  decide

end Quechua.PolarityItems
