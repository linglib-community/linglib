module

public import Linglib.Fragments.English.PolarityItems
public import Linglib.Semantics.PolarityItem.Licensing
public import Linglib.Data.Examples.Szabolcsi2004
public import Linglib.Data.Examples.Readers

/-!
# Szabolcsi (2004): Positive Polarity – Negative Polarity

Szabolcsi observes that *someone* cannot take scope immediately below clausemate negation, a
negative quantifier or *without*, but can below *at most five*, and that what sets the first three
apart is that they are anti-additive while *at most five* is merely decreasing. With *someone*'s
Fragment entry, which is blocked by anti-additive operators, the licensing theory blocks exactly
the starred narrow-scope readings of her paradigm (`readings_predicted`), and an operator blocks it
exactly when it is anti-additive (`antiLicenses_someone_iff`).

## References

* [szabolcsi-2004]
-/

@[expose] public section

namespace Szabolcsi2004

open PolarityItem English.PolarityItems

theorem antiLicenses_someone_iff (L : Licenser) :
    L.AntiLicenses someone ↔ L.Holds .antiAdd :=
  Licenser.antiLicenses_iff_holds (r := .antiAdditive) rfl

/-- The operator a row names. -/
def operatorOf : String → Option LicensingContext
  | "not" => some .negation
  | "no one" => some .nobody
  | "without" => some .withoutClause
  | "at most five" => some .atMost
  | _ => none

theorem readings_predicted :
    ∀ d ∈ Examples.all, d.feature? "item" = some "someone" ∧
      ∃ c ∈ (d.feature? "operator").bind operatorOf, ∃ r ∈ d.readings.head?,
        (r.2 = .acceptable ↔ ¬ c.licenser.AntiLicenses someone) := by
  decide +kernel

end Szabolcsi2004
