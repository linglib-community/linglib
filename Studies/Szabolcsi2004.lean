module

public import Linglib.Fragments.English.PolarityItems
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Data.Examples.Szabolcsi2004

/-!
# Szabolcsi (2004): Positive Polarity – Negative Polarity

Szabolcsi observes that *someone* cannot take scope immediately below clausemate negation, a
negative quantifier or *without*, but can below *at most five*, and that what sets the first three
apart is that they are anti-additive while *at most five* is merely decreasing. With *someone*'s
Fragment entry, which is blocked by anti-additive operators, the licensing theory blocks exactly
the starred narrow-scope readings of her paradigm (`readings_predicted`), and over the paradigm's
operators being blocked is being anti-additive (`antiLicenses_someone_iff`).

## References

* [szabolcsi-2004]
-/

@[expose] public section

namespace Szabolcsi2004

open PolarityItem English.PolarityItems

/-- The operators of the paradigm, clausemate negation, *no one*, *without* and *at most five*. -/
def paradigm : List LicensingContext := [.negation, .nobody, .withoutClause, .atMost]

theorem antiLicenses_someone_iff :
    ∀ c ∈ paradigm, c.licenser.AntiLicenses someone ↔ c.licenser.Holds .antiAdd := by
  simp only [paradigm, List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl)
  · exact iff_of_true (by decide) (LicensingContext.holds_negation .antiAdditive)
  · exact iff_of_true (by decide)
      (LicensingContext.holds_nobody_iff (s := .antiAdditive) |>.2 le_rfl)
  · exact iff_of_true (by decide)
      (LicensingContext.holds_withoutClause_iff (s := .antiAdditive) |>.2 le_rfl)
  · exact iff_of_false (by decide)
      fun h ↦ absurd (LicensingContext.holds_atMost_iff (s := .antiAdditive) |>.1 h) (by decide)

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
