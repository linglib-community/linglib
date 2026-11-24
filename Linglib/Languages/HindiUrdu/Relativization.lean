module

public import Linglib.Syntax.Clause.Relative

/-!
# Hindi-Urdu relative clauses

Hindi-Urdu relativizes with the relative pronoun *jo*, oblique *jis-*, which carries the same
postpositions as an ordinary noun phrase and so codes the relativized position. It occurs in two
constructions, a postnominal clause and the correlative *jo … vo*, in which the head noun
stands inside the relative clause and is picked up by *vo* in the main clause; the paper codes
the correlative as an internally headed strategy. Both relativize subjects through genitives,
and objects of comparison are treated as obliques governed by postpositions. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace HindiUrdu

/-- The postnominal clause with the relative pronoun *jo* relativizes subjects through genitives. -/
def relJo : Relativizer where
  placement := .postNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- The correlative *jo … vo* keeps the head inside the relative clause and relativizes subjects
through genitives. -/
def relCorrelative : Relativizer where
  placement := .correlative
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- The Hindi-Urdu relativizers. -/
def relativizers : List Relativizer := [relJo, relCorrelative]

end HindiUrdu
