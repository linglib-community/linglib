module

public import Linglib.Syntax.Clause.Relative

/-!
# French relative clauses

French has one relative-clause strategy, postnominal, with a relative pronoun whose form codes
the relativized position: *qui* for subjects, *que* for direct objects, *dont* for genitives and
*lequel* after prepositions. It relativizes subjects through genitives; an object of comparison
cannot be relativized, so there is no relative clause for *le jeune homme* in *Marie est plus
grande que le jeune homme*. The data are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace French

/-- The relative pronouns *qui*, *que*, *dont* and *lequel* code the relativized position and
relativize subjects through genitives. -/
def relQui : Relativizer where
  placement := .postNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- The French relativizers. -/
def relativizers : List Relativizer := [relQui]

end French
