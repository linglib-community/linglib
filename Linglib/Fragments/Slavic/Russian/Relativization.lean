module

public import Linglib.Syntax.Clause.Relative

/-!
# Russian relative clauses

Russian has one relative-clause strategy, postnominal, with the relative pronoun *kotoryj*
declining for the case of the relativized position: *devuška, kotoruju Džon ljubit* 'the girl
who John likes' against *devuška, kotoraja ljubit Džona* 'the girl who likes John', the
paper's illustration of a case-coding strategy. It relativizes subjects through genitives. The
participial construction that relativizes subjects only, which the paper mentions for Russian
alongside German and Polish, is not entered in its Table 1 and is not recorded here. The data
are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace Russian

/-- The relative pronoun *kotoryj* declines for the case of the relativized position and
relativizes subjects through genitives. -/
def relKotoryj : Relativizer where
  placement := .postNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- The Russian relativizers. -/
def relativizers : List Relativizer := [relKotoryj]

end Russian
