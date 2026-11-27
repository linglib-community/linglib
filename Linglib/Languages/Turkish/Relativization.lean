module

public import Linglib.Syntax.Clause.Relative

/-!
# Turkish relative clauses

Turkish relative clauses precede their head and their verb is a participle, *-(y)En* when the
head is the subject and *-DIK* otherwise, with the subject of the clause in the genitive. With
the relativized position left empty this relativizes subjects through obliques. Below that a
pronominal element is retained, a possessive suffix on the head noun for genitives and a
stressed pronoun for objects of comparison, the latter with reduced acceptability. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace Turkish

/-- The participial suffixes of a prenominal clause, *-(y)En* and *-DIK*: the relativized
position is left empty from subjects through obliques, and a pronominal element is retained at
genitives and, marginally, objects of comparison. -/
def relParticiple : Relativizer where
  placement := .preNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique => {.gap}
    | .genitive | .objComparison => {.resumptive}

/-- The Turkish relativizers. -/
def relativizers : List Relativizer := [relParticiple]

end Turkish
