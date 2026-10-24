module

public import Linglib.Syntax.Clause.Relative

/-!
# Japanese relative clauses

Japanese relative clauses precede their head with no relativizer and no relative pronoun. The
relativized position is normally left empty, and this relativizes subjects, direct objects and
indirect objects freely and obliques and genitives for some noun phrases; objects of comparison
are not relativized, though the paper judges the result not too bad. A pronoun may instead be
retained, and only when the relativized position is a genitive. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace Japanese

/-- The zero relativizer of the unmarked prenominal clause: the relativized position is left
empty from subjects through genitives, and at a genitive a pronoun may instead be retained. -/
def relZero : Relativizer where
  placement := .preNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique => {.gap}
    | .genitive => {.gap, .resumptive}
    | .objComparison => ∅

/-- The Japanese relativizers. -/
def relativizers : List Relativizer := [relZero]

end Japanese
