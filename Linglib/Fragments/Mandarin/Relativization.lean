module

public import Linglib.Syntax.Clause.Relative

/-!
# Mandarin relative clauses

Mandarin relative clauses precede their head and end in the particle *de*. The relativized
position may be left empty, which relativizes subjects and direct objects, or filled by a
personal pronoun, which relativizes everything from direct objects down to objects of
comparison; the two overlap at direct objects, where retention is optional. Mandarin is the
sample's only prenominal-clause language whose pronoun-retention strategy reaches the bottom of
the hierarchy. The data are [keenan-comrie-1977]'s, whose Table 1 lists the language as
Chinese (spoken Pekingese).

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace Mandarin

/-- The particle *de* closes a prenominal clause whose relativized position is left empty at the
subject, left empty or filled by a personal pronoun at the direct object, and filled by a
personal pronoun from the indirect object down. -/
def relDe : Relativizer where
  placement := .preNominal
  realize
    | .subject => {.gap}
    | .directObject => {.gap, .resumptive}
    | _ => {.resumptive}

/-- The Mandarin relativizers. -/
def relativizers : List Relativizer := [relDe]

end Mandarin
