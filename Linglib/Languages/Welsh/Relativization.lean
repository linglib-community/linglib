module

public import Linglib.Syntax.Clause.Relative

/-!
# Welsh relative clauses

Welsh has two relative particles. *A* introduces a postnominal relative clause in which the
relativized position is left empty, and it relativizes subjects and direct objects: *y bachgen a
oedd yn darllen* 'the boy who was reading'. *Y* introduces a postnominal relative clause in which
the relativized position holds a personal pronoun, and it relativizes everything from indirect
objects down to objects of comparison: *dyma'r llyfr y darllenais y stori ynddo* 'here is the
book in which I read the story', with the pronoun in *ynddo* 'in it'. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace Welsh

/-- The particle *a* leaves the relativized position empty and relativizes subjects and direct
objects. -/
def relParticleA : Relativizer where
  placement := .postNominal
  realize
    | .subject | .directObject => {.gap}
    | _ => ∅

/-- The particle *y* puts a personal pronoun in the relativized position and relativizes
everything from indirect objects down. -/
def relParticleY : Relativizer where
  placement := .postNominal
  realize
    | .indirectObject | .oblique | .genitive | .objComparison => {.resumptive}
    | _ => ∅

/-- The Welsh relativizers. -/
def relativizers : List Relativizer := [relParticleA, relParticleY]

end Welsh
