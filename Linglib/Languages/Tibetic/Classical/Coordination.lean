module

public import Linglib.Syntax.Category.Coordinator

/-!
# Classical Tibetan coordinators

Classical Tibetan conjoins noun phrases with *-daŋ*, attached to the first coordinand, in the
example Haspelmath cites from Beyer. The conjunction is the same form as the accompaniment role
particle *-daŋ* 'with', so that 'lama-*daŋ* king go' reads as 'the lama and the king go' or as
'the king goes with the lama', as Beyer notes (p. 241, n. 47).

## Main definitions

* `ClassicalTibetan.Coordination.dang`: the conjunctive enclitic.

## References

* [haspelmath-2007]
* [beyer-1992]
-/

@[expose] public section

namespace ClassicalTibetan.Coordination

/-- *-daŋ* 'and', on the first coordinand, also the accompaniment role particle 'with',
`ClassicalTibetan.Case.accompaniment`. -/
def dang : Coordinator :=
  { morph := .encl "daŋ", gloss := "and", role := .conjunctive }

end ClassicalTibetan.Coordination
