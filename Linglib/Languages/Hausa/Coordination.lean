module

public import Linglib.Syntax.Category.Coordinator

/-!
# Hausa coordinators

Hausa conjoins noun phrases with the free word *dà* before the second conjunct, *gidā dà mōtā* 'a
house and a car', and often before the first as well, *dà Bellò dà Mūsā* 'both Musa and Bello',
as Newman gives them. The same word is the comitative preposition 'with', the source from which
Haspelmath derives the coordinator, citing Schwartz's data.

## Main definitions

* `Hausa.Coordination.da`: the conjunctive coordinator.

## References

* [haspelmath-2007]
* [newman-2000]
* [schwartz-1989]
-/

@[expose] public section

namespace Hausa.Coordination

/-- *dà* 'and', also the comitative preposition 'with', `Hausa.Adpositions.da`. -/
def da : Coordinator :=
  { morph := .free "dà", gloss := "and", role := .conjunctive }

end Hausa.Coordination
