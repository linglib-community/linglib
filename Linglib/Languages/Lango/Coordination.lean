module

public import Linglib.Syntax.Category.Coordinator

/-!
# Lango coordinators

Lango, a Nilotic language of Uganda, conjoins noun phrases with the free word *kèdè* before
the second coordinand, *cây kèdè càk* 'tea and milk'. The same word is the comitative 'with',
and Haspelmath gives the construction, from Noonan's grammar, as an example of a
comitative-derived coordinator.

## Main definitions

* `Lango.Coordination.kede`: the conjunctive coordinator.

## References

* [haspelmath-2007]
* [noonan-1992]
-/

@[expose] public section

namespace Lango.Coordination

/-- *kèdè* 'and', also the comitative preposition 'with', `Lango.Adpositions.kede`. -/
def kede : Coordinator :=
  { morph := .free "kèdè", gloss := "and", role := .conjunctive }

end Lango.Coordination
