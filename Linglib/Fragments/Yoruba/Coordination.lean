module

public import Linglib.Syntax.Category.Coordinator

/-!
# Yoruba coordinators

Yoruba conjoins noun phrases with the free word *àtí* before the second coordinand. Repeated
before each coordinand, *àtí A àtí B*, it gives the emphatic 'both … and', the construction
Haspelmath cites from Rowlands.

## Main definitions

* `Yoruba.Coordination.ati`: the conjunctive coordinator.
* `Yoruba.Coordination.atiAti`: the emphatic conjunction.

## References

* [haspelmath-2007]
* [rowlands-1969]
-/

@[expose] public section

namespace Yoruba.Coordination

/-- *àtí* 'and', repeated for 'both … and'. -/
def ati : Coordinator :=
  { morph := .free "àtí", gloss := "and", role := .conjunctive }

/-- *àtí … àtí* 'both … and'. -/
def atiAti : Coordinator.Correlative := ⟨[ati.morph], [ati.morph], ati⟩

end Yoruba.Coordination
