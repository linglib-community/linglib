module

public import Linglib.Syntax.Category.Coordinator

/-!
# German coordinators

German coordinates with free words that stand before the second coordinand: *und* 'and', *oder*
'or', and two adversative coordinators, *aber* 'but' and the corrective *sondern* 'but rather',
which requires a negated first coordinand. The emphatic conjunction is *sowohl … als auch*,
neither member of which is the plain coordinator, and the emphatic disjunction *entweder …
oder*.

## Main definitions

* `German.Coordination.und`, `German.Coordination.oder`: the conjunctive and the disjunctive
  coordinator.
* `German.Coordination.aber`, `German.Coordination.sondern`: the adversative coordinators.
* `German.Coordination.sowohlAlsAuch`, `German.Coordination.entwederOder`: the emphatic
  constructions.

## References

* [haspelmath-2007]
-/

@[expose] public section

namespace German.Coordination

/-- *und* 'and'. -/
def und : Coordinator :=
  { morph := .free "und", gloss := "and", role := .conjunctive }

/-- *oder* 'or'. -/
def oder : Coordinator :=
  { morph := .free "oder", gloss := "or", role := .disjunctive }

/-- *aber* 'but'. -/
def aber : Coordinator :=
  { morph := .free "aber", gloss := "but", role := .adversative }

/-- *sondern* 'but rather', after a negated first coordinand. -/
def sondern : Coordinator :=
  { morph := .free "sondern", gloss := "but rather", role := .adversative }

/-- *sowohl … als auch* 'both … and'. -/
def sowohlAlsAuch : Coordinator.Correlative := ⟨[.free "sowohl"], [.free "als", .free "auch"], und⟩

/-- *entweder … oder* 'either … or'. -/
def entwederOder : Coordinator.Correlative := ⟨[.free "entweder"], [oder.morph], oder⟩

end German.Coordination
