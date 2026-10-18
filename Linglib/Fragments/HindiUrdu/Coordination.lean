module

public import Linglib.Syntax.Category.Coordinator

/-!
# Hindi-Urdu coordinators

Hindi-Urdu conjoins with the free word *aur* 'and' before the second coordinand. The additive
particle *bhii* 'also, too' follows the phrase it associates with, and repeated after each
coordinand gives 'both … and'.

## Main definitions

* `HindiUrdu.Coordination.aur`, `HindiUrdu.Coordination.bhii`: the conjunctive coordinator and
  the additive particle that conjoins when repeated.

## TODO

The entries have not been checked against a grammar of Hindi-Urdu.
-/

@[expose] public section

namespace HindiUrdu.Coordination

/-- *aur* 'and'. -/
def aur : Coordinator :=
  { morph := .free "aur", gloss := "and", role := .conjunctive }

/-- *bhii*, after each coordinand 'both … and', also the additive particle
`HindiUrdu.FocusParticles.bhii`. -/
def bhii : Coordinator :=
  { morph := .free "bhii", gloss := "and", role := .conjunctive }

/-- The coordinators. -/
def allEntries : List Coordinator := [aur, bhii]

end HindiUrdu.Coordination
