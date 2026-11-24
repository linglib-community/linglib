module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Feature.Case.Function

/-!
# Classical Tibetan role particles

Classical Tibetan marks the role of a participant by a role particle after its noun phrase
([beyer-1992], p. 252): the patient by none, the agency, agent and instrument alike, by *-KYis*
(p. 269, n. 15), a locus by *-la*, or by *-na* where the locus is an enclosed space, a source
likewise by *-las* or *-nas* (pp. 268–269), and the accompaniment by *-daŋ*, the same form as the
conjunction 'and' (p. 241, n. 47). A locus particle marks the site of a verb of location and the
target of a verb of motion alike (p. 269).

## Main definitions

* `ClassicalTibetan.Case`, `ClassicalTibetan.Case.exponents`: the role particles.
* `ClassicalTibetan.Case.label`, `ClassicalTibetan.Case.functions`: the comparative value each is
  named for, and the functions it marks.

## Implementation notes

* *-KYis* is in Beyer's notation, capitals for the segments that assimilate to the noun.

## References

* [beyer-1992]
-/

@[expose] public section

namespace ClassicalTibetan

/-- The role particles. -/
inductive Case where
  /-- The patient, unmarked. -/
  | patient
  /-- The agency, agent or instrument. -/
  | agency
  /-- The locus. -/
  | locus
  /-- The locus as an enclosed space. -/
  | boundedLocus
  /-- The source. -/
  | source
  /-- The source as an enclosed space. -/
  | boundedSource
  /-- The accompaniment. -/
  | accompaniment
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a particle is named for. -/
def label : Case → _root_.Case
  | patient => .abs
  | agency => .erg
  | locus | boundedLocus => .loc
  | source | boundedSource => .abl
  | accompaniment => .com

/-- The functions a particle marks: the agency also the instrument, and a locus also
the goal of motion. -/
def functions : Case → Finset _root_.Case.Function
  | agency => {.argument .A, .instrumental}
  | locus | boundedLocus => {.spatial none .place, .spatial none .goal}
  | source | boundedSource => {.spatial none .source}
  | c => c.label.functions

theorem label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

/-- The role particle of a case. -/
def exponents : Case → List Morphology.Morph
  | patient => []
  | agency => [.encl "KYis"]
  | locus => [.encl "la"]
  | boundedLocus => [.encl "na"]
  | source => [.encl "las"]
  | boundedSource => [.encl "nas"]
  | accompaniment => [.encl "daŋ"]

end Case

end ClassicalTibetan
