module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Syntax.Category.Adposition.Spatial

/-! # Verb entry readers

The readers of a verb entry beyond its fields: the entailment profile of the participant in a
slot, lookup by citation form and sense, and the predicate a verb forms with a path phrase. The
semantic classifications of an entry live with their theories, each under the `Verb` namespace:
factivity and trigger status in `Semantics/Presupposition/Verb.lean` and unaccusativity in
`Semantics/ArgumentStructure/Unaccusativity.lean`.

## Main definitions

* `Verb.slotProfile?`: the entailment profile of the participant in a slot of the basic
  diathesis.
* `Verb.find?`: the entry with a citation form and sense.
* `Verb.withPath`: the predicate a verb forms with a path phrase.

## References

* [levin-hovav-1995]
* [sorace-2000]
* [zwarts-2005]
-/

@[expose] public section

open ArgumentStructure

namespace Verb

/-- The entailment profile of the participant in slot `s` of the basic diathesis. -/
def slotProfile? (v : Verb) (s : ArgumentFrame.Slot) : Option EntailmentProfile :=
  v.valency.basic?.bind (v.valency.profileAt · s)

/-- The entry with the given citation form and sense, if the list has one. -/
def find? (verbs : List Verb) (form : String) (tag : SenseTag := .default) : Option Verb :=
  verbs.find? fun v ↦ v.form == form && v.senseTag == tag

/-! ### Path phrases -/

/-- The predicate a verb forms with a path phrase of reading `p`. A directional phrase that the
verb selects as a complement gives the theme's path its direction, the directed motion use of a
verb of manner of motion ([levin-hovav-1995] p. 185), and a bounded one an endpoint, which makes
the predicate telic ([zwarts-2005]). A locative phrase, and a phrase the verb does not select, an
adjunct, leave the verb as it is: *correre* 'run' has a directed motion use in Italian but
*nuotare* 'swim' has none ([sorace-2000] §4.3). -/
def withPath (v : Verb) (p : Adposition.SpatialReading) : Verb :=
  if p.direction = .place ∨ ¬ v.TakesSpatial then v else
    { v with
      direction := some p.direction
      vendlerClass := if p.IsBounded then v.vendlerClass.map (·.telicize) else v.vendlerClass }

section withPath

variable {v : Verb} {p : Adposition.SpatialReading}

@[simp] theorem withPath_of_direction_eq_place (h : p.direction = .place) : v.withPath p = v := by
  simp [withPath, h]

@[simp] theorem withPath_of_not_takesSpatial (h : ¬ v.TakesSpatial) : v.withPath p = v := by
  simp [withPath, h]

@[simp] theorem direction_withPath (hv : v.TakesSpatial) (h : p.direction ≠ .place) :
    (v.withPath p).direction = some p.direction := by
  simp [withPath, hv, h]

@[simp] theorem vendlerClass_withPath_of_isBounded (hv : v.TakesSpatial) (hb : p.IsBounded) :
    (v.withPath p).vendlerClass = v.vendlerClass.map (·.telicize) := by
  simp [withPath, hv, hb.direction_ne_place, hb]

@[simp] theorem vendlerClass_withPath_of_not_isBounded (hb : ¬ p.IsBounded) :
    (v.withPath p).vendlerClass = v.vendlerClass := by
  unfold withPath
  split_ifs <;> rfl

end withPath

end Verb
