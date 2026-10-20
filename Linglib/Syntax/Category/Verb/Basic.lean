module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Syntax.Category.Adposition.Spatial

/-! # Verb entry readers

The readers of a verb entry beyond its fields: the entailment profile of a participant, the
entry's own or else the one its Levin classes agree on, lookup by citation form and sense, and
the predicate a verb forms with a path phrase. The semantic classifications of an entry live
with their theories, each under the `Verb` namespace: factivity and trigger status in
`Semantics/Presupposition/Verb.lean` and unaccusativity in
`Semantics/ArgumentStructure/Unaccusativity.lean`.

## Main definitions

* `Verb.participantProfile?`: the entailment profile of a participant.
* `Verb.slotProfile?`: the entailment profile of the participant in a slot of the basic
  diathesis.
* `Verb.find?`: the entry with a citation form and sense.
* `Verb.withPath`: the predicate a verb forms with a path phrase.

## Main results

* `Verb.participantProfile?_of_get_eq_some`: a profile the entry records wins over the Levin
  classes'.
* `Verb.slotProfile?_of_levinClasses_eq_empty`: without Levin classes a slot's profile is the
  recorded one.

## References

* [levin-1993]
* [dowty-1991]
* [levin-hovav-1995]
* [sorace-2000]
* [zwarts-2005]
-/

@[expose] public section

open ArgumentStructure

namespace Verb

/-- The entailment profile of a participant, the entry's own or else the one the verb's Levin
classes agree on for the participant's slot in the basic diathesis, subject or object
([levin-1993], [dowty-1991]). -/
def participantProfile? (v : Verb) (i : Fin v.valency.arity) : Option EntailmentProfile :=
  v.valency.profiles.get i <|> v.valency.basic?.bind fun d ↦ (d.links.get i).bind fun s ↦
    if s = .external then LevinClass.commonProfile LevinClass.subjectProfile v.levinClasses
    else if d.objectSlot? = some s then
      LevinClass.commonProfile LevinClass.objectProfile v.levinClasses
    else none

/-- The entailment profile of the participant in slot `s` of the basic diathesis. -/
def slotProfile? (v : Verb) (s : ArgumentFrame.Slot) : Option EntailmentProfile :=
  v.valency.basic?.bind fun d ↦ (d.participantAt s).bind v.participantProfile?

section profile

variable {v : Verb}

theorem participantProfile?_of_get_eq_some {i : Fin v.valency.arity} {θ : EntailmentProfile}
    (h : v.valency.profiles.get i = some θ) : v.participantProfile? i = some θ := by
  simp [participantProfile?, h]

theorem participantProfile?_of_levinClasses_eq_empty (h : v.levinClasses = ∅)
    (i : Fin v.valency.arity) : v.participantProfile? i = v.valency.profiles.get i := by
  rcases hi : v.valency.profiles.get i with _ | θ
  · rcases v.valency.basic? with _ | d <;> simp [participantProfile?, hi, h]
  · exact participantProfile?_of_get_eq_some hi

theorem slotProfile?_of_levinClasses_eq_empty (h : v.levinClasses = ∅) (s : ArgumentFrame.Slot) :
    v.slotProfile? s = v.valency.basic?.bind (v.valency.profileAt · s) := by
  simp [slotProfile?, Valency.profileAt, participantProfile?_of_levinClasses_eq_empty h]

end profile

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
