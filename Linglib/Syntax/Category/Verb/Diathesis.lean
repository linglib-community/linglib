module

public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Linglib.Morphology.Morph

/-!
# Diatheses

A diathesis of a verb is the correspondence between its participants and the syntactic positions
expressing them: here, an argument frame together with the slot each participant occupies, or
none for a participant the construction leaves out. A verb's valency is its participants and its
diatheses, the basic diathesis first, so one participant can be followed across the verb's
constructions: the thing broken is the object of transitive *break* and the subject of
intransitive *break*. Which diatheses a verb has, and which participant fills which slot, are
lexical data; theories of argument linking are predicates on them. An alternation relates two
diatheses of a verb, and a voice is an alternation the verb's form marks.

## Main definitions

* `Diathesis n`: an argument frame, the slot of each of `n` participants, and the verb's form
  where it departs from the citation form.
* `Diathesis.ofSlots`: the diathesis whose slots, in order, hold the listed participants.
* `Diathesis.controller`, `Diathesis.controllerRole`: the participant controlling the open
  complement and its argument role.
* `Diathesis.IsRaising`: no participant fills the slot controlling the open complement.
* `Verb.Valency`: a verb's participants, with their entailment profiles, and its diatheses, the
  basic diathesis first.
* `Verb.Valency.of`, `Verb.Valency.ofFrames`: a valency from frames with the participants of
  their slots, or from frames whose slots hold the participants in order.

## Implementation notes

* A link runs from a participant to its slot, so two participants can share a slot, as in
  Baker's reflexive-reciprocal formation; an implied participant occupies an implicit position
  of the frame, and one understood as the subject itself or its members is cumulated with it.
* Participants are numbered, and a diathesis is entered as the participants of its slots in slot
  order, the external argument first: `ofSlots .np [0, 1]` puts participant 0 in subject
  position and participant 1 in object position.
* A diathesis may leave out a participant another diathesis of the verb expresses, as the
  intransitive of *break* leaves out the breaker, so a causative or anticausative pair is two
  diatheses of one verb. Mel'čuk's narrower diathesis keeps the semantic actants fixed and
  treats such a pair as two lexical units.
* The frame records the slot whose subject an open complement shares
  (`ArgumentFrame.ComplementSubject`); the diathesis records whether a participant fills it. The
  controller is that participant, as Chierchia's controller is an argument of the verb, so that
  subject and object control are the controller's argument role, never stored, and the
  controller can be followed across diatheses, as Visser's and Bach's generalizations need. Under
  raising no participant fills the slot, which only the semantically unrestricted functions may
  leave unfilled ([bresnan-1982]): *seem* raises into its subject and *believe* into its object.
* A diathesis records the verb's form where the verb takes another form in it, as Spanish
  *romperse* beside *romper*, so an alternation the form marks stays within one valency, its
  participants followed across both forms. Mel'čuk's diathesis is the rest, without the form.

## References

* [bresnan-1982]
* [chierchia-1984]
* [melcuk-1993]
* [zuniga-kittila-2019]
-/

@[expose] public section

open ArgumentFrame (Slot)

/-- A diathesis of `n` participants is an argument frame together with the slot each participant
occupies in it, `none` for a participant the construction leaves out. -/
structure Diathesis (n : ℕ) extends ArgumentFrame where
  /-- The slot each participant occupies. -/
  links : Vector (Option Slot) n
  /-- The verb's form in this diathesis, where it departs from the citation form, as Spanish
  *romperse* or the Sinhala involitive *kædennə*. -/
  form : Option (List Morphology.Morph) := none
  deriving DecidableEq, Repr

namespace Diathesis

variable {n : ℕ}

/-- `ofSlots fr ps c f r` is the diathesis of `fr` whose slots, in the order of
`ArgumentFrame.slots`, hold the participants `ps`, and in which the verb has the form `f`. Its
clausal complement is open to the slot of participant `c`, under equi, or to the slot `r`, which
then holds no participant, under raising; a participant `ps` does not list is left out. -/
def ofSlots (fr : ArgumentFrame) (ps : List ℕ) (c : Option ℕ := none)
    (f : Option (List Morphology.Morph) := none) (r : Option Slot := none) : Diathesis n :=
  let link (i : ℕ) : Option Slot :=
    (((fr.slots.filter (some · ≠ r)).zip ps).find? (·.2 = i)).map (·.1)
  { toArgumentFrame := (r.orElse fun _ ↦ c.bind link).elim fr fr.controlledBy
    links := .ofFn fun i ↦ link i.val
    form := f }

/-- The participant occupying a slot, the first if several share it. -/
def participantAt (d : Diathesis n) (s : Slot) : Option (Fin n) :=
  (List.finRange n).find? fun i ↦ d.links.get i = some s

/-- The argument role of a participant, that of its slot. -/
def participantRole (d : Diathesis n) (i : Fin n) : Option ArgumentRole :=
  (d.links.get i).bind d.argumentRole

/-- The controller is the participant in the slot whose subject the open complement shares. -/
def controller (d : Diathesis n) : Option (Fin n) := d.controllerSlot?.bind d.participantAt

/-- The diathesis is raising when no participant fills the slot controlling its open complement. -/
def IsRaising (d : Diathesis n) : Prop := ∃ s ∈ d.controllerSlot?, d.participantAt s = none

instance (d : Diathesis n) : Decidable d.IsRaising := inferInstanceAs (Decidable (∃ s ∈ _, _))

/-- The argument role of the controller is that of its slot, S or A under subject control and P
under object control. -/
def controllerRole (d : Diathesis n) : Option ArgumentRole :=
  d.controller.bind d.participantRole

end Diathesis

open ArgumentStructure (EntailmentProfile)

/-- A verb's valency is its participants, each with the proto-role entailment profile the entry
records for it, and its diatheses, the basic diathesis first. -/
structure Verb.Valency where
  /-- The number of participants. -/
  arity : ℕ
  /-- The entailment profile of each participant, where the entry records one. -/
  profiles : Vector (Option EntailmentProfile) arity
  /-- The diatheses, the basic diathesis first. -/
  diatheses : List (Diathesis arity)
  deriving DecidableEq, Repr

namespace Verb.Valency

/-- The valency whose diatheses are given as frames with the participants of their slots in slot
order, with the controllers of their clausal complements, the verb's forms in them and the slots
they raise into in the same order, and whose participants have the listed profiles; the
participants are numbered from 0. -/
def of (frs : List (ArgumentFrame × List ℕ)) (profiles : List (Option EntailmentProfile) := [])
    (controllers : List (Option ℕ) := []) (forms : List (Option (List Morphology.Morph)) := [])
    (raised : List (Option Slot) := []) : Valency :=
  let n := max profiles.length ((frs.flatMap (·.2)).foldr (fun p m ↦ max (p + 1) m) 0)
  ⟨n, .ofFn fun i ↦ profiles[i.val]?.join,
    frs.mapIdx fun i x ↦
      Diathesis.ofSlots x.1 x.2 controllers[i]?.join forms[i]?.join raised[i]?.join⟩

/-- The valency whose diatheses are the frames `frs`, each slot holding its own participant in
slot order, so that a participant fills the same slot in every frame, with the controllers of
their clausal complements, the verb's forms in them and the slots they raise into, which hold no
participant, in the same order. -/
def ofFrames (frs : List ArgumentFrame) (profiles : List (Option EntailmentProfile) := [])
    (controllers : List (Option ℕ) := []) (forms : List (Option (List Morphology.Morph)) := [])
    (raised : List (Option Slot) := []) : Valency :=
  of (frs.mapIdx fun i fr ↦
      (fr, List.range (fr.slots.filter (some · ≠ raised[i]?.join)).length))
    profiles controllers forms raised

/-- The valency of a verb with one diathesis, each slot of its frame holding its own participant
in slot order, its clausal complement open to the slot of participant `controller` or to the slot
`raised`, which then holds no participant. -/
def ofFrame (fr : ArgumentFrame) (profiles : List (Option EntailmentProfile) := [])
    (controller : Option ℕ := none) (raised : Option Slot := none) : Valency :=
  ofFrames [fr] profiles [controller] [] [raised]

variable (V : Valency)

/-- The basic diathesis, the first. -/
def basic? : Option (Diathesis V.arity) := V.diatheses.head?

/-- The argument frames of the diatheses. -/
def frames : List ArgumentFrame := V.diatheses.map (·.toArgumentFrame)

/-- The entailment profile of the participant in a slot of one of the diatheses. -/
def profileAt (d : Diathesis V.arity) (s : Slot) : Option EntailmentProfile :=
  (d.participantAt s).bind V.profiles.get

end Verb.Valency
