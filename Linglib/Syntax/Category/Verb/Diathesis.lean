module

public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic

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

* `Diathesis n`: an argument frame and the slot of each of `n` participants.
* `Diathesis.ofSlots`: the diathesis whose slots, in order, hold the listed participants.
* `Verb.Valency`: a verb's participants, with their entailment profiles, and its diatheses, the
  basic diathesis first.

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

## References

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
  deriving DecidableEq, Repr

namespace Diathesis

variable {n : ℕ}

/-- `ofSlots fr ps` is the diathesis of `fr` whose slots, in the order of `ArgumentFrame.slots`,
hold the participants `ps`; a participant `ps` does not list is left out. -/
def ofSlots (fr : ArgumentFrame) (ps : List ℕ) : Diathesis n :=
  { fr with links := .ofFn fun i ↦ ((fr.slots.zip ps).find? (·.2 = i.val)).map (·.1) }

/-- The participant occupying a slot, the first if several share it. -/
def participantAt (d : Diathesis n) (s : Slot) : Option (Fin n) :=
  (List.finRange n).find? fun i ↦ d.links.get i = some s

/-- The argument role of a participant, that of its slot. -/
def participantRole (d : Diathesis n) (i : Fin n) : Option ArgumentRole :=
  (d.links.get i).bind d.argumentRole

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
order, and whose participants have the listed profiles; the participants are numbered from 0. -/
def of (frs : List (ArgumentFrame × List ℕ)) (profiles : List (Option EntailmentProfile) := []) :
    Valency :=
  let n := max profiles.length ((frs.flatMap (·.2)).foldr (fun p m ↦ max (p + 1) m) 0)
  ⟨n, .ofFn fun i ↦ profiles[i.val]?.join, frs.map fun x ↦ Diathesis.ofSlots x.1 x.2⟩

/-- The valency of a verb with one diathesis, each slot of its frame holding its own participant
in slot order. -/
def ofFrame (fr : ArgumentFrame) (profiles : List (Option EntailmentProfile) := []) : Valency :=
  of [(fr, List.range fr.slots.length)] profiles

variable (V : Valency)

/-- The basic diathesis, the first. -/
def basic? : Option (Diathesis V.arity) := V.diatheses.head?

/-- The argument frames of the diatheses. -/
def frames : List ArgumentFrame := V.diatheses.map (·.toArgumentFrame)

/-- The entailment profile of the participant in a slot of one of the diatheses. -/
def profileAt (d : Diathesis V.arity) (s : Slot) : Option EntailmentProfile :=
  (d.participantAt s).bind V.profiles.get

@[simp] theorem frames_of (frs : List (ArgumentFrame × List ℕ))
    (ps : List (Option EntailmentProfile)) : (of frs ps).frames = frs.map (·.1) := by
  simp [of, frames, Diathesis.ofSlots, Function.comp_def]

end Verb.Valency
