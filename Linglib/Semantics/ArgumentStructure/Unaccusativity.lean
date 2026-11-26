module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Unaccusativity

An intransitive verb is unaccusative when its sole argument is an underlying object, as with
*arrive*, and unergative when it is an external argument, as with *work*. This file reads two of
Levin and Rappaport Hovav's linking rules off a verb entry. By the Directed Change Linking Rule
an argument that undergoes a directed change is internal, so the verb is unaccusative. By the
Immediate Cause Linking Rule an argument that is the immediate cause of the eventuality is
external, so the verb is unergative, unless the argument also undergoes a directed change. The two
classifications are disjoint, and an entry that records neither condition has neither.

## Main definitions

* `Verb.Valency.HasCausativeAlternation`: some participant is the object of a plain transitive
  diathesis and the subject of an intransitive one that leaves out the transitive's subject.
* `Verb.HasImmediateCause`: the condition of the Immediate Cause Linking Rule, read off an entry.
* `Verb.IsUnaccusative`: the condition of the Directed Change Linking Rule, read off an entry.
* `Verb.IsUnergative`: an intransitive verb with an immediate cause and no directed change.

## Main results

* `Verb.IsUnergative.not_isUnaccusative`: the two classifications are disjoint.

## Implementation notes

* The two linking conditions are this file's reading of rules stated over meanings. The Immediate
  Cause Linking Rule, "The argument of a verb that denotes the immediate cause of the eventuality
  described by that verb is its external argument" ([levin-hovav-1995] (1), p. 135), is read as a
  sole argument entailed to act volitionally or to cause, Dowty's volition and causation. The
  Directed Change Linking Rule, "The argument of a verb that corresponds to the entity undergoing
  the directed change described by that verb is its direct internal argument" ((24), p. 146), is
  read as the causative alternation, a direction of motion, or a scale along which a verb that is
  not a verb of attitude measures change (`Verb.changeScale`). The Directed Change rule takes precedence, as
  the book argues (§4.2), so *run* with a directional phrase is unaccusative though its runner
  acts.
* The classifications are not exhaustive: an entry without a directed change or a profile for its
  sole argument is classified as neither, and no entry stores a classification. A class that a
  reference grammar prints is a list in the language's file, as `Dutch.Verbs.unaccusatives` is.
* The Existence and Default Linking Rules are not read, since no field of an entry says that the
  existence of an argument is asserted or that an argument is not an immediate cause. A verb of
  existence or appearance is therefore classified as neither; `Studies/LevinRappaportHovav1995`
  applies all four rules to Levin's classes.
* Unaccusativity is not read off the perfect auxiliary: German *rennen* 'run' takes *sein* and
  is not unaccusative, and French *rougir* 'redden' alternates and takes *avoir*. A grammar
  that relates the two states its rule against the auxiliaries an entry records
  (`Verb.perfectAuxiliaries`).
* The test does not separate the causative alternation from the causative pairs of verbs of
  emission, *The postman buzzed the doorbell* beside *The doorbell buzzed*, which Levin and
  Rappaport Hovav take to pair two unrelated meanings (§3.2.5).

## References

* [burzio-1986]
* [levin-1993]
* [levin-hovav-1995]
* [dowty-1991]
-/

@[expose] public section

namespace Verb.Valency

variable (V : Valency)

/-- A valency has the causative alternation when some participant is the P of a plain transitive
diathesis and the S of another that leaves out the first one's A, as the thing broken is the object
of transitive *break* and the subject of intransitive *break*. A causative that needs a directional
phrase, *We ran the mouse through the maze* but not *We ran the mouse*, is not the causative
alternation ([levin-1993] p. 31, [levin-hovav-1995] p. 111). -/
def HasCausativeAlternation : Prop :=
  ∃ c ∈ V.diatheses, c.toArgumentFrame = .np ∧ ∃ d ∈ V.diatheses, ∃ i,
    c.participantRole i = some .P ∧ d.participantRole i = some .S ∧
      ∀ j, c.participantRole j = some .A → d.links.get j = none

instance : Decidable V.HasCausativeAlternation :=
  inferInstanceAs (Decidable (∃ c ∈ _, _ ∧ ∃ d ∈ _, ∃ _, _))

end Verb.Valency

namespace Verb

open ArgumentStructure

variable {v : Verb}

/-- The subject of the verb's basic diathesis is the immediate cause of the eventuality, the
condition of the Immediate Cause Linking Rule: it is entailed to act volitionally or to cause. -/
def HasImmediateCause (v : Verb) : Prop :=
  ∃ p ∈ v.slotProfile? .external, ProtoRoleFeature.volition ∈ p ∨ ProtoRoleFeature.causation ∈ p

instance : DecidablePred HasImmediateCause := fun v ↦ by
  unfold HasImmediateCause; infer_instance

/-- The verb is unaccusative when its sole argument undergoes a directed change, the condition of
the Directed Change Linking Rule: the verb takes part in the causative alternation, or it has an
intransitive frame and lexicalizes a direction of motion or measures change along a scale. -/
def IsUnaccusative (v : Verb) : Prop :=
  v.valency.HasCausativeAlternation ∨ (∃ fr ∈ v.valency.frames, fr.IsIntransitive) ∧
    ((∃ d ∈ v.direction, d ≠ .place) ∨ v.changeScale.isSome)

instance : DecidablePred IsUnaccusative := fun v ↦ by
  unfold IsUnaccusative; infer_instance

/-- The verb is unergative when it has an intransitive frame and its sole argument is the
immediate cause of the eventuality and undergoes no directed change. -/
def IsUnergative (v : Verb) : Prop :=
  (∃ fr ∈ v.valency.frames, fr.IsIntransitive) ∧ ¬ v.IsUnaccusative ∧ v.HasImmediateCause

instance : DecidablePred IsUnergative := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem IsUnergative.not_isUnaccusative (h : v.IsUnergative) : ¬ v.IsUnaccusative := h.2.1

theorem IsUnergative.hasImmediateCause (h : v.IsUnergative) : v.HasImmediateCause := h.2.2

theorem IsUnaccusative.not_isUnergative (h : v.IsUnaccusative) : ¬ v.IsUnergative :=
  fun hu ↦ hu.not_isUnaccusative h

end Verb
