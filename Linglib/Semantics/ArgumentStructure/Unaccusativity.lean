module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Unaccusativity

This file defines when a verb entry is unaccusative. An intransitive verb is unaccusative when
its sole argument is an underlying object and no external argument is introduced, as with
*arrive* and *melt*, and unergative otherwise, as with *work*. The classification is read off
the entry's voice where one is recorded, and otherwise off the causative alternation: the
intransitive of a verb that alternates, *the vase broke* beside *Kim broke the vase*, has as its
subject the participant the transitive has as its object.

## Main definitions

* `Verb.Valency.HasCausativeAlternation`: some participant is the object of a plain transitive
  diathesis and the subject of an intransitive one that leaves out the transitive's subject.
* `Verb.IsUnaccusative`: the verb's voice introduces no external argument, or the verb takes
  part in the causative alternation.

## Implementation notes

* Unaccusativity is not read off the perfect auxiliary: German *rennen* 'run' takes *sein* and
  is not unaccusative, and French *rougir* 'redden' alternates and takes *avoir*. A grammar
  that relates the two states its rule against the auxiliaries an entry records
  (`Verb.perfectAuxiliaries`).
* The test does not separate the causative alternation from the causative pairs of verbs of
  emission, *The postman buzzed the doorbell* beside *The doorbell buzzed*, which Levin and
  Rappaport Hovav take to pair two unrelated meanings (§3.2.5).

## References

* [burzio-1986]
* [kratzer-1996]
* [levin-1993]
* [levin-hovav-1995]
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

/-- The verb is unaccusative when its voice, if recorded, introduces no external argument, and
otherwise when it takes part in the causative alternation. -/
def Verb.IsUnaccusative (v : Verb) : Prop :=
  match v.voiceType with
  | some vt => ¬ vt.AssignsTheta
  | none => v.valency.HasCausativeAlternation

instance : DecidablePred Verb.IsUnaccusative := fun v ↦ by
  unfold Verb.IsUnaccusative; split <;> infer_instance
