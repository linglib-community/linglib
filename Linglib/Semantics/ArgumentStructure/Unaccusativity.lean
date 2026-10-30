module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Unaccusativity

An intransitive verb is unaccusative when its sole argument is an underlying object, as with
*arrive*, and unergative when it is an external argument, as with *work*. A recorded voice
[decides](##Verb.isUnaccusative_iff_of_voiceType_eq_some). Without one, Levin and Rappaport Hovav's
linking rules decide: an argument that undergoes a directed change
[is internal](##Verb.isUnaccusative_iff_of_voiceType_eq_none), and one that is the immediate cause
of the eventuality
[is external unless it also undergoes one](##Verb.isUnergative_iff_of_voiceType_eq_none). The two
classifications are [disjoint](##Verb.IsUnergative.not_isUnaccusative).

## Main definitions

* `Verb.Valency.HasCausativeAlternation`: some participant is the object of a plain transitive
  diathesis and the subject of an intransitive one that leaves out the transitive's subject.
* `Verb.HasExternalArgument`: the recorded voice introduces an external argument.
* `Verb.UndergoesDirectedChange`, `Verb.HasImmediateCause`: the conditions of the Directed
  Change and the Immediate Cause Linking Rules, read off an entry.
* `Verb.IsUnaccusative`, `Verb.IsUnergative`: the two classifications.

## Implementation notes

* The two linking conditions are this file's reading of rules stated over meanings. The Immediate
  Cause Linking Rule, "The argument of a verb that denotes the immediate cause of the eventuality
  described by that verb is its external argument" ([levin-hovav-1995] (1), p. 135), is read as a
  sole argument entailed to act volitionally or to cause, Dowty's volition and causation. The
  Directed Change Linking Rule, "The argument of a verb that corresponds to the entity undergoing
  the directed change described by that verb is its direct internal argument" ((24), p. 146), is
  read as the causative alternation, a direction of motion, or a scale along which a verb that is
  not a state measures change (`Verb.changeScale`). The Directed Change rule takes precedence, as
  the book argues (§4.2), so *run* with a directional phrase is unaccusative though its runner
  acts.
* The classifications are not exhaustive: an entry without a voice, a directed change or a
  profile for its sole argument is classified as neither. Unaccusativity asks for no intransitive
  frame, since Japanese *deru* 'exit' is an unaccusative with an *o*-marked path
  (`Studies/Ozaki2026.lean`); unergativity does.
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

/-- The verb's recorded voice introduces an external argument. -/
def HasExternalArgument (v : Verb) : Prop := ∃ vt ∈ v.voiceType, vt.AssignsTheta

instance : DecidablePred HasExternalArgument := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The sole argument of the verb undergoes a directed change, the condition of the Directed
Change Linking Rule: the verb takes part in the causative alternation, or it has an intransitive
frame and lexicalizes a direction of motion or measures change along a scale. -/
def UndergoesDirectedChange (v : Verb) : Prop :=
  v.valency.HasCausativeAlternation ∨ (∃ fr ∈ v.valency.frames, fr.IsIntransitive) ∧
    ((∃ d ∈ v.direction, d ≠ .place) ∨ v.changeScale.isSome)

instance : DecidablePred UndergoesDirectedChange := fun v ↦ by
  unfold UndergoesDirectedChange; infer_instance

/-- The subject of the verb's basic diathesis is the immediate cause of the eventuality, the
condition of the Immediate Cause Linking Rule: it is entailed to act volitionally or to cause. -/
def HasImmediateCause (v : Verb) : Prop :=
  ∃ p ∈ v.slotProfile? .external, ProtoRoleFeature.volition ∈ p ∨ ProtoRoleFeature.causation ∈ p

instance : DecidablePred HasImmediateCause := fun v ↦ by
  unfold HasImmediateCause; infer_instance

/-- The verb is unaccusative when its voice, if recorded, introduces no external argument, and
otherwise when its sole argument undergoes a directed change. -/
def IsUnaccusative (v : Verb) : Prop :=
  match v.voiceType with
  | some vt => ¬ vt.AssignsTheta
  | none => v.UndergoesDirectedChange

instance : DecidablePred IsUnaccusative := fun v ↦ by
  unfold IsUnaccusative; split <;> infer_instance

/-- The verb is unergative when it has an intransitive frame and its voice, if recorded,
introduces an external argument, and otherwise when its sole argument is the immediate cause of
the eventuality and undergoes no directed change. -/
def IsUnergative (v : Verb) : Prop :=
  (∃ fr ∈ v.valency.frames, fr.IsIntransitive) ∧
    match v.voiceType with
    | some vt => vt.AssignsTheta
    | none => ¬ v.UndergoesDirectedChange ∧ v.HasImmediateCause

instance : DecidablePred IsUnergative := fun v ↦ by
  unfold IsUnergative; split <;> infer_instance

variable {v : Verb} {vt : VoiceType}

theorem isUnaccusative_iff_of_voiceType_eq_some (h : v.voiceType = some vt) :
    v.IsUnaccusative ↔ ¬ vt.AssignsTheta := by
  simp only [IsUnaccusative, h]

theorem isUnaccusative_iff_of_voiceType_eq_none (h : v.voiceType = none) :
    v.IsUnaccusative ↔ v.UndergoesDirectedChange := by
  simp only [IsUnaccusative, h]

theorem isUnergative_iff_of_voiceType_eq_some (h : v.voiceType = some vt) :
    v.IsUnergative ↔ (∃ fr ∈ v.valency.frames, fr.IsIntransitive) ∧ vt.AssignsTheta := by
  simp only [IsUnergative, h]

theorem isUnergative_iff_of_voiceType_eq_none (h : v.voiceType = none) :
    v.IsUnergative ↔ (∃ fr ∈ v.valency.frames, fr.IsIntransitive) ∧
      ¬ v.UndergoesDirectedChange ∧ v.HasImmediateCause := by
  simp only [IsUnergative, h]

theorem IsUnergative.hasImmediateCause_of_voiceType_eq_none (h : v.IsUnergative)
    (hv : v.voiceType = none) : v.HasImmediateCause :=
  ((isUnergative_iff_of_voiceType_eq_none hv).1 h).2.2

theorem HasExternalArgument.not_isUnaccusative (h : v.HasExternalArgument) :
    ¬ v.IsUnaccusative := by
  obtain ⟨vt, hvt, ht⟩ := h
  exact fun hu ↦ (isUnaccusative_iff_of_voiceType_eq_some (Option.mem_def.1 hvt)).1 hu ht

theorem IsUnergative.not_isUnaccusative (h : v.IsUnergative) : ¬ v.IsUnaccusative := by
  cases hv : v.voiceType with
  | some vt =>
    exact fun hu ↦ (isUnaccusative_iff_of_voiceType_eq_some hv).1 hu
      ((isUnergative_iff_of_voiceType_eq_some hv).1 h).2
  | none =>
    exact fun hu ↦ ((isUnergative_iff_of_voiceType_eq_none hv).1 h).2.1
      ((isUnaccusative_iff_of_voiceType_eq_none hv).1 hu)

end Verb
