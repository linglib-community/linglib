/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Person.Geometry
public import Linglib.Syntax.Feature.Person.Participants
public import Linglib.Syntax.Feature.Person.Valued

/-!
# The participant sets of a valued person feature

Harbour takes the deixis of objects, spaces and paths to be built from the person features: a
demonstrative locates its referent in the vicinity of the referents that have its feature value.
This file gives the participant sets of those referents. The plus value of a feature covers the
participant sets that bear it and the minus value the rest, so [+speaker], the value of English
*this*, covers what the first person does, and [−participant] what the third does.

## Main definitions

* `Person.ValuedFeature.participantSets`: the participant sets a valued feature covers.

## Main results

* `Person.ValuedFeature.participantSets_plus_addressee`: [+addressee] covers the sets of the
  second person and the set of both participants, which [+speaker] covers too.
* `Person.ValuedFeature.participantSets_minus`: the minus value covers what the plus value does
  not.

## Implementation notes

A degree of distance from the referents, as the medial term of a distance-oriented system has, is
not a feature value and is not recorded.

## References

* [harbour-2016]
* [terenghi-2023]
-/

@[expose] public section

open SpeechAct Finset

namespace Person.ValuedFeature

/-- A participant set has a feature value when it bears the feature, for the plus value, or does
not, for the minus value. -/
def Holds : ValuedFeature → Finset Role → Prop
  | ⟨f, .plus⟩, s => Bears s f
  | ⟨f, .minus⟩, s => ¬ Bears s f

instance : (v : ValuedFeature) → DecidablePred v.Holds
  | ⟨f, .plus⟩ => fun s ↦ inferInstanceAs (Decidable (Bears s f))
  | ⟨f, .minus⟩ => fun s ↦ inferInstanceAs (Decidable (¬ Bears s f))

/-- The participant sets a valued feature covers are those that have the value. -/
def participantSets (v : ValuedFeature) : Finset (Finset Role) := univ.filter v.Holds

@[simp] theorem mem_participantSets {v : ValuedFeature} {s : Finset Role} :
    s ∈ v.participantSets ↔ v.Holds s := by
  simp [participantSets]

/-- The minus value of a feature covers the participant sets its plus value does not. -/
theorem participantSets_minus (f : Feature) :
    (⟨f, .minus⟩ : ValuedFeature).participantSets =
      (⟨f, .plus⟩ : ValuedFeature).participantSetsᶜ := by
  ext s; simp [Holds]

theorem participantSets_plus_speaker :
    (⟨.speaker, .plus⟩ : ValuedFeature).participantSets = Person.first.participantSets := by
  decide

theorem participantSets_minus_participant :
    (⟨.participant, .minus⟩ : ValuedFeature).participantSets = Person.third.participantSets := by
  decide

/-- [+addressee] covers the participant sets of the second person and the set of both
participants, which [+speaker] covers too. -/
theorem participantSets_plus_addressee :
    (⟨.addressee, .plus⟩ : ValuedFeature).participantSets =
      Person.second.participantSets ∪ {{.speaker, .addressee}} := by
  decide

end Person.ValuedFeature
