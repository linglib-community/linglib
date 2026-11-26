/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Person.Category
public import Linglib.Syntax.Feature.Person.Partition

/-!
# The features of the person values

A person value bears a feature when every participant set it covers does. On [participant] and
[speaker], the first person bears both, the second bears [participant] alone and the third bears
neither, so the person hierarchy, first over second over third, is inclusion of these bundles.
These two features do not tell the inclusive from the exclusive.

A referential category bears the features its participants bear. Without [addressee] the three
groups that contain the speaker share a bundle.

## Main definitions

* `Person.toFeatures F p`: the features of the inventory `F` that every participant set of `p`
  bears.
* `Category.toFeatures F c`: the features of `F` that the participants of `c` bear.

## Main results

* `Person.toFeatures_subset_toFeatures_iff`: the order of the persons is inclusion of their
  bundles on [participant] and [speaker].
* `Person.toFeatures_ofParticipants`: without [addressee], the person of a participant set
  bears what the set bears.

## References

* [harbour-2016]
* [cysouw-2003]
* [zwicky-1977b]
* [corbett-2006]
* [haspelmath-2021]
-/

@[expose] public section

open Finset SpeechAct Order

namespace Person

/-! ### The bundle of a person value -/

/-- The bundle of a person value in the inventory `F` is the set of features of `F` its
participant sets all bear. -/
def toFeatures (F : Features) (p : Person) : Features :=
  F.filter fun f ↦ ∀ s ∈ p.participantSets, Bears s f

theorem mem_toFeatures {F : Features} {p : Person} {f : Feature} :
    f ∈ p.toFeatures F ↔ f ∈ F ∧ ∀ s ∈ p.participantSets, Bears s f :=
  Finset.mem_filter

@[simp] theorem toFeatures_first :
    toFeatures {.participant, .speaker} .first = {.participant, .speaker} := by decide
@[simp] theorem toFeatures_second :
    toFeatures {.participant, .speaker} .second = {.participant} := by decide
@[simp] theorem toFeatures_third (F : Features) : toFeatures F .third = ∅ := by
  revert F; decide

theorem coe_toFeatures (F : Features) (p : Person) :
    (p.toFeatures F : Set Feature) =
      ↑F ∩ upperPolar Bears (p.participantSets : Set (Finset Role)) := by
  ext f; simp [mem_toFeatures, mem_upperPolar_iff]

theorem toFeatures_eq_inter (F : Features) (p : Person) :
    p.toFeatures F = F ∩ p.toFeatures univ := by
  ext f; simp [mem_toFeatures]

/-- Without [addressee], the person of a participant set bears what the set bears: the features
do not tell the inclusive from the exclusive. -/
theorem toFeatures_ofParticipants {F : Features} (hF : .addressee ∉ F) (s : Finset Role) :
    (ofParticipants s).toFeatures F = bundle F s := by
  revert F s; decide

/-- Without [addressee], the bundle of a coordination is the union of its conjuncts' bundles. -/
theorem toFeatures_sup {F : Features} (hF : .addressee ∉ F) (p q : Person) :
    (p ⊔ q).toFeatures F = p.toFeatures F ∪ q.toFeatures F := by
  revert F p q; decide

theorem toFeatures_wellFormed {F : Features} (hF : IsLowerSet (↑F : Set Feature)) (p : Person) :
    IsLowerSet (↑(p.toFeatures F) : Set Feature) := by
  revert F p; decide

theorem ne_third_iff_participant_mem {p : Person} :
    p ≠ .third ↔ .participant ∈ p.toFeatures univ := by
  revert p; decide

theorem includesSpeaker_iff_speaker {p : Person} :
    p.IncludesSpeaker ↔ .speaker ∈ p.toFeatures univ := by
  revert p; decide

/-- A person covers exactly the participant sets whose [participant] and [speaker] features are
its bundle. -/
theorem mem_participantSets_iff {p : Person} (s : Finset Role) :
    s ∈ p.participantSets ↔
      bundle {.participant, .speaker} s = p.toFeatures {.participant, .speaker} := by
  revert p s; decide

/-- The order of the persons is inclusion of their bundles on [participant] and [speaker]. -/
theorem toFeatures_subset_toFeatures_iff {p q : Person} :
    p.toFeatures {.participant, .speaker} ⊆ q.toFeatures {.participant, .speaker} ↔ p ≤ q := by
  revert p q; decide

/-! ### The features of a referential category -/

namespace Category

variable {c : Category} {F : Features}

/-- The bundle of a category in the inventory `F` is the set of features of `F` its participants
bear. Without [addressee] the features underdetermine the first person complex, whose three
categories share a bundle; the decomposition that distinguishes the exclusive is Harbour's
(`Harbour2016.signOf`). -/
def toFeatures (F : Features) (c : Category) : Features := bundle F c.participants

@[simp] theorem mem_toFeatures {f : Feature} :
    f ∈ c.toFeatures F ↔ f ∈ F ∧ Bears c.participants f :=
  mem_bundle

theorem speaker_mem_toFeatures : .speaker ∈ c.toFeatures univ ↔ c.IncludesSpeaker := by
  simp [IncludesSpeaker]

theorem participant_mem_toFeatures :
    .participant ∈ c.toFeatures univ ↔ c.IncludesSpeaker ∨ c.IncludesAddressee := by
  cases c <;> decide +kernel

/-- Without [addressee], a category bears the features its person does. -/
theorem toFeatures_person (hF : .addressee ∉ F) (c : Category) :
    c.person.toFeatures F = c.toFeatures F := by
  revert F; cases c <;> decide

theorem toFeatures_wellFormed (hF : IsLowerSet (↑F : Set Feature)) (c : Category) :
    IsLowerSet (↑(c.toFeatures F) : Set Feature) := by
  revert F; cases c <;> decide +kernel

/-- A set of categories has a person iff the categories share a bundle of [participant] and
[speaker]. -/
theorem sharedPerson_isSome_iff (s : Finset Category) :
    (sharedPerson s).isSome ↔ s.Nonempty ∧ ∀ c ∈ s, ∀ d ∈ s,
      c.toFeatures {.participant, .speaker} = d.toFeatures {.participant, .speaker} := by
  revert s; decide +kernel

end Category

end Person
