/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Person.Category
public import Linglib.Syntax.Feature.Person.System

/-!
# The features of the person values

This file relates the values of `Person` to the person features. A value bears a feature when
every participant set it covers does.

On [participant] and [speaker], the second person bears one feature and the first person two.
[The number of them a value bears](##Person.prominence_le_iff) is the person hierarchy, first
over second over third, and it is the order of resolution. These two features
[do not tell the inclusive from the exclusive](##Person.toFeatures_ofParticipants), and the
persons are [the classes of the standard
tripartition](##Person.mem_participantSets_ofParticipants).

## Main definitions

* `Person.toFeatures`: the features of an inventory that a value bears.
* `Person.prominence`: the number of [participant] and [speaker] a value bears.
* `Person.Category.toFeatures`: the features a person-number category bears.

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

theorem isSAP_iff_participant {p : Person} : p.IsSAP ↔ .participant ∈ p.toFeatures univ := by
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

/-! ### Prominence

On the features [participant] and [speaker] a bundle is a lower set of a chain, so it is
determined by how many of them it has, and ordering values by that number is the person hierarchy
1 > 2 > 3. It is the order coordination induces up to clusivity: a coordination takes the person
of its most prominent conjunct, as Zwicky's hierarchy of reference and Corbett's resolution rules
state. It is not the only person scale: Zwicky's morphosyntactic hierarchies can order the
participants otherwise, as Algonquian ranks the second person above the first, and the person
scale of Haspelmath's argument coding splits is the binary cut between participants and the rest
(`Person.Class`). -/

/-- The prominence of a value is the number of the features [participant] and [speaker] it bears:
two for the first person, one for the second, none for the third. -/
def prominence (p : Person) : ℕ := (p.toFeatures {.participant, .speaker}).card

@[simp] theorem prominence_first : prominence .first = 2 := by decide
@[simp] theorem prominence_second : prominence .second = 1 := by decide
@[simp] theorem prominence_third : prominence .third = 0 := by decide

/-- Prominence orders values by inclusion of their bundles. -/
theorem prominence_le_iff_subset {p q : Person} :
    p.prominence ≤ q.prominence ↔
      p.toFeatures {.participant, .speaker} ⊆ q.toFeatures {.participant, .speaker} := by
  revert p q; decide

/-- Prominence is the order of resolution: `p` is at most as prominent as `q` iff coordinating
them gives `q`. -/
theorem prominence_le_iff {p q : Person} : p.prominence ≤ q.prominence ↔ p ≤ q := by
  revert p q; decide

theorem prominence_mono : Monotone prominence := fun _ _ h ↦ prominence_le_iff.2 h

/-! ### The persons as the standard tripartition -/

section

variable {s t : Finset Role}

/-- The prominence of a participant set's person is its value in the standard tripartition. -/
theorem prominence_ofParticipants (s : Finset Role) :
    (ofParticipants s).prominence = standardTripartition s := by
  revert s; decide

/-- Each class of the standard tripartition is the family of participant sets its person
covers. -/
theorem mem_participantSets_ofParticipants :
    t ∈ (ofParticipants s).participantSets ↔
      standardTripartition s = standardTripartition t := by
  revert s t; decide

/-- Resolution selects the more prominent conjunct. -/
theorem ofParticipants_union_eq (s t : Finset Role) :
    ofParticipants (s ∪ t) =
      if (ofParticipants t).prominence ≤ (ofParticipants s).prominence
      then ofParticipants s else ofParticipants t := by
  revert s t; decide

end

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
