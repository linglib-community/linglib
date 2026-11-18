/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Person.Category
public import Linglib.Syntax.Person.System

/-!
# The features of the person values

This file relates the values of `Person` to the person features. A value bears a feature when
every participant set it covers does.

On [participant] and [speaker], the second person bears one feature and the first person two.
[The number of them a value bears](##Person.prominence_le_iff) is the person hierarchy, first
over second over third. These two features
[do not tell the inclusive from the exclusive](##Person.toFeatures_coarsen).

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
@[simp] theorem toFeatures_firstInclusive :
    toFeatures {.participant, .speaker} .firstInclusive = {.participant, .speaker} := by decide
@[simp] theorem toFeatures_firstExclusive :
    toFeatures {.participant, .speaker} .firstExclusive = {.participant, .speaker} := by decide
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

/-- A value with one participant set bears what that set bears. -/
theorem toFeatures_ofParticipants (F : Features) (s : Finset Role) :
    (ofParticipants s).toFeatures F = bundle F s := by
  revert F s; decide

/-- The bundle of a coordination is the union of its conjuncts' bundles. -/
theorem toFeatures_sup (F : Features) (p q : Person) :
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

/-- Without [addressee] the features do not see clusivity. -/
theorem toFeatures_coarsen {F : Features} (hF : .addressee ∉ F) (p : Person) :
    p.coarsen.toFeatures F = p.toFeatures F := by
  revert F p; decide

/-- A value of the standard tripartition covers exactly the participant sets whose [participant]
and [speaker] features are its bundle. -/
theorem mem_participantSets_iff {p : Person} (hp : p.coarsen = p) (s : Finset Role) :
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
@[simp] theorem prominence_firstInclusive : prominence .firstInclusive = 2 := by decide
@[simp] theorem prominence_firstExclusive : prominence .firstExclusive = 2 := by decide
@[simp] theorem prominence_second : prominence .second = 1 := by decide
@[simp] theorem prominence_third : prominence .third = 0 := by decide

/-- Prominence orders values by inclusion of their bundles. -/
theorem prominence_le_iff_subset {p q : Person} :
    p.prominence ≤ q.prominence ↔
      p.toFeatures {.participant, .speaker} ⊆ q.toFeatures {.participant, .speaker} := by
  revert p q; decide

/-- Prominence is the order resolution induces up to clusivity, `p` being at most as prominent as
`q` iff coordinating them gives `q`'s value in the standard tripartition. -/
theorem prominence_le_iff {p q : Person} :
    p.prominence ≤ q.prominence ↔ (p ⊔ q).coarsen = q.coarsen := by
  revert p q; decide

theorem prominence_mono : Monotone prominence := fun p q h ↦
  prominence_le_iff.2 (by rw [sup_eq_right.2 h])

/-! ### The values as cells of two systems -/

section

variable {s t : Finset Role}

/-- The prominence of a participant set's person is its value in the standard tripartition. -/
theorem prominence_ofParticipants (s : Finset Role) :
    (ofParticipants s).prominence = standardTripartition s := by
  revert s; decide

/-- Each class of the standard tripartition is the family of participant sets its person
covers. -/
theorem mem_participantSets_coarsen_ofParticipants :
    t ∈ (ofParticipants s).coarsen.participantSets ↔
      standardTripartition s = standardTripartition t := by
  revert s t; decide

/-- In the standard tripartition, resolution selects the more prominent conjunct. -/
theorem coarsen_ofParticipants_union (s t : Finset Role) :
    (ofParticipants (s ∪ t)).coarsen =
      if (ofParticipants t).prominence ≤ (ofParticipants s).prominence
      then (ofParticipants s).coarsen else (ofParticipants t).coarsen := by
  revert s t; decide

/-- Each class of the system the three features generate is a single participant set, the one
its person of the quadripartition covers. -/
theorem mem_participantSets_ofParticipants {s t : Finset Role} :
    t ∈ (ofParticipants s).participantSets ↔ bundle univ s = bundle univ t := by
  rw [participantSets_ofParticipants, mem_singleton]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (bundle_univ_injective h).symm⟩

/-- Every person value is a cell of one of the two systems: a person of the quadripartition or
the general first person of the standard tripartition. -/
theorem exists_eq_ofParticipants_or_eq_coarsen (p : Person) :
    ∃ s, p = ofParticipants s ∨ p = (ofParticipants s).coarsen := by
  revert p; decide

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

theorem toFeatures_person (F : Features) (c : Category) :
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
