/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Finset.Lattice.Fold
public import Linglib.Discourse.SpeechAct.Role
public import Linglib.Syntax.Feature.Person.Feature
public import Mathlib.Order.Concept

/-!
# Participant sets

The *participant set* of a referent is the set of speech-act roles it includes: the speaker, the
addressee, both or neither. This file relates the person features to participant sets.
[participant] is about both roles, [speaker] about the speaker and [addressee] about the
addressee, and a participant set bears a feature when it includes a role the feature is about. A
group includes a role as soon as one of its members does, so a union bears a feature exactly when
one of its parts does.

The dependency among the features is then entailment: one feature depends on
another exactly when every participant set that bears the first bears the second. Harley and
Ritter note that in a geometry not every entailment is a dependence; among the person features
the two coincide. The well-formed bundles are exactly those that some family of participant sets
has in common, and with all three features no two participant sets have the same bundle.

## Main definitions

* `Person.Feature.roles`: the roles a feature is about.
* `Person.Bears`: a participant set bears a feature.
* `Person.bundle`: the features of an inventory that a participant set bears, as a map
  preserving unions.

## Main results

* `Person.Feature.le_iff_forall_bears`: dependency is entailment.
* `Person.Feature.exists_roles_eq_iff`: the features are about the nonempty sets of roles.
* `Person.wellFormed_iff_isIntent`: the well-formed bundles are the closed sets of features.
* `Person.bundle_univ_injective`: the three features tell the participant sets apart.

## References

* [halle-1997]
* [bejar-rezac-2009]
* [harley-ritter-2002]
* [harbour-2016]
-/

@[expose] public section

open Finset SpeechAct Order

namespace Person

namespace Feature

/-- The roles a feature is about. -/
def roles : Feature → Finset Role
  | participant => univ
  | speaker => {.speaker}
  | addressee => {.addressee}

@[simp] theorem roles_participant : participant.roles = univ := rfl
@[simp] theorem roles_speaker : speaker.roles = {.speaker} := rfl
@[simp] theorem roles_addressee : addressee.roles = {.addressee} := rfl

theorem roles_injective : Function.Injective roles := by decide

theorem roles_nonempty (f : Feature) : f.roles.Nonempty := by cases f <;> decide

/-- The features are about the nonempty sets of roles, one feature for each. -/
theorem exists_roles_eq_iff {A : Finset Role} : (∃ f : Feature, f.roles = A) ↔ A.Nonempty := by
  revert A; decide

/-- A feature depends on another exactly when it is about fewer roles. -/
theorem le_iff_roles_subset {f g : Feature} : f ≤ g ↔ g.roles ⊆ f.roles := by
  revert f g; decide

end Feature

/-! ### The context of participant sets and features -/

/-- A participant set bears a feature when it includes a role the feature is about:
[participant] when it is nonempty, [speaker] when it contains the speaker and [addressee] when it
contains the addressee. -/
def Bears (s : Finset Role) (f : Feature) : Prop := ¬ Disjoint s f.roles

instance (s : Finset Role) : DecidablePred (Bears s) := fun _ ↦ inferInstanceAs (Decidable (¬ _))

@[simp] theorem bears_participant {s : Finset Role} : Bears s .participant ↔ s.Nonempty := by
  revert s; decide

@[simp] theorem bears_speaker {s : Finset Role} : Bears s .speaker ↔ .speaker ∈ s := by
  simp [Bears]

@[simp] theorem bears_addressee {s : Finset Role} : Bears s .addressee ↔ .addressee ∈ s := by
  simp [Bears]

/-- Bearing a feature is preserved by union, and the empty set bears none. -/
theorem bears_union {s t : Finset Role} {f : Feature} :
    Bears (s ∪ t) f ↔ Bears s f ∨ Bears t f := by
  simp only [Bears, disjoint_union_left, not_and_or]

theorem Bears.participant {s : Finset Role} {f : Feature} (h : Bears s f) :
    Bears s .participant :=
  fun hd ↦ h (hd.mono_right (subset_univ _))

/-- A feature depends on another exactly when bearing it entails bearing the other. -/
theorem Feature.le_iff_forall_bears {f g : Feature} : f ≤ g ↔ ∀ s, Bears s g → Bears s f := by
  revert f g; decide

/-- The features of the inventory `F` a participant set bears, the features about any of its
roles. The bundle of a union is the union of the bundles. -/
def bundle (F : Features) : SupBotHom (Finset Role) Features :=
  supBotLift fun r ↦ F.filter (r ∈ ·.roles)

@[simp] theorem mem_bundle {F : Features} {s : Finset Role} {f : Feature} :
    f ∈ bundle F s ↔ f ∈ F ∧ Bears s f := by
  simp only [bundle, supBotLift_apply, mem_sup, mem_filter, Bears, not_disjoint_iff]
  exact ⟨fun ⟨r, hr, hf, hrf⟩ ↦ ⟨hf, r, hr, hrf⟩, fun ⟨hf, r, hr, hrf⟩ ↦ ⟨r, hr, hf, hrf⟩⟩

/-- The three features tell every participant set from every other. -/
theorem bundle_univ_injective : Function.Injective (bundle univ) := by decide

private theorem mem_upperPolar_lowerPolar (t : Features) (f : Feature) :
    f ∈ upperPolar Bears (lowerPolar Bears (t : Set Feature)) ↔
      ∀ s : Finset Role, (∀ g ∈ t, Bears s g) → Bears s f := by
  simp [mem_upperPolar_iff, mem_lowerPolar_iff]

/-- The bundles closed under dependency are exactly the closed sets of features of the
context. -/
theorem wellFormed_iff_isIntent (t : Features) :
    IsLowerSet (↑t : Set Feature) ↔ IsIntent Bears (t : Set Feature) := by
  rw [isIntent_iff, Set.ext_iff]
  simp only [mem_upperPolar_lowerPolar, Finset.mem_coe]
  revert t; decide

end Person
