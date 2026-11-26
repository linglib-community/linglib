/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Finset.Lattice.Fold
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Discourse.SpeechAct.Role
public import Linglib.Syntax.Feature.Person.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Concept

/-!
# The person feature geometry

The *participant set* of a referent is the set of speech-act roles it includes: the speaker, the
addressee, both or neither. This file says what the three person features refer to, in terms of
participant sets, and gives the dependency among them, their geometry.

[participant] is about both roles, [speaker] about the speaker and [addressee] about the
addressee, and a participant set bears a feature when it includes a role the feature is about:
the speaker with the addressee bears all three, and a third party none. A group includes a role
as soon as one of its members does, so a union bears a feature exactly when one of its parts
does.

[speaker] and [addressee] each depend on [participant]: a participant set that bears either
bears [participant]. The dependency is entailment, one feature depending on another exactly when
every participant set that bears the first bears the second. Harley and Ritter note that in a
geometry not every entailment is a dependence; among the person features the two coincide.

A bundle of features is well formed when it contains [participant] whenever it contains either
of the others. There are five well-formed bundles, they are exactly the bundles that some family
of participant sets has in common, and with all three features no two participant sets have the
same bundle.

## Main definitions

* The dependency order on `Feature`, [participant] below [speaker] and [addressee].
* `Feature.roles f`: the roles the feature `f` is about.
* `Bears s f`: the participant set `s` includes a role that `f` is about.
* `bundle F s`: the features of the inventory `F` that `s` bears, as a map preserving unions.

## Main results

* `Feature.le_iff_forall_bears`: dependency is entailment.
* `card_wellFormed`: there are five well-formed bundles.
* `wellFormed_iff_isIntent`: the well-formed bundles are those some family of participant sets
  has in common.
* `bundle_univ_injective`: the three features tell the participant sets apart.

## Implementation notes

The dependency among the features is given here and not with the features, since that [speaker]
and [addressee] depend on [participant], and not the reverse, supposes what the features are
about. It is given by cases, and a theorem states it as entailment between features.

## References

* [halle-1997]
* [bejar-rezac-2009]
* [harley-ritter-2002]
* [harbour-2016]
-/

@[expose] public section

open Finset SpeechAct Order

/-! ### The roles of a feature -/

namespace Person

namespace Feature

/-- [speaker] and [addressee] depend on [participant]: `f ≤ g` when `g` depends on `f`. A
participant set that bears a feature bears every feature it depends on. -/
instance : PartialOrder Feature where
  le f g := f = participant ∨ f = g
  le_refl _ := .inr rfl
  le_trans := by rintro _ _ _ (rfl | rfl) h <;> [exact .inl rfl; exact h]
  le_antisymm := by rintro _ _ (rfl | rfl) (h | h) <;> first | rfl | exact h.symm

theorem le_iff {f g : Feature} : f ≤ g ↔ f = participant ∨ f = g := Iff.rfl

instance : DecidableLE Feature := fun f g ↦ inferInstanceAs (Decidable (f = participant ∨ f = g))

instance : OrderBot Feature where
  bot := participant
  bot_le _ := .inl rfl

@[simp] theorem bot_eq_participant : (⊥ : Feature) = participant := rfl

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

theorem not_wellFormed_singleton_speaker :
    ¬ IsLowerSet (↑({.speaker} : Features) : Set Feature) := by
  decide

-- (25), (26) [harley-ritter-2002]
theorem card_wellFormed : Fintype.card {t : Features // IsLowerSet (↑t : Set Feature)} = 5 := by
  decide

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
