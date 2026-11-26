/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype

/-!
# Person features

This file defines the three person features, [participant], [speaker] and [addressee], and the
dependency among them: [speaker] and [addressee] each depend on [participant]. A feature
geometry records the dependency, and a bundle of features is well formed when it contains
[participant] whenever it contains either of the others. There are five well-formed bundles, the
empty bundle and Harley and Ritter's four possibilities under Participant.

Theories of person differ in the features they use. Béjar and Rezac, citing Halle, use
[participant] and [author], here [speaker]; Harley and Ritter add [addressee].

## Main definitions

* `Person.Feature`: the three features, ordered by dependency with [participant] least.
* `Person.Features`: a set of features, an inventory or a bundle.

## Main results

* `Person.card_wellFormed`: there are five well-formed bundles.

## Implementation notes

The features are formal objects: nothing here says what a feature is about. Which speech-act
roles each feature concerns, and that the dependency coincides with entailment between features,
is stated in `Syntax/Feature/Person/Participants.lean`, which an account of agreement that
manipulates the features alone does not import.

## References

* [halle-1997]
* [bejar-rezac-2009]
* [harley-ritter-2002]
-/

@[expose] public section

namespace Person

/-- The person features. -/
inductive Feature where
  /-- [participant]. -/
  | participant
  /-- [speaker], [author] in other inventories. -/
  | speaker
  /-- [addressee], [hearer] in other inventories. -/
  | addressee
  deriving DecidableEq, Repr, Fintype

namespace Feature

/-- [speaker] and [addressee] depend on [participant]: `f ≤ g` when `g` depends on `f`. -/
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

end Feature

/-- A set of person features, an inventory or a bundle. -/
abbrev Features := Finset Feature

theorem not_wellFormed_singleton_speaker :
    ¬ IsLowerSet (↑({.speaker} : Features) : Set Feature) := by
  decide

-- (25), (26) [harley-ritter-2002]
theorem card_wellFormed : Fintype.card {t : Features // IsLowerSet (↑t : Set Feature)} = 5 := by
  decide

end Person
