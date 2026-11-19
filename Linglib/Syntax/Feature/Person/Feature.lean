/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Finset.Lattice.Fold
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Discourse.SpeechAct.Role
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Concept

/-!
# Person features

Grammatical person classifies a referent by the speech-act roles it includes, the speaker, the
addressee, both or neither: its participant set. A person feature is about one or both of the
roles, [the roles of the feature](##Person.Feature.roles), and a participant set bears it when it
includes one of them. There are three: [participant] is about both roles, [speaker] about the
speaker and [addressee] about the addressee. A group includes a role as soon as one of its members
does, so [a union bears a feature exactly when one of its parts does](##Person.bears_union).

Theories of person differ in the features they use. Béjar and Rezac, citing Halle, use
[participant] and [author], here [speaker]; Harley and Ritter add [addressee].
[The features of an inventory that a participant set bears](##Person.bundle) are its bundle, and
with all three features [no two participant sets share a bundle](##Person.bundle_univ_injective).

[speaker] and [addressee] each entail [participant], which a feature geometry records as
dependence: a bundle is well formed when it contains [participant] whenever it contains either of
the others. [The well-formed bundles are exactly those that some family of participant sets has
in common](##Person.wellFormed_iff_isIntent), and [there are five](##Person.card_wellFormed), the
empty bundle and Harley and Ritter's four possibilities under Participant. They note that in a
geometry not every entailment is a dependence; among the person features
[the two coincide](##Person.Feature.le_iff_forall_bears).

## References

* [halle-1997]
* [bejar-rezac-2009]
* [harley-ritter-2002]
* [harbour-2016]
-/

@[expose] public section

open Finset SpeechAct Order

namespace Person

/-- A person feature is a nonempty set of roles, those it is about. -/
@[ext]
structure Feature where
  /-- The roles the feature is about. -/
  roles : Finset Role
  nonempty : roles.Nonempty

namespace Feature

theorem roles_injective : Function.Injective roles := fun _ _ ↦ Feature.ext

instance : DecidableEq Feature := fun f g ↦
  decidable_of_iff (f.roles = g.roles) Feature.ext_iff.symm

instance : Fintype Feature :=
  .ofEquiv {A : Finset Role // A.Nonempty}
    ⟨fun A ↦ ⟨A.1, A.2⟩, fun f ↦ ⟨f.1, f.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- [participant] holds of a referent including a speech-act participant. -/
def participant : Feature := ⟨univ, univ_nonempty⟩

/-- [speaker] holds of a referent including the speaker, [author] in other inventories. -/
def speaker : Feature := ⟨{.speaker}, singleton_nonempty _⟩

/-- [addressee] holds of a referent including the addressee, [hearer] in other inventories. -/
def addressee : Feature := ⟨{.addressee}, singleton_nonempty _⟩

@[simp] theorem roles_participant : participant.roles = univ := rfl
@[simp] theorem roles_speaker : speaker.roles = {.speaker} := rfl
@[simp] theorem roles_addressee : addressee.roles = {.addressee} := rfl

@[simp] theorem participant_ne_speaker : participant ≠ speaker := by decide
@[simp] theorem participant_ne_addressee : participant ≠ addressee := by decide
@[simp] theorem speaker_ne_participant : speaker ≠ participant := by decide
@[simp] theorem speaker_ne_addressee : speaker ≠ addressee := by decide
@[simp] theorem addressee_ne_participant : addressee ≠ participant := by decide
@[simp] theorem addressee_ne_speaker : addressee ≠ speaker := by decide

/-- The features are [participant], [speaker] and [addressee]. -/
theorem eq_participant_or_eq_speaker_or_eq_addressee (f : Feature) :
    f = participant ∨ f = speaker ∨ f = addressee := by
  revert f; decide

/-- Case analysis on a feature: it is [participant], [speaker] or [addressee]. -/
@[elab_as_elim, cases_eliminator]
def casesOn' {motive : Feature → Sort*} (f : Feature) (participant : motive participant)
    (speaker : motive speaker) (addressee : motive addressee) : motive f :=
  if hp : f = Feature.participant then hp ▸ participant
  else if hs : f = Feature.speaker then hs ▸ speaker
  else
    have ha : f = Feature.addressee :=
      (f.eq_participant_or_eq_speaker_or_eq_addressee.resolve_left hp).resolve_left hs
    ha ▸ addressee

instance : Repr Feature where
  reprPrec f _ := f.casesOn' "participant" "speaker" "addressee"

/-- [speaker] and [addressee] depend on [participant]: `f ≤ g` when `g` depends on `f`, which is
when `g` is about fewer roles. -/
instance : PartialOrder Feature :=
  PartialOrder.lift (fun f ↦ OrderDual.toDual f.roles) roles_injective

theorem le_iff_roles_subset {f g : Feature} : f ≤ g ↔ g.roles ⊆ f.roles := Iff.rfl

instance : DecidableLE Feature := fun f g ↦ inferInstanceAs (Decidable (g.roles ⊆ f.roles))

instance : OrderBot Feature where
  bot := participant
  bot_le := by decide

end Feature

/-- A set of person features, an inventory or a bundle. -/
abbrev Features := Finset Feature

/-! ### The context of participant sets and features -/

/-- A participant set bears a feature when it includes a role the feature is about:
[participant] when it is nonempty, [speaker] when it contains the speaker and [addressee] when it
contains the addressee. -/
def Bears (s : Finset Role) (f : Feature) : Prop := ¬ Disjoint s f.roles

instance (s : Finset Role) : DecidablePred (Bears s) := fun _ ↦ inferInstanceAs (Decidable (¬ _))

@[simp] theorem bears_participant {s : Finset Role} : Bears s .participant ↔ s.Nonempty := by
  revert s; decide

@[simp] theorem bears_speaker {s : Finset Role} : Bears s .speaker ↔ .speaker ∈ s := by
  simp [Bears, Feature.speaker]

@[simp] theorem bears_addressee {s : Finset Role} : Bears s .addressee ↔ .addressee ∈ s := by
  simp [Bears, Feature.addressee]

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

theorem not_wellFormed_singleton_speaker :
    ¬ IsLowerSet (↑({.speaker} : Features) : Set Feature) := by
  decide

-- (25), (26) [harley-ritter-2002]
theorem card_wellFormed : Fintype.card {t : Features // IsLowerSet (↑t : Set Feature)} = 5 := by
  decide

end Person
