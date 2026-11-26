/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Finset.Lattice.Fold
public import Linglib.Discourse.SpeechAct.Role
public import Linglib.Syntax.Feature.Person.Defs
public import Linglib.Syntax.Feature.Person.Feature
public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Concept

/-!
# Participant sets

The *participant set* of a referent is the set of speech-act roles it includes: the speaker, the
addressee, both or neither. This file relates the person values, clusivity and the person
features to participant sets.

Each person value covers some participant sets: the third person covers the set with neither
role, the second the addressee alone, and the first the speaker with or without the addressee.
A participant set is covered by exactly one value, its person, and the person of a union is the
larger of the two persons, so the order of resolution is that of coordinated referents, as Zwicky
proposes and as Dalrymple and Kaplan resolve their marker sets. An inclusive form's referents
include the addressee and an exclusive form's do not, so a clusivity narrows the participant
sets of a person: with the first person it gives the inclusive or the exclusive first person.

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

* `Person.participantSets`: the participant sets a person covers.
* `Person.ofParticipants`: the person of a participant set, first with the speaker, otherwise
  second with the addressee, otherwise third.
* The order of person resolution on `Person`, third below second below first.
* `Person.IncludesSpeaker`: each participant set the person covers contains the speaker.
* `Clusivity.Holds`: a participant set satisfies the inclusive when it contains the addressee,
  and the exclusive when it does not.
* `Clusivity.restrict`: the participant sets of a family that satisfy a clusivity, or all of
  them when no clusivity is given.
* `Person.Feature.roles`: the roles a feature is about.
* `Person.Bears`: a participant set bears a feature.
* `Person.bundle`: the features of an inventory that a participant set bears, as a map
  preserving unions.

## Main results

* `Person.mem_participantSets_iff_eq_ofParticipants`: a participant set is covered by its
  person and by no other.
* `Person.le_iff_exists_subset`: one person lies below another exactly when a referent of the
  first is part of a referent of the second.
* `Person.ofParticipants_union`: the person of a union is the larger of the persons.
* `Person.ne_third_iff_forall_nonempty`: the first and the second person are those of the
  speech-act participants, the values whose participant sets are all nonempty.
* `Person.Feature.le_iff_forall_bears`: dependency is entailment.
* `Person.Feature.exists_roles_eq_iff`: the features are about the nonempty sets of roles.
* `Person.wellFormed_iff_isIntent`: the well-formed bundles are the closed sets of features.
* `Person.bundle_univ_injective`: the three features tell the participant sets apart.

## Implementation notes

The second person with the inclusive covers what the second person covers, and the second person
with the exclusive and the third with the inclusive cover nothing.

The order on the person values is given here and not with the values, since it is the order of
their referents. It is computed from the position of a value, and a theorem states it of the
participant sets.

## References

* [zwicky-1977b]
* [dalrymple-kaplan-2000]
* [cysouw-2003]
* [siewierska-2004]
* [halle-1997]
* [bejar-rezac-2009]
* [harley-ritter-2002]
* [harbour-2016]
-/

@[expose] public section

open Finset SpeechAct Order

open scoped FinsetFamily

namespace Person

/-! ### The participant sets of a person -/

/-- `p.participantSets` is the family of participant sets of the referents `p` covers. This is
what the value means, not what every form bearing it refers to: a third person form may be used
of the addressee. -/
def participantSets : Person → Finset (Finset Role)
  | .first => {{.speaker}, {.speaker, .addressee}}
  | .second => {{.addressee}}
  | .third => {∅}

theorem participantSets_injective : Function.Injective participantSets := by decide

@[simp] theorem participantSets_inj {p q : Person} :
    p.participantSets = q.participantSets ↔ p = q :=
  participantSets_injective.eq_iff

theorem participantSets_nonempty (p : Person) : p.participantSets.Nonempty := by
  cases p <;> decide

/-- The person of a referent whose participants are `s`: first with the speaker, otherwise second
with the addressee, otherwise third. -/
def ofParticipants (s : Finset Role) : Person :=
  if .speaker ∈ s then .first else if .addressee ∈ s then .second else .third

theorem supClosed_participantSets (p : Person) :
    SupClosed (p.participantSets : Set (Finset Role)) := by
  rw [← sups_eq_self]; cases p <;> decide

/-- A participant set is covered by its person, and by no other. -/
theorem mem_participantSets_iff_eq_ofParticipants {p : Person} {s : Finset Role} :
    s ∈ p.participantSets ↔ p = ofParticipants s := by
  revert p s; decide

theorem mem_participantSets_ofParticipants_self (s : Finset Role) :
    s ∈ (ofParticipants s).participantSets :=
  mem_participantSets_iff_eq_ofParticipants.2 rfl

theorem ofParticipants_surjective : Function.Surjective ofParticipants := by decide

/-! ### The order of resolution -/

/-- Persons are ordered by resolution: a coordination of a first person with anything is first
person, and of a second with a third is second. The order is that of the referents: one person
lies below another when a referent of the first is part of a referent of the second. -/
instance : LinearOrder Person :=
  LinearOrder.lift' (fun p ↦ OrderDual.toDual p.ctorIdx) (by decide)

instance : OrderBot Person where
  bot := .third
  bot_le := by decide

@[simp] theorem bot_eq_third : (⊥ : Person) = .third := rfl

/-- One person lies below another exactly when some referent the first covers is part of some
referent the second covers. -/
theorem le_iff_exists_subset {p q : Person} :
    p ≤ q ↔ ∃ s ∈ p.participantSets, ∃ t ∈ q.participantSets, s ⊆ t := by
  revert p q; decide

/-- The unions of the participant sets of two conjuncts are among those of their
coordination. -/
theorem participantSets_sups_subset (p q : Person) :
    p.participantSets ⊻ q.participantSets ⊆ (p ⊔ q).participantSets := by
  revert p q; decide

@[simp] theorem ofParticipants_empty : ofParticipants ∅ = ⊥ := rfl

/-- The person of a union of participant sets is the larger of their persons. -/
theorem ofParticipants_union (s t : Finset Role) :
    ofParticipants (s ∪ t) = ofParticipants s ⊔ ofParticipants t := by
  revert s t; decide

/-! ### Predicates -/

/-- The value includes the speaker when each of its participant sets contains the speaker. -/
def IncludesSpeaker (p : Person) : Prop := ∀ s ∈ p.participantSets, .speaker ∈ s

instance : DecidablePred IncludesSpeaker := fun p ↦
  inferInstanceAs (Decidable (∀ s ∈ p.participantSets, .speaker ∈ s))

/-- The first and the second person are those of the speech-act participants: the values whose
participant sets are all nonempty. -/
theorem ne_third_iff_forall_nonempty {p : Person} :
    p ≠ .third ↔ ∀ s ∈ p.participantSets, s.Nonempty := by
  revert p; decide

/-- The first person is the value that includes the speaker. -/
theorem includesSpeaker_iff_eq_first {p : Person} : p.IncludesSpeaker ↔ p = .first := by
  revert p; decide

theorem IncludesSpeaker.mono {p q : Person} (hp : p.IncludesSpeaker) (h : p ≤ q) :
    q.IncludesSpeaker := by
  revert p q; decide

end Person

/-! ### Clusivity -/

namespace Clusivity

variable {s t : Finset Role}

/-- A participant set satisfies the inclusive when it contains the addressee and the exclusive
when it does not. -/
def Holds : Clusivity → Finset Role → Prop
  | inclusive, s => .addressee ∈ s
  | exclusive, s => .addressee ∉ s

instance (c : Clusivity) : DecidablePred c.Holds := fun _ ↦ by
  cases c <;> unfold Holds <;> infer_instance

@[simp] theorem holds_inclusive : inclusive.Holds s ↔ .addressee ∈ s := Iff.rfl

@[simp] theorem holds_exclusive : exclusive.Holds s ↔ .addressee ∉ s := Iff.rfl

/-- A union includes the addressee exactly when one of its parts does. -/
theorem holds_inclusive_union : inclusive.Holds (s ∪ t) ↔ inclusive.Holds s ∨ inclusive.Holds t :=
  Finset.mem_union

/-- A union excludes the addressee exactly when both of its parts do. -/
theorem holds_exclusive_union : exclusive.Holds (s ∪ t) ↔ exclusive.Holds s ∧ exclusive.Holds t :=
  Finset.notMem_union

/-- The participant sets of a family that satisfy a clusivity, all of them where none is
specified. -/
def restrict (c : Option Clusivity) (S : Finset (Finset Role)) : Finset (Finset Role) :=
  S.filter fun s ↦ ∀ c' ∈ c, c'.Holds s

@[simp] theorem mem_restrict {c : Option Clusivity} {S : Finset (Finset Role)} :
    s ∈ restrict c S ↔ s ∈ S ∧ ∀ c' ∈ c, c'.Holds s :=
  Finset.mem_filter

@[simp] theorem restrict_none (S : Finset (Finset Role)) : restrict none S = S := by
  ext s; simp

/-- The first person with the inclusive covers the speaker with the addressee. -/
theorem restrict_inclusive_first :
    restrict (some inclusive) Person.first.participantSets = {{.speaker, .addressee}} := by
  decide

/-- The first person with the exclusive covers the speaker alone. -/
theorem restrict_exclusive_first :
    restrict (some exclusive) Person.first.participantSets = {{.speaker}} := by
  decide

theorem restrict_inclusive_second :
    restrict (some inclusive) Person.second.participantSets = Person.second.participantSets := by
  decide

theorem restrict_exclusive_third :
    restrict (some exclusive) Person.third.participantSets = Person.third.participantSets := by
  decide

theorem restrict_exclusive_second :
    restrict (some exclusive) Person.second.participantSets = ∅ := by
  decide

theorem restrict_inclusive_third :
    restrict (some inclusive) Person.third.participantSets = ∅ := by
  decide

end Clusivity

/-! ### The roles of a feature -/

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
