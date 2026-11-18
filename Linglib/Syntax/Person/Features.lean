/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Finset.Lattice.Fold
public import Linglib.Syntax.Person.Category
public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Order.Concept
public import Mathlib.Order.Hom.Lattice

/-!
# Person features

A person feature is a nonempty set of roles, [those it is about](##Person.Feature.roles), and a
participant set bears it when it includes one of them, a property preserved by union:
[participant] holds of the nonempty sets, [speaker] of those containing the speaker and
[addressee] of those containing the addressee. A theory of person selects an inventory of them, and
[the features of an inventory that a participant set bears](##Person.bundle) are its bundle there;
the two features Béjar and Rezac cite from Halle, [participant] and [author], are the inventory
of [participant] and [speaker], on which the second person bears [participant] alone, and Harley
and Ritter's geometry adds [addressee]. The three features tell
[every participant set from every other](##Person.bundle_univ_injective), so the full inventory
sees clusivity and the two-feature one [does not](##Person.toFeatures_coarsen).

[speaker] and [addressee] depend on [participant], being about fewer roles, and
[the bundles closed under that dependency are exactly the closed sets of the
context](##Person.wellFormed_iff_isIntent) of participant sets and features,
[five in all](##Person.card_wellFormed): the third person's empty bundle and Harley and Ritter's
four possibilities under Participant. In a feature geometry dependence generally captures logical
implication, though, as they note of the inclusive and the plural, not every implication is a
dependence; among the person features [the two
coincide](##Person.Feature.le_iff_forall_bears).
[Counting the features of [participant] and [speaker] a value bears](##Person.prominence_le_iff)
is the person hierarchy.

## References

* [halle-1997]
* [bejar-rezac-2009]
* [harley-ritter-2002]
* [harbour-2016]
* [cysouw-2003]
* [zwicky-1977b]
* [corbett-2006]
* [haspelmath-2021]
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
