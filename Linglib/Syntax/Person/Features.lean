/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Person.Category
public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Order.Concept

/-!
# Bivalent person features

Person decomposes into two features, [participant] and [author], the bivalent system Ackema and
Neeleman trace to Halle. Read on participant sets, [participant] holds of the nonempty ones and
[author] of those containing the speaker, so the participant sets and the features form a formal
context (`Person.Bears`). A value's bundle is the set of features holding of all its participant
sets, its intent in the context. Every set containing the speaker is nonempty, so the closed sets of
features are exactly the lower sets of the chain participant < author: the containment filter
that rules out an author who is no participant is the closure of the context. Harley and Ritter
caution that a geometry encodes morphological dependency, which need not follow logical
implication, so the chain stays a stipulated order, and its coincidence with the closure is a
theorem about person. Two features see the tripartition and not clusivity: a tripartition value
covers exactly the participant sets whose own features are its bundle.

## Main definitions

* `Person.Feature`: the two features, ordered participant < author.
* `Person.Bears`: the features a participant set bears.
* `Person.toFeatures`: the bundle of a person value.
* `Person.prominence`: the top of a value's bundle, the person hierarchy.
* `Person.Category.toFeatures`: the bundle of a referential category.

## Main results

* `Person.wellFormed_iff_isIntent`: the well-formed bundles are the closed sets of the context.
* `Person.card_wellFormed`: there are three well-formed bundles, so no fourth person.
* `Person.mem_participantSets_iff`: a tripartition value covers the participant sets whose
  features are its bundle.
* `Person.toFeatures_sup`: the bundle of a coordination is the union of its conjuncts' bundles.
* `Person.mem_toFeatures_iff`: a value bears exactly the features up to its prominence.
* `Person.prominence_le_iff`: prominence is the order resolution induces up to clusivity.
* `Person.prominence_le_iff_subset`: prominence orders values by inclusion of their bundles.
* `Person.Category.sharedPerson_isSome_iff`: a set of categories has a person iff they share a
  bundle.

## References

* [ackema-neeleman-2018]
* [harley-ritter-2002]
* [harbour-2016]
* [cysouw-2003]
-/

@[expose] public section

open Finset Discourse Order

namespace Person

/-- Person has two features, the author feature depending on the participant feature. -/
inductive Feature where
  /-- [participant] holds of a referent including a speech-act participant. -/
  | participant
  /-- [author] holds of a referent including the speaker. -/
  | author
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places participant below author on the dependency chain. -/
def Feature.rank : Feature → Fin 2
  | .participant => 0
  | .author => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

instance : LocallyFiniteOrderBot Feature := Fintype.toLocallyFiniteOrderBot

/-- A person feature bundle is the set of its positive features. -/
abbrev Features := Finset Feature

/-! ### The context of participant sets and features -/

/-- A participant set bears [participant] when it is nonempty and [author] when it contains the
speaker. -/
def Bears (s : Finset Role) : Feature → Prop
  | .participant => s.Nonempty
  | .author => .speaker ∈ s

instance (s : Finset Role) : DecidablePred (Bears s) := fun f ↦ by
  cases f <;> unfold Bears <;> infer_instance

theorem Bears.participant {s : Finset Role} (h : Bears s .author) : Bears s .participant :=
  ⟨_, h⟩

private theorem mem_upperPolar_lowerPolar (t : Features) (f : Feature) :
    f ∈ upperPolar Bears (lowerPolar Bears (t : Set Feature)) ↔
      ∀ s : Finset Role, (∀ g ∈ t, Bears s g) → Bears s f := by
  simp [mem_upperPolar_iff, mem_lowerPolar_iff]

/-- The bundles passing the containment filter, the lower sets of the chain, are exactly the
closed sets of features of the context. -/
theorem wellFormed_iff_isIntent (t : Features) :
    IsLowerSet (↑t : Set Feature) ↔ IsIntent Bears (t : Set Feature) := by
  rw [isIntent_iff, Set.ext_iff]
  simp only [mem_upperPolar_lowerPolar, Finset.mem_coe]
  revert t; decide

theorem intentClosure_singleton_author :
    intentClosure Bears {Feature.author} = Set.univ := by
  ext f; cases f
  · simp [intentClosure, mem_upperPolar_iff, mem_lowerPolar_iff, Bears]
    exact fun _ h ↦ ⟨_, h⟩
  · simp [intentClosure, mem_upperPolar_iff, mem_lowerPolar_iff, Bears]

theorem not_wellFormed_singleton_author :
    ¬ IsLowerSet (↑({.author} : Features) : Set Feature) := by
  decide

/-- Exactly three bundles pass the containment filter. -/
theorem card_wellFormed : Fintype.card {pf : Features // IsLowerSet (↑pf : Set Feature)} = 3 := by
  rw [Fintype.card_subtype_isLowerSet]; rfl

/-! ### The bundle of a person value -/

/-- The bundle of a person value is the set of features its participant sets all bear. -/
def toFeatures (p : Person) : Features :=
  univ.filter fun f ↦ ∀ s ∈ p.participantSets, Bears s f

theorem coe_toFeatures (p : Person) :
    (p.toFeatures : Set Feature) = upperPolar Bears (p.participantSets : Set (Finset Role)) := by
  ext f; simp [toFeatures, mem_upperPolar_iff]

@[simp] theorem toFeatures_first : toFeatures .first = {.participant, .author} := by decide
@[simp] theorem toFeatures_firstInclusive :
    toFeatures .firstInclusive = {.participant, .author} := by decide
@[simp] theorem toFeatures_firstExclusive :
    toFeatures .firstExclusive = {.participant, .author} := by decide
@[simp] theorem toFeatures_second : toFeatures .second = {.participant} := by decide
@[simp] theorem toFeatures_third : toFeatures .third = ∅ := by decide

@[simp] theorem toFeatures_coarsen (p : Person) : p.coarsen.toFeatures = p.toFeatures := by
  cases p <;> decide

/-- The bundle of a coordination is the union of its conjuncts' bundles. -/
theorem toFeatures_sup (p q : Person) : (p ⊔ q).toFeatures = p.toFeatures ∪ q.toFeatures := by
  revert p q; decide

theorem toFeatures_wellFormed (p : Person) : IsLowerSet (↑p.toFeatures : Set Feature) := by
  revert p; decide

theorem isSAP_iff_participant {p : Person} : p.IsSAP ↔ .participant ∈ p.toFeatures := by
  revert p; decide

theorem includesSpeaker_iff_author {p : Person} : p.IncludesSpeaker ↔ .author ∈ p.toFeatures := by
  revert p; decide

/-- A tripartition value covers exactly the participant sets whose features are its bundle, the
sets in the domain of its bundle and in no domain of a more specified one. -/
theorem mem_participantSets_iff {p : Person} (hp : p.coarsen = p) (s : Finset Role) :
    s ∈ p.participantSets ↔ univ.filter (Bears s) = p.toFeatures := by
  revert p s; decide

theorem coarsen_ofParticipants_eq_iff (s t : Finset Role) :
    (ofParticipants s).coarsen = (ofParticipants t).coarsen ↔
      univ.filter (Bears s) = univ.filter (Bears t) := by
  revert s t; decide

/-! ### Prominence

A bundle is a lower set of the chain participant < author, so it is determined by its top
feature, and ordering values by their tops is the person hierarchy 1 > 2 > 3. It is the order
coordination induces up to clusivity: a coordination takes the person of its most prominent
conjunct, as Zwicky's hierarchy of reference and Corbett's resolution rules state. -/

/-- The prominence of a value is the top feature of its bundle: [author] for the first person,
[participant] for the second, none for the third. -/
def prominence (p : Person) : WithBot Feature := p.toFeatures.max

@[simp] theorem prominence_first : prominence .first = Feature.author := by decide
@[simp] theorem prominence_firstInclusive : prominence .firstInclusive = Feature.author := by
  decide
@[simp] theorem prominence_firstExclusive : prominence .firstExclusive = Feature.author := by
  decide
@[simp] theorem prominence_second : prominence .second = Feature.participant := by decide
@[simp] theorem prominence_third : prominence .third = ⊥ := by decide

/-- A value bears exactly the features up to its prominence. -/
theorem mem_toFeatures_iff {p : Person} {f : Feature} : f ∈ p.toFeatures ↔ ↑f ≤ p.prominence := by
  revert p f; decide

/-- Prominence orders values by inclusion of their bundles. -/
theorem prominence_le_iff_subset {p q : Person} :
    p.prominence ≤ q.prominence ↔ p.toFeatures ⊆ q.toFeatures := by
  revert p q; decide

/-- Prominence is the order resolution induces up to clusivity, `p` being at most as prominent as
`q` iff coordinating them gives `q`'s tripartition value. -/
theorem prominence_le_iff {p q : Person} :
    p.prominence ≤ q.prominence ↔ (p ⊔ q).coarsen = q.coarsen := by
  revert p q; decide

/-! ### The features of a referential category -/

namespace Category

variable {c : Category}

/-- The bundle of a category is the set of features its participants bear. The features
underdetermine the first person complex, whose three categories share a bundle; the
decomposition that distinguishes the exclusive is Harbour's (`Studies.Harbour2016.signOf`). -/
def toFeatures (c : Category) : Features := univ.filter (Bears c.participants)

@[simp] theorem mem_toFeatures {f : Feature} : f ∈ c.toFeatures ↔ Bears c.participants f := by
  simp [toFeatures]

@[simp] theorem author_mem_toFeatures : .author ∈ c.toFeatures ↔ c.IncludesSpeaker := by
  simp [Bears, IncludesSpeaker]

@[simp] theorem participant_mem_toFeatures :
    .participant ∈ c.toFeatures ↔ c.IncludesSpeaker ∨ c.IncludesAddressee := by
  cases c <;> decide +kernel

theorem toFeatures_person (c : Category) : c.person.toFeatures = c.toFeatures := by
  cases c <;> decide

theorem toFeatures_wellFormed (c : Category) : IsLowerSet (↑c.toFeatures : Set Feature) := by
  cases c <;> decide +kernel

/-- A set of categories has a person iff the categories share a bundle. -/
theorem sharedPerson_isSome_iff (s : Finset Category) :
    (sharedPerson s).isSome ↔ s.Nonempty ∧ ∀ c ∈ s, ∀ d ∈ s, c.toFeatures = d.toFeatures := by
  revert s; decide +kernel

end Category

end Person
