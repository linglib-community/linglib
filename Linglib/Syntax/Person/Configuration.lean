/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Person.Category

/-!
# Configurations of a referent

The *configuration* of a referent is the set of speech-act participants it contains together
with the number of its other members. One configuration lies below another when it has a subset
of the participants and no more others, as the configuration of a part lies below that of the
whole. Cysouw's referential categories are the configurations with several others counted
alike: [every configuration but the empty one has exactly one
category](##Person.Configuration.category_eq_some_iff).

A referent with a participant has no others at the least, and one with none has one, so the
smallest configuration with given participants has `Person.Configuration.minimum` others. This
is the logical minimum of Corbett's account of Rembarrnga, two members for the speaker with the
addressee and one otherwise.

## Main definitions

* `Person.Configuration`: the participants of a referent and the number of its others.
* `Person.Configuration.card`: the number of members.
* `Person.Configuration.minimum`: the fewest others beside given participants.
* `Person.Configuration.category`: the referential category of a configuration.
* `Person.Category.ofNumber`: the categories a number label covers in a person's region.

## Implementation notes

The order is the product order on the two fields. No join is given: the configuration of a sum
of two referents depends on the others they share, which a configuration does not record.

## References

* [cysouw-2003]
* [corbett-2000]
-/

@[expose] public section

namespace Person

open SpeechAct

/-- The configuration of a referent: the speech-act participants it contains and the number of
its other members. -/
@[ext]
structure Configuration where
  /-- The speech-act participants the referent contains. -/
  participants : Finset Role
  /-- The number of members that are not participants. -/
  others : ℕ

namespace Configuration

variable {x y : Configuration} {s : Finset Role}

/-- The pair of the participants and the number of others, the injection that induces the
order. -/
def toProd (x : Configuration) : Finset Role × ℕ := (x.participants, x.others)

theorem toProd_injective : Function.Injective toProd := fun _ _ h ↦
  Configuration.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : DecidableEq Configuration := toProd_injective.decidableEq

instance : LE Configuration := ⟨fun x y ↦ x.participants ⊆ y.participants ∧ x.others ≤ y.others⟩

theorem le_def : x ≤ y ↔ x.participants ⊆ y.participants ∧ x.others ≤ y.others := Iff.rfl

instance : DecidableLE Configuration := fun _ _ ↦ decidable_of_iff' _ le_def

instance : PartialOrder Configuration := { PartialOrder.lift toProd toProd_injective with
  le := (· ≤ ·) }

/-- `toProd` as an order embedding. -/
@[simps]
def toProdHom : Configuration ↪o Finset Role × ℕ where
  toFun := toProd
  inj' := toProd_injective
  map_rel_iff' := Iff.rfl

/-- The empty configuration, of no referent, lies below every other. -/
instance : OrderBot Configuration where
  bot := ⟨∅, 0⟩
  bot_le _ := ⟨Finset.empty_subset _, Nat.zero_le _⟩

@[simp] theorem participants_bot : (⊥ : Configuration).participants = ∅ := rfl

@[simp] theorem others_bot : (⊥ : Configuration).others = 0 := rfl

/-- The number of members of a referent with the configuration. -/
def card (x : Configuration) : ℕ := x.participants.card + x.others

theorem eq_bot_iff_card_eq_zero : x = ⊥ ↔ x.card = 0 := by
  simp [Configuration.ext_iff, card]

theorem card_le_card (h : x ≤ y) : x.card ≤ y.card :=
  Nat.add_le_add (Finset.card_le_card h.1) h.2

/-- The fewest others a referent with the participants `s` has: one where it has no participant,
none otherwise. -/
def minimum (s : Finset Role) : ℕ := if s = ∅ then 1 else 0

@[simp] theorem minimum_empty : minimum ∅ = 1 := rfl

theorem minimum_of_nonempty (h : s.Nonempty) : minimum s = 0 := by simp [minimum, h.ne_empty]

/-- A configuration is of some referent exactly when it has at least the minimum of others. -/
theorem ne_bot_iff_minimum_le : x ≠ ⊥ ↔ minimum x.participants ≤ x.others := by
  obtain ⟨s, n⟩ := x
  rcases s.eq_empty_or_nonempty with rfl | h
  · simp [Configuration.ext_iff, Nat.one_le_iff_ne_zero]
  · simp [Configuration.ext_iff, minimum_of_nonempty h, h.ne_empty]

/-- The referential category of a configuration, several others counting alike, and none for
the empty configuration. -/
def category (x : Configuration) : Option Category :=
  match decide (Role.speaker ∈ x.participants), decide (Role.addressee ∈ x.participants),
    x.others with
  | true, true, 0 => some .speakerAddressee
  | true, true, _ + 1 => some .speakerAddresseeOthers
  | true, false, 0 => some .speaker
  | true, false, _ + 1 => some .speakerOthers
  | false, true, 0 => some .addressee
  | false, true, _ + 1 => some .addresseeOthers
  | false, false, 0 => none
  | false, false, 1 => some .other
  | false, false, _ + 2 => some .others

@[simp] theorem category_bot : (⊥ : Configuration).category = none := rfl

/-- The others of a configuration as a category counts them: one or several beside no
participant, none or some beside one. -/
def otherCount (x : Configuration) : ℕ :=
  if x.participants = ∅ then min x.others 2 else min x.others 1

/-- A category is that of a configuration exactly when it has the configuration's participants
and counts its others. -/
theorem category_eq_some_iff {c : Category} :
    x.category = some c ↔
      x ≠ ⊥ ∧ c.participants = x.participants ∧ c.otherCount = x.otherCount := by
  have key : ∀ (m : Fin 3) (s : Finset Role) (c : Category),
      category ⟨s, m⟩ = some c ↔
        (⟨s, m⟩ : Configuration) ≠ ⊥ ∧ c.participants = s ∧
          (c.otherCount : ℕ) = otherCount ⟨s, m⟩ := by
    decide
  obtain ⟨s, n⟩ := x
  rcases n with _ | _ | n
  · exact key 0 s c
  · exact key 1 s c
  · have h1 : category ⟨s, n + 2⟩ = category ⟨s, 2⟩ := by
      simp only [category]; split <;> simp_all
    have h2 : otherCount ⟨s, n + 2⟩ = otherCount ⟨s, 2⟩ := by
      simp only [otherCount]; split_ifs <;> omega
    have h3 : (⟨s, n + 2⟩ : Configuration) ≠ ⊥ ↔ (⟨s, 2⟩ : Configuration) ≠ ⊥ := by
      simp [Configuration.ext_iff]
    rw [h1, h2, h3]
    exact key 2 s c

/-! ### The categories a number label covers -/

/-- The region of the referents whose participants are among `S`. -/
def InRegion (S : Finset (Finset Role)) (x : Configuration) : Prop := x.participants ∈ S ∧ x ≠ ⊥

instance (S : Finset (Finset Role)) : DecidablePred (InRegion S) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The configurations of the region of `S` with at most three others, enough to hold the
referents of each category and of each exact number. -/
def bounded (S : Finset (Finset Role)) : Finset Configuration :=
  ((S ×ˢ Finset.range 4).image fun p ↦ (⟨p.1, p.2⟩ : Configuration)).filter (· ≠ ⊥)

theorem mem_bounded_iff {S : Finset (Finset Role)} :
    x ∈ bounded S ↔ InRegion S x ∧ x.others < 4 := by
  obtain ⟨s, n⟩ := x
  simp only [bounded, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists, mk.injEq, InRegion]
  exact ⟨fun ⟨⟨_, _, ⟨hs, hn⟩, rfl, rfl⟩, hx⟩ ↦ ⟨⟨hs, hx⟩, hn⟩,
    fun ⟨⟨hs, hx⟩, hn⟩ ↦ ⟨⟨s, n, ⟨hs, hn⟩, rfl, rfl⟩, hx⟩⟩

/-- The minimal elements of a finite set of configurations. -/
def minimals (T : Finset Configuration) : Finset Configuration :=
  T.filter fun x ↦ ∀ y ∈ T, y ≤ x → x ≤ y

/-- The minimal configurations with at most three others are the minimal ones of the region,
which have the fewest others their participants allow. -/
theorem mem_minimals_bounded_iff {S : Finset (Finset Role)} :
    x ∈ minimals (bounded S) ↔ Minimal (InRegion S) x := by
  simp only [minimals, Finset.mem_filter, mem_bounded_iff]
  constructor
  · rintro ⟨⟨hx, hlt⟩, hmin⟩
    exact ⟨hx, fun y hy hyx ↦ hmin y ⟨hy, lt_of_le_of_lt hyx.2 hlt⟩ hyx⟩
  · rintro ⟨hx, hmin⟩
    have hle := hmin (y := ⟨x.participants, minimum x.participants⟩)
      ⟨hx.1, ne_bot_iff_minimum_le.2 le_rfl⟩ ⟨subset_rfl, ne_bot_iff_minimum_le.1 hx.2⟩
    have h1 : minimum x.participants ≤ 1 := by unfold minimum; split_ifs <;> omega
    exact ⟨⟨hx, lt_of_le_of_lt (hle.2.trans h1) (by omega)⟩, fun y hy hyx ↦ hmin hy.1 hyx⟩

/-- The configurations of the region of `S` that a number label covers at the least: the exact
numbers by the count of members, the minimal as the smallest referents of the region, the
augmented as the rest and the unit augmented as the smallest of the rest, and the plural and
the approximative numbers as the groups. A system narrows a label further by its other
labels, as the plural excludes two where there is a dual. -/
def covered (S : Finset (Finset Role)) : Number → Finset Configuration
  | .general => bounded S
  | .singular => (bounded S).filter (·.card = 1)
  | .dual => (bounded S).filter (·.card = 2)
  | .trial => (bounded S).filter (·.card = 3)
  | .minimal => minimals (bounded S)
  | .augmented => bounded S \ minimals (bounded S)
  | .unitAugmented => minimals (bounded S \ minimals (bounded S))
  | .plural | .paucal | .greaterPaucal | .greaterPlural | .globalPlural =>
    (bounded S).filter (2 ≤ ·.card)

end Configuration

namespace Category

/-- The categories of the referents in the region of `S` that a number label covers. -/
def ofNumber (S : Finset (Finset Role)) (n : Number) : Finset Category :=
  (Configuration.covered S n).biUnion fun x ↦ x.category.toFinset

/-- The categories a person, an optional clusivity and a number label cover: those of the
referents in the region of the person, narrowed by the clusivity, that the label covers. The
first person without a clusivity is every referent with the speaker, of which the speaker
alone is the smallest; with one, the inclusive has the speaker and the addressee as its
smallest and the exclusive the speaker alone. -/
def ofPersonNumber (p : Person) (cl : Option Clusivity) (n : Number) : Finset Category :=
  ofNumber (Clusivity.restrict cl p.participantSets) n

/-- Every category is recovered from its person and clusivity at some number label. -/
theorem ofPersonNumber_person (c : Category) :
    ∃ n, ofPersonNumber c.person c.clusivity n = {c} := by
  cases c
  · exact ⟨.singular, by decide⟩
  · exact ⟨.singular, by decide⟩
  · exact ⟨.singular, by decide⟩
  · exact ⟨.minimal, by decide⟩
  · exact ⟨.augmented, by decide⟩
  · exact ⟨.plural, by decide⟩
  · exact ⟨.plural, by decide⟩
  · exact ⟨.plural, by decide⟩

/-- A category without others has exactly its participants, so a number label of fixed
cardinality covers it only at that cardinality. -/
theorem exactCard_eq_card_of_mem_ofPersonNumber :
    ∀ p cl n c, c ∈ ofPersonNumber p cl n → c.otherCount = 0 →
      ∀ k ∈ n.exactCard, (k : ℕ) = c.card := by
  decide

/-- No category of a region is both minimal and augmented in it. -/
theorem disjoint_ofNumber_minimal_augmented :
    ∀ S, Disjoint (ofNumber S .minimal) (ofNumber S .augmented) := by
  decide

theorem sharedPerson_ofPersonNumber (p : Person) (cl : Option Clusivity) (n : Number)
    (h : (ofPersonNumber p cl n).Nonempty) : sharedPerson (ofPersonNumber p cl n) = some p := by
  revert h; revert p cl n; decide

theorem sharedNumber_ofPersonNumber_eq_general (p : Person) (cl : Option Clusivity) (n : Number)
    (h : sharedNumber (ofPersonNumber p cl n) = some .general) : n = .general := by
  revert h; revert p cl n; decide

end Category

end Person
