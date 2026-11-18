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
  deriving DecidableEq

namespace Configuration

variable {x y : Configuration} {s : Finset Role}

/-- The pair of the participants and the number of others, the injection that induces the
order. -/
def toProd (x : Configuration) : Finset Role × ℕ := (x.participants, x.others)

theorem toProd_injective : Function.Injective toProd := fun _ _ h ↦
  Configuration.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

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

end Configuration

end Person
