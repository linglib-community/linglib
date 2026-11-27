/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct.Role
public import Linglib.Syntax.Feature.Person.Defs
public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Participant sets

Every act of speech has a speaker and an addressee. The *participant set* of a referent is the
set of these two roles it includes: the speaker, the addressee, both or neither. *I* refers to
someone whose participant set is the speaker alone, and an inclusive *we* to a group whose
participant set has both. This file says what the person values and the clusivities refer to,
in terms of participant sets. What the person features refer to is in
`Syntax/Feature/Person/Geometry.lean`.

Each person covers some participant sets: the third person the set with neither role, the
second the addressee alone, and the first the speaker with or without the addressee. A
participant set is covered by exactly one person. The person of a group is the larger of the
persons of its parts, with the first person largest and the third least, so the order of the
persons is the order of person resolution in coordination: *you and I* is first person. Zwicky
proposes this order, and Dalrymple and Kaplan resolve their marker sets by it.

An inclusive form's referents include the addressee and an exclusive form's do not, so a
clusivity narrows the participant sets of a person: with the first person it gives the
inclusive or the exclusive first person.

## Main definitions

* `Person.participantSets p`: the participant sets the person `p` covers.
* `Person.ofParticipants s`: the person of the participant set `s`.
* `Clusivity.Holds c s`: `s` contains the addressee for the inclusive, and does not for the
  exclusive.

## Main results

* `Person.le_iff_exists_subset`: one person lies below another exactly when a referent of the
  first is part of a referent of the second.
* `Person.ofParticipants_union`: the person of a union is the larger of the persons.
* `Person.ne_third_iff_forall_nonempty`: the first and the second person are those of the
  speech-act participants.

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

/-- `ofParticipants` as a map preserving the empty set and unions. -/
@[simps!]
def ofParticipantsHom : SupBotHom (Finset Role) Person :=
  ⟨⟨ofParticipants, ofParticipants_union⟩, ofParticipants_empty⟩

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
