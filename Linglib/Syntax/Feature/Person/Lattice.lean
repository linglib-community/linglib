/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Feature.Person.Basic

/-!
# Person resolution

*Person resolution* gives the person of a coordination: *you and I* is first person, and *you
and she* is second person. A coordination refers to the referents of its conjuncts together,
so, as Zwicky proposes, [the unions of their participant sets are among
its own](##Person.participantSets_sups_subset).

Resolution makes `Person` a chain, third below second below first, with resolution as the
larger of two persons. [The person of a union of participant sets is the larger of their
persons](##Person.ofParticipants_union), which is how Dalrymple and Kaplan resolve their marker
sets.

## References

* [zwicky-1977b]
* [dalrymple-kaplan-2000]
-/

@[expose] public section

open scoped FinsetFamily

namespace Person

open Finset SpeechAct

/-! ### Participant sets -/

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

/-! ### Resolution -/

/-- Persons are ordered by resolution: a coordination of a first person with anything is first
person, and of a second with a third is second. -/
instance : LinearOrder Person :=
  LinearOrder.lift' (fun p ↦ OrderDual.toDual p.ctorIdx) (by decide)

instance : OrderBot Person where
  bot := .third
  bot_le := by decide

@[simp] theorem bot_eq_third : (⊥ : Person) = .third := rfl

/-- The unions of the participant sets of two conjuncts are among those of their
coordination. -/
theorem participantSets_sups_subset (p q : Person) :
    p.participantSets ⊻ q.participantSets ⊆ (p ⊔ q).participantSets := by
  revert p q; decide

theorem IsSAP.mono {p q : Person} (hp : p.IsSAP) (h : p ≤ q) : q.IsSAP := by
  revert p q; decide

theorem IncludesSpeaker.mono {p q : Person} (hp : p.IncludesSpeaker) (h : p ≤ q) :
    q.IncludesSpeaker := by
  revert p q; decide

/-! ### The person of a participant set -/

@[simp] theorem ofParticipants_empty : ofParticipants ∅ = ⊥ := rfl

/-- The person of a union of participant sets is the larger of their persons. -/
theorem ofParticipants_union (s t : Finset Role) :
    ofParticipants (s ∪ t) = ofParticipants s ⊔ ofParticipants t := by
  revert s t; decide

end Person
