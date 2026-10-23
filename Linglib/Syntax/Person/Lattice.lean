/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Person.Basic

/-!
# The lattice of persons

A person value covers the referents whose participants form one of its participant sets
(`Person.participantSets`). As Zwicky proposes, a
coordination refers to the union of its conjuncts' referents, so its participant sets are the
pairwise unions `⊻` of theirs. Distinct values cover distinct participant sets, so this makes
`Person` a join-semilattice whose join `⊔` is person resolution, with third person at the
bottom. Dalrymple and Kaplan's marker sets are the participant sets of the
quadripartition, and their union is the join (`Person.ofParticipants_union`).

## Main definitions

* the `SemilatticeSup Person` instance: person resolution as the join.

## Main results

* `Person.participantSets_sup`: the participant sets of a join are the pairwise unions.
* `Person.ofParticipants_union`: the person of a union of participant sets is the join of their
  persons.
* `Person.coarsen_eq_iff`: coarsening sends a value to the tripartition value covering it.

## References

* [zwicky-1977b]
* [dalrymple-kaplan-2000]
-/

@[expose] public section

open scoped FinsetFamily

namespace Person

open Finset Discourse

/-! ### Participant sets -/

theorem supClosed_participantSets (p : Person) :
    SupClosed (p.participantSets : Set (Finset Role)) := by
  rw [← sups_eq_self]; cases p <;> decide

/-! ### Resolution -/

/-- In person resolution third person is neutral, the first person unmarked for clusivity
absorbs the exclusive, and any other two distinct values together cover both the speaker and the
addressee. -/
instance : Max Person where
  max
    | .third, p | p, .third => p
    | .first, .firstExclusive | .firstExclusive, .first => .first
    | p, q => if p = q then p else .firstInclusive

@[simp] theorem participantSets_sup (p q : Person) :
    (p ⊔ q).participantSets = p.participantSets ⊻ q.participantSets := by
  revert p q; decide

instance : SemilatticeSup Person :=
  SemilatticeSup.mk'
    (fun _ _ ↦ participantSets_injective <| by simp only [participantSets_sup, sups_comm])
    (fun _ _ _ ↦ participantSets_injective <| by simp only [participantSets_sup, sups_assoc])
    (fun p ↦ participantSets_injective <| by
      rw [participantSets_sup, sups_eq_self]; exact supClosed_participantSets p)

instance : DecidableLE Person := fun p q ↦ inferInstanceAs (Decidable (p ⊔ q = q))

instance : OrderBot Person where
  bot := .third
  bot_le p := show .third ⊔ p = p by cases p <;> rfl

@[simp] theorem bot_eq_third : (⊥ : Person) = .third := rfl

/-! ### The person of a participant set -/

@[simp] theorem ofParticipants_empty : ofParticipants ∅ = ⊥ := rfl

theorem ofParticipants_union (s t : Finset Role) :
    ofParticipants (s ∪ t) = ofParticipants s ⊔ ofParticipants t :=
  participantSets_injective <| by simp

/-! ### Coarsening -/

theorem participantSets_subset_coarsen (p : Person) :
    p.participantSets ⊆ p.coarsen.participantSets := by
  cases p <;> decide

theorem coarsen_eq_iff (p q : Person) :
    p.coarsen = q ↔ q.coarsen = q ∧ p.participantSets ⊆ q.participantSets := by
  revert p q; decide

theorem coarsen_sup (p q : Person) : (p ⊔ q).coarsen = (p.coarsen ⊔ q.coarsen).coarsen := by
  revert p q; decide

end Person
