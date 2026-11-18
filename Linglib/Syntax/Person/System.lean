/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Finset.Lattice.Fold
public import Linglib.Syntax.Person.Features

/-!
# Person systems

A person system gives each role a value in a join-semilattice with a bottom and each participant
set the join of its roles' values, `Finset.supBotLift`; its persons are the values it takes, and
the person of a coordination is the join of its conjuncts' persons. Which participant sets a
system identifies [depends only](##Person.forall_sup_eq_iff) on which role's value is the bottom and
on how the two values compare, so the systems number seven, and a linearly ordered one
[identifies the inclusive](##Person.not_injective_sup_of_linearOrder) with the exclusive or with
the second person. Harbour's [standard tripartition](##Person.standardTripartition) ranks the
speaker above the addressee, first with the speaker, otherwise second with the addressee,
otherwise third, Zwicky's correspondence principle; its value is
[the prominence](##Person.prominence_ofParticipants) of the person, so
[resolution in it selects the more prominent conjunct](##Person.coarsen_ofParticipants_union), as
Corbett's resolution rules state. An inventory of person features generates the system whose
person is the bundle, and [every system is so generated](##Person.exists_bundle_eq_iff). The
values of `Person` are the cells of two of these systems:
[the three features](##Person.mem_participantSets_ofParticipants) give the quadripartition and
[[participant] and [speaker]](##Person.bundle_participant_speaker_eq_iff) the standard
tripartition, whose general first person [covers the two clusives](##Person.participantSets_first).

## References

* [harbour-2016]
* [zwicky-1977b]
* [corbett-2006]
-/

@[expose] public section

namespace Person

open SpeechAct Finset

variable {β β' : Type*} [SemilatticeSup β] [OrderBot β] [SemilatticeSup β'] [OrderBot β']
  {s t : Finset Role}

/-! ### Systems -/

private theorem eq_empty_or_singleton_or_univ (s : Finset Role) :
    s = ∅ ∨ s = {.speaker} ∨ s = {.addressee} ∨ s = {.speaker, .addressee} := by
  revert s; decide

/-- Two assignments of values to the roles identify the same participant sets exactly when they
agree on which role's value is the bottom and on how the two values compare. -/
theorem forall_sup_eq_iff (g : Role → β) (g' : Role → β') :
    (∀ s t : Finset Role, s.sup g = t.sup g ↔ s.sup g' = t.sup g') ↔
      (g .speaker = ⊥ ↔ g' .speaker = ⊥) ∧ (g .addressee = ⊥ ↔ g' .addressee = ⊥) ∧
      (g .speaker ≤ g .addressee ↔ g' .speaker ≤ g' .addressee) ∧
      (g .addressee ≤ g .speaker ↔ g' .addressee ≤ g' .speaker) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h {.speaker} ∅
    · simpa using h {.addressee} ∅
    · simpa [sup_insert] using h {.speaker, .addressee} {.addressee}
    · simpa [sup_insert] using h {.speaker, .addressee} {.speaker}
  · rintro ⟨h₁, h₂, h₃, h₄⟩ s t
    have e₁ : g .speaker ⊔ g .addressee = ⊥ ↔ g' .speaker ⊔ g' .addressee = ⊥ := by
      rw [sup_eq_bot_iff, sup_eq_bot_iff, h₁, h₂]
    have e₂ : g .speaker = g .addressee ↔ g' .speaker = g' .addressee := by
      rw [le_antisymm_iff, le_antisymm_iff, h₃, h₄]
    have e₃ : g .speaker ⊔ g .addressee = g .speaker ↔
        g' .speaker ⊔ g' .addressee = g' .speaker := by rw [sup_eq_left, sup_eq_left, h₄]
    have e₄ : g .speaker ⊔ g .addressee = g .addressee ↔
        g' .speaker ⊔ g' .addressee = g' .addressee := by rw [sup_eq_right, sup_eq_right, h₃]
    rcases eq_empty_or_singleton_or_univ s with rfl | rfl | rfl | rfl <;>
      rcases eq_empty_or_singleton_or_univ t with rfl | rfl | rfl | rfl <;>
      simp only [sup_empty, sup_singleton, sup_insert] <;>
      first
        | exact h₁ | exact h₂ | exact e₁ | exact e₂ | exact e₃ | exact e₄
        | exact eq_comm.trans (h₁.trans eq_comm) | exact eq_comm.trans (h₂.trans eq_comm)
        | exact eq_comm.trans (e₁.trans eq_comm) | exact eq_comm.trans (e₂.trans eq_comm)
        | exact eq_comm.trans (e₃.trans eq_comm) | exact eq_comm.trans (e₄.trans eq_comm)

/-- A linearly ordered system gives the inclusive the person of the exclusive or of the second
person. -/
theorem not_injective_sup_of_linearOrder {γ : Type*} [LinearOrder γ] [OrderBot γ]
    (g : Role → γ) : ¬ Function.Injective fun s : Finset Role ↦ s.sup g := by
  intro h
  rcases le_total (g .speaker) (g .addressee) with hle | hle
  · exact absurd (h (show ({.speaker, .addressee} : Finset Role).sup g = sup {.addressee} g by
      simp [sup_insert, hle])) (by decide)
  · exact absurd (h (show ({.speaker, .addressee} : Finset Role).sup g = sup {.speaker} g by
      simp [sup_insert, hle])) (by decide)

/-! ### The standard tripartition -/

/-- The ranking of the roles in which the speaker outranks the addressee. -/
def speakerRank : Role → ℕ
  | .speaker => 2
  | .addressee => 1

/-- The standard tripartition gives a participant set the rank of its highest role: first
person with the speaker, otherwise second with the addressee, otherwise third. -/
def standardTripartition : SupBotHom (Finset Role) ℕ := supBotLift speakerRank

/-- The standard tripartition is generated by the participant and author features. -/
theorem standardTripartition_eq_iff :
    standardTripartition s = standardTripartition t ↔
      (s.Nonempty ↔ t.Nonempty) ∧ (.speaker ∈ s ↔ .speaker ∈ t) := by
  revert s t; decide

/-- The prominence of a participant set's person is its value in the standard tripartition. -/
theorem prominence_ofParticipants (s : Finset Role) :
    (ofParticipants s).prominence = standardTripartition s := by
  revert s; decide

/-- Each class of the standard tripartition is the family of participant sets its person
covers. -/
theorem mem_participantSets_coarsen_ofParticipants :
    t ∈ (ofParticipants s).coarsen.participantSets ↔
      standardTripartition s = standardTripartition t := by
  revert s t; decide

/-- In the standard tripartition, resolution selects the more prominent conjunct. -/
theorem coarsen_ofParticipants_union (s t : Finset Role) :
    (ofParticipants (s ∪ t)).coarsen =
      if (ofParticipants t).prominence ≤ (ofParticipants s).prominence
      then (ofParticipants s).coarsen else (ofParticipants t).coarsen := by
  revert s t; decide

/-! ### The system an inventory generates -/

/-- Two participant sets have the same bundle iff they bear the same features of the inventory. -/
theorem bundle_eq_bundle_iff {F : Features} :
    bundle F s = bundle F t ↔ ∀ f ∈ F, (Bears s f ↔ Bears t f) := by
  simp only [Finset.ext_iff, mem_bundle]
  refine ⟨fun h f hf ↦ ?_, fun h f ↦ ?_⟩
  · simpa only [hf, true_and] using h f
  · by_cases hf : f ∈ F
    · simp only [hf, true_and, h f hf]
    · simp [hf]

private theorem subset_iff_or_exists (a : Finset Role) :
    a = univ ∨ ∃ f : Feature, ∀ s, s ⊆ a ↔ ¬ Bears s f := by
  revert a; decide

/-- Every system is generated by the features it respects: it identifies the participant sets
with the same bundle of them. -/
theorem exists_bundle_eq_iff (g : Role → β) :
    ∃ F : Features, ∀ s t : Finset Role, s.sup g = t.sup g ↔ bundle F s = bundle F t := by
  classical
  refine ⟨univ.filter fun f ↦ ∀ u v : Finset Role, u.sup g = v.sup g → (Bears u f ↔ Bears v f),
    fun s t ↦ ?_⟩
  rw [bundle_eq_bundle_iff]
  refine ⟨fun hst f hf ↦ (mem_filter.mp hf).2 s t hst, fun h ↦ eq_of_forall_ge_iff fun a ↦ ?_⟩
  have key (u : Finset Role) : u.sup g ≤ a ↔ u ⊆ univ.filter fun r ↦ g r ≤ a := by
    simp [Finset.sup_le_iff, subset_iff]
  rw [key, key]
  rcases subset_iff_or_exists (univ.filter fun r ↦ g r ≤ a) with hA | ⟨f, hf⟩
  · simp [hA]
  · rw [hf, hf, not_iff_not]
    refine h f (mem_filter.mpr ⟨mem_univ f, fun u v huv ↦ ?_⟩)
    rw [← not_iff_not, ← hf, ← hf, ← key, ← key, huv]

/-- The standard tripartition is the system [participant] and [speaker] generate. -/
theorem bundle_participant_speaker_eq_iff :
    bundle {.participant, .speaker} s = bundle {.participant, .speaker} t ↔
      standardTripartition s = standardTripartition t := by
  revert s t; decide

/-- Each class of the system the three features generate is a single participant set, the one
its person of the quadripartition covers. -/
theorem mem_participantSets_ofParticipants {s t : Finset Role} :
    t ∈ (ofParticipants s).participantSets ↔ bundle univ s = bundle univ t := by
  rw [participantSets_ofParticipants, mem_singleton]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (bundle_univ_injective h).symm⟩

/-- Every person value is a cell of one of the two systems: a person of the quadripartition or
the general first person of the standard tripartition. -/
theorem exists_eq_ofParticipants_or_eq_coarsen (p : Person) :
    ∃ s, p = ofParticipants s ∨ p = (ofParticipants s).coarsen := by
  revert p; decide

end Person
