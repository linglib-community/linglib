/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Discourse.SpeechAct.Role

/-!
# Grammatical person

`Person` names the four persons of Harbour's quadripartition, first exclusive, first inclusive,
second and third, and the general first person `first` into which his standard tripartition
conflates the two clusives (English *we*), the conflation being `Person.coarsen`. A value means
the participant sets its referents can have (`Person.participantSets`),
[one for each person of the quadripartition](##Person.participantSets_eq_singleton_iff) and two
for the general first person, and whether it includes the speaker, is a speech-act participant or
marks clusivity is read off them. The merged cells of the bipartitions and the monopartition are
not values, nor is the impersonal, `none : Option Person` as the Universal Dependencies tag
`Person=0` is ingested (`Morphology/Word/UD.lean`).

## References

* [harbour-2016]
* [siewierska-2004]
-/

@[expose] public section

-- The clusives are [siewierska-2004]'s inclusive and exclusive (pp. 82-83); the Tok Pisin forms
-- and the general first person are [harbour-2016]'s (p. 43).
/-- Grammatical person: the persons of the quadripartition and the general first person of the
standard tripartition. Clusivity is a distinction among persons rather than an orthogonal
feature. -/
inductive Person where
  /-- The general first person, including the speaker whether or not it includes the addressee
  (English *we*). -/
  | first
  /-- The first person including the addressee (Tok Pisin *yumi*). -/
  | firstInclusive
  /-- The first person excluding the addressee (Tok Pisin *mi*). -/
  | firstExclusive
  /-- The second person, including the addressee and not the speaker. -/
  | second
  /-- The third person, including neither the speaker nor the addressee. -/
  | third
  deriving DecidableEq, Repr, Fintype

namespace Person

/-! ### Participant sets

A person value covers the referents whose participants, the speaker and the addressee among them,
form one of its participant sets: `{speaker}` or `{speaker, addressee}` for the general first
person and a single set for each person of the quadripartition. -/

open SpeechAct

/-- `p.participantSets` is the family of participant sets of the referents `p` covers. -/
def participantSets : Person → Finset (Finset Role)
  | .first => {{.speaker}, {.speaker, .addressee}}
  | .firstInclusive => {{.speaker, .addressee}}
  | .firstExclusive => {{.speaker}}
  | .second => {{.addressee}}
  | .third => {∅}

theorem participantSets_injective : Function.Injective participantSets := by decide

@[simp] theorem participantSets_inj {p q : Person} :
    p.participantSets = q.participantSets ↔ p = q :=
  participantSets_injective.eq_iff

theorem participantSets_nonempty (p : Person) : p.participantSets.Nonempty := by
  cases p <;> decide

/-- The quadripartition person of a referent whose participants are `s` is first inclusive with
both, first exclusive with the speaker alone, second with the addressee alone, and third with
neither. -/
def ofParticipants (s : Finset Role) : Person :=
  if .speaker ∈ s then if .addressee ∈ s then .firstInclusive else .firstExclusive
  else if .addressee ∈ s then .second else .third

@[simp] theorem participantSets_ofParticipants (s : Finset Role) :
    (ofParticipants s).participantSets = {s} := by
  unfold ofParticipants
  split_ifs with hS hH hH <;> simp only [participantSets, Finset.singleton_inj] <;>
    ext r <;> cases r <;> simp_all

theorem participantSets_eq_singleton_iff {p : Person} {s : Finset Role} :
    p.participantSets = {s} ↔ p = ofParticipants s := by
  rw [← participantSets_inj, participantSets_ofParticipants]

theorem ofParticipants_injective : Function.Injective ofParticipants := fun s t h ↦ by
  simpa using congrArg participantSets h

/-! ### Predicates -/

/-- The value includes the speaker when each of its participant sets contains the speaker. -/
def IncludesSpeaker (p : Person) : Prop := ∀ s ∈ p.participantSets, .speaker ∈ s

instance : DecidablePred IncludesSpeaker := fun p ↦
  inferInstanceAs (Decidable (∀ s ∈ p.participantSets, .speaker ∈ s))

/-- A speech-act participant value has only nonempty participant sets. -/
def IsSAP (p : Person) : Prop := ∀ s ∈ p.participantSets, s.Nonempty

instance : DecidablePred IsSAP := fun p ↦
  inferInstanceAs (Decidable (∀ s ∈ p.participantSets, s.Nonempty))

/-- The value marks clusivity when it includes the speaker and covers a single participant set,
fixing whether the addressee is included. -/
def MarksClusivity (p : Person) : Prop :=
  IncludesSpeaker p ∧ p.participantSets.card = 1

instance : DecidablePred MarksClusivity := fun p ↦
  inferInstanceAs (Decidable (IncludesSpeaker p ∧ p.participantSets.card = 1))

/-! ### Coarsening

The standard tripartition conflates the clusives into the general first person, so a system
without clusivity gives inclusive and exclusive referents one value, as a system without a dual
gives a dual referent the plural (`Number.coarsen`). -/

/-- `coarsen` conflates the clusives into the general first person and keeps every other
value. -/
def coarsen (p : Person) : Person := if p.MarksClusivity then .first else p

@[simp] theorem coarsen_coarsen (p : Person) : p.coarsen.coarsen = p.coarsen := by
  revert p; decide

theorem coarsen_eq_self_iff {p : Person} : p.coarsen = p ↔ ¬ p.MarksClusivity := by
  revert p; decide

end Person
