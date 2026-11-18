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

The *person* of a form says whether its referents include the speaker and whether they include
the addressee. The *participant set* of a referent is the set of these two roles it includes, so
there are four: neither, the speaker, the addressee, and both.

`Person` is first, second or third. Each covers some participant sets: the third person covers
neither role, the second the addressee alone, and the first the speaker with or without the
addressee. Whether a first person form includes the addressee is its clusivity
(`Syntax/Person/Clusivity.lean`), a feature beside person.

## Main definitions

* `Person`: first, second, third.
* `Person.participantSets`: the participant sets a person covers.
* `Person.ofParticipants`: the person of a participant set, first with the speaker, otherwise
  second with the addressee, otherwise third.
* `Person.IncludesSpeaker`, `Person.IsSAP`: properties of a person, read off the participant
  sets it covers.

## Implementation notes

The impersonal is not a value: it is `none : Option Person`, as the Universal Dependencies tag
`Person=0` is ingested (`Morphology/Word/UD.lean`).

## References

* [harbour-2016]
* [siewierska-2004]
-/

@[expose] public section

/-- Grammatical person: first, second or third. -/
inductive Person where
  /-- The first person, including the speaker. -/
  | first
  /-- The second person, including the addressee and not the speaker. -/
  | second
  /-- The third person, including neither the speaker nor the addressee. -/
  | third
  deriving DecidableEq, Repr, Fintype

namespace Person

open SpeechAct

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

/-! ### Predicates -/

/-- The value includes the speaker when each of its participant sets contains the speaker. -/
def IncludesSpeaker (p : Person) : Prop := ∀ s ∈ p.participantSets, .speaker ∈ s

instance : DecidablePred IncludesSpeaker := fun p ↦
  inferInstanceAs (Decidable (∀ s ∈ p.participantSets, .speaker ∈ s))

/-- A speech-act participant value has only nonempty participant sets. -/
def IsSAP (p : Person) : Prop := ∀ s ∈ p.participantSets, s.Nonempty

instance : DecidablePred IsSAP := fun p ↦
  inferInstanceAs (Decidable (∀ s ∈ p.participantSets, s.Nonempty))

end Person
