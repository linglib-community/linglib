/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Person.Basic

/-!
# Clusivity

*Clusivity* is the distinction between an *inclusive* form, whose referents include the
addressee, and an *exclusive* form, whose referents do not. Languages with the distinction have
two forms where English has *we*.

A clusivity narrows a person. The first person with the inclusive is
[the inclusive first person](##Clusivity.restrict_inclusive_first), and with the exclusive
[the exclusive first person](##Clusivity.restrict_exclusive_first). A coordination is inclusive
[exactly when one of its conjuncts is](##Clusivity.holds_inclusive_union).

## Main definitions

* `Clusivity`: inclusive or exclusive.
* `Clusivity.Holds`: a participant set satisfies the inclusive when it contains the addressee,
  and the exclusive when it does not.
* `Clusivity.restrict`: the participant sets of a family that satisfy a clusivity, or all of
  them when no clusivity is given.

## Implementation notes

A clusivity is recorded beside a person, as Universal Dependencies records it, and is left
unspecified where a form marks none. The second person with the inclusive covers what the second
person covers, and the second person with the exclusive and the third with the inclusive cover
nothing.

## References

* [cysouw-2003]
* [siewierska-2004]
-/

@[expose] public section

open SpeechAct

/-- Clusivity: whether the referents of a form include the addressee. -/
inductive Clusivity where
  /-- The addressee is included. -/
  | inclusive
  /-- The addressee is excluded. -/
  | exclusive
  deriving DecidableEq, Repr, Fintype

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
