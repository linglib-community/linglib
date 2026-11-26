/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical person and clusivity

Grammatical person is the value a form bears: first, second or third. *Clusivity* is the
distinction between an *inclusive* and an *exclusive* form, which languages that have it mark
where English has *we*.

## Main definitions

* `Person`: first, second, third.
* `Clusivity`: inclusive or exclusive.

## Implementation notes

The values are labels: nothing here says what a value refers to, and they carry no order. The
participant sets a value covers, and the order of person resolution, in which a coordination
with a first person conjunct is first person, are in `Syntax/Feature/Person/Participants.lean`:
the order is that of the referents, the person of a referent lying below that of any referent
it is part of.

A clusivity is recorded beside a person, as Universal Dependencies records it, and is left
unspecified where a form marks none. That an inclusive form's referents include the addressee,
and which persons a clusivity narrows, are in `Syntax/Feature/Person/Participants.lean` too.

The impersonal is not a value: it is `none : Option Person`, as the Universal Dependencies tag
`Person=0` is ingested (`Morphology/Word/UD.lean`).

## References

* [cysouw-2003]
* [siewierska-2004]
* [zwicky-1977b]
* [corbett-2006]
-/

@[expose] public section

/-- Grammatical person: first, second or third. -/
inductive Person where
  /-- The first person. -/
  | first
  /-- The second person. -/
  | second
  /-- The third person. -/
  | third
  deriving DecidableEq, Repr, Fintype

/-- Clusivity: inclusive or exclusive. -/
inductive Clusivity where
  /-- The inclusive. -/
  | inclusive
  /-- The exclusive. -/
  | exclusive
  deriving DecidableEq, Repr, Fintype
