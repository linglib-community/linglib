/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype

/-!
# Clusivity

*Clusivity* is the distinction between an *inclusive* and an *exclusive* form. Languages with
the distinction have two forms where English has *we*.

## Main definitions

* `Clusivity`: inclusive or exclusive.

## Implementation notes

A clusivity is recorded beside a person, as Universal Dependencies records it, and is left
unspecified where a form marks none. The value is formal: that an inclusive form's referents
include the addressee, and which persons a clusivity narrows, are in
`Syntax/Feature/Person/Participants.lean`.

## References

* [cysouw-2003]
* [siewierska-2004]
-/

@[expose] public section

/-- Clusivity: inclusive or exclusive. -/
inductive Clusivity where
  /-- The inclusive. -/
  | inclusive
  /-- The exclusive. -/
  | exclusive
  deriving DecidableEq, Repr, Fintype
