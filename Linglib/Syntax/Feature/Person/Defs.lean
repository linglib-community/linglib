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

Pronouns and the verb forms that agree with them come in three persons: English *I am* is first
person, *you are* second and *she is* third. In the traditional description the first person is
that of the speaker, the second that of the addressee and the third that of anyone else. Some
languages have two forms where English has *we*, an *inclusive* one for a group that has the
addressee in it and an *exclusive* one for a group that does not, as Tagalog *tayo* and *kami*.

This file defines the two sets of labels and nothing more.

## Main definitions

* `Person`: first, second or third.
* `Clusivity`: inclusive or exclusive.

## Implementation notes

The traditional description is not part of these definitions. What a label refers to, and the
order of the persons under coordination, in which a first person conjunct makes the whole first
person, are stated in `Syntax/Feature/Person/Participants.lean`, so that a file which uses the
labels alone takes on no claim about referents.

A clusivity is recorded beside a person, as Universal Dependencies records it, and is left
unspecified where a form marks none.

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
