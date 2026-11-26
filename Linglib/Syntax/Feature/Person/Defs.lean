/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical person, clusivity and the person features

Languages distinguish three persons, first, second and third, as English *I*, *you* and *she*.
In the traditional description the first person is that of the speaker, the second that of the
addressee and the third that of anyone else. Person is marked on pronouns and on the words that
agree with them, as the verb forms *am*, *are* and *is* are. Some languages have two forms where
English has *we*, an *inclusive* one for a group that has the addressee in it and an *exclusive*
one for a group that does not, as Tagalog *tayo* and *kami*.

Theories that decompose the persons use features: [participant], [speaker], which other
inventories call [author], and [addressee]. Béjar and Rezac, citing Halle, use the first two, and
Harley and Ritter add the third.

This file defines the three sets of labels and nothing more.

## Main definitions

* `Person`: first, second or third.
* `Clusivity`: inclusive or exclusive.
* `Person.Feature`: [participant], [speaker] or [addressee].
* `Person.Features`: a set of features, an inventory or a bundle.

## Implementation notes

The traditional description is not part of these definitions. What a label refers to, the order
of the persons under coordination, in which a first person conjunct makes the whole first
person, and the dependency of [speaker] and [addressee] on [participant] are stated in
`Syntax/Feature/Person/Participants.lean`, so that a file which uses the labels alone takes on
no claim about referents.

A clusivity is recorded beside a person, as Universal Dependencies records it, and is left
unspecified where a form marks none.

The impersonal is not a value: it is `none : Option Person`, as the Universal Dependencies tag
`Person=0` is ingested (`Morphology/Word/UD.lean`).

## References

* [bejar-rezac-2009]
* [cysouw-2003]
* [halle-1997]
* [harley-ritter-2002]
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

namespace Person

/-- The person features. -/
inductive Feature where
  /-- [participant]. -/
  | participant
  /-- [speaker], [author] in other inventories. -/
  | speaker
  /-- [addressee], [hearer] in other inventories. -/
  | addressee
  deriving DecidableEq, Repr, Fintype

/-- A set of person features, an inventory or a bundle. -/
abbrev Features := Finset Feature

end Person
