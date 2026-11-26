/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical person

`Person` is the person value a form bears: first, second or third. The values form a chain,
third below second below first, which is the order of *person resolution*: a coordination with
a first person conjunct is first person, and otherwise one with a second person conjunct is
second person.

## Main definitions

* `Person`: first, second, third, ordered by resolution with the third person least.

## Implementation notes

The values are formal: nothing here says what a value refers to. The participant sets a value
covers, and the fact that resolution is the person of a union of referents, are in
`Syntax/Feature/Person/Participants.lean`. Whether a first person form includes the addressee
is its clusivity (`Syntax/Feature/Person/Clusivity.lean`), a feature beside person.

The impersonal is not a value: it is `none : Option Person`, as the Universal Dependencies tag
`Person=0` is ingested (`Morphology/Word/UD.lean`).

## References

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

namespace Person

/-- Persons are ordered by resolution: a coordination of a first person with anything is first
person, and of a second with a third is second. -/
instance : LinearOrder Person :=
  LinearOrder.lift' (fun p ↦ OrderDual.toDual p.ctorIdx) (by decide)

instance : OrderBot Person where
  bot := .third
  bot_le := by decide

@[simp] theorem bot_eq_third : (⊥ : Person) = .third := rfl

end Person
