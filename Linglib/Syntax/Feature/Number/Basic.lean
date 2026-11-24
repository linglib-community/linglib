/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical number

`Number` is the vocabulary of number values a form carries and agrees in, the labels of
Corbett's typology. A label has no reference of its own: which referents it covers is a matter
of the number system it belongs to, as the plural is whatever the system's other values leave
over, and is stated in `Semantics/Plurality/Cardinality.lean` for the values fixed by a
cardinality and in `Syntax/Feature/Person/Configuration.lean` for the values of a person. The Universal
Dependencies tags that corpora annotate (`Morphology/Word/UD.lean`) lack the general, minimal,
augmented and unit augmented values and add inverse, collective and count categories. The
quadral is excluded, Corbett reanalysing apparent quadrals (Sursurunga, Tangga) as paucals.

A number system is the set of values a language has, a `Finset Number`.

## Main definitions

* `Number`: the number values.
* `Number.elim`: a function on a system of the singular and the plural, by its values at the two.

## References

* [corbett-2000]
* [harbour-2014]
* [grimm-2018]
-/

@[expose] public section

/-- The grammatical number values are those of [corbett-2000]'s typology. -/
inductive Number where
  /-- The general is noncommittal to cardinality and lies outside the number system (Bayso
      *lúban* 'lion(s)', Japanese *inu* 'dog(s)'). It is a form of a noun that has number,
      unlike a noncountable noun, which lacks the contrast ([grimm-2018],
      `Studies/Grimm2018.lean`). -/
  | general
  /-- The singular is for exactly one individual. -/
  | singular
  /-- The dual is for exactly two. -/
  | dual
  /-- The trial is for exactly three. -/
  | trial
  /-- The paucal is for a few, with no fixed upper boundary. -/
  | paucal
  /-- The plural is for more individuals than the system's other values cover, the residual
      value. -/
  | plural
  /-- The greater paucal is for more than the paucal, again with no fixed boundary. -/
  | greaterPaucal
  /-- The greater plural is for an abundance. -/
  | greaterPlural
  /-- The minimal is for the smallest group of its person: one individual, or the speaker and the
      addressee alone in the first person inclusive. -/
  | minimal
  /-- The augmented is for a group larger than the minimal of its person. -/
  | augmented
  /-- The unit augmented is for the minimal group of its person and one more. -/
  | unitAugmented
  /-- The global plural is for every instance in the domain of discourse, tentative in
      [harbour-2014]. -/
  | globalPlural
  deriving DecidableEq, Repr, Fintype

namespace Number

/-- A function on the values of a system of the singular and the plural, by its value at
each. -/
def elim {β : Sort*} (s : Finset Number) (sg pl : β)
    (_h : s = {.singular, .plural} := by decide) (n : s) : β :=
  if n.1 = .plural then pl else sg

variable {β : Sort*} {s : Finset Number} {sg pl : β} {h : s = {.singular, .plural}}

@[simp] theorem elim_singular (hs : .singular ∈ s) : elim s sg pl h ⟨.singular, hs⟩ = sg :=
  rfl

@[simp] theorem elim_plural (hp : .plural ∈ s) : elim s sg pl h ⟨.plural, hp⟩ = pl :=
  rfl

end Number
