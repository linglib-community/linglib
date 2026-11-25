/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Verb.Diathesis

/-!
# Voices

A voice relates an initial and a derived diathesis of the same participants. This file defines
the type alone, below the lexical entry of a verb, so that an entry can record what its grammar
says of single voices (`Verb.voices`). The voices themselves, their classification and the
alternations of a verb are in `Syntax/Voice/Basic.lean`.

## Main definitions

* `Voice`: an initial and a derived diathesis, with a pivot and a marker.

## References

* [creissels-2024]
-/

@[expose] public section

/-- A voice relates an initial and a derived diathesis of its participants, privileges a slot of
the derived diathesis as its pivot, and is coded by a marker on the verb; its classification is
computed from the two diatheses. -/
structure Voice where
  /-- The number of participants. -/
  arity : ℕ
  /-- The initial diathesis. -/
  initial : Diathesis arity
  /-- The derived diathesis, which leaves out the participants the voice suppresses. -/
  derived : Diathesis arity
  /-- The syntactically privileged term of the derived construction is by default its first core
  slot (S or A), unless a symmetrical voice selects another, and is `none` for an impersonal
  construction ([creissels-2024] §8.1.7). -/
  pivot : Option ArgumentFrame.Slot := derived.coreSlots.head?
  /-- The morphs (affixes or an auxiliary) coding the voice on the verb, in surface order; empty
      for a zero-marked or an unmarked voice. -/
  marker : List Morphology.Morph := []
  deriving DecidableEq, Repr
