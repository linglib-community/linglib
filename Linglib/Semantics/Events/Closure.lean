/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# Closure of the eventuality argument

A clause denotes a world-indexed predicate of eventualities until some head closes the
eventuality argument existentially. `Event.closure P` is the proposition that some eventuality
satisfies `P`. Accounts differ on the head that closes the argument: mood, an aspect head, or a
head that a clause of full size contains and a smaller one lacks.

## References

* [grano-2024]
* [fusco-sgrizzi-2026]
-/

@[expose] public section

namespace Event

variable {Ev W : Type*} {P Q : W → Ev → Prop} {w : W}

/-- Existential closure of a clause's eventuality argument, yielding a proposition. -/
def closure (P : W → Ev → Prop) (w : W) : Prop := ∃ e, P w e

theorem closure_mono (h : ∀ e, P w e → Q w e) : closure P w → closure Q w :=
  Exists.imp h

end Event
