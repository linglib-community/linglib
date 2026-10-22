/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# The context of utterance

The context of utterance of Kaplan, a tuple of an agent, a world, a time and a position, with the
addressee of Speas and Tenny as a fifth coordinate.

## References

* [kaplan-1989]
* [speas-tenny-2003]
-/

@[expose] public section

namespace Kaplan

/-- A context of utterance has an agent, an addressee, a world, a time and a position. -/
@[ext]
structure Context (W : Type*) (E : Type*) (P : Type*) (T : Type*) where
  /-- The agent, the speaker. -/
  agent : E
  /-- The addressee, the hearer. -/
  addressee : E
  /-- The world. -/
  world : W
  /-- The time. -/
  time : T
  /-- The position, the location. -/
  position : P
  deriving DecidableEq

end Kaplan
