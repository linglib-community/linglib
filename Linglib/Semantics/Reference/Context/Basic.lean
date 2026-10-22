/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# The context of utterance

The context of utterance of [kaplan-1989], a tuple of an agent, a world, a time and a
position, with the addressee of [speas-tenny-2003] as a fifth coordinate. A context is
*proper* when its agent exists at its world (`Context.Proper`), which validates *I exist*, and
*located* when its agent is at its position at its time in its world (`Context.Located`),
which validates *I am here now*.

Contexts may also be taken as primitive, with functions returning their coordinates
[schlenker-2011]: Kaplan's tenets in `Reference/Kaplan.lean` take the coordinate projections
as arguments, and `Context` supplies them.

## References

* [kaplan-1989]
* [speas-tenny-2003]
* [schlenker-2011]
-/

@[expose] public section

namespace Kaplan

/-- A context of utterance has an agent, an addressee, a world, a time and a position. -/
@[ext]
structure Context (W : Type*) (E : Type*) (P : Type*) (T : Type*) where
  /-- The agent (speaker) of the context -/
  agent : E
  /-- The addressee (hearer) of the context -/
  addressee : E
  /-- The world of the context -/
  world : W
  /-- The time of the context -/
  time : T
  /-- The position (location) of the context -/
  position : P
  deriving DecidableEq

namespace Context

variable {W E P T : Type*} (c : Context W E P T)

/-- A context is proper when its agent exists at its world. -/
def Proper (exists_ : E → W → Prop) : Prop := exists_ c.agent c.world

/-- A context is located when its agent is at its position at its time in its world. -/
def Located (located : E → P → T → W → Prop) : Prop :=
  located c.agent c.position c.time c.world

end Context

end Kaplan
