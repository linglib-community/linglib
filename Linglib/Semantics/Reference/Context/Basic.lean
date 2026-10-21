/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Index

/-!
# The context of utterance

The context of utterance of [kaplan-1989], a tuple of an agent, a world, a time and a
position, with the addressee of [speas-tenny-2003] as a fifth coordinate. A context is
*proper* when its agent exists at its world (`Context.Proper`), which validates *I exist*, and
*located* when its agent is at its position at its time in its world (`Context.Located`),
which validates *I am here now*. The world and time of a context form its index of evaluation
(`Context.toIndex`), and replacing them by another index (`Context.shiftWorldTime`) is the
shift to an alternative situation that keeps the agent fixed, used to quantify a concept
across a believer's alternatives.

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

/-- The index of evaluation of a context is its world and time. -/
def toIndex : Index W T := ⟨c.world, c.time⟩

/-- Replace the world and time of a context by those of an index, keeping the agent, the
addressee and the position. -/
def shiftWorldTime (s : Index W T) : Context W E P T := { c with world := s.world, time := s.time }

variable (s : Index W T)

@[simp] theorem shiftWorldTime_world : (c.shiftWorldTime s).world = s.world := rfl
@[simp] theorem shiftWorldTime_time : (c.shiftWorldTime s).time = s.time := rfl
@[simp] theorem shiftWorldTime_agent : (c.shiftWorldTime s).agent = c.agent := rfl
@[simp] theorem shiftWorldTime_toIndex : (c.shiftWorldTime s).toIndex = s := rfl

end Context

end Kaplan
