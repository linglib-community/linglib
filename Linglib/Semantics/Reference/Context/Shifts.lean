/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Tower

/-!
# Standard context shifts

The shifts of `Context` that embedding operators push: an attitude verb makes the holder the
agent and an accessible world the world (`attitudeShift`, [schlenker-2003]), a
sequence-of-tense embedding moves the time to the matrix event time (`temporalShift`,
[von-stechow-2009]), and a counterfactual or subjunctive embedding moves the world alone
(`worldShift`, the modal exclusion of [iatridou-2000]); a Kaplan-compliant English attitude
verb pushes the identity `1`. The lemmas record which coordinates each shift changes and which
it preserves.

## References

* [schlenker-2003]
* [von-stechow-2009]
* [iatridou-2000]
-/

@[expose] public section

namespace Kaplan

variable {W E P T : Type*} (c : Context W E P T)

/-- The attitude shift makes the holder the agent and the attitude world the world, preserving the
addressee, the time and the position. -/
def attitudeShift (holder : E) (attWorld : W) : Function.End (Context W E P T) :=
  fun c ↦ { c with agent := holder, world := attWorld }

/-- The temporal shift moves the time to `newTime` and preserves every other coordinate. -/
def temporalShift (newTime : T) : Function.End (Context W E P T) :=
  fun c ↦ { c with time := newTime }

/-- The world shift moves the world to `newWorld` and preserves every other coordinate. -/
def worldShift (newWorld : W) : Function.End (Context W E P T) :=
  fun c ↦ { c with world := newWorld }

section attitudeShift

variable (holder : E) (attWorld : W)

@[simp] theorem attitudeShift_agent :
    (attitudeShift (P := P) (T := T) holder attWorld c).agent = holder := rfl
@[simp] theorem attitudeShift_world :
    (attitudeShift (P := P) (T := T) holder attWorld c).world = attWorld := rfl
@[simp] theorem attitudeShift_addressee :
    (attitudeShift (P := P) (T := T) holder attWorld c).addressee = c.addressee := rfl
@[simp] theorem attitudeShift_time :
    (attitudeShift (P := P) (T := T) holder attWorld c).time = c.time := rfl
@[simp] theorem attitudeShift_position :
    (attitudeShift (P := P) (T := T) holder attWorld c).position = c.position := rfl

end attitudeShift

section temporalShift

variable (newTime : T)

@[simp] theorem temporalShift_time :
    (temporalShift (W := W) (E := E) (P := P) newTime c).time = newTime := rfl
@[simp] theorem temporalShift_agent :
    (temporalShift (W := W) (E := E) (P := P) newTime c).agent = c.agent := rfl
@[simp] theorem temporalShift_world :
    (temporalShift (W := W) (E := E) (P := P) newTime c).world = c.world := rfl
@[simp] theorem temporalShift_addressee :
    (temporalShift (W := W) (E := E) (P := P) newTime c).addressee = c.addressee := rfl
@[simp] theorem temporalShift_position :
    (temporalShift (W := W) (E := E) (P := P) newTime c).position = c.position := rfl

end temporalShift

section worldShift

variable (newWorld : W)

@[simp] theorem worldShift_world :
    (worldShift (E := E) (P := P) (T := T) newWorld c).world = newWorld := rfl
@[simp] theorem worldShift_agent :
    (worldShift (E := E) (P := P) (T := T) newWorld c).agent = c.agent := rfl
@[simp] theorem worldShift_addressee :
    (worldShift (E := E) (P := P) (T := T) newWorld c).addressee = c.addressee := rfl
@[simp] theorem worldShift_time :
    (worldShift (E := E) (P := P) (T := T) newWorld c).time = c.time := rfl
@[simp] theorem worldShift_position :
    (worldShift (E := E) (P := P) (T := T) newWorld c).position = c.position := rfl

end worldShift

end Kaplan
