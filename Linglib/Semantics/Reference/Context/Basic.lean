/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct.Role

/-!
# The context of utterance

A context of utterance is a tuple of an agent, an addressee, a world, a time and a position.
Kaplan's contexts have the agent, the time, the position and the world; the addressee is a
coordinate of the contexts of Schlenker and of the work on indexical shift after him, where a
context and an index are tuples of one type. The agent and the addressee are the holders of the
two discourse roles, `Kaplan.Context.holder`.

## References

* [kaplan-1989]
* [schlenker-2003]
* [anand-nevins-2004]
* [deal-2020]
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

namespace Context

variable {W E P T : Type*} (c : Context W E P T)

/-- The holder of a discourse role at a context, the agent for the speaker and the addressee for
the addressee. -/
def holder : SpeechAct.Role → E
  | .speaker => c.agent
  | .addressee => c.addressee

@[simp] theorem holder_speaker : c.holder .speaker = c.agent := rfl
@[simp] theorem holder_addressee : c.holder .addressee = c.addressee := rfl

end Context

end Kaplan
