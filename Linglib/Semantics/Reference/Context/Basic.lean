/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct.Role

/-!
# The context of utterance

This file defines contexts of utterance. A context of utterance consists of an agent, an
addressee, a world, a time and a position. The agent is the speaker and the addressee is the
hearer.

For example, when Ann says *I am here now* to Bo in Paris at noon, the agent of the context is
Ann, the addressee is Bo, the position is Paris and the time is noon.

## Main definitions

* `Context W E P T`: the type of contexts with agent and addressee in `E`, world in `W`, time in
  `T` and position in `P`.
* `Context.holder c r`: the agent of `c` if `r` is the speaker role, and the addressee of `c` if
  `r` is the addressee role.

## Implementation notes

Kaplan's contexts have an agent, a time, a position and a world. The addressee is a coordinate of
the contexts of Schlenker and of the later work on indexical shift, where a context and an index
are tuples of one type.

## References

* [kaplan-1989]
* [schlenker-2003]
* [anand-nevins-2004]
* [deal-2020]
-/

@[expose] public section

namespace SpeechAct

/-- A **context of utterance** consists of an agent, an addressee, a world, a time and a
position. -/
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

/-- The **holder** of a discourse role at a context `c` is the agent of `c` for the speaker role
and the addressee of `c` for the addressee role. -/
def holder : SpeechAct.Role → E
  | .speaker => c.agent
  | .addressee => c.addressee

@[simp] theorem holder_speaker : c.holder .speaker = c.agent := rfl
@[simp] theorem holder_addressee : c.holder .addressee = c.addressee := rfl

end Context

end SpeechAct
