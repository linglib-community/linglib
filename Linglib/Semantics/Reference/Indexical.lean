/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Linglib.Semantics.Reference.Context.Basic

/-!
# Indexicals

This file defines the indexicals *I*, *you* and *here*. An indexical is an expression whose value
is a coordinate of the context of utterance: *I* denotes the agent of the context, *you* its
addressee and *here* its position. The value does not depend on the index, so the content of an
indexical at a context is rigid.

For example, when Ann says *I am hungry* to Bo, the content of *I* is Ann at every world.

## Main definitions

* `Indexical.I`: the character `dthat Context.agent`.
* `Indexical.you`: the character `dthat Context.addressee`.
* `Indexical.here`: the character `dthat Context.position`.

## Main results

* `Indexical.isDirectlyReferential_I`: the indexical *I* is directly referential.

## Implementation notes

These are the indexical constants of Kaplan's logic of demonstratives. The file
`Semantics/Reference/Pronoun.lean` gives a personal pronoun a different denotation: a first
person pronoun is a variable whose value is presupposed to include the agent of the context.

## TODO

The relation between these characters and the denotation of a first person pronoun is not stated.

## References

* [kaplan-1989]
-/

@[expose] public section

namespace Indexical

open SpeechAct Character

variable {W E P T V : Type*}

/-- The indexical ***I*** is the character whose value at a context `c` and any index is the agent
of `c`. -/
def I : Character (Context W E P T) V E := dthat Context.agent

/-- The indexical ***you*** is the character whose value at a context `c` and any index is the
addressee of `c`. -/
def you : Character (Context W E P T) V E := dthat Context.addressee

/-- The indexical ***here*** is the character whose value at a context `c` and any index is the
position of `c`. -/
def here : Character (Context W E P T) V P := dthat Context.position

variable (c : Context W E P T) (v : V)

@[simp] theorem I_apply : I c v = c.agent := rfl

@[simp] theorem you_apply : you c v = c.addressee := rfl

@[simp] theorem here_apply : here c v = c.position := rfl

/-- The indexical *I* is directly referential. -/
theorem isDirectlyReferential_I : (I : Character (Context W E P T) V E).IsDirectlyReferential :=
  dthat_isDirectlyReferential _

/-- The indexical *you* is directly referential. -/
theorem isDirectlyReferential_you :
    (you : Character (Context W E P T) V E).IsDirectlyReferential :=
  dthat_isDirectlyReferential _

/-- The indexical *here* is directly referential. -/
theorem isDirectlyReferential_here :
    (here : Character (Context W E P T) V P).IsDirectlyReferential :=
  dthat_isDirectlyReferential _

end Indexical
