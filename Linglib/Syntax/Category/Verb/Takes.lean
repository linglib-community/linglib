/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Verb–complementizer selection

Which complementizers a verb takes: those some frame of the verb takes
(`ArgumentFrame.Takes`). The complementizers of a verb within a language's inventory are read off
this relation, so a language file states a verb's complementizers as a theorem about its frames
and the inventory, and does not list them.

## Main definitions

* `Verb.Takes`: some frame of the verb takes the complementizer.
* `Verb.typers`: the complementizers a verb takes within an inventory.

## References

* [noonan-2007]
-/

@[expose] public section

namespace Verb

variable {v : Verb} {z : Complementizer} {inv : List Complementizer}

/-- The verb takes `z` when some frame does. -/
def Takes (v : Verb) (z : Complementizer) : Prop :=
  ∃ fr ∈ v.valency.frames, fr.Takes z

instance : Decidable (v.Takes z) := inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- A verb taking a complementizer takes a clausal complement. -/
theorem Takes.takesClausal (h : v.Takes z) : v.TakesClausal :=
  h.imp fun _ ⟨hf, ht⟩ ↦ ⟨hf, ht.hasClausal⟩

/-- No verb takes a complementizer restricting nothing, as a converb suffix restricts nothing. -/
theorem not_takes_of_eq_top (hz : z.toSelection = ⊤) : ¬ v.Takes z :=
  fun ⟨_, _, h⟩ ↦ ArgumentFrame.not_takes_of_eq_top hz h

/-- The complementizers `v` takes within a language's inventory. -/
def typers (v : Verb) (inv : List Complementizer) : List Complementizer :=
  inv.filter (v.Takes ·)

@[simp] theorem mem_typers : z ∈ v.typers inv ↔ z ∈ inv ∧ v.Takes z := by
  simp [typers]

end Verb
