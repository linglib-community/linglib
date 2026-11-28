/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Complementizer selection of a valency

A valency takes a complementizer when some complement position of its frames does. The
complementizers a verb takes within a language's inventory are read off this relation, so a
language file states a verb's complementizers as a theorem about its frames and the inventory,
and does not list them.

## Main definitions

* `Verb.Valency.Takes`: some complement position takes the complementizer.
* `Verb.Valency.typers`: the complementizers taken within an inventory.

## References

* [noonan-2007]
-/

@[expose] public section

namespace Verb.Valency

variable {V : Verb.Valency} {z : Complementizer}

/-- The valency takes `z` when some complement position of its frames does. -/
def Takes (V : Verb.Valency) (z : Complementizer) : Prop := ∃ p ∈ V.complements, p.Takes z

instance : Decidable (V.Takes z) := inferInstanceAs (Decidable (∃ p ∈ V.complements, _))

/-- The complementizers of an inventory that the valency takes. -/
def typers (V : Verb.Valency) (inv : List Complementizer) : List Complementizer :=
  inv.filter (V.Takes ·)

end Verb.Valency
