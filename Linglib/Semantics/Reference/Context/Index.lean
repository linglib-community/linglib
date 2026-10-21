/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# Indices of evaluation

An index of evaluation is a world–time pair, the circumstance of evaluation of [kaplan-1989] with
world and temporal coordinates only: a product, with its coordinates named (`Index.world`,
`Index.time`), so that the `Prod` instances and API apply. It is not the Kratzer situation, a
preordered type with parthood, nor the Pearl–Halpern partial valuation (`Causation.Situation`).

## References

* [kaplan-1989]
-/

@[expose] public section

namespace Kaplan

/-- A world–time index of evaluation. -/
abbrev Index (W T : Type*) := W × T

namespace Index

variable {W T : Type*}

/-- The world coordinate. -/
abbrev world (i : Index W T) : W := i.1

/-- The temporal coordinate. -/
abbrev time (i : Index W T) : T := i.2

@[simp] theorem world_mk (w : W) (t : T) : Index.world (w, t) = w := rfl
@[simp] theorem time_mk (w : W) (t : T) : Index.time (w, t) = t := rfl

end Index

end Kaplan
