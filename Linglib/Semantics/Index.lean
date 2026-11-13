/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# Indices of evaluation

An index of evaluation is a world and a time, the circumstance of evaluation of [kaplan-1989] with
world and temporal coordinates only. It is not the Kratzer situation, a preordered type with
parthood, nor the Pearl–Halpern partial valuation (`Causation.Situation`).

## References

* [kaplan-1989]
-/

@[expose] public section

/-- A world and a time of evaluation. -/
@[ext]
structure Index (W T : Type*) where
  /-- The world coordinate. -/
  world : W
  /-- The temporal coordinate. -/
  time : T
  deriving DecidableEq
