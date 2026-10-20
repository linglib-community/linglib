/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Data.Nat.Notation

/-!
# The CV skeleton

The skeleton is the timing tier of an autosegmental representation, a sequence of slots each
consonantal or vocalic, to which the melodies associate. A prosodic template in McCarthy's
theory of nonconcatenative morphology is a skeleton, and in Strict CV the skeleton alternates
consonantal and vocalic slots.

## Main definitions

* `Slot`: a consonantal or vocalic timing slot.
* `Skeleton`: a sequence of slots, with `Skeleton.cSlots` and `Skeleton.vSlots` the positions of
  its consonantal and vocalic slots.

## References

* [mccarthy-1981]
* [lowenstamm-1996]
-/

@[expose] public section

namespace Autosegmental

/-- A slot of the skeleton is consonantal or vocalic. -/
inductive Slot where
  /-- A consonantal slot. -/
  | C
  /-- A vocalic slot. -/
  | V
  deriving DecidableEq, Repr

/-- A skeleton is a sequence of timing slots. -/
abbrev Skeleton := List Slot

namespace Skeleton

/-- The positions of the consonantal slots, in order. -/
def cSlots (t : Skeleton) : List ℕ := t.findIdxs (· == .C)

/-- The positions of the vocalic slots, in order. -/
def vSlots (t : Skeleton) : List ℕ := t.findIdxs (· == .V)

end Skeleton

end Autosegmental
