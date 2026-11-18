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
consonantal and vocalic slots. The positions of the slots of one class are `t.idxsOf .C` and
`t.idxsOf .V`.

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

end Autosegmental
