/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Index
public import Linglib.Semantics.Situation.World

/-!
# The index of a situation

A situation has a world and, where situations have times, a time. This file defines the index of
evaluation of a situation, its world paired with its time. Where the time of a part of a situation
is within the time of the situation, a situation and a situation it is part of have indices in one
world whose times are ordered, so parthood of situations is a temporal step between their indices.

## Main definitions

* `Situation.toIndex`: the world and the time of a situation.

## Implementation notes

The time is any monotone map into a preorder, as the run time is into the intervals under
inclusion. An index has no parts, and the worlds of a situation semantics over indices are given
by the world coordinate and not as maximal indices: over a line without endpoints no interval is
maximal.

## References

* [kratzer-1989]
* [kaplan-1989]
-/

@[expose] public section

namespace Situation

open scoped SetRel

variable {S I : Type*} [PartialOrder S] {c : ClosureOperator S} {τ : S → I} {s t : S}

/-- The index of a situation, its world and its time. -/
def toIndex (c : ClosureOperator S) (τ : S → I) (s : S) : Index S I := ⟨c s, τ s⟩

@[simp] theorem world_toIndex (s : S) : (toIndex c τ s).world = c s := rfl

@[simp] theorem time_toIndex (s : S) : (toIndex c τ s).time = τ s := rfl

/-- A situation and a situation it is part of have indices in one world, the time of the first
within the time of the second. -/
theorem toIndex_mem_temporal [Preorder I] (hc : IsWorldMap c) (hτ : Monotone τ) (h : s ≤ t) :
    toIndex c τ s ~[Index.temporal {x : I × I | x.1 ≤ x.2}] toIndex c τ t :=
  ⟨hc.eq_of_le h, hτ h⟩

end Situation
