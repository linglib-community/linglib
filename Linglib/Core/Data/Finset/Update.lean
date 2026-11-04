/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Data.Finset.Update`.
-/
module

public import Mathlib.Data.Finset.Update

/-!
# The range of `Function.updateFinset`

Updating `x` on a finite set `s` reaches exactly the functions that agree with `x` off `s`, so
quantifying over the values on `s` is quantifying over those functions.
-/

public section

namespace Function

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] {x x' : ∀ i, π i} {s : Finset ι}

theorem mem_range_updateFinset_iff : x' ∈ Set.range (updateFinset x s) ↔ ∀ i ∉ s, x' i = x i := by
  refine ⟨?_, fun h ↦ ⟨s.restrict x', funext fun i ↦ ?_⟩⟩
  · rintro ⟨y, rfl⟩ i hi
    simp [updateFinset, hi]
  · by_cases hi : i ∈ s <;> simp [updateFinset, hi, h]

end Function
