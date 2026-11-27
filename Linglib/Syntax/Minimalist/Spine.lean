/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Spine.Label

/-!
# The standard clauses

This file defines the spines of the vP, the TP and the CP, the clauses of the verbal spine that are
named for their highest head.

## Main definitions

* `Spine.vP`, `Spine.tP`, `Spine.cP`: the spines `[V, v]`, `[V, v, T]` and `[V, v, T, C]`.

## References

* [wurmbrand-2014]
* [keine-2020]
-/

@[expose] public section

namespace Spine

open Minimalist

/-- The **vP** is the spine `[V, v]`, the small nonfinite clause. -/
def vP : Spine Cat := ⟨[.V, .v]⟩

/-- The **TP** is the spine `[V, v, T]`, the large nonfinite clause. -/
def tP : Spine Cat := ⟨[.V, .v, .T]⟩

/-- The **CP** is the spine `[V, v, T, C]`, the finite clause. -/
def cP : Spine Cat := ⟨[.V, .v, .T, .C]⟩

@[simp] theorem tP_below_T : tP.below .T = vP := by decide

@[simp] theorem cP_below_T : cP.below .T = vP := by decide

@[simp] theorem cP_below_C : cP.below .C = tP := by decide

theorem vP_le_tP : vP ≤ tP := by decide

theorem tP_le_cP : tP ≤ cP := by decide

end Spine
