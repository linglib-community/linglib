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

Three clauses of the verbal spine are named for their highest head. The **vP** has the verb and
little v, the **TP** adds tense, and the **CP** adds the complementizer. Each is the complement of
the next head up in the larger ones: tense takes the vP as its complement, and the complementizer
takes the TP. A smaller clause projects some of the heads of a larger one and no others.

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
