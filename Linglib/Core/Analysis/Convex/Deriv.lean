/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Convex.Deriv

/-!
# Convex functions and the Fréchet derivative  `[UPSTREAM]`

Let `f` be convex on a set `s` of a real normed space and differentiable at `x ∈ s` with
derivative `f'`. Then `f` [lies above its tangent](##ConvexOn.apply_sub_le_sub_of_hasFDerivAt) at
`x`: for every `y ∈ s`, `f' (y - x) ≤ f y - f x`. In particular, if `f' = 0` then `x` [is a
minimum](##ConvexOn.isMinOn_of_hasFDerivAt_zero) of `f` on `s`. The same holds for concave
functions with the inequalities reversed.

Mathlib proves these statements for functions `ℝ → ℝ`. The general case follows by restricting
`f` to the segment from `x` to `y`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {x y : E}

/-- If `f` is convex on `s` and differentiable at `x ∈ s`, then it lies above its tangent at `x`:
`f' (y - x) ≤ f y - f x` for every `y ∈ s`. -/
theorem ConvexOn.apply_sub_le_sub_of_hasFDerivAt (hf : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hd : HasFDerivAt f f' x) : f' (y - x) ≤ f y - f x := by
  have hg := hf.comp_affineMap (AffineMap.lineMap x y)
  have hd' : HasDerivAt (fun r : ℝ ↦ f (AffineMap.lineMap x y r)) (f' (y - x)) 0 :=
    HasFDerivAt.comp_hasDerivAt 0 (by simpa using hd) AffineMap.hasDerivAt_lineMap
  simpa [slope_def_field] using
    hg.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simpa) (by simpa) one_pos hd'

/-- If `f` is convex on `s` and its derivative at `x ∈ s` is zero, then `x` is a minimum of `f`
on `s`. -/
theorem ConvexOn.isMinOn_of_hasFDerivAt_zero (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := fun y hy ↦ by
  simpa using hf.apply_sub_le_sub_of_hasFDerivAt hx hy hd

/-- If `f` is concave on `s` and differentiable at `x ∈ s`, then it lies below its tangent at
`x`: `f y - f x ≤ f' (y - x)` for every `y ∈ s`. -/
theorem ConcaveOn.sub_le_apply_sub_of_hasFDerivAt (hf : ConcaveOn ℝ s f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasFDerivAt f f' x) : f y - f x ≤ f' (y - x) := by
  have := hf.neg.apply_sub_le_sub_of_hasFDerivAt hx hy hd.neg
  simp only [neg_apply, Pi.neg_apply] at this
  linarith

/-- If `f` is concave on `s` and its derivative at `x ∈ s` is zero, then `x` is a maximum of `f`
on `s`. -/
theorem ConcaveOn.isMaxOn_of_hasFDerivAt_zero (hf : ConcaveOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMaxOn f s x := fun y hy ↦ by
  simpa using hf.sub_le_apply_sub_of_hasFDerivAt hx hy hd
