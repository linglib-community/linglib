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
# Convex functions and their Fréchet derivative  `[UPSTREAM]`

A convex function on a normed space [lies above](##ConvexOn.apply_sub_le_sub_of_hasFDerivAt) its
tangent at a point where it is differentiable, `f' (y - x) ≤ f y - f x`, so a point where the
derivative vanishes [is a minimum](##ConvexOn.isMinOn_of_hasFDerivAt_zero) on the whole set.
Dually, a concave function [has a maximum](##ConcaveOn.isMaxOn_of_hasFDerivAt_zero) where its
derivative vanishes. The proofs restrict the function to the segment from `x` to `y` and apply
`ConvexOn.le_slope_of_hasDerivAt`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {x y : E}

/-- A convex function lies above its tangent at a point of differentiability. -/
theorem ConvexOn.apply_sub_le_sub_of_hasFDerivAt (hf : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hd : HasFDerivAt f f' x) : f' (y - x) ≤ f y - f x := by
  have hg := hf.comp_affineMap (AffineMap.lineMap x y)
  have hd' : HasDerivAt (fun r : ℝ ↦ f (AffineMap.lineMap x y r)) (f' (y - x)) 0 :=
    HasFDerivAt.comp_hasDerivAt 0 (by simpa using hd) AffineMap.hasDerivAt_lineMap
  simpa [slope_def_field] using
    hg.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simpa) (by simpa) one_pos hd'

/-- A convex function has a minimum where its derivative vanishes. -/
theorem ConvexOn.isMinOn_of_hasFDerivAt_zero (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := fun y hy ↦ by
  simpa using hf.apply_sub_le_sub_of_hasFDerivAt hx hy hd

/-- A concave function lies below its tangent at a point of differentiability. -/
theorem ConcaveOn.sub_le_apply_sub_of_hasFDerivAt (hf : ConcaveOn ℝ s f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasFDerivAt f f' x) : f y - f x ≤ f' (y - x) := by
  have := hf.neg.apply_sub_le_sub_of_hasFDerivAt hx hy hd.neg
  simp only [neg_apply, Pi.neg_apply] at this
  linarith

/-- A concave function has a maximum where its derivative vanishes. -/
theorem ConcaveOn.isMaxOn_of_hasFDerivAt_zero (hf : ConcaveOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMaxOn f s x := fun y hy ↦ by
  simpa using hf.sub_le_apply_sub_of_hasFDerivAt hx hy hd
