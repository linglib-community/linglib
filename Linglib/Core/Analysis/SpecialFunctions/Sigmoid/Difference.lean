module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Differences of the logistic function

The difference of the logistic function at two points is a ratio of hyperbolic functions of their
half-difference and their midpoint, as `Real.sin_sub_sin` is for the sine. Of two pairs of points
the same positive distance apart, the pair whose midpoint is nearer zero has the larger
difference.
-/

@[expose] public section

namespace Real

theorem sigmoid_sub_sigmoid (x y : ℝ) :
    sigmoid x - sigmoid y = sinh ((x - y) / 2) / (cosh ((x + y) / 2) + cosh ((x - y) / 2)) := by
  have hx := exp_pos (x / 2)
  have hy := exp_pos (y / 2)
  have ex : exp x = exp (x / 2) ^ 2 := by rw [sq, ← exp_add, add_halves]
  have ey : exp y = exp (y / 2) ^ 2 := by rw [sq, ← exp_add, add_halves]
  simp only [sinh_eq, cosh_eq, sigmoid_def, exp_neg, exp_add, exp_sub, add_div, sub_div, ex, ey]
  field_simp
  ring

theorem sigmoid_sub_sigmoid_lt_sigmoid_sub_sigmoid_iff {x y x' y' : ℝ} (h : x' - y' = x - y)
    (hyx : y < x) :
    sigmoid x' - sigmoid y' < sigmoid x - sigmoid y ↔ |x + y| < |x' + y'| := by
  rw [sigmoid_sub_sigmoid, sigmoid_sub_sigmoid, h,
    div_lt_div_iff_of_pos_left (sinh_pos_iff.2 (by linarith)) (by positivity) (by positivity),
    add_lt_add_iff_right, cosh_lt_cosh, abs_div, abs_div, abs_two,
    div_lt_div_iff_of_pos_right two_pos]

end Real
