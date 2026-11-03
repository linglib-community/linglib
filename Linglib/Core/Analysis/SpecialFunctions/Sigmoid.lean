module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The logistic function and the log-odds

The log-odds `Real.logit p = log (p / (1 - p))` invert the logistic function on `(0, 1)`. The share
of one of two exponentials in their sum is the logistic function of the difference of their
exponents. The difference of the logistic function at two points is a ratio of hyperbolic
functions of their half-difference and midpoint, as `Real.sin_sub_sin` is for the sine.
-/

@[expose] public section

namespace Real

theorem exp_div_add_exp_eq_sigmoid (x y : ℝ) : exp x / (exp x + exp y) = sigmoid (x - y) := by
  have hx := exp_pos x
  have hy := exp_pos y
  rw [sigmoid_def, neg_sub, exp_sub]
  field_simp

theorem sigmoid_log {x : ℝ} (hx : 0 < x) : sigmoid (log x) = x / (x + 1) := by
  rw [sigmoid_def, exp_neg, exp_log hx]
  field_simp

theorem sigmoid_sub_sigmoid (x y : ℝ) :
    sigmoid x - sigmoid y = sinh ((x - y) / 2) / (cosh ((x + y) / 2) + cosh ((x - y) / 2)) := by
  have hx := exp_pos (x / 2)
  have hy := exp_pos (y / 2)
  have ex : exp x = exp (x / 2) ^ 2 := by rw [sq, ← exp_add, add_halves]
  have ey : exp y = exp (y / 2) ^ 2 := by rw [sq, ← exp_add, add_halves]
  simp only [sinh_eq, cosh_eq, sigmoid_def, exp_neg, exp_add, exp_sub, add_div, sub_div, ex, ey]
  field_simp
  ring

theorem sigmoid_add_sub_sigmoid_sub (x a : ℝ) :
    sigmoid (x + a) - sigmoid (x - a) = sinh a / (cosh x + cosh a) := by
  rw [sigmoid_sub_sigmoid]
  ring_nf

/-- The log-odds `log (p / (1 - p))`, the inverse of `Real.sigmoid`. -/
noncomputable def logit (p : ℝ) : ℝ := log (p / (1 - p))

@[simp] theorem logit_sigmoid (x : ℝ) : logit (sigmoid x) = x := by
  rw [logit, ← sigmoid_neg, ← sigmoid_mul_rexp_neg, div_mul_cancel_left₀ (sigmoid_pos x).ne',
    ← exp_neg, neg_neg, log_exp]

theorem sigmoid_logit {p : ℝ} (hp : p ∈ Set.Ioo 0 1) : sigmoid (logit p) = p := by
  obtain ⟨x, rfl⟩ : p ∈ Set.range sigmoid := range_sigmoid ▸ hp
  rw [logit_sigmoid]

end Real
