module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators

/-!
# The softmax function

This file defines the softmax function `Real.softmax s i = exp (s i) / ∑ j, exp (s j)`, which
normalizes the exponentials of a score vector over a finite type. It is Luce's choice rule with
exponential scores, McFadden's multinomial logit, and the Boltzmann–Gibbs distribution. An
inverse temperature enters by scaling the argument, as in `softmax (α • s)`. With two
alternatives softmax is `Real.sigmoid` of the score difference.

Log-sum-exp `x ↦ log (∑ i, exp (x i))`, the logarithm of the normalizer, is convex, and its
derivative is the softmax expectation of the derivative of the scores.

## Main definitions

* `Real.softmax`: the normalized exponential of a score vector.

## Main results

* `Real.sum_softmax`, `Real.softmax_pos`: `softmax s` is a probability distribution.
* `Real.softmax_div_softmax`, `Real.log_softmax_div_softmax`: odds are exponentiated score
  differences (independence of irrelevant alternatives).
* `Real.softmax_le_softmax_iff`, `Real.softmax_update_strictMono`: monotonicity in the scores.
* `Real.softmax_add_const`, `Real.softmax_const`: translation invariance, and the uniform
  distribution for constant scores.
* `Real.convexOn_log_sum_exp`, `HasFDerivAt.log_sum_exp`: log-sum-exp is convex, and its
  derivative is the softmax-weighted derivative of the scores.
* `Real.tendsto_softmax_atTop`: softmax concentrates on a strict maximizer as the inverse
  temperature grows.
* `Real.softmax_eq_sigmoid_of_univ_eq_pair`, `Real.softmax_fin_two`: two alternatives give
  `Real.sigmoid`.
* `Real.softmax_sum_apply`: a separable score on a product type gives a product distribution.

## References

* [R. D. Luce, *Individual Choice Behavior: A Theoretical Analysis* (1959)][luce-1959]
* [D. McFadden, *Conditional logit analysis of qualitative choice behavior*
  (1974)][mcfadden-1974]
-/

@[expose] public section

namespace Real

open Finset

variable {ι : Type*} [Fintype ι]

/-- The softmax function sends a score vector `s` to `i ↦ exp (s i) / ∑ j, exp (s j)`. An
inverse temperature enters by scaling the argument, as in `softmax (α • s)`. -/
noncomputable def softmax (s : ι → ℝ) : ι → ℝ := fun i ↦ exp (s i) / ∑ j, exp (s j)

theorem softmax_apply (s : ι → ℝ) (i : ι) : softmax s i = exp (s i) / ∑ j, exp (s j) := rfl

/-- Softmax is invariant under translating every score by the same constant. -/
theorem softmax_add_const (s : ι → ℝ) (c : ℝ) : softmax (fun i ↦ s i + c) = softmax s := by
  funext i
  simp only [softmax_apply, exp_add, ← sum_mul]
  exact mul_div_mul_right _ _ (exp_pos c).ne'

@[simp] theorem softmax_zero : softmax (0 : ι → ℝ) = fun _ ↦ (Fintype.card ι : ℝ)⁻¹ := by
  funext i; simp [softmax_apply, card_univ]

/-- Equal scores give the uniform distribution. -/
@[simp] theorem softmax_const (c : ℝ) :
    softmax (fun _ : ι ↦ c) = fun _ ↦ (Fintype.card ι : ℝ)⁻¹ := by
  simpa using softmax_add_const (0 : ι → ℝ) c

section Nonempty

variable [Nonempty ι] (s : ι → ℝ) (i j : ι)

theorem sum_exp_pos : 0 < ∑ j, exp (s j) := sum_pos (fun _ _ ↦ exp_pos _) univ_nonempty

@[bound] theorem softmax_pos : 0 < softmax s i := div_pos (exp_pos _) (sum_exp_pos s)

@[bound] theorem softmax_nonneg : 0 ≤ softmax s i := (softmax_pos s i).le

@[simp] theorem sum_softmax : ∑ i, softmax s i = 1 := by
  simp [softmax_apply, ← sum_div, (sum_exp_pos s).ne']

@[bound] theorem softmax_le_one : softmax s i ≤ 1 :=
  (single_le_sum (fun j _ ↦ softmax_nonneg s j) (mem_univ i)).trans_eq (sum_softmax s)

/-- The odds of two alternatives are their exponentiated score difference, whatever the other
alternatives are. -/
theorem softmax_div_softmax : softmax s i / softmax s j = exp (s i - s j) := by
  rw [softmax_apply, softmax_apply, div_div_div_cancel_right₀ (sum_exp_pos s).ne', exp_sub]

theorem log_softmax_div_softmax : log (softmax s i / softmax s j) = s i - s j := by
  rw [softmax_div_softmax, log_exp]

theorem log_softmax : log (softmax s i) = s i - log (∑ j, exp (s j)) := by
  rw [softmax_apply, log_div (exp_pos _).ne' (sum_exp_pos s).ne', log_exp]

theorem softmax_eq_exp_sub : softmax s i = exp (s i - log (∑ j, exp (s j))) := by
  rw [exp_sub, exp_log (sum_exp_pos s)]; rfl

variable {s i j}

theorem softmax_le_softmax_iff : softmax s i ≤ softmax s j ↔ s i ≤ s j := by
  rw [softmax_apply, softmax_apply, div_le_div_iff_of_pos_right (sum_exp_pos s), exp_le_exp]

theorem softmax_lt_softmax_iff : softmax s i < softmax s j ↔ s i < s j := by
  rw [softmax_apply, softmax_apply, div_lt_div_iff_of_pos_right (sum_exp_pos s), exp_lt_exp]

end Nonempty

/-! ### Convexity -/

/-- Log-sum-exp, the logarithm of softmax's normalizer, is convex. Hölder's inequality with
exponents `a⁻¹` and `b⁻¹` bounds `∑ i, exp (a * s i + b * t i)` by
`(∑ i, exp (s i)) ^ a * (∑ i, exp (t i)) ^ b`. -/
theorem convexOn_log_sum_exp [Nonempty ι] :
    ConvexOn ℝ Set.univ fun s : ι → ℝ ↦ log (∑ i, exp (s i)) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab ↦ ?_⟩
  rcases ha.eq_or_lt with rfl | ha
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb
  · obtain rfl : a = 1 := by linarith
    simp
  have key := inner_le_Lp_mul_Lq_of_nonneg univ (HolderConjugate.inv_inv ha hb hab)
    (f := fun i ↦ exp (a * s i)) (g := fun i ↦ exp (b * t i))
    (fun _ _ ↦ (exp_pos _).le) (fun _ _ ↦ (exp_pos _).le)
  have hpow (c x : ℝ) (hc : 0 < c) : exp (c * x) ^ c⁻¹ = exp x := by
    rw [← exp_mul, mul_comm c, mul_assoc, mul_inv_cancel₀ hc.ne', mul_one]
  simp only [hpow _ _ ha, hpow _ _ hb, one_div, inv_inv, ← exp_add] at key
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc log (∑ i, exp (a * s i + b * t i))
      ≤ log ((∑ i, exp (s i)) ^ a * (∑ i, exp (t i)) ^ b) :=
        log_le_log (sum_exp_pos fun i ↦ a * s i + b * t i) key
    _ = a * log (∑ i, exp (s i)) + b * log (∑ i, exp (t i)) := by
        rw [log_mul (rpow_pos_of_pos (sum_exp_pos s) _).ne' (rpow_pos_of_pos (sum_exp_pos t) _).ne',
          log_rpow (sum_exp_pos s), log_rpow (sum_exp_pos t)]

/-! ### The derivative of log-sum-exp -/

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nonempty ι] {f : ι → E → ℝ}
  {f' : ι → E →L[ℝ] ℝ} {x : E}

/-- The derivative of log-sum-exp of a family of scores is the softmax-weighted sum of their
derivatives. -/
theorem _root_.HasFDerivAt.log_sum_exp (hf : ∀ i, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (fun y ↦ log (∑ i, exp (f i y))) (∑ i, softmax (f · x) i • f' i) x := by
  convert (HasFDerivAt.fun_sum fun i _ ↦ (hf i).exp).log (sum_exp_pos (f · x)).ne' using 1
  simp only [smul_sum, smul_smul, softmax_apply, div_eq_inv_mul]

end Deriv

section Update

variable [DecidableEq ι] [Nontrivial ι]

/-- `softmax (update s i x) i` is strictly increasing in the score `x`. -/
theorem softmax_update_strictMono (s : ι → ℝ) (i : ι) :
    StrictMono fun x ↦ softmax (Function.update s i x) i := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hR : 0 < ∑ k ∈ univ.erase i, exp (s k) :=
    sum_pos (fun _ _ ↦ exp_pos _) ⟨j, mem_erase.2 ⟨hj, mem_univ j⟩⟩
  have h (x : ℝ) : softmax (Function.update s i x) i =
      exp x / (exp x + ∑ k ∈ univ.erase i, exp (s k)) := by
    rw [softmax_apply, ← add_sum_erase _ _ (mem_univ i), Function.update_self,
      sum_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_erase hk)]]
  intro x y hxy
  simp only [h]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right (exp_lt_exp.2 hxy) hR]

theorem softmax_lt_softmax_of_single_lt {s s' : ι → ℝ} {i : ι} (hlt : s i < s' i)
    (heq : ∀ j ≠ i, s' j = s j) : softmax s i < softmax s' i := by
  rw [show s' = Function.update s i (s' i) from Function.eq_update_iff.2 ⟨rfl, heq⟩]
  conv_lhs => rw [← Function.update_eq_self i s]
  exact softmax_update_strictMono s i hlt

end Update

/-! ### The limit of low temperature -/

section Limit

open Filter Topology

theorem softmax_eq_inv_sum_exp_sub (s : ι → ℝ) (i : ι) :
    softmax s i = (∑ j, exp (s j - s i))⁻¹ := by
  simp only [softmax_apply, exp_sub, ← sum_div, inv_div]

/-- As the inverse temperature grows, softmax concentrates on a strict maximizer. -/
theorem tendsto_softmax_atTop {s : ι → ℝ} {i : ι} (h : ∀ j ≠ i, s j < s i) :
    Tendsto (fun α : ℝ ↦ softmax (α • s) i) atTop (𝓝 1) := by
  classical
  simp only [softmax_eq_inv_sum_exp_sub, Pi.smul_apply, smul_eq_mul, ← mul_sub]
  have : Tendsto (fun α : ℝ ↦ ∑ j, exp (α * (s j - s i))) atTop
      (𝓝 (∑ j, if j = i then 1 else 0)) := by
    refine tendsto_finsetSum _ fun j _ ↦ ?_
    split_ifs with hj
    · simp [hj]
    · simpa [Function.comp_def] using
        tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 (h j hj)))
  simpa using this.inv₀ (by simp)

end Limit

/-! ### Two alternatives -/

/-- With two alternatives, softmax is the logistic function of the score difference. -/
theorem softmax_eq_sigmoid_of_univ_eq_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (h : (univ : Finset ι) = {i, j}) (s : ι → ℝ) : softmax s i = sigmoid (s i - s j) := by
  rw [softmax_apply, h, sum_pair hij, exp_div_add_exp_eq_sigmoid]

theorem softmax_fin_two (s : Fin 2 → ℝ) : softmax s 0 = sigmoid (s 0 - s 1) :=
  softmax_eq_sigmoid_of_univ_eq_pair zero_ne_one (by decide) s

theorem logit_softmax_fin_two (s : Fin 2 → ℝ) : logit (softmax s 0) = s 0 - s 1 := by
  rw [softmax_fin_two, logit_sigmoid]

/-! ### Product types -/

section Pi

variable {V : Type*} [DecidableEq ι] [Fintype V]

/-- The softmax of a separable score `∑ i, c i (g i)` on assignments `g : ι → V` is the product
of the coordinate softmaxes. -/
theorem softmax_sum_apply (c : ι → V → ℝ) (f : ι → V) :
    softmax (fun g : ι → V ↦ ∑ i, c i (g i)) f = ∏ i, softmax (c i) (f i) := by
  simp only [softmax_apply, exp_sum, prod_div_distrib, Fintype.prod_sum]

end Pi

end Real
