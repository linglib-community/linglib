module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators

/-!
# The softmax function

This file defines the softmax function `Real.softmax s i = exp (s i) / ∑ j, exp (s j)`, which
normalizes the exponentials of a score vector over a finite type. It is Luce's choice rule with
exponential scores, McFadden's multinomial logit, and the Boltzmann–Gibbs distribution. An
inverse temperature enters by scaling the argument, as in `softmax (α • s)`. With two
alternatives softmax is `Real.sigmoid` of the score difference, and `Real.logit` inverts
`Real.sigmoid`.

Log-sum-exp `x ↦ log (∑ i, exp (x i))` is the log-partition function, and its derivative along
a curve of scores is the softmax expectation of the score derivative. Along a line of scores
`t ↦ t • s + r` it is, up to an additive constant, the cumulant generating function
`ProbabilityTheory.cgf s` under the counting measure tilted by `r`, which is convex by
`ProbabilityTheory.convexOn_cgf`.

## Main definitions

* `Real.softmax`: the normalized exponential of a score vector.
* `Real.logit`: the inverse of `Real.sigmoid`.

## Main results

* `Real.sum_softmax`, `Real.softmax_pos`: `softmax s` is a probability distribution.
* `Real.softmax_div_softmax`, `Real.log_softmax_div_softmax`: odds are exponentiated score
  differences (independence of irrelevant alternatives).
* `Real.softmax_le_softmax_iff`, `Real.softmax_update_strictMono`: monotonicity in the scores.
* `HasDerivAt.log_sum_exp`, `HasDerivAt.log_softmax`: along a curve of scores, log-sum-exp has
  the softmax expectation of the score derivative as its derivative.
* `Real.softmax_add_const`, `Real.softmax_const`: translation invariance, and the uniform
  distribution for constant scores.
* `Real.softmax_eq_sigmoid_of_univ_eq_pair`, `Real.softmax_fin_two`: two alternatives give
  `Real.sigmoid`.
* `Real.tendsto_softmax_nhds_zero`, `Real.tendsto_softmax_atTop`,
  `Real.tendsto_softmax_atTop_pi`, `Real.tendsto_softmax_atBot`: softmax is uniform at inverse
  temperature `0` and tends to a point mass on a strict maximizer (minimizer) as `α → ∞`
  (`α → -∞`).
* `Real.tendsto_sum_negMulLog_softmax_atTop`: the entropy vanishes in the hard limit.
* `Real.softmax_sum_apply`, `Real.sum_softmax_eval_eq`: a separable score on a product type gives
  a product distribution, with coordinate marginals.
* `Real.rpow_div_sum_rpow`: Luce's power rule is the softmax of the log-scores.

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
noncomputable def softmax (s : ι → ℝ) : ι → ℝ := fun i => exp (s i) / ∑ j, exp (s j)

theorem softmax_def (s : ι → ℝ) (i : ι) : softmax s i = exp (s i) / ∑ j, exp (s j) := rfl

/-- Softmax is invariant under translating every score by the same constant. -/
theorem softmax_add_const (s : ι → ℝ) (c : ℝ) : softmax (fun i => s i + c) = softmax s := by
  funext i
  simp only [softmax_def, exp_add, ← sum_mul]
  exact mul_div_mul_right _ _ (exp_pos c).ne'

@[simp] theorem softmax_zero : softmax (0 : ι → ℝ) = fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  funext i; simp [softmax_def, card_univ]

/-- Equal scores give the uniform distribution. -/
@[simp] theorem softmax_const (c : ℝ) :
    softmax (fun _ : ι => c) = fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  simpa using softmax_add_const (0 : ι → ℝ) c

section Nonempty

variable [Nonempty ι] (s : ι → ℝ) (i j : ι)

theorem sum_exp_pos : 0 < ∑ j, exp (s j) := sum_pos (fun _ _ => exp_pos _) univ_nonempty

@[bound] theorem softmax_pos : 0 < softmax s i := div_pos (exp_pos _) (sum_exp_pos s)

@[bound] theorem softmax_nonneg : 0 ≤ softmax s i := (softmax_pos s i).le

@[simp] theorem sum_softmax : ∑ i, softmax s i = 1 := by
  simp [softmax_def, ← sum_div, (sum_exp_pos s).ne']

@[bound] theorem softmax_le_one : softmax s i ≤ 1 :=
  (single_le_sum (fun j _ => softmax_nonneg s j) (mem_univ i)).trans_eq (sum_softmax s)

/-- The odds of two alternatives are their exponentiated score difference, whatever the other
alternatives are. -/
theorem softmax_div_softmax : softmax s i / softmax s j = exp (s i - s j) := by
  rw [softmax_def, softmax_def, div_div_div_cancel_right₀ (sum_exp_pos s).ne', exp_sub]

theorem log_softmax_div_softmax : log (softmax s i / softmax s j) = s i - s j := by
  rw [softmax_div_softmax, log_exp]

theorem softmax_eq_softmax_mul_exp_sub : softmax s i = softmax s j * exp (s i - s j) :=
  ((div_eq_iff (softmax_pos s j).ne').1 (softmax_div_softmax s i j)).trans (mul_comm _ _)

theorem log_softmax : log (softmax s i) = s i - log (∑ j, exp (s j)) := by
  rw [softmax_def, log_div (exp_pos _).ne' (sum_exp_pos s).ne', log_exp]

theorem softmax_eq_exp_sub : softmax s i = exp (s i - log (∑ j, exp (s j))) := by
  rw [exp_sub, exp_log (sum_exp_pos s)]; rfl

variable {s i j}

theorem softmax_le_softmax_iff : softmax s i ≤ softmax s j ↔ s i ≤ s j := by
  rw [softmax_def, softmax_def, div_le_div_iff_of_pos_right (sum_exp_pos s), exp_le_exp]

theorem softmax_lt_softmax_iff : softmax s i < softmax s j ↔ s i < s j := by
  rw [softmax_def, softmax_def, div_lt_div_iff_of_pos_right (sum_exp_pos s), exp_lt_exp]

alias ⟨_, softmax_le_softmax⟩ := softmax_le_softmax_iff

alias ⟨_, softmax_lt_softmax⟩ := softmax_lt_softmax_iff

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

/-! ### Derivatives along a curve of scores -/

section Deriv

variable [Nonempty ι] {f : ℝ → ι → ℝ} {f' : ι → ℝ} {x : ℝ}

/-- The derivative of log-sum-exp along a curve is the softmax-weighted derivative of the
scores. -/
theorem _root_.HasDerivAt.log_sum_exp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ log (∑ i, exp (f t i))) (∑ i, softmax (f x) i * f' i) x := by
  have hsum : HasDerivAt (fun t ↦ ∑ i, exp (f t i)) (∑ i, exp (f x i) * f' i) x :=
    .fun_sum fun i _ ↦ (hasDerivAt_pi.1 hf i).exp
  convert hsum.log (sum_exp_pos (f x)).ne' using 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [softmax_def]; ring

/-- The derivative of a log-softmax coordinate along a curve is that coordinate's score
derivative minus its softmax expectation. -/
theorem _root_.HasDerivAt.log_softmax (hf : HasDerivAt f f' x) (i : ι) :
    HasDerivAt (fun t ↦ log (softmax (f t) i)) (f' i - ∑ j, softmax (f x) j * f' j) x := by
  simp only [Real.log_softmax]
  exact (hasDerivAt_pi.1 hf i).sub hf.log_sum_exp

end Deriv

section Update

variable [DecidableEq ι] [Nontrivial ι]

/-- `softmax (update s i x) i` is strictly increasing in the score `x`. -/
theorem softmax_update_strictMono (s : ι → ℝ) (i : ι) :
    StrictMono fun x => softmax (Function.update s i x) i := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hR : 0 < ∑ k ∈ univ.erase i, exp (s k) :=
    sum_pos (fun _ _ => exp_pos _) ⟨j, mem_erase.2 ⟨hj, mem_univ j⟩⟩
  have h (x : ℝ) : softmax (Function.update s i x) i =
      exp x / (exp x + ∑ k ∈ univ.erase i, exp (s k)) := by
    rw [softmax_def, ← add_sum_erase _ _ (mem_univ i), Function.update_self,
      sum_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_erase hk)]]
  intro x y hxy
  simp only [h]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right (exp_lt_exp.2 hxy) hR]

/-- Raising one score while holding the others fixed raises its probability. -/
theorem softmax_lt_softmax_of_single_lt {s s' : ι → ℝ} {i : ι} (hlt : s i < s' i)
    (heq : ∀ j ≠ i, s' j = s j) : softmax s i < softmax s' i := by
  rw [show s' = Function.update s i (s' i) from Function.eq_update_iff.2 ⟨rfl, heq⟩]
  conv_lhs => rw [← Function.update_eq_self i s]
  exact softmax_update_strictMono s i hlt

end Update

/-! ### Limits in the inverse temperature

`softmax (α • s)` is continuous in the inverse temperature `α`. It is uniform at `α = 0`,
concentrates on a strict maximizer as `α → ∞` and on a strict minimizer as `α → -∞`, and its
entropy vanishes in the limit. -/

section Limit

open Filter Topology

variable (s : ι → ℝ) (i : ι)

theorem softmax_eq_inv_sum_exp_sub : softmax s i = (∑ j, exp (s j - s i))⁻¹ := by
  simp only [softmax_def, exp_sub, ← sum_div, inv_div]

theorem softmax_le_exp_sub [Nonempty ι] (j : ι) : softmax s i ≤ exp (s i - s j) := by
  rw [softmax_eq_softmax_mul_exp_sub s i j]
  exact mul_le_of_le_one_left (exp_pos _).le (softmax_le_one s j)

@[fun_prop]
theorem continuous_softmax_smul [Nonempty ι] : Continuous fun α : ℝ => softmax (α • s) i := by
  simp only [softmax_def, Pi.smul_apply, smul_eq_mul]
  exact (continuous_exp.comp (continuous_mul_const _)).div
    (continuous_finsetSum _ fun j _ => continuous_exp.comp (continuous_mul_const _))
    fun α => (sum_exp_pos (α • s)).ne'

/-- At inverse temperature `0`, softmax is uniform. -/
theorem tendsto_softmax_nhds_zero [Nonempty ι] :
    Tendsto (fun α : ℝ => softmax (α • s) i) (𝓝 0) (𝓝 (Fintype.card ι : ℝ)⁻¹) := by
  simpa using (continuous_softmax_smul s i).tendsto 0

variable {s i}

/-- As the inverse temperature grows, softmax concentrates on a strict maximizer. -/
theorem tendsto_softmax_atTop (h : ∀ j ≠ i, s j < s i) :
    Tendsto (fun α : ℝ => softmax (α • s) i) atTop (𝓝 1) := by
  classical
  simp only [softmax_eq_inv_sum_exp_sub, Pi.smul_apply, smul_eq_mul, ← mul_sub]
  have : Tendsto (fun α : ℝ => ∑ j, exp (α * (s j - s i))) atTop
      (𝓝 (∑ j, if j = i then 1 else 0)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    split_ifs with hj
    · simp [hj]
    · simpa [Function.comp_def] using
        tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 (h j hj)))
  simpa using this.inv₀ (by simp)

/-- As the inverse temperature grows, a strictly dominated alternative vanishes. -/
theorem tendsto_softmax_atTop_of_lt {j : ι} (h : s i < s j) :
    Tendsto (fun α : ℝ => softmax (α • s) i) atTop (𝓝 0) := by
  have : Nonempty ι := ⟨i⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun α => softmax_nonneg _ _) (fun α => softmax_le_exp_sub (α • s) i j)
  simpa [Function.comp_def, ← mul_sub] using
    tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 h))

/-- Softmax converges to the point mass on a strict maximizer. -/
theorem tendsto_softmax_atTop_pi [DecidableEq ι] (h : ∀ j ≠ i, s j < s i) :
    Tendsto (fun α : ℝ => softmax (α • s)) atTop (𝓝 (Pi.single i 1)) := by
  refine tendsto_pi_nhds.2 fun j => ?_
  by_cases hj : j = i
  · subst hj; simpa using tendsto_softmax_atTop h
  · simpa [hj] using tendsto_softmax_atTop_of_lt (h j hj)

/-- As the inverse temperature tends to `-∞`, softmax concentrates on a strict
minimizer. -/
theorem tendsto_softmax_atBot (h : ∀ j ≠ i, s i < s j) :
    Tendsto (fun α : ℝ => softmax (α • s) i) atBot (𝓝 1) := by
  have := (tendsto_softmax_atTop (s := -s) fun j hj => neg_lt_neg (h j hj)).comp
    tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-- The entropy of softmax vanishes as it concentrates on a strict maximizer. -/
theorem tendsto_sum_negMulLog_softmax_atTop (h : ∀ j ≠ i, s j < s i) :
    Tendsto (fun α : ℝ => ∑ j, negMulLog (softmax (α • s) j)) atTop (𝓝 0) := by
  classical
  have hc : Continuous fun p : ι → ℝ => ∑ j, negMulLog (p j) :=
    continuous_finsetSum _ fun j _ => continuous_negMulLog.comp (continuous_apply j)
  have h0 : ∑ j, negMulLog ((Pi.single i (1 : ℝ) : ι → ℝ) j) = 0 :=
    sum_eq_zero fun j _ => by by_cases hj : j = i <;> simp [hj]
  have := (hc.tendsto _).comp (tendsto_softmax_atTop_pi h)
  simp only [Function.comp_def] at this
  rwa [h0] at this

end Limit

/-! ### Two alternatives and the logit -/

/-- With two alternatives, softmax is the logistic function of the score
difference. -/
theorem softmax_eq_sigmoid_of_univ_eq_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (h : (univ : Finset ι) = {i, j}) (s : ι → ℝ) : softmax s i = sigmoid (s i - s j) := by
  rw [softmax_def, h, sum_pair hij, sigmoid_def, neg_sub, exp_sub,
    ← div_self (exp_pos (s i)).ne', ← add_div, inv_div]

theorem softmax_fin_two (s : Fin 2 → ℝ) : softmax s 0 = sigmoid (s 0 - s 1) :=
  softmax_eq_sigmoid_of_univ_eq_pair zero_ne_one (by decide) s

/-- With two alternatives, the log-odds are the score difference. -/
theorem logit_softmax_fin_two (s : Fin 2 → ℝ) : logit (softmax s 0) = s 0 - s 1 := by
  rw [softmax_fin_two, logit_sigmoid]

/-- Luce's power rule `f i ^ α / ∑ j, f j ^ α` is the softmax of the scaled
log-scores. -/
theorem rpow_div_sum_rpow [Nonempty ι] {f : ι → ℝ} (hf : ∀ i, 0 < f i) (α : ℝ) (i : ι) :
    f i ^ α / ∑ j, f j ^ α = softmax (α • fun j => log (f j)) i := by
  have h (j : ι) : f j ^ α = exp (α * log (f j)) := by rw [rpow_def_of_pos (hf j), mul_comm]
  simp only [h, softmax_def, Pi.smul_apply, smul_eq_mul]

/-! ### Product types

A separable score `s f = ∑ i, c i (f i)` on assignments `f : ι → V` gives a
softmax that factorizes into the coordinate softmaxes, so marginalizing the joint
distribution at coordinate `i` recovers `softmax (c i)`. -/

section Pi

variable {V : Type*} [DecidableEq ι] [Fintype V]

/-- The softmax of a separable score is the product of the coordinate softmaxes. -/
theorem softmax_sum_apply (c : ι → V → ℝ) (f : ι → V) :
    softmax (fun g : ι → V => ∑ i, c i (g i)) f = ∏ i, softmax (c i) (f i) := by
  simp only [softmax_def, exp_sum, prod_div_distrib, Fintype.prod_sum]

/-- Marginalizing the softmax of a separable score at coordinate `i` recovers the
coordinate softmax `softmax (c i)`. -/
theorem sum_softmax_eval_eq [DecidableEq V] [Nonempty V] (c : ι → V → ℝ) (i : ι) (v : V) :
    ∑ f with f i = v, softmax (fun g : ι → V => ∑ j, c j (g j)) f = softmax (c i) v := by
  set F : ι → V → ℝ := fun j w =>
    if j = i then (if w = v then softmax (c i) v else 0) else softmax (c j) w with hF
  have h (f : ι → V) : (if f i = v then ∏ j, softmax (c j) (f j) else 0) = ∏ j, F j (f j) := by
    split_ifs with hf
    · exact prod_congr rfl fun j _ => by by_cases hj : j = i <;> simp [hF, hj, hf]
    · exact (prod_eq_zero (mem_univ i) (by simp [hF, hf])).symm
  have hrest : ∏ j ∈ univ.erase i, ∑ w, F j w = 1 :=
    prod_eq_one fun j hj => by simp [hF, ne_of_mem_erase hj, sum_softmax]
  simp only [softmax_sum_apply, sum_filter, h]
  rw [← Fintype.prod_sum F, ← mul_prod_erase univ _ (mem_univ i), hrest]
  simp [hF]

end Pi

end Real
