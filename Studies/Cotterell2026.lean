/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.Probability.AutoregressiveSequenceModel.Tight
public import Linglib.Core.Probability.Kernel.Softmax

/-!
# Cotterell (2026): Surprisal Theory is Tautological (without Rational Grounding)

Surprisal theory holds that the processing difficulty of a unit in context is an affine function
of its surprisal under some language model, with a positive slope and a baseline that may depend
on the context. The paper argues that the claim is a tautology unless the language model is
constrained: any nonnegative difficulty measure `d` over the next unit, or the end of the string,
given a prefix, defines the model whose next-unit distribution is the softmax of `-d`, and its
surprisal is `d` plus the log partition function of the prefix (`surprisal_softmaxModel`), so
the claim holds with slope one and the negative log partition function as baseline. The one
condition is that the model be a language model, i.e. tight. When the end difficulty is bounded
along a series whose exponentials diverge, the softmax model ends with probability at least those
exponentials over the size of the extended alphabet, and it is tight by Du and colleagues'
sufficient condition (`isTight_softmaxModel`). A tight model's next-unit distributions are the
next-unit laws of the language model it defines
(`AutoregressiveSequenceModel.IsTight.next_ofMeasure_stringMeasure`), so the difficulty is the
surprisal of the unit under that language model up to a context-dependent baseline
(`surprisal_next_ofMeasure_stringMeasure`), the tautology
(`exists_difficulty_eq_surprisal`). A constant bound `C` also bounds the expected
length by `(1 - η) / η` for `η = exp (-C)` over the size of the extended alphabet
(`lintegral_length_softmaxModel_le`). Without the bound the construction can fail: an
end difficulty growing linearly in the length of the prefix leaves the softmax model non-tight
(`not_isTight_softmaxModel_length`).

## Implementation notes

* The difficulty measure takes the next unit before the prefix, `d o u` for `d(o | u)`, with
  `none` for the end of the string, and the model's next-unit kernel is the softmax kernel
  `ProbabilityTheory.Kernel.softmax` of the real score `-d`.
* The divergence hypothesis is stated in `ℝ≥0∞`, where a sum of nonnegative terms equals `∞`
  exactly when the series diverges; the paper states it for real series.
* The paper's bound `f` is nonnegative and its constant bound positive; neither sign condition is
  needed here.
* The paper remarks that the softmax construction need not give a language model but gives no
  example; `not_isTight_softmaxModel_length` is an added witness.
* The paper's fitness measure, its consistency theorem for maximum-likelihood estimation, and its
  scaling implication are not formalized.

## References

* [cotterell-2026]
* [du-etal-2023]
-/

@[expose] public section

namespace Cotterell2026

open InformationTheory MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The model whose next-unit distribution after `u` is the softmax of `-d (· | u)`. -/
noncomputable def softmaxModel (d : Option α → List α → ℝ) : AutoregressiveSequenceModel α where
  next := Kernel.softmax fun u o ↦ ((-d o u : ℝ) : EReal)
  isMarkovKernel_next := Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨none, EReal.coe_ne_bot _⟩)
    fun _ _ ↦ EReal.coe_ne_top _

variable (d : Option α → List α → ℝ)

theorem real_next_softmaxModel (u : List α) (o : Option α) :
    ((softmaxModel d).next u).real {o} = softmax (fun o ↦ -d o u) o :=
  Kernel.softmax_coe_real_singleton (fun u o ↦ -d o u) u o

theorem surprisal_softmaxModel (u : List α) (o : Option α) :
    surprisal ((softmaxModel d).next u) o = d o u + log (∑ o', exp (-d o' u)) := by
  rw [surprisal, real_next_softmaxModel, log_softmax]
  ring

variable {d}

theorem le_next_softmaxModel (hd : ∀ o u, 0 ≤ d o u) (u : List α) (o : Option α) :
    ENNReal.ofReal (exp (-d o u)) / Fintype.card (Option α) ≤ (softmaxModel d).next u {o} := by
  rw [softmaxModel, Kernel.softmax_apply_singleton]
  simp only [EReal.exp_coe]
  refine ENNReal.div_le_div le_rfl ?_
  calc ∑ o, ENNReal.ofReal (exp (-d o u)) ≤ ∑ _o : Option α, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun o _ ↦
          ENNReal.ofReal_le_one.2 (exp_le_one_iff.2 (by linarith [hd o u]))
    _ = Fintype.card (Option α) := by simp

/-- A nonnegative difficulty measure with end difficulty bounded by `f` and `∑ exp (-f t)` divergent
gives a tight softmax model (Proposition 1(a)). -/
theorem isTight_softmaxModel (hd : ∀ o u, 0 ≤ d o u) {f : ℕ → ℝ}
    (hf : ∀ u, d none u ≤ f (u.length + 1)) (hdiv : ∑' t, ENNReal.ofReal (exp (-f (t + 1))) = ∞) :
    (softmaxModel d).IsTight := by
  refine (softmaxModel d).isTight_of_le_next_none
    (f := fun t ↦ ENNReal.ofReal (exp (-f t)) / Fintype.card (Option α)) (fun u ↦ ?_) ?_
  · refine le_trans ?_ (le_next_softmaxModel hd u none)
    gcongr
    exact hf u
  · simp only [div_eq_mul_inv, ENNReal.tsum_mul_right, hdiv]
    exact ENNReal.top_mul (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))

theorem not_isTight_softmaxModel_length [Nonempty α] :
    ¬ (softmaxModel fun (o : Option α) u ↦ o.elim ((u.length : ℝ) + 1) fun _ ↦ 0).IsTight := by
  set w : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (exp (-((n : ℝ) + 1)))
  have hk : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hw (n : ℕ) : w n ≠ ∞ := ENNReal.ofReal_ne_top
  rw [(softmaxModel _).isTight_iff_of_next_none_eq (e := fun n ↦ w n / (w n + Fintype.card α))
    (fun x ↦ by
      simp only [softmaxModel, Kernel.softmax_apply_singleton, Option.elim, EReal.exp_coe]
      simp [Fintype.sum_option, w])
    fun n ↦ ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_self_add)]
  rintro (⟨n, hn⟩ | hsum)
  · rw [ENNReal.div_eq_one_iff (by simp [hk]) (by simp [hw n])] at hn
    exact hk ((ENNReal.add_right_inj (hw n)).1 (hn.symm.trans (add_zero _).symm))
  · have hle (n : ℕ) : w n / (w n + Fintype.card α) ≤ w n :=
      ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' ((Nat.one_le_cast.2 Fintype.card_pos).trans
        le_add_self))
    have hr : ENNReal.ofReal (exp (-1)) < 1 :=
      ENNReal.ofReal_lt_one.2 (exp_lt_one_iff.2 (by norm_num))
    have hpow (n : ℕ) : w n = ENNReal.ofReal (exp (-1)) ^ (n + 1) := by
      simp only [w, ← ENNReal.ofReal_pow (exp_pos _).le, ← exp_nat_mul]
      congr 2; push_cast; ring
    refine ((ENNReal.tsum_le_tsum hle).trans_lt ?_).ne hsum
    calc ∑' n, w n = ∑' n : ℕ, ENNReal.ofReal (exp (-1)) ^ (n + 1) := tsum_congr hpow
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (exp (-1)) ^ n :=
        ENNReal.tsum_le_tsum fun n ↦ pow_le_pow_of_le_one bot_le hr.le n.le_succ
      _ < ∞ := by rw [ENNReal.tsum_geometric]; exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr)

theorem surprisal_next_ofMeasure_stringMeasure (hd : ∀ o u, 0 ≤ d o u) {f : ℕ → ℝ}
    (hf : ∀ u, d none u ≤ f (u.length + 1)) (hdiv : ∑' t, ENNReal.ofReal (exp (-f (t + 1))) = ∞)
    (u : List α) (o : Option α) :
    surprisal ((AutoregressiveSequenceModel.ofMeasure (softmaxModel d).stringMeasure).next u) o =
      d o u + log (∑ o', exp (-d o' u)) := by
  have hpos : (softmaxModel d).prefixProb u ≠ 0 :=
    (softmaxModel d).condPrefixProb_ne_zero (fun _ _ ↦ Kernel.softmax_apply_singleton_ne_zero
      (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _) [] u
  rw [(isTight_softmaxModel hd hf hdiv).next_ofMeasure_stringMeasure hpos, surprisal_softmaxModel]

theorem exists_difficulty_eq_surprisal (hd : ∀ o u, 0 ≤ d o u) {f : ℕ → ℝ}
    (hf : ∀ u, d none u ≤ f (u.length + 1)) (hdiv : ∑' t, ENNReal.ofReal (exp (-f (t + 1))) = ∞) :
    ∃ μ : Measure (List α), IsProbabilityMeasure μ ∧ ∃ b : List α → ℝ,
      ∀ o u, d o u = surprisal ((AutoregressiveSequenceModel.ofMeasure μ).next u) o + b u :=
  ⟨(softmaxModel d).stringMeasure,
    (softmaxModel d).isTight_iff_isProbabilityMeasure.1 (isTight_softmaxModel hd hf hdiv),
    fun u ↦ -log (∑ o', exp (-d o' u)),
    fun o u ↦ by rw [surprisal_next_ofMeasure_stringMeasure hd hf hdiv]; ring⟩

/-- A constant bound `C` on end difficulty bounds the expected length of the softmax model by `(1 -
η) / η` (Proposition 1(b)). -/
theorem lintegral_length_softmaxModel_le (hd : ∀ o u, 0 ≤ d o u) {C : ℝ}
    (hC : ∀ u, d none u ≤ C) :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂(softmaxModel d).stringMeasure ≤
      (1 - ENNReal.ofReal (exp (-C)) / Fintype.card (Option α)) /
        (ENNReal.ofReal (exp (-C)) / Fintype.card (Option α)) :=
  (softmaxModel d).lintegral_length_le_div fun u ↦ by
    refine le_trans ?_ (le_next_softmaxModel hd u none)
    gcongr
    exact hC u

theorem lintegral_length_softmaxModel_ne_top (hd : ∀ o u, 0 ≤ d o u) {C : ℝ}
    (hC : ∀ u, d none u ≤ C) :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂(softmaxModel d).stringMeasure ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.div_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
    (ENNReal.div_ne_zero.2 ⟨(ENNReal.ofReal_pos.2 (exp_pos _)).ne', ENNReal.natCast_ne_top _⟩))
    (lintegral_length_softmaxModel_le hd hC)

end Cotterell2026
