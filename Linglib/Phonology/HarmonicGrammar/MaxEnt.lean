/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.Probability.GibbsVariational
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# MaxEnt grammars

A MaxEnt grammar makes harmonies into probabilities: a candidate whose violation vector is `T c`
has probability proportional to the exponential of its harmony `-(w ⬝ᵥ T c)`. As a measure, the
MaxEnt distribution is the counting measure on the candidates tilted by harmony, the exponential
family with statistic `T` and parameter `-w`. Violations are counts for a constraint set
(`OptimalityTheory.ConstraintSet.violations`) and may be any reals, as when a lexicon scales them.

The name records a duality. Among the distributions of the candidates with the same expected
violations as a MaxEnt distribution, the MaxEnt one has the greatest entropy, and no other has as
much. The log-likelihood of an empirical distribution is concave in the weights, with gradient the
expected less the observed violations, so the weights that maximize it are exactly those whose
distribution has the observed expected violations, and the most likely MaxEnt grammar is the
maximum-entropy one.

## Main definitions

* `HarmonicGrammar.maxEnt T w`: the MaxEnt distribution of the candidates.
* `HarmonicGrammar.logLikelihood T p w`: the expected log-probability, under the grammar, of the
  candidates drawn from `p`.

## Main results

* `maxEnt_real_singleton`: a candidate's probability is the softmax of the harmonies.
* `log_maxEnt_real_singleton_div`: log-odds are harmony differences.
* `maxEnt_real_singleton_of_pair`: of two candidates, one has the sigmoid of its harmony
  advantage.
* `isGreatest_measureEntropy_maxEnt`, `eq_maxEnt_of_measureEntropy_eq`: the maximum entropy
  principle.
* `concaveOn_logLikelihood`, `hasFDerivAt_logLikelihood`: the log-likelihood is concave, with
  gradient the expected less the observed violations.
* `isMaxOn_logLikelihood_iff`, `isGreatest_measureEntropy_of_isMaxOn`: maximum likelihood is
  matching the observed violations, and gives the maximum-entropy distribution.
* `maxEnt_sum`: additive violations over several inputs give independent outputs.
* `tendsto_maxEnt_smul_atTop`: scaling the weights concentrates the distribution on the harmony
  maximum.

## Implementation notes

* The candidates of one input form a finite type. A conditional grammar takes, at an input `i`,
  the violations `(con.comap (i, ·)).violations` of the candidates paired with `i`.
* Goldwater and Johnson write the exponent as `∑ i, wᵢ fᵢ` without a sign; harmony negates the
  weighted violations here, as in Hayes and Wilson, so that positive weights penalize.
* The log-likelihood takes the empirical distribution of a sample; the log-probability of `n`
  draws is `n` times it.

## References

* [goldwater-johnson-2003]
* [hayes-wilson-2008]
* [berger-della-pietra-della-pietra-1996]
* [della-pietra-della-pietra-lafferty-1997]
* [smolensky-legendre-2006]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real Finset Filter Topology
open scoped ENNReal

namespace HarmonicGrammar

variable {C ι : Type*} [MeasurableSpace C] [Fintype ι]

/-- The MaxEnt distribution of candidates with violation vectors `T` under weights `w` weighs each
candidate by the exponential of its harmony. -/
noncomputable def maxEnt (T : C → ι → ℝ) (w : ι → ℝ) : Measure C :=
  Measure.count.tilted (harmony T w)

/-- A MaxEnt distribution depends on the violations and weights only through the harmonies. -/
theorem maxEnt_congr {ι' : Type*} [Fintype ι'] {T : C → ι → ℝ} {w : ι → ℝ} {T' : C → ι' → ℝ}
    {w' : ι' → ℝ} (h : harmony T w = harmony T' w') : maxEnt T w = maxEnt T' w' := by
  simp only [maxEnt, h]

/-- The log-likelihood of an empirical distribution `p` under a grammar is the expected
log-probability of the candidates drawn from `p`. -/
noncomputable def logLikelihood (T : C → ι → ℝ) (p : Measure C) (w : ι → ℝ) : ℝ :=
  ∫ c, log ((maxEnt T w).real {c}) ∂p

/-- The log-likelihood of a single observation is its log-probability. -/
@[simp] theorem logLikelihood_dirac [MeasurableSingletonClass C] (T : C → ι → ℝ) (w : ι → ℝ)
    (c : C) : logLikelihood T (Measure.dirac c) w = log ((maxEnt T w).real {c}) := by
  simp [logLikelihood]

variable [Fintype C] [MeasurableSingletonClass C] (T : C → ι → ℝ) (w : ι → ℝ)

instance : IsZeroOrProbabilityMeasure (maxEnt T w) := by
  unfold maxEnt; infer_instance

instance [Nonempty C] : IsProbabilityMeasure (maxEnt T w) :=
  isProbabilityMeasure_tilted .of_finite

/-- On finitely many candidates the expected violation vector is a weighted sum. -/
theorem integral_eq_sum (q : Measure C) [IsFiniteMeasure q] :
    ∫ c, T c ∂q = ∑ c, q.real {c} • T c :=
  integral_fintype .of_finite

/-! ### Probabilities -/

theorem maxEnt_real_singleton (c : C) : (maxEnt T w).real {c} = softmax (harmony T w) c := by
  simp [maxEnt, tilted_real_singleton, softmax_def]

theorem maxEnt_singleton (c : C) :
    maxEnt T w {c} = ENNReal.ofReal (softmax (harmony T w) c) := by
  rw [← maxEnt_real_singleton, ofReal_measureReal]

theorem maxEnt_real_singleton_pos (c : C) : 0 < (maxEnt T w).real {c} := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton]
  exact softmax_pos _ c

/-- Every candidate has positive probability, so every distribution of the candidates is
absolutely continuous with respect to the MaxEnt distribution. -/
theorem absolutelyContinuous_maxEnt (q : Measure C) : q ≪ maxEnt T w := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · simp
  · exact absurd (measure_mono_null (Set.singleton_subset_iff.2 hc) hs) fun h0 ↦
      (maxEnt_real_singleton_pos T w c).ne' (by simp [measureReal_def, h0])

/-- Harmony is log-probability up to the log of the normalizing constant. -/
theorem log_maxEnt_real_singleton (c : C) :
    log ((maxEnt T w).real {c}) = harmony T w c - log (∑ c', exp (harmony T w c')) := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton, log_softmax]

/-- The log-odds of two candidates are their harmony difference, `-(w ⬝ᵥ (T a - T b))`, linear
in the weights. -/
theorem log_maxEnt_real_singleton_div (a b : C) :
    log ((maxEnt T w).real {a} / (maxEnt T w).real {b}) = harmony T w a - harmony T w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, log_softmax_div_softmax]

theorem maxEnt_real_singleton_lt_iff {a b : C} :
    (maxEnt T w).real {a} < (maxEnt T w).real {b} ↔ harmony T w a < harmony T w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, softmax_lt_softmax_iff]

theorem maxEnt_real_singleton_le_iff {a b : C} :
    (maxEnt T w).real {a} ≤ (maxEnt T w).real {b} ↔ harmony T w a ≤ harmony T w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, softmax_le_softmax_iff]

/-- Of exactly two candidates, one has the sigmoid of its harmony advantage over the other. -/
theorem maxEnt_real_singleton_of_pair [DecidableEq C] {a b : C} (hab : a ≠ b)
    (h : (univ : Finset C) = {a, b}) :
    (maxEnt T w).real {a} = sigmoid (harmony T w a - harmony T w b) := by
  rw [maxEnt_real_singleton, softmax_eq_sigmoid_of_univ_eq_pair hab h]

/-- Scaling the weights scales the harmonies, so the MaxEnt distribution concentrates on a
candidate of strictly greatest harmony. -/
theorem tendsto_maxEnt_smul_atTop {c : C} (h : ∀ c' ≠ c, harmony T w c' < harmony T w c) :
    Tendsto (fun α : ℝ ↦ (maxEnt T (α • w)).real {c}) atTop (𝓝 1) := by
  simpa [maxEnt_real_singleton, harmony_smul] using tendsto_softmax_atTop h

/-! ### Expected log-probability -/

/-- The expected log-probability of the candidates under a distribution `q` depends on `q` only
through its expected violations. -/
theorem integral_log_maxEnt_real_singleton (q : Measure C) [IsProbabilityMeasure q] :
    ∫ c, log ((maxEnt T w).real {c}) ∂q =
      -(w ⬝ᵥ ∫ c, T c ∂q) - log (∑ c, exp (harmony T w c)) := by
  rw [integral_fintype .of_finite, integral_eq_sum]
  simp only [smul_eq_mul, log_maxEnt_real_singleton, mul_sub, sum_sub_distrib, ← sum_mul,
    sum_measureReal_singleton_eq_one, one_mul, harmony, dotProduct_sum, dotProduct_smul,
    mul_neg, sum_neg_distrib]

variable (p : Measure C) [IsProbabilityMeasure p]

theorem logLikelihood_eq :
    logLikelihood T p w = -(w ⬝ᵥ ∫ c, T c ∂p) - log (∑ c, exp (harmony T w c)) :=
  integral_log_maxEnt_real_singleton T w p

variable [Nonempty C]

/-! ### The maximum entropy principle -/

/-- The divergence of `q` from the MaxEnt distribution and the entropy of `q` add up to the
expected penalty `w ⬝ᵥ ∫ c, T c ∂q` plus the log of the normalizing constant. -/
theorem toReal_klDiv_maxEnt_add_measureEntropy (q : Measure C) [IsProbabilityMeasure q] :
    (klDiv q (maxEnt T w)).toReal + Hm[q] =
      w ⬝ᵥ (∫ c, T c ∂q) + log (∑ c, exp (harmony T w c)) := by
  have h := integral_log_maxEnt_real_singleton T w q
  rw [integral_fintype .of_finite] at h
  simp only [smul_eq_mul] at h
  rw [toReal_klDiv_add_measureEntropy (absolutelyContinuous_maxEnt T w q), h]
  ring

theorem measureEntropy_maxEnt :
    Hm[maxEnt T w] = w ⬝ᵥ (∫ c, T c ∂maxEnt T w) + log (∑ c, exp (harmony T w c)) := by
  simpa using toReal_klDiv_maxEnt_add_measureEntropy T w (maxEnt T w)

/-- A distribution with the expected violations of a MaxEnt distribution falls short of its
entropy by its divergence from it. -/
theorem measureEntropy_add_toReal_klDiv_maxEnt {q : Measure C} [IsProbabilityMeasure q]
    (hq : ∫ c, T c ∂q = ∫ c, T c ∂maxEnt T w) :
    Hm[q] + (klDiv q (maxEnt T w)).toReal = Hm[maxEnt T w] := by
  rw [measureEntropy_maxEnt, ← hq, ← toReal_klDiv_maxEnt_add_measureEntropy, add_comm]

/-- The maximum entropy principle. No distribution with the expected violations of a MaxEnt
distribution has more entropy. -/
theorem measureEntropy_le_maxEnt {q : Measure C} [IsProbabilityMeasure q]
    (hq : ∫ c, T c ∂q = ∫ c, T c ∂maxEnt T w) : Hm[q] ≤ Hm[maxEnt T w] := by
  rw [← measureEntropy_add_toReal_klDiv_maxEnt T w hq]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- The MaxEnt distribution is the only distribution with its expected violations and its
entropy. -/
theorem eq_maxEnt_of_measureEntropy_eq {q : Measure C} [IsProbabilityMeasure q]
    (hq : ∫ c, T c ∂q = ∫ c, T c ∂maxEnt T w) (h : Hm[q] = Hm[maxEnt T w]) :
    q = maxEnt T w := by
  have hkl := measureEntropy_add_toReal_klDiv_maxEnt T w hq
  rw [h, add_eq_left] at hkl
  exact klDiv_eq_zero_iff.1 (((ENNReal.toReal_eq_zero_iff _).1 hkl).resolve_right
    (klDiv_ne_top (absolutelyContinuous_maxEnt T w q) .of_finite))

/-- The MaxEnt distribution has the greatest entropy among the distributions with its expected
violations. -/
theorem isGreatest_measureEntropy_maxEnt :
    IsGreatest (measureEntropy '' {q | IsProbabilityMeasure q ∧
      ∫ c, T c ∂q = ∫ c, T c ∂maxEnt T w}) (Hm[maxEnt T w]) :=
  ⟨⟨maxEnt T w, ⟨inferInstance, rfl⟩, rfl⟩, by
    rintro _ ⟨q, ⟨hq, hv⟩, rfl⟩
    exact measureEntropy_le_maxEnt T w hv⟩

/-! ### Learning -/

/-- The log-likelihood is concave in the weights: it is linear in them less the log-sum-exp of
the harmonies, which are linear in them. -/
theorem concaveOn_logLikelihood : ConcaveOn ℝ Set.univ (logLikelihood T p) := by
  have hlin : ConcaveOn ℝ Set.univ fun w : ι → ℝ ↦ -(w ⬝ᵥ ∫ c, T c ∂p) :=
    (LinearMap.concaveOn (-(dotProductBilin ℝ ℝ |>.flip (∫ c, T c ∂p))) convex_univ).congr
      fun w _ ↦ by simp
  have hlse : ConvexOn ℝ Set.univ fun w : ι → ℝ ↦ log (∑ c, exp (harmony T w c)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    have := convexOn_log_sum_exp.2 (Set.mem_univ (harmony T x)) (Set.mem_univ (harmony T y))
      ha hb hab
    simpa [harmony_add, harmony_smul] using this
  exact (hlin.sub hlse).congr fun w _ ↦ (logLikelihood_eq T w p).symm

/-- The gradient of the log-likelihood is the expected less the observed violation vector. -/
theorem hasFDerivAt_logLikelihood :
    HasFDerivAt (logLikelihood T p)
      (LinearMap.toContinuousLinearMap
        (dotProductBilin ℝ ℝ ((∫ c, T c ∂maxEnt T w) - ∫ c, T c ∂p))) w := by
  let ℓ (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ a)
  have hℓ (a v : ι → ℝ) : ℓ a v = a ⬝ᵥ v := rfl
  have hH (c : C) : HasFDerivAt (fun w ↦ harmony T w c) (-ℓ (T c)) w :=
    (-ℓ (T c)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w ↦ by simp [harmony, hℓ, dotProduct_comm])
  have hZ := (HasFDerivAt.fun_sum fun c (_ : c ∈ univ) ↦ (hH c).exp).log
    (sum_exp_pos (harmony T w)).ne'
  have hlin : HasFDerivAt (fun w ↦ -(w ⬝ᵥ ∫ c, T c ∂p)) (-ℓ (∫ c, T c ∂p)) w :=
    (-ℓ (∫ c, T c ∂p)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w ↦ by simp [hℓ, dotProduct_comm])
  refine (hlin.sub hZ).congr_of_eventuallyEq (Eventually.of_forall fun w ↦ logLikelihood_eq T w p)
    |>.congr_fderiv ?_
  ext v
  simp only [sub_apply, neg_apply, smul_apply, _root_.sum_apply, hℓ, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap', dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk,
    integral_eq_sum, maxEnt_real_singleton, softmax_def, sub_dotProduct, sum_dotProduct,
    smul_dotProduct, mul_neg, sum_neg_distrib, mul_sum, div_eq_inv_mul, mul_assoc]
  ring

/-- The partial derivative of the log-likelihood in the weight of constraint `j` is that
constraint's expected violations less its observed ones. -/
theorem hasDerivAt_logLikelihood_update [DecidableEq ι] (j : ι) :
    HasDerivAt (fun t ↦ logLikelihood T p (Function.update w j t))
      ((∫ c, T c ∂maxEnt T w) j - (∫ c, T c ∂p) j) (w j) := by
  have := (hasFDerivAt_logLikelihood T w p).comp_hasDerivAt_of_eq (w j)
    (hasDerivAt_update w j (w j)) (Function.update_eq_self j w).symm
  exact this.congr_deriv (by simp [dotProductBilin, dotProduct_single])

/-- Weights maximize the log-likelihood exactly when their MaxEnt distribution has the observed
expected violations. -/
theorem isMaxOn_logLikelihood_iff :
    IsMaxOn (logLikelihood T p) Set.univ w ↔ ∫ c, T c ∂maxEnt T w = ∫ c, T c ∂p := by
  classical
  constructor
  · intro h
    have h0 := (h.isLocalMax Filter.univ_mem).hasFDerivAt_eq_zero (hasFDerivAt_logLikelihood T w p)
    funext j
    have := congrArg (· (Pi.single j 1)) h0
    simpa [dotProductBilin, dotProduct_single, sub_eq_zero] using this
  · intro h w' _
    have hent := toReal_klDiv_maxEnt_add_measureEntropy T w' (maxEnt T w)
    have hent' := measureEntropy_maxEnt T w
    change logLikelihood T p w' ≤ logLikelihood T p w
    rw [logLikelihood_eq, logLikelihood_eq, ← h]
    linarith [ENNReal.toReal_nonneg (a := klDiv (maxEnt T w) (maxEnt T w'))]

/-- The most likely MaxEnt grammar of an empirical distribution gives the maximum-entropy
distribution among those with the observed expected violations. -/
theorem isGreatest_measureEntropy_of_isMaxOn (h : IsMaxOn (logLikelihood T p) Set.univ w) :
    IsGreatest (measureEntropy '' {q | IsProbabilityMeasure q ∧
      ∫ c, T c ∂q = ∫ c, T c ∂p}) (Hm[maxEnt T w]) := by
  simpa [(isMaxOn_logLikelihood_iff T w p).1 h] using isGreatest_measureEntropy_maxEnt T w

/-! ### Joint evaluation -/

section Joint

variable {κ O : Type*} [Fintype κ] [DecidableEq κ] [Fintype O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [Nonempty O] (T : κ → O → ι → ℝ)

/-- When the violations of an output tuple add up its coordinates' violations, the MaxEnt
distribution of the tuples is the product of the coordinates' MaxEnt distributions, so the
coordinates are independent. -/
theorem maxEnt_sum :
    maxEnt (fun f : κ → O ↦ ∑ k, T k (f k)) w = Measure.pi fun k ↦ maxEnt (T k) w := by
  refine Measure.ext_iff_singleton.2 fun f ↦ ?_
  simp_rw [Measure.pi_singleton, maxEnt_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ ↦ softmax_nonneg _ _, funext (harmony_sum T w),
    softmax_sum_apply (fun k ↦ harmony (T k) w) f]

/-- The marginal of such a distribution at a coordinate is that coordinate's MaxEnt
distribution. -/
theorem map_eval_maxEnt_sum (k : κ) :
    (maxEnt (fun f : κ → O ↦ ∑ k, T k (f k)) w).map (Function.eval k) = maxEnt (T k) w := by
  simp [maxEnt_sum, Measure.pi_map_eval]

end Joint

end HarmonicGrammar
