/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Core.InformationTheory.Entropy.Basic
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
maximum-entropy one. A conditional grammar, a Markov kernel from inputs to the MaxEnt
distributions of their candidates, satisfies the same duality with conditional entropy, the
expected violations averaged over the observed inputs.

## Main definitions

* `HarmonicGrammar.maxEnt T w`: the MaxEnt distribution of the candidates.
* `HarmonicGrammar.logPartition T w`: the log of its normalizing constant.
* `HarmonicGrammar.logLikelihood T p w`: the expected log-probability, under the grammar, of the
  candidates drawn from `p`.
* `HarmonicGrammar.condMaxEnt T w`, `HarmonicGrammar.condLogLikelihood T p w`: the conditional
  grammar and its log-likelihood on input–output pairs drawn from `p`.

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
* `isGreatest_condEntropy_condMaxEnt`, `isMaxOn_condLogLikelihood_iff`,
  `condLogLikelihood_eq_neg_condEntropy`, `isGreatest_condEntropy_of_isMaxOn`: the conditional
  duality.
* `tendsto_maxEnt_smul_atTop`: scaling the weights concentrates the distribution on the harmony
  maximum.

## Implementation notes

* The candidates of one input form a finite type. A conditional grammar takes, at an input `i`,
  the violations `(con.comap (i, ·)).violations` of the candidates paired with `i`, and
  `condMaxEnt` assembles these into a kernel over finitely many inputs.
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

variable {C ι : Type*} [Fintype ι]

section LogPartition

variable [Fintype C] (T : C → ι → ℝ) (w : ι → ℝ)

/-- The log-partition function, the log of the normalizing constant of the MaxEnt
distribution. -/
noncomputable def logPartition : ℝ :=
  log (∑ c, exp (harmony T w c))

theorem convexOn_logPartition [Nonempty C] : ConvexOn ℝ Set.univ (logPartition T) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have := convexOn_log_sum_exp.2 (Set.mem_univ (harmony T x)) (Set.mem_univ (harmony T y))
    ha hb hab
  simpa [logPartition, harmony_add, harmony_smul] using this

end LogPartition

variable [MeasurableSpace C]

/-- The MaxEnt distribution of candidates with violation vectors `T` under weights `w` weighs each
candidate by the exponential of its harmony. -/
noncomputable def maxEnt (T : C → ι → ℝ) (w : ι → ℝ) : Measure C :=
  Measure.count.tilted (harmony T w)

theorem maxEnt_congr {ι' : Type*} [Fintype ι'] {T : C → ι → ℝ} {w : ι → ℝ} {T' : C → ι' → ℝ}
    {w' : ι' → ℝ} (h : harmony T w = harmony T' w') : maxEnt T w = maxEnt T' w' := by
  simp only [maxEnt, h]

/-- The log-likelihood of an empirical distribution `p` under a grammar is the expected
log-probability of the candidates drawn from `p`. -/
noncomputable def logLikelihood (T : C → ι → ℝ) (p : Measure C) (w : ι → ℝ) : ℝ :=
  ∫ c, log ((maxEnt T w).real {c}) ∂p

@[simp] theorem logLikelihood_dirac [MeasurableSingletonClass C] (T : C → ι → ℝ) (w : ι → ℝ)
    (c : C) : logLikelihood T (Measure.dirac c) w = log ((maxEnt T w).real {c}) := by
  simp [logLikelihood]

variable [Fintype C] [MeasurableSingletonClass C] (T : C → ι → ℝ) (w : ι → ℝ)

instance : IsZeroOrProbabilityMeasure (maxEnt T w) := by
  unfold maxEnt; infer_instance

instance [Nonempty C] : IsProbabilityMeasure (maxEnt T w) :=
  isProbabilityMeasure_tilted .of_finite

theorem integral_eq_sum (q : Measure C) [IsFiniteMeasure q] :
    ∫ c, T c ∂q = ∑ c, q.real {c} • T c :=
  integral_fintype .of_finite

/-! ### Probabilities -/

theorem maxEnt_real_singleton (c : C) : (maxEnt T w).real {c} = softmax (harmony T w) c :=
  count_tilted_real_singleton _ c

theorem maxEnt_singleton (c : C) :
    maxEnt T w {c} = ENNReal.ofReal (softmax (harmony T w) c) := by
  rw [← maxEnt_real_singleton, ofReal_measureReal]

theorem maxEnt_real_singleton_pos (c : C) : 0 < (maxEnt T w).real {c} := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton]
  exact softmax_pos _ c

theorem absolutelyContinuous_maxEnt (q : Measure C) : q ≪ maxEnt T w := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · simp
  · exact absurd (measure_mono_null (Set.singleton_subset_iff.2 hc) hs) fun h0 ↦
      (maxEnt_real_singleton_pos T w c).ne' (by simp [measureReal_def, h0])

theorem log_maxEnt_real_singleton (c : C) :
    log ((maxEnt T w).real {c}) = harmony T w c - logPartition T w := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton, log_softmax, logPartition]

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

/-- Scaling the weights scales the harmonies, so the MaxEnt distribution concentrates on the sole
candidate of greatest harmony. -/
theorem tendsto_maxEnt_smul_atTop {c : C} (h : univ.argmax (harmony T w) = {c}) :
    Tendsto (fun α : ℝ ↦ (maxEnt T (α • w)).real {c}) atTop (𝓝 1) := by
  simpa [maxEnt_real_singleton, harmony_smul] using tendsto_softmax_atTop fun c' hc' ↦
    (Finset.argmax_eq_singleton_iff.1 h).2 c' (mem_univ c') hc'

/-! ### Expected log-probability -/

theorem integral_log_maxEnt_real_singleton (q : Measure C) [IsProbabilityMeasure q] :
    ∫ c, log ((maxEnt T w).real {c}) ∂q =
      -(w ⬝ᵥ ∫ c, T c ∂q) - logPartition T w := by
  rw [integral_fintype .of_finite, integral_eq_sum]
  simp only [smul_eq_mul, log_maxEnt_real_singleton, mul_sub, sum_sub_distrib, ← sum_mul,
    sum_measureReal_singleton_eq_one, one_mul, harmony, dotProduct_sum, dotProduct_smul,
    mul_neg, sum_neg_distrib]

variable (p : Measure C) [IsProbabilityMeasure p]

theorem logLikelihood_eq :
    logLikelihood T p w = -(w ⬝ᵥ ∫ c, T c ∂p) - logPartition T w :=
  integral_log_maxEnt_real_singleton T w p

variable [Nonempty C]

/-! ### The maximum entropy principle -/

theorem toReal_klDiv_maxEnt_add_measureEntropy (q : Measure C) [IsProbabilityMeasure q] :
    (klDiv q (maxEnt T w)).toReal + Hm[q] =
      w ⬝ᵥ (∫ c, T c ∂q) + logPartition T w := by
  have h := integral_log_maxEnt_real_singleton T w q
  rw [integral_fintype .of_finite] at h
  simp only [smul_eq_mul] at h
  rw [toReal_klDiv_add_measureEntropy (absolutelyContinuous_maxEnt T w q), h]
  ring

theorem measureEntropy_maxEnt :
    Hm[maxEnt T w] = w ⬝ᵥ (∫ c, T c ∂maxEnt T w) + logPartition T w := by
  simpa using toReal_klDiv_maxEnt_add_measureEntropy T w (maxEnt T w)

theorem measureEntropy_add_toReal_klDiv_maxEnt {q : Measure C} [IsProbabilityMeasure q]
    (hq : ∫ c, T c ∂q = ∫ c, T c ∂maxEnt T w) :
    Hm[q] + (klDiv q (maxEnt T w)).toReal = Hm[maxEnt T w] := by
  rw [measureEntropy_maxEnt, ← hq, ← toReal_klDiv_maxEnt_add_measureEntropy, add_comm]

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

theorem hasFDerivAt_logPartition :
    HasFDerivAt (logPartition T)
      (-LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ (∫ c, T c ∂maxEnt T w))) w := by
  let ℓ (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ a)
  have hℓ (a v : ι → ℝ) : ℓ a v = a ⬝ᵥ v := rfl
  have hH (c : C) : HasFDerivAt (fun w ↦ harmony T w c) (-ℓ (T c)) w :=
    (-ℓ (T c)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w ↦ by simp [harmony, hℓ, dotProduct_comm])
  refine (HasFDerivAt.log_sum_exp hH).congr_fderiv ?_
  ext v
  simp only [smul_neg, sum_neg_distrib, neg_apply, _root_.sum_apply, smul_apply, hℓ,
    LinearMap.coe_toContinuousLinearMap', dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk,
    integral_eq_sum, maxEnt_real_singleton, sum_dotProduct, smul_dotProduct, smul_eq_mul]

/-- The log-likelihood is concave in the weights: it is linear in them less the log-partition
function. -/
theorem concaveOn_logLikelihood : ConcaveOn ℝ Set.univ (logLikelihood T p) := by
  have hlin : ConcaveOn ℝ Set.univ fun w : ι → ℝ ↦ -(w ⬝ᵥ ∫ c, T c ∂p) :=
    (LinearMap.concaveOn (-(dotProductBilin ℝ ℝ |>.flip (∫ c, T c ∂p))) convex_univ).congr
      fun w _ ↦ by simp
  exact (hlin.sub (convexOn_logPartition T)).congr fun w _ ↦ (logLikelihood_eq T w p).symm

/-- The gradient of the log-likelihood is the expected less the observed violation vector. -/
theorem hasFDerivAt_logLikelihood :
    HasFDerivAt (logLikelihood T p)
      (LinearMap.toContinuousLinearMap
        (dotProductBilin ℝ ℝ ((∫ c, T c ∂maxEnt T w) - ∫ c, T c ∂p))) w := by
  let ℓ (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ a)
  have hℓ (a v : ι → ℝ) : ℓ a v = a ⬝ᵥ v := rfl
  have hlin : HasFDerivAt (fun w ↦ -(w ⬝ᵥ ∫ c, T c ∂p)) (-ℓ (∫ c, T c ∂p)) w :=
    (-ℓ (∫ c, T c ∂p)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w ↦ by simp [hℓ, dotProduct_comm])
  refine (hlin.sub (hasFDerivAt_logPartition T w)).congr_of_eventuallyEq
    (Eventually.of_forall fun w ↦ logLikelihood_eq T w p) |>.congr_fderiv ?_
  ext v
  simp only [sub_apply, neg_apply, hℓ, LinearMap.coe_toContinuousLinearMap', dotProductBilin,
    LinearMap.coe_mk, AddHom.coe_mk, sub_dotProduct]
  ring

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

theorem map_eval_maxEnt_sum (k : κ) :
    (maxEnt (fun f : κ → O ↦ ∑ k, T k (f k)) w).map (Function.eval k) = maxEnt (T k) w := by
  simp [maxEnt_sum, Measure.pi_map_eval]

end Joint

/-! ### Conditional MaxEnt -/

section Conditional

variable {X Y : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] (T : X × Y → ι → ℝ) (w : ι → ℝ)

/-- The conditional MaxEnt grammar takes each input to the MaxEnt distribution of its candidates,
whose violation vectors are `T (x, ·)`. -/
noncomputable def condMaxEnt : Kernel X Y where
  toFun x := maxEnt (fun y ↦ T (x, y)) w
  measurable' := .of_discrete

@[simp] theorem condMaxEnt_apply (x : X) : condMaxEnt T w x = maxEnt (fun y ↦ T (x, y)) w :=
  rfl

/-- The conditional log-likelihood of an empirical distribution `p` of input–output pairs is the
expected log-probability of each output given its input. -/
noncomputable def condLogLikelihood (p : Measure (X × Y)) (w : ι → ℝ) : ℝ :=
  ∫ z, log ((condMaxEnt T w z.1).real {z.2}) ∂p

variable [Fintype Y] [MeasurableSingletonClass Y] (p : Measure (X × Y)) [IsProbabilityMeasure p]

theorem condLogLikelihood_eq :
    condLogLikelihood T p w =
      -(w ⬝ᵥ ∫ z, T z ∂p) - ∑ x, p.fst.real {x} * logPartition (fun y ↦ T (x, y)) w := by
  simp only [condLogLikelihood, integral_fintype .of_finite, Fintype.sum_prod_type, smul_eq_mul,
    condMaxEnt_apply, log_maxEnt_real_singleton, Measure.fst_real_singleton_eq_sum, mul_sub,
    sum_sub_distrib, sum_mul, harmony, dotProduct_sum, dotProduct_smul, mul_neg,
    sum_neg_distrib]

variable [Nonempty Y]

instance : IsMarkovKernel (condMaxEnt T w) :=
  ⟨fun x ↦ by rw [condMaxEnt_apply]; infer_instance⟩

variable (ν : Measure X) [IsProbabilityMeasure ν]

theorem sum_toReal_klDiv_condMaxEnt_add_condEntropy (q : Kernel X Y) [IsMarkovKernel q] :
    ∑ x, ν.real {x} * (klDiv (q x) (condMaxEnt T w x)).toReal + H[Prod.snd | Prod.fst ; ν ⊗ₘ q] =
      w ⬝ᵥ (∫ z, T z ∂(ν ⊗ₘ q)) + ∑ x, ν.real {x} * logPartition (fun y ↦ T (x, y)) w := by
  rw [condEntropy_snd_fst_compProd q ν, Measure.integral_compProd_eq_sum, dotProduct_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [dotProduct_smul, smul_eq_mul, ← mul_add, ← mul_add, condMaxEnt_apply,
    toReal_klDiv_maxEnt_add_measureEntropy]

theorem condEntropy_condMaxEnt :
    H[Prod.snd | Prod.fst ; ν ⊗ₘ condMaxEnt T w] =
      w ⬝ᵥ (∫ z, T z ∂(ν ⊗ₘ condMaxEnt T w)) +
        ∑ x, ν.real {x} * logPartition (fun y ↦ T (x, y)) w := by
  simpa using sum_toReal_klDiv_condMaxEnt_add_condEntropy T w ν (condMaxEnt T w)

theorem condEntropy_add_sum_toReal_klDiv {q : Kernel X Y} [IsMarkovKernel q]
    (hq : ∫ z, T z ∂(ν ⊗ₘ q) = ∫ z, T z ∂(ν ⊗ₘ condMaxEnt T w)) :
    H[Prod.snd | Prod.fst ; ν ⊗ₘ q] + ∑ x, ν.real {x} * (klDiv (q x) (condMaxEnt T w x)).toReal =
      H[Prod.snd | Prod.fst ; ν ⊗ₘ condMaxEnt T w] := by
  rw [condEntropy_condMaxEnt, ← hq, ← sum_toReal_klDiv_condMaxEnt_add_condEntropy, add_comm]

theorem condEntropy_le_condMaxEnt {q : Kernel X Y} [IsMarkovKernel q]
    (hq : ∫ z, T z ∂(ν ⊗ₘ q) = ∫ z, T z ∂(ν ⊗ₘ condMaxEnt T w)) :
    H[Prod.snd | Prod.fst ; ν ⊗ₘ q] ≤ H[Prod.snd | Prod.fst ; ν ⊗ₘ condMaxEnt T w] := by
  rw [← condEntropy_add_sum_toReal_klDiv T w ν hq]
  exact le_add_of_nonneg_right <| sum_nonneg fun x _ ↦
    mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg

theorem eq_condMaxEnt_of_condEntropy_eq {q : Kernel X Y} [IsMarkovKernel q]
    (hq : ∫ z, T z ∂(ν ⊗ₘ q) = ∫ z, T z ∂(ν ⊗ₘ condMaxEnt T w))
    (h : H[Prod.snd | Prod.fst ; ν ⊗ₘ q] = H[Prod.snd | Prod.fst ; ν ⊗ₘ condMaxEnt T w]) {x : X}
    (hx : ν {x} ≠ 0) : q x = condMaxEnt T w x := by
  have hkl := condEntropy_add_sum_toReal_klDiv T w ν hq
  rw [h, add_eq_left, sum_eq_zero_iff_of_nonneg fun x _ ↦
    mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg] at hkl
  have hx' := (mul_eq_zero.1 (hkl x (mem_univ x))).resolve_left
    ((measureReal_ne_zero_iff (measure_ne_top _ _)).2 hx)
  rw [condMaxEnt_apply] at hx' ⊢
  exact klDiv_eq_zero_iff.1 (((ENNReal.toReal_eq_zero_iff _).1 hx').resolve_right
    (klDiv_ne_top (absolutelyContinuous_maxEnt _ w (q x)) .of_finite))

/-- The conditional MaxEnt grammar has the greatest conditional entropy among the conditional
models with its average expected violations. -/
theorem isGreatest_condEntropy_condMaxEnt :
    IsGreatest ((fun q : Kernel X Y ↦ H[Prod.snd | Prod.fst ; ν ⊗ₘ q]) ''
      {q | IsMarkovKernel q ∧ ∫ z, T z ∂(ν ⊗ₘ q) = ∫ z, T z ∂(ν ⊗ₘ condMaxEnt T w)})
      (H[Prod.snd | Prod.fst ; ν ⊗ₘ condMaxEnt T w]) :=
  ⟨⟨condMaxEnt T w, ⟨inferInstance, rfl⟩, rfl⟩, by
    rintro _ ⟨q, ⟨hq, hv⟩, rfl⟩
    exact condEntropy_le_condMaxEnt T w ν hv⟩


theorem concaveOn_condLogLikelihood : ConcaveOn ℝ Set.univ (condLogLikelihood T p) := by
  have hlin : ConcaveOn ℝ Set.univ fun w : ι → ℝ ↦ -(w ⬝ᵥ ∫ z, T z ∂p) :=
    (LinearMap.concaveOn (-(dotProductBilin ℝ ℝ |>.flip (∫ z, T z ∂p))) convex_univ).congr
      fun w _ ↦ by simp
  have hZ : ConvexOn ℝ Set.univ fun w : ι → ℝ ↦
      ∑ x, p.fst.real {x} * logPartition (fun y ↦ T (x, y)) w := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
    simp only [smul_eq_mul, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ ↦ ?_
    have h := (convexOn_logPartition (fun y ↦ T (x, y))).2 (Set.mem_univ u) (Set.mem_univ v)
      ha hb hab
    simp only [smul_eq_mul] at h
    calc _ ≤ p.fst.real {x} * (a * logPartition (fun y ↦ T (x, y)) u +
          b * logPartition (fun y ↦ T (x, y)) v) := mul_le_mul_of_nonneg_left h measureReal_nonneg
      _ = _ := by ring
  exact (hlin.sub hZ).congr fun w _ ↦ (condLogLikelihood_eq T w p).symm

theorem hasFDerivAt_condLogLikelihood :
    HasFDerivAt (condLogLikelihood T p)
      (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ
        ((∫ z, T z ∂(p.fst ⊗ₘ condMaxEnt T w)) - ∫ z, T z ∂p))) w := by
  let ℓ (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ a)
  have hℓ (a v : ι → ℝ) : ℓ a v = a ⬝ᵥ v := rfl
  have hlin : HasFDerivAt (fun w ↦ -(w ⬝ᵥ ∫ z, T z ∂p)) (-ℓ (∫ z, T z ∂p)) w :=
    (-ℓ (∫ z, T z ∂p)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w ↦ by simp [hℓ, dotProduct_comm])
  have hZ := HasFDerivAt.fun_sum fun x (_ : x ∈ univ) ↦
    (hasFDerivAt_logPartition (fun y ↦ T (x, y)) w).const_mul (p.fst.real {x})
  refine (hlin.sub hZ).congr_of_eventuallyEq
    (Eventually.of_forall fun w ↦ condLogLikelihood_eq T w p) |>.congr_fderiv ?_
  ext v
  simp only [sub_apply, neg_apply, _root_.sum_apply, smul_apply, hℓ, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap', dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk,
    Measure.integral_compProd_eq_sum, condMaxEnt_apply, sub_dotProduct, sum_dotProduct,
    smul_dotProduct, mul_neg, sum_neg_distrib]
  ring

/-- Weights maximize the conditional log-likelihood exactly when the expected violations of their
grammar, over the observed inputs, are the observed ones. -/
theorem isMaxOn_condLogLikelihood_iff :
    IsMaxOn (condLogLikelihood T p) Set.univ w ↔
      ∫ z, T z ∂(p.fst ⊗ₘ condMaxEnt T w) = ∫ z, T z ∂p := by
  classical
  constructor
  · intro h
    have h0 := (h.isLocalMax Filter.univ_mem).hasFDerivAt_eq_zero
      (hasFDerivAt_condLogLikelihood T w p)
    funext j
    have := congrArg (· (Pi.single j 1)) h0
    simpa [dotProductBilin, dotProduct_single, sub_eq_zero] using this
  · intro h w' _
    have h₁ := sum_toReal_klDiv_condMaxEnt_add_condEntropy T w' p.fst (condMaxEnt T w)
    have h₂ := condEntropy_condMaxEnt T w p.fst
    have h₃ : 0 ≤ ∑ x, p.fst.real {x} * (klDiv (condMaxEnt T w x) (condMaxEnt T w' x)).toReal :=
      sum_nonneg fun x _ ↦ mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg
    change condLogLikelihood T p w' ≤ condLogLikelihood T p w
    rw [condLogLikelihood_eq, condLogLikelihood_eq, ← h]
    linarith

/-- At weights matching the observed violations the conditional log-likelihood is minus the
conditional entropy of the grammar, the common value of the two dual problems. -/
theorem condLogLikelihood_eq_neg_condEntropy
    (h : ∫ z, T z ∂(p.fst ⊗ₘ condMaxEnt T w) = ∫ z, T z ∂p) :
    condLogLikelihood T p w = -H[Prod.snd | Prod.fst ; p.fst ⊗ₘ condMaxEnt T w] := by
  rw [condLogLikelihood_eq, condEntropy_condMaxEnt, h]
  ring

/-- The most likely conditional MaxEnt grammar of an empirical distribution has the greatest
conditional entropy among the conditional models with the observed expected violations. -/
theorem isGreatest_condEntropy_of_isMaxOn (h : IsMaxOn (condLogLikelihood T p) Set.univ w) :
    IsGreatest ((fun q : Kernel X Y ↦ H[Prod.snd | Prod.fst ; p.fst ⊗ₘ q]) ''
      {q | IsMarkovKernel q ∧ ∫ z, T z ∂(p.fst ⊗ₘ q) = ∫ z, T z ∂p})
      (H[Prod.snd | Prod.fst ; p.fst ⊗ₘ condMaxEnt T w]) := by
  simpa [(isMaxOn_condLogLikelihood_iff T w p).1 h] using
    isGreatest_condEntropy_condMaxEnt T w p.fst

end Conditional

end HarmonicGrammar
