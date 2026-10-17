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
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# MaxEnt grammars

A MaxEnt grammar makes the harmonies of a Harmonic Grammar into probabilities: a candidate's
probability is proportional to the exponential of its harmony, so harmony is log-probability up to
a normalizing constant. As a measure, the MaxEnt distribution of a constraint set under a weight
vector is the counting measure on the candidates tilted by harmony.

The name records a duality. Among the distributions of the candidates with the same expected
violations as a MaxEnt distribution, the MaxEnt one has the greatest entropy. The log-likelihood
of an empirical distribution is concave in the weights, its partial derivatives are expected less
observed violations, and the weights that maximize it are exactly those whose distribution matches
the observed violations, so the most likely MaxEnt grammar is the maximum-entropy one.

## Main definitions

* `HarmonicGrammar.maxEnt con w`: the MaxEnt distribution of the candidates.
* `OptimalityTheory.ConstraintSet.expectedViolations con q`: each constraint's expected
  violations under a distribution `q`.
* `HarmonicGrammar.logLikelihood con p w`: the expected log-probability, under the grammar, of
  the candidates drawn from `p`.

## Main results

* `maxEnt_real_singleton`: a candidate's probability is the softmax of the harmonies.
* `log_maxEnt_real_singleton_div`: log-odds are harmony differences.
* `maxEnt_real_singleton_of_pair`: of two candidates, one has the sigmoid of the harmony
  difference.
* `isGreatest_measureEntropy_maxEnt`, `eq_maxEnt_of_measureEntropy_eq`: the maximum entropy
  principle.
* `concaveOn_logLikelihood`, `hasDerivAt_logLikelihood_update`: the log-likelihood is concave, with
  partial derivatives expected less observed violations.
* `isMaxOn_logLikelihood_iff`, `isGreatest_measureEntropy_of_isMaxOn`: maximum likelihood is
  matching the observed violations, and gives the maximum-entropy distribution.
* `maxEnt_joint`: jointly evaluated inputs are independent.
* `tendsto_maxEnt_smul_atTop`: scaling the weights concentrates the distribution on the harmony
  maximum.

## Implementation notes

* The candidates of one input form a finite type. A conditional grammar takes, at an input `i`,
  the constraint set `con.comap (i, ·)` of the candidates paired with `i`.
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

namespace OptimalityTheory.ConstraintSet

variable {C ι : Type*} [MeasurableSpace C]

/-- The expected violations of each constraint under a distribution `q` of the candidates. -/
noncomputable def expectedViolations (con : ConstraintSet C ι) (q : Measure C) : ι → ℝ :=
  fun j ↦ ∫ c, (con j c : ℝ) ∂q

theorem expectedViolations_apply [Fintype C] [MeasurableSingletonClass C]
    (con : ConstraintSet C ι) (q : Measure C) [IsFiniteMeasure q] (j : ι) :
    con.expectedViolations q j = ∑ c, q.real {c} * con j c := by
  simp [expectedViolations, integral_fintype .of_finite]

@[simp] theorem expectedViolations_dirac [MeasurableSingletonClass C] (con : ConstraintSet C ι)
    (c : C) : con.expectedViolations (Measure.dirac c) = fun j ↦ (con j c : ℝ) := by
  funext j
  simp [expectedViolations]

end OptimalityTheory.ConstraintSet

namespace HarmonicGrammar

open OptimalityTheory

variable {C ι : Type*} [MeasurableSpace C] [Fintype ι]

/-- The MaxEnt distribution of a harmonic grammar weighs each candidate by the exponential of its
harmony. -/
noncomputable def maxEnt (con : ConstraintSet C ι) (w : ι → ℝ) : Measure C :=
  Measure.count.tilted (harmonyScore con w)

/-- A MaxEnt distribution depends on the grammar only through its harmonies. -/
theorem maxEnt_congr {ι' : Type*} [Fintype ι'] {con : ConstraintSet C ι} {w : ι → ℝ}
    {con' : ConstraintSet C ι'} {w' : ι' → ℝ} (h : harmonyScore con w = harmonyScore con' w') :
    maxEnt con w = maxEnt con' w' := by
  simp only [maxEnt, h]

/-- The log-likelihood of an empirical distribution `p` under a grammar is the expected
log-probability of the candidates drawn from `p`. -/
noncomputable def logLikelihood (con : ConstraintSet C ι) (p : Measure C) (w : ι → ℝ) : ℝ :=
  ∫ c, log ((maxEnt con w).real {c}) ∂p

/-- The log-likelihood of a single observation is its log-probability. -/
@[simp] theorem logLikelihood_dirac [MeasurableSingletonClass C] (con : ConstraintSet C ι)
    (w : ι → ℝ) (c : C) :
    logLikelihood con (Measure.dirac c) w = log ((maxEnt con w).real {c}) := by
  simp [logLikelihood]

variable [Fintype C] [MeasurableSingletonClass C] (con : ConstraintSet C ι) (w : ι → ℝ)

instance : IsZeroOrProbabilityMeasure (maxEnt con w) := by
  unfold maxEnt; infer_instance

instance [Nonempty C] : IsProbabilityMeasure (maxEnt con w) :=
  isProbabilityMeasure_tilted .of_finite

/-! ### Probabilities -/

theorem maxEnt_real_singleton (c : C) :
    (maxEnt con w).real {c} = softmax (harmonyScore con w) c := by
  simp [maxEnt, tilted_real_singleton, softmax_def]

theorem maxEnt_singleton (c : C) :
    maxEnt con w {c} = ENNReal.ofReal (softmax (harmonyScore con w) c) := by
  rw [← maxEnt_real_singleton, ofReal_measureReal]

theorem maxEnt_real_singleton_pos (c : C) : 0 < (maxEnt con w).real {c} := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton]
  exact softmax_pos _ c

/-- Every candidate has positive probability, so every distribution of the candidates is
absolutely continuous with respect to the MaxEnt distribution. -/
theorem absolutelyContinuous_maxEnt (q : Measure C) : q ≪ maxEnt con w := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · simp
  · exact absurd (measure_mono_null (Set.singleton_subset_iff.2 hc) hs) fun h0 ↦
      (maxEnt_real_singleton_pos con w c).ne' (by simp [measureReal_def, h0])

/-- Harmony is log-probability up to the log of the normalizing constant. -/
theorem log_maxEnt_real_singleton (c : C) :
    log ((maxEnt con w).real {c}) = harmonyScore con w c - log (∑ c', exp (harmonyScore con w c')) := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton, log_softmax]

/-- The log-odds of two candidates are their harmony difference, which `harmonyScore_sub` makes
linear in the weights against the difference of their violations. -/
theorem log_maxEnt_real_singleton_div (a b : C) :
    log ((maxEnt con w).real {a} / (maxEnt con w).real {b}) =
      harmonyScore con w a - harmonyScore con w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, log_softmax_div_softmax]

theorem maxEnt_real_singleton_lt_iff {a b : C} :
    (maxEnt con w).real {a} < (maxEnt con w).real {b} ↔ harmonyScore con w a < harmonyScore con w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, softmax_lt_softmax_iff]

theorem maxEnt_real_singleton_le_iff {a b : C} :
    (maxEnt con w).real {a} ≤ (maxEnt con w).real {b} ↔ harmonyScore con w a ≤ harmonyScore con w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, softmax_le_softmax_iff]

/-- Of exactly two candidates, one has the sigmoid of its harmony advantage over the other. -/
theorem maxEnt_real_singleton_of_pair [DecidableEq C] {a b : C} (hab : a ≠ b)
    (h : (univ : Finset C) = {a, b}) :
    (maxEnt con w).real {a} = sigmoid (harmonyScore con w a - harmonyScore con w b) := by
  rw [maxEnt_real_singleton, softmax_eq_sigmoid_of_univ_eq_pair hab h]

/-- Scaling the weights scales the harmonies, so the MaxEnt distribution concentrates on a
candidate of strictly greatest harmony. -/
theorem tendsto_maxEnt_smul_atTop {c : C}
    (h : ∀ c' ≠ c, harmonyScore con w c' < harmonyScore con w c) :
    Tendsto (fun α : ℝ ↦ (maxEnt con (α • w)).real {c}) atTop (𝓝 1) := by
  simpa [maxEnt_real_singleton, harmonyScore_smul] using tendsto_softmax_atTop h

/-! ### Expected log-probability -/

/-- The expected log-probability of the candidates under a distribution `q` depends on `q` only
through its expected violations. -/
theorem integral_log_maxEnt_real_singleton (q : Measure C) [IsProbabilityMeasure q] :
    ∫ c, log ((maxEnt con w).real {c}) ∂q =
      -(w ⬝ᵥ con.expectedViolations q) - log (∑ c, exp (harmonyScore con w c)) := by
  rw [integral_fintype .of_finite]
  simp only [smul_eq_mul, log_maxEnt_real_singleton, mul_sub, sum_sub_distrib, ← sum_mul,
    sum_measureReal_singleton_eq_one, one_mul]
  congr 1
  simp only [harmonyScore_eq_neg_sum, dotProduct, ConstraintSet.expectedViolations_apply,
    mul_neg, sum_neg_distrib, mul_sum, neg_inj]
  rw [sum_comm]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun c _ ↦ by ring

variable (p : Measure C) [IsProbabilityMeasure p]

theorem logLikelihood_eq :
    logLikelihood con p w =
      -(w ⬝ᵥ con.expectedViolations p) - log (∑ c, exp (harmonyScore con w c)) :=
  integral_log_maxEnt_real_singleton con w p

variable [Nonempty C]

/-! ### The maximum entropy principle -/

/-- The divergence of `q` from the MaxEnt distribution and the entropy of `q` add up to the
expected penalty `w ⬝ᵥ` (expected violations) plus the log of the normalizing constant. -/
theorem toReal_klDiv_maxEnt_add_measureEntropy (q : Measure C) [IsProbabilityMeasure q] :
    (klDiv q (maxEnt con w)).toReal + Hm[q] =
      w ⬝ᵥ con.expectedViolations q + log (∑ c, exp (harmonyScore con w c)) := by
  have h := integral_log_maxEnt_real_singleton con w q
  rw [integral_fintype .of_finite] at h
  simp only [smul_eq_mul] at h
  rw [toReal_klDiv_add_measureEntropy (absolutelyContinuous_maxEnt con w q), h]
  ring

theorem measureEntropy_maxEnt :
    Hm[maxEnt con w] =
      w ⬝ᵥ con.expectedViolations (maxEnt con w) + log (∑ c, exp (harmonyScore con w c)) := by
  simpa using toReal_klDiv_maxEnt_add_measureEntropy con w (maxEnt con w)

/-- A distribution with the expected violations of a MaxEnt distribution falls short of its
entropy by its divergence from it. -/
theorem measureEntropy_add_toReal_klDiv_maxEnt {q : Measure C} [IsProbabilityMeasure q]
    (hq : con.expectedViolations q = con.expectedViolations (maxEnt con w)) :
    Hm[q] + (klDiv q (maxEnt con w)).toReal = Hm[maxEnt con w] := by
  rw [measureEntropy_maxEnt, ← hq, ← toReal_klDiv_maxEnt_add_measureEntropy, add_comm]

/-- The maximum entropy principle. No distribution with the expected violations of a MaxEnt
distribution has more entropy. -/
theorem measureEntropy_le_maxEnt {q : Measure C} [IsProbabilityMeasure q]
    (hq : con.expectedViolations q = con.expectedViolations (maxEnt con w)) :
    Hm[q] ≤ Hm[maxEnt con w] := by
  rw [← measureEntropy_add_toReal_klDiv_maxEnt con w hq]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- The MaxEnt distribution is the only distribution with its expected violations and its
entropy. -/
theorem eq_maxEnt_of_measureEntropy_eq {q : Measure C} [IsProbabilityMeasure q]
    (hq : con.expectedViolations q = con.expectedViolations (maxEnt con w))
    (h : Hm[q] = Hm[maxEnt con w]) : q = maxEnt con w := by
  have hkl := measureEntropy_add_toReal_klDiv_maxEnt con w hq
  rw [h, add_eq_left] at hkl
  exact klDiv_eq_zero_iff.1 (((ENNReal.toReal_eq_zero_iff _).1 hkl).resolve_right
    (klDiv_ne_top (absolutelyContinuous_maxEnt con w q) .of_finite))

/-- The MaxEnt distribution has the greatest entropy among the distributions with its expected
violations. -/
theorem isGreatest_measureEntropy_maxEnt :
    IsGreatest (measureEntropy '' {q | IsProbabilityMeasure q ∧
      con.expectedViolations q = con.expectedViolations (maxEnt con w)}) (Hm[maxEnt con w]) :=
  ⟨⟨maxEnt con w, ⟨inferInstance, rfl⟩, rfl⟩, by
    rintro _ ⟨q, ⟨hq, hv⟩, rfl⟩
    exact measureEntropy_le_maxEnt con w hv⟩

/-! ### Learning -/

/-- The log-likelihood is concave in the weights: it is linear in them less the log-sum-exp of
the harmonies, which are linear in them. -/
theorem concaveOn_logLikelihood : ConcaveOn ℝ Set.univ (logLikelihood con p) := by
  have hlin : ConcaveOn ℝ Set.univ fun w : ι → ℝ ↦ -(w ⬝ᵥ con.expectedViolations p) :=
    (LinearMap.concaveOn (-(dotProductBilin ℝ ℝ |>.flip (con.expectedViolations p)))
      convex_univ).congr fun w _ ↦ by simp
  have hlse : ConvexOn ℝ Set.univ fun w : ι → ℝ ↦ log (∑ c, exp (harmonyScore con w c)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    have := convexOn_log_sum_exp.2 (Set.mem_univ (harmonyScore con x))
      (Set.mem_univ (harmonyScore con y)) ha hb hab
    simpa [harmonyScore_add, harmonyScore_smul] using this
  exact (hlin.sub hlse).congr fun w _ ↦ (logLikelihood_eq con w p).symm

/-- The partial derivative of the log-likelihood in the weight of constraint `j` is that
constraint's expected violations less its observed ones. -/
theorem hasDerivAt_logLikelihood_update [DecidableEq ι] (j : ι) :
    HasDerivAt (fun t ↦ logLikelihood con p (Function.update w j t))
      (con.expectedViolations (maxEnt con w) j - con.expectedViolations p j) (w j) := by
  have hH : HasDerivAt (fun t ↦ harmonyScore con (Function.update w j t))
      (fun c ↦ -(con j c : ℝ)) (w j) := by
    refine hasDerivAt_pi.2 fun c ↦ ?_
    have := ((hasDerivAt_id (w j)).mul_const (con j c : ℝ)).add_const
      (∑ k ∈ univ.erase j, w k * con k c)
    convert this.neg using 1
    · funext t
      simp only [harmonyScore_eq_neg_sum, id, Pi.neg_apply]
      rw [← add_sum_erase _ _ (mem_univ j), Function.update_self,
        sum_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_erase hk)]]
    · simp
  have hv : HasDerivAt (fun t ↦ Function.update w j t ⬝ᵥ con.expectedViolations p)
      (con.expectedViolations p j) (w j) := by
    have := ((hasDerivAt_id (w j)).mul_const (con.expectedViolations p j)).add_const
      (∑ k ∈ univ.erase j, w k * con.expectedViolations p k)
    convert this using 1
    · funext t
      simp only [dotProduct, id]
      rw [← add_sum_erase _ _ (mem_univ j), Function.update_self,
        sum_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_erase hk)]]
    · simp
  have := hv.neg.sub hH.log_sum_exp
  convert this using 1
  · funext t
    exact logLikelihood_eq con _ p
  · rw [Function.update_eq_self, ConstraintSet.expectedViolations_apply]
    simp only [maxEnt_real_singleton, mul_neg, sum_neg_distrib]
    ring

/-- Weights maximize the log-likelihood exactly when their MaxEnt distribution has the observed
expected violations. -/
theorem isMaxOn_logLikelihood_iff :
    IsMaxOn (logLikelihood con p) Set.univ w ↔
      con.expectedViolations (maxEnt con w) = con.expectedViolations p := by
  classical
  constructor
  · intro h
    funext j
    have hmax : IsLocalMax (fun t ↦ logLikelihood con p (Function.update w j t)) (w j) :=
      IsMaxOn.isLocalMax (fun t _ ↦ by
        simpa [Function.update_eq_self] using h (Set.mem_univ (Function.update w j t)))
        Filter.univ_mem
    exact sub_eq_zero.1 (hmax.hasDerivAt_eq_zero (hasDerivAt_logLikelihood_update con w p j))
  · intro h w' _
    have hent := toReal_klDiv_maxEnt_add_measureEntropy con w' (maxEnt con w)
    have hent' := measureEntropy_maxEnt con w
    change logLikelihood con p w' ≤ logLikelihood con p w
    rw [logLikelihood_eq, logLikelihood_eq, ← h]
    linarith [ENNReal.toReal_nonneg (a := klDiv (maxEnt con w) (maxEnt con w'))]

/-- The most likely MaxEnt grammar of an empirical distribution gives the maximum-entropy
distribution among those with the observed expected violations. -/
theorem isGreatest_measureEntropy_of_isMaxOn (h : IsMaxOn (logLikelihood con p) Set.univ w) :
    IsGreatest (measureEntropy '' {q | IsProbabilityMeasure q ∧
      con.expectedViolations q = con.expectedViolations p}) (Hm[maxEnt con w]) := by
  simpa [(isMaxOn_logLikelihood_iff con w p).1 h] using isGreatest_measureEntropy_maxEnt con w

/-! ### Joint evaluation -/

section Joint

variable {κ I O : Type*} [Fintype κ] [DecidableEq κ] [Fintype O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [Nonempty O] (inputs : κ → I) (con : ConstraintSet (I × O) ι)

/-- A constraint set evaluated jointly over several inputs gives the product of the inputs' MaxEnt
distributions, so the inputs' outputs are independent. -/
theorem maxEnt_joint :
    maxEnt (con.joint inputs) w = Measure.pi fun k ↦ maxEnt (con.comap (inputs k, ·)) w := by
  refine Measure.ext_iff_singleton.2 fun f ↦ ?_
  simp_rw [Measure.pi_singleton, maxEnt_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ ↦ softmax_nonneg _ _,
    funext (harmonyScore_joint inputs con w)]
  exact congrArg ENNReal.ofReal (softmax_sum_apply (fun k o ↦ harmonyScore con w (inputs k, o)) f)

/-- The marginal of the joint distribution at an input is that input's MaxEnt distribution. -/
theorem map_eval_maxEnt_joint (k : κ) :
    (maxEnt (con.joint inputs) w).map (Function.eval k) =
      maxEnt (con.comap (inputs k, ·)) w := by
  simp [maxEnt_joint, Measure.pi_map_eval]

end Joint

end HarmonicGrammar
