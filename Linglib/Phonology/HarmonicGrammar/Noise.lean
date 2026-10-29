module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Core.Probability.Choice.RandomUtility
public import Linglib.Core.Probability.Distributions.Gaussian

/-!
# Noisy harmonic grammar

Boersma and Pater make harmonic grammar stochastic by adding independent Gaussian noise to every
constraint weight at each evaluation, so that a candidate wins with the probability that its noisy
harmony is the highest. Flemming reads this as a random utility model whose utilities are the
noisy harmonies. The candidates share the weights, so their noisy harmonies are correlated, and the
model is the choice rule `choiceProb` at the pushforward of the weight noise rather than at a
product of independent laws. The harmony difference of two candidates is Gaussian with variance
`v * (d ⬝ᵥ d)` for their violation difference `d`, so how noisy a comparison is depends on the
violation profile and not only on the harmonies, unlike in MaxEnt, where the utilities are
independent.

## Main definitions

* `weightNoise`: independent `N(0, v)` noise on every constraint weight.
* `weightNoiseChoiceProb`: the probability that a candidate has the highest harmony under noisy
  weights, the random-utility choice probability under the law of the noisy harmonies.

## Main results

* `map_weightNoise_harmonyScore_sub`: the harmony difference of two candidates is Gaussian with
  variance `v * (d ⬝ᵥ d)`.
* `variance_harmonyScore_sub`, `covariance_harmonyScore_sub`: the variances and covariances of
  the harmony differences.
* `weightNoise_setOf_harmonyScore_lt`, `weightNoiseChoiceProb_of_forall_ne_eq`,
  `weightNoiseChoiceProb_fin_two`: the probability that one candidate beats another is the probit
  of their harmony difference over its standard deviation.

## Implementation notes

The noise has variance `v : ℝ≥0`, as in mathlib's `gaussianReal`. Boersma and Pater leave its width
free, and their noisy learners of §4.2 evaluate with a standard deviation of 2.
Flemming's normal MaxEnt, with independent Gaussian noise on the candidates' harmonies, needs no
definition: it is `choiceProb (Measure.pi fun c ↦ gaussianReal (harmonyScore con w c) v)`, with
binary case `choiceProb_pi_gaussianReal`. His censored variant, which clamps noisy weights at zero,
has no closed form and is not formalized.

## References

* [boersma-pater-2016]
* [flemming-2021]
-/

@[expose] public section

namespace HarmonicGrammar

open MeasureTheory ProbabilityTheory OptimalityTheory
open scoped NNReal ENNReal

variable {C ι : Type*} [Fintype ι] (con : ConstraintSet C ι) (w : ι → ℝ) (v : ℝ≥0)

/-- The weight noise of noisy harmonic grammar perturbs each constraint weight by independent
`N(0, v)` noise. -/
noncomputable def weightNoise (ι : Type*) [Fintype ι] (v : ℝ≥0) : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι ↦ gaussianReal 0 v

instance : IsProbabilityMeasure (weightNoise ι v) := by
  unfold weightNoise; infer_instance

theorem measurable_harmonyScore_add (c : C) :
    Measurable fun η : ι → ℝ ↦ harmonyScore con (w + η) c := by
  simp only [harmonyScore_eq_neg_sum, Pi.add_apply]
  fun_prop

theorem measurable_harmonyScore_add_sub (a b : C) :
    Measurable fun η : ι → ℝ ↦ harmonyScore con (w + η) a - harmonyScore con (w + η) b := by
  simp only [harmonyScore_eq_neg_sum, Pi.add_apply]
  fun_prop

theorem dotProduct_violationDiff_self_nonneg (a b : C) :
    0 ≤ (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ) :=
  Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

/-- `weightNoiseChoiceProb con w v a` is the probability that `a` has the highest harmony when the
weights `w` are perturbed by weight noise of variance `v`: the random-utility choice probability
of `a` under the law of the noisy harmonies. -/
noncomputable def weightNoiseChoiceProb [Fintype C] (a : C) : ℝ≥0∞ :=
  choiceProb ((weightNoise ι v).map fun η c ↦ harmonyScore con (w + η) c) a

theorem weightNoiseChoiceProb_eq [Fintype C] (a : C) :
    weightNoiseChoiceProb con w v a =
      weightNoise ι v {η | ∀ b, b ≠ a → harmonyScore con (w + η) b < harmonyScore con (w + η) a} :=
  choiceProb_map _ (measurable_pi_iff.mpr (measurable_harmonyScore_add con w)) a

theorem harmonyScore_add_sub (η : ι → ℝ) (a b : C) :
    harmonyScore con (w + η) a - harmonyScore con (w + η) b =
      harmonyScore con w a - harmonyScore con w b + ∑ i, -con.violationDiff a b i * η i := by
  rw [harmonyScore_sub, harmonyScore_sub, add_dotProduct, dotProduct_comm η]
  simp only [dotProduct, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Under weight noise the harmony difference of two candidates is Gaussian, with mean their
harmony difference and variance `v` times the squared length of their violation difference. -/
theorem map_weightNoise_harmonyScore_sub (a b : C) :
    (weightNoise ι v).map (fun η ↦ harmonyScore con (w + η) a - harmonyScore con (w + η) b) =
      gaussianReal (harmonyScore con w a - harmonyScore con w b)
        (v * (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ).toNNReal) := by
  have hgap : (fun η ↦ harmonyScore con (w + η) a - harmonyScore con (w + η) b) =
      (· + (harmonyScore con w a - harmonyScore con w b)) ∘
        fun η ↦ ∑ i, -con.violationDiff a b i * η i := by
    funext η
    rw [Function.comp_apply, harmonyScore_add_sub, add_comm]
  rw [hgap, ← Measure.map_map (by fun_prop) (by fun_prop), weightNoise,
    map_pi_gaussianReal_sum_mul, gaussianReal_map_add_const]
  congr 1
  · simp
  · ext
    push_cast
    rw [Real.coe_toNNReal _ (dotProduct_violationDiff_self_nonneg con a b), dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The variance of the harmony difference of two candidates is `v` times the squared length of
their violation difference. -/
theorem variance_harmonyScore_sub (a b : C) :
    Var[fun η ↦ harmonyScore con (w + η) a - harmonyScore con (w + η) b; weightNoise ι v] =
      v * (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ) := by
  rw [← variance_id_map (measurable_harmonyScore_add_sub con w a b).aemeasurable,
    map_weightNoise_harmonyScore_sub, variance_id_gaussianReal, NNReal.coe_mul,
    Real.coe_toNNReal _ (dotProduct_violationDiff_self_nonneg con a b)]

/-- The covariance of the harmony differences of `b` and of `c` from a common candidate `a` is `v`
times the dot product of their violation differences, so the joint law of the differences
depends on the whole violation profile and not only on the harmonies. -/
theorem covariance_harmonyScore_sub (a b c : C) :
    cov[fun η ↦ harmonyScore con (w + η) b - harmonyScore con (w + η) a,
      fun η ↦ harmonyScore con (w + η) c - harmonyScore con (w + η) a; weightNoise ι v] =
      v * (con.violationDiff b a ⬝ᵥ con.violationDiff c a : ℝ) := by
  have hint (d : ι → ℝ) : Integrable (fun η : ι → ℝ ↦ ∑ i, d i * η i) (weightNoise ι v) := by
    rw [weightNoise]
    exact integrable_finsetSum _ fun i _ ↦ (((memLp_id_gaussianReal 2).const_mul
      (d i)).comp_measurePreserving (measurePreserving_eval _ i)).integrable (by norm_num)
  simp_rw [harmonyScore_add_sub con w _ b a, harmonyScore_add_sub con w _ c a]
  rw [covariance_const_add_left (hint _), covariance_const_add_right (hint _), weightNoise,
    covariance_pi_gaussianReal_sum_mul, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The probability that `a` has a higher noisy harmony than `b` is the probit of their harmony
difference over its standard deviation. -/
theorem weightNoise_setOf_harmonyScore_lt (hv : v ≠ 0) {a b : C}
    (hab : (con.violationDiff a b : ι → ℝ) ≠ 0) :
    weightNoise ι v {η | harmonyScore con (w + η) b < harmonyScore con (w + η) a} =
      ENNReal.ofReal (normalCDF ((harmonyScore con w a - harmonyScore con w b) /
        √(v * (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ)))) := by
  have hdd : 0 < (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ) :=
    (dotProduct_violationDiff_self_nonneg con a b).lt_of_ne
      (Ne.symm (mt dotProduct_self_eq_zero.mp hab))
  have hσ : 0 < √(v * (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)) hdd)
  rw [show {η : ι → ℝ | harmonyScore con (w + η) b < harmonyScore con (w + η) a} =
      (fun η ↦ harmonyScore con (w + η) a - harmonyScore con (w + η) b) ⁻¹' Set.Ioi 0 by
    ext; simp [sub_pos],
    ← Measure.map_apply (measurable_harmonyScore_add_sub con w a b) measurableSet_Ioi,
    map_weightNoise_harmonyScore_sub, ← ofReal_measureReal, ← gaussianReal_real_Ioi_zero _ hσ]
  congr 3
  ext
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hdd.le, NNReal.coe_mk, Real.sq_sqrt (by positivity)]

/-- When `b` is the only other candidate, the probability that `a` wins is the probit of their
harmony difference over its standard deviation. -/
theorem weightNoiseChoiceProb_of_forall_ne_eq [Fintype C] (hv : v ≠ 0) {a b : C}
    (hb : ∀ c, c ≠ a → c = b) (hab : a ≠ b) (hd : (con.violationDiff a b : ι → ℝ) ≠ 0) :
    weightNoiseChoiceProb con w v a =
      ENNReal.ofReal (normalCDF ((harmonyScore con w a - harmonyScore con w b) /
        √(v * (con.violationDiff a b ⬝ᵥ con.violationDiff a b : ℝ)))) := by
  rw [weightNoiseChoiceProb_eq, ← weightNoise_setOf_harmonyScore_lt con w v hv hd]
  congr 1
  ext η
  exact ⟨fun h ↦ h b hab.symm, fun h c hc ↦ hb c hc ▸ h⟩

section FinTwo

variable (con : ConstraintSet (Fin 2) ι) (w : ι → ℝ) (v : ℝ≥0)

/-- With two candidates, the probability that the first wins is the probit of their harmony
difference over its standard deviation. -/
theorem weightNoiseChoiceProb_fin_two (hv : v ≠ 0) (hd : (con.violationDiff 0 1 : ι → ℝ) ≠ 0) :
    weightNoiseChoiceProb con w v 0 =
      ENNReal.ofReal (normalCDF ((harmonyScore con w 0 - harmonyScore con w 1) /
        √(v * (con.violationDiff 0 1 ⬝ᵥ con.violationDiff 0 1 : ℝ)))) :=
  weightNoiseChoiceProb_of_forall_ne_eq con w v hv (fun c hc ↦ by omega) zero_ne_one hd

end FinTwo

end HarmonicGrammar
