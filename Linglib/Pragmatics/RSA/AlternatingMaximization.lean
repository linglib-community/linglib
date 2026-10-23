module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Pragmatics.RSA.Basic

/-!
# The RSA recursion as alternating maximization

A speaker observes the state through a kernel and addresses a listener, who hears her utterance
and infers the state. The free energy of a speaker and a listener is the conditional entropy of
the utterance given the observation plus the rationality times the expected utility, the
listener's log-probability of the state less the cost of the utterance. The two agents of the
Rational Speech Act recursion are its two partial maximizers. Against a fixed listener the
speaker of `RSA.speaker` at the Bayesian belief maximizes it, and against a fixed speaker the
Bayesian listener does, so a round of the recursion never lowers it.

## Main definitions

* `RSA.expectedUtility`, `RSA.freeEnergy`: the expected utility and the free energy of a speaker
  and a listener, for a prior over states and an observation kernel.
* `RSA.informationLoss`, `RSA.expectedCost`: the two parts of the expected utility, the expected
  surprisal of the state under the listener and the expected cost of the utterance.

## Main statements

* `RSA.expectedUtility_eq_neg_add`: the expected utility is minus the information loss and the
  expected cost.
* `RSA.freeEnergy_add_sum_klDiv`, `RSA.freeEnergy_le_freeEnergy_speaker`: against a fixed
  listener the free energy of a speaker falls short of the RSA speaker's by her expected
  divergence from it.
* `RSA.freeEnergy_le_freeEnergy_listener`: against a fixed speaker her Bayesian listener
  maximizes the free energy.
* `RSA.freeEnergy_speaker_le_freeEnergy_listener`,
  `RSA.freeEnergy_listener_le_freeEnergy_speaker`: in a round of the recursion the
  listener's update and the speaker's update each raise the free energy, with no condition on
  the supports.

## Implementation notes

* The free energy is the functional the source calls the RSA tradeoff. Row by row it is the free
  energy of the Gibbs variational principle, entropy plus expected log-weight, for the weights
  the speaker normalizes.
* The speaker's belief is any family `b` that satisfies Bayes' rule with the denominator cleared,
  `(κ ∘ₘ μ) {o} * b o {w} = μ {w} * κ w {o}` on reals. The listener `listener μ κ` of the
  observation kernel is one (`RSA.comp_real_mul_listener_real`), and so is the point mass for a
  speaker who observes the state itself (`RSA.id_comp_real_mul_dirac_real`).
* The utility is real-valued, with `Real.log 0 = 0`, where an extended-real utility would be `−∞`
  at a state the listener rules out. The two agree for a speaker who uses no utterance whose
  listener rules out a state she entertains, and the two maximality statements quantify over
  such competitors. Along the recursion the condition holds of itself.
* The source proves the two maximality statements for a speaker who knows the state. The
  statements here, for a speaker who observes it through a kernel, run the same argument with her
  belief in place of the point mass.

## References

* [zaslavsky-hu-levy-2020]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

namespace RSA

variable {W O U : Type*} [MeasurableSpace W] [MeasurableSpace O] [MeasurableSpace U]

/-! ### The rows of the speaker -/

section Row

variable [Fintype W] [Fintype U] [MeasurableSingletonClass U] [Countable O]
  [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} {L : U → Measure W}
  [∀ u, IsFiniteMeasure (L u)] {b : O → Measure W} {o : O} {q : Measure U}
  [IsProbabilityMeasure q]

theorem isProbabilityMeasure_speaker_of_absolutelyContinuous (hα : 0 ≤ α)
    (hq : q ≪ speaker α C L b o) : IsProbabilityMeasure (speaker α C L b o) := by
  refine Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous (fun _ ↦ ?_) hq
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα
    (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)) ENNReal.ofReal_ne_top

variable [MeasurableSingletonClass W] [IsFiniteMeasure (b o)]

theorem toReal_klDiv_speaker_add_measureEntropy (hα : 0 ≤ α) (hq : q ≪ speaker α C L b o) :
    (klDiv q (speaker α C L b o)).toReal + Hm[q] =
      log (∑ u, ((b o).geomMean (fun w ↦ L u {w}) ^ α).toReal * exp (-(α * C u))) -
        α * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂q := by
  have hw (u : U) : (b o).geomMean (fun w ↦ L u {w}) ^ α ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hα (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)
  have hterm (u : U) : q.real {u} *
        log ((b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (exp (-(α * C u)))).toReal =
      α * (q.real {u} * (∫ w, log ((L u).real {w}) ∂(b o) - C u)) := by
    rcases eq_or_ne (q {u}) 0 with h | h
    · rw [measureReal_def, h, ENNReal.toReal_zero, zero_mul, zero_mul, mul_zero]
    rcases hα.eq_or_lt with rfl | hα'
    · simp
    have hdom (w : W) (hbw : b o {w} ≠ 0) : L u {w} ≠ 0 := fun hL ↦
      h (hq ((speaker_apply_singleton_eq_zero_iff hα').2 ⟨w, hbw, hL⟩))
    rw [Measure.geomMean_eq_ofReal_exp_sum_log hdom fun _ _ ↦ measure_ne_top _ _,
      ENNReal.ofReal_rpow_of_pos (exp_pos _), ← exp_mul, ← ENNReal.ofReal_mul (exp_pos _).le,
      ← exp_add, ENNReal.toReal_ofReal (exp_pos _).le, log_exp, integral_fintype .of_finite]
    simp only [smul_eq_mul, measureReal_def]
    ring
  have key := toReal_klDiv_ofWeights_add_measureEntropy (μ := q) (i := o)
    (w := fun o u ↦ (b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (exp (-(α * C u))))
    (fun u ↦ ENNReal.mul_ne_top (hw u) ENNReal.ofReal_ne_top) hq
  simp only [hterm, ← Finset.mul_sum] at key
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at key
  rw [integral_fintype .of_finite]
  simp only [smul_eq_mul]
  exact key

theorem measureEntropy_add_utility_le_speaker (hα : 0 ≤ α) (hq : q ≪ speaker α C L b o) :
    Hm[q] + α * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂q ≤
      Hm[speaker α C L b o] +
        α * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(speaker α C L b o) := by
  have := isProbabilityMeasure_speaker_of_absolutelyContinuous hα hq
  have h := toReal_klDiv_speaker_add_measureEntropy hα hq
  have h' := toReal_klDiv_speaker_add_measureEntropy hα
    (Measure.AbsolutelyContinuous.refl (speaker α C L b o))
  rw [klDiv_self, ENNReal.toReal_zero, zero_add] at h'
  linarith [ENNReal.toReal_nonneg (a := klDiv q (speaker α C L b o))]

end Row

/-! ### The free energy -/

variable (μ : Measure W) (κ : Kernel W O) (C : U → ℝ) (α : ℝ)

section Defs

variable [Fintype W]

/-- The expected utility of a speaker and a listener averages the listener's log-probability of
the state, less the cost of the utterance, over the states, the speaker's observations and her
utterances. -/
noncomputable def expectedUtility (S : Kernel O U) (L : Kernel U W) : ℝ :=
  ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)

/-- The information the listener loses about the state, its expected surprisal under her
interpretation of the speaker's utterance. -/
noncomputable def informationLoss (S : Kernel O U) (L : Kernel U W) : ℝ :=
  ∑ w, μ.real {w} * ∫ u, surprisal (L u) w ∂((S ∘ₖ κ) w)

/-- The expected cost of the speaker's utterances. -/
noncomputable def expectedCost (S : Kernel O U) : ℝ :=
  ∑ w, μ.real {w} * ∫ u, C u ∂((S ∘ₖ κ) w)

theorem expectedCost_smul (β : ℝ) (S : Kernel O U) :
    expectedCost μ κ (β • C) S = β * expectedCost μ κ C S := by
  simp only [expectedCost, Pi.smul_apply, smul_eq_mul, integral_const_mul, Finset.mul_sum,
    mul_left_comm β]

theorem expectedUtility_eq_neg_add [Finite U] [MeasurableSingletonClass U] [IsFiniteKernel κ]
    (S : Kernel O U) [IsFiniteKernel S] (L : Kernel U W) :
    expectedUtility μ κ C S L = -(informationLoss μ κ S L + expectedCost μ κ C S) := by
  simp only [expectedUtility, informationLoss, expectedCost, surprisal, integral_neg,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [integral_sub .of_finite .of_finite]
  ring

variable [Fintype O]

/-- The free energy of a speaker and a listener is the conditional entropy of the utterance given
the speaker's observation plus `α` times the expected utility. -/
noncomputable def freeEnergy (S : Kernel O U) (L : Kernel U W) : ℝ :=
  ∑ o, (κ ∘ₘ μ).real {o} * Hm[S o] + α * expectedUtility μ κ C S L

theorem freeEnergy_id (S : Kernel W U) (L : Kernel U W) :
    freeEnergy μ Kernel.id C α S L =
      ∑ w, μ.real {w} * Hm[S w] +
        α * ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂(S w) := by
  simp only [freeEnergy, expectedUtility, Measure.id_comp, Kernel.comp_id]

end Defs

section Bound

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] [IsProbabilityMeasure μ]
  [IsMarkovKernel κ]

theorem freeEnergy_le {α : ℝ} (hα : 0 ≤ α) (S : Kernel O U) [IsMarkovKernel S] (L : Kernel U W)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    freeEnergy μ κ C α S L ≤ log (Fintype.card U) + α * ∑ u, |C u| := by
  have hV (w : W) : ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w) ≤ ∑ u, |C u| :=
    calc ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)
      _ ≤ ∫ _, ∑ u, |C u| ∂((S ∘ₖ κ) w) := integral_mono .of_finite .of_finite fun u ↦ by
          have := Finset.single_le_sum (fun v _ ↦ abs_nonneg (C v)) (Finset.mem_univ u)
          have := log_nonpos measureReal_nonneg (measureReal_le_one (μ := L u) (s := {w}))
          have := neg_abs_le (C u)
          beta_reduce
          linarith
      _ = ∑ u, |C u| := by simp
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hα)
  · calc ∑ o, (κ ∘ₘ μ).real {o} * Hm[S o]
      _ ≤ ∑ o, (κ ∘ₘ μ).real {o} * log (Fintype.card U) := Finset.sum_le_sum fun o _ ↦
          mul_le_mul_of_nonneg_left (measureEntropy_le_log_card _) measureReal_nonneg
      _ = log (Fintype.card U) := by
          rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]
  · calc expectedUtility μ κ C S L
      _ ≤ ∑ w, μ.real {w} * ∑ u, |C u| := Finset.sum_le_sum fun w _ ↦
          mul_le_mul_of_nonneg_left (hV w) measureReal_nonneg
      _ = ∑ u, |C u| := by rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

end Bound

/-! ### The speaker's step -/

section Speaker

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] {μ κ C α} [IsFiniteMeasure μ]
  [IsFiniteKernel κ] {b : O → Measure W} [∀ o, IsFiniteMeasure (b o)]
  (hb : ∀ o w, (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o})
include hb

theorem expectedUtility_eq_sum_comp (S : Kernel O U) [IsFiniteKernel S] (L : Kernel U W) :
    expectedUtility μ κ C S L =
      ∑ o, (κ ∘ₘ μ).real {o} * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(S o) := by
  have hrow (o : O) (u : U) :
      (κ ∘ₘ μ).real {o} * (∑ w, (b o).real {w} * log ((L u).real {w}) - C u) =
        ∑ w, μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u) := by
    have h1 : (κ ∘ₘ μ).real {o} * ∑ w, (b o).real {w} * log ((L u).real {w}) =
        ∑ w, μ.real {w} * (κ w).real {o} * log ((L u).real {w}) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by rw [← mul_assoc, hb]
    rw [mul_sub, h1, Measure.comp_real_singleton, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  calc expectedUtility μ κ C S L
    _ = ∑ w, ∑ u, ∑ o, (S o).real {u} *
          (μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u)) := by
        simp_rw [expectedUtility, integral_fintype (.of_finite), smul_eq_mul,
          Kernel.comp_real_singleton, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun u _ ↦
          Finset.sum_congr rfl fun o _ ↦ by ring
    _ = ∑ o, ∑ u, ∑ w, (S o).real {u} *
          (μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u)) := by
        rw [Finset.sum_comm]
        exact (Finset.sum_congr rfl fun u _ ↦ Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ o, (κ ∘ₘ μ).real {o} * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(S o) := by
        refine Finset.sum_congr rfl fun o _ ↦ ?_
        rw [integral_fintype .of_finite, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [integral_fintype .of_finite]
        simp only [smul_eq_mul]
        rw [← Finset.mul_sum, ← hrow, mul_left_comm]

variable (hα : 0 ≤ α) (L : Kernel U W) [IsFiniteKernel L]
  (S : Kernel O U) [IsMarkovKernel S] (hS : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o ≪ speaker α C L b o)
include hα hS

/-- Against a fixed listener, the free energy of a speaker and her expected divergence from the RSA
speaker add up to the expected log partition function. -/
theorem freeEnergy_add_sum_klDiv :
    freeEnergy μ κ C α S L +
        ∑ o, (κ ∘ₘ μ).real {o} * (klDiv (S o) (speaker α C L b o)).toReal =
      ∑ o, (κ ∘ₘ μ).real {o} *
        log (∑ u, ((b o).geomMean (fun w ↦ L u {w}) ^ α).toReal * exp (-(α * C u))) := by
  rw [freeEnergy, expectedUtility_eq_sum_comp hb S L, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with h | h
  · simp [measureReal_def, h]
  · linear_combination
      (κ ∘ₘ μ).real {o} * toReal_klDiv_speaker_add_measureEntropy (C := C) hα (hS o h)

/-- Against a fixed listener the speaker at the Bayesian belief maximizes the free energy. -/
theorem freeEnergy_le_freeEnergy_speaker :
    freeEnergy μ κ C α S L ≤ freeEnergy μ κ C α (speaker α C L b) L := by
  rw [freeEnergy, freeEnergy, expectedUtility_eq_sum_comp hb S L,
    expectedUtility_eq_sum_comp hb (speaker α C L b) L, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun o _ ↦ ?_
  rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with h | h
  · simp [measureReal_def, h]
  · have := mul_le_mul_of_nonneg_left
      (measureEntropy_add_utility_le_speaker (C := C) hα (hS o h))
      (measureReal_nonneg (μ := κ ∘ₘ μ) (s := {o}))
    linarith

end Speaker

/-! ### The listener's step -/

section Listener

variable [Fintype W] [Fintype U] [MeasurableSingletonClass W] [MeasurableSingletonClass U]
  [Nonempty W] [IsProbabilityMeasure μ] [IsMarkovKernel κ] (S : Kernel O U) [IsMarkovKernel S]

theorem expectedUtility_listener_eq_posterior :
    expectedUtility μ κ C S (listener μ (S ∘ₖ κ)) = expectedUtility μ κ C S ((S ∘ₖ κ)†μ) := by
  simp_rw [expectedUtility, integral_fintype (.of_finite), smul_eq_mul]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rcases eq_or_ne (μ {w}) 0 with hμ | hμ
  · simp [measureReal_def, hμ]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rcases eq_or_ne ((S ∘ₖ κ) w {u}) 0 with hS | hS
  · simp [measureReal_def, hS]
  rw [listener_apply_eq_posterior _ _ (Measure.comp_apply_singleton_ne_zero _ _ hμ hS)]

variable (L : Kernel U W) [∀ u, IsZeroOrProbabilityMeasure (L u)]
  (hL : ∀ u, ((S ∘ₖ κ) ∘ₘ μ) {u} ≠ 0 → listener μ (S ∘ₖ κ) u ≪ L u)
include hL

theorem expectedUtility_le_listener :
    expectedUtility μ κ C S L ≤ expectedUtility μ κ C S (listener μ (S ∘ₖ κ)) := by
  rw [expectedUtility_listener_eq_posterior]
  have h := sum_mul_integral_log_le (S ∘ₖ κ) μ L fun u hu ↦ by
    rw [← listener_apply_eq_posterior _ _ hu]
    exact hL u hu
  simp_rw [expectedUtility, integral_sub (.of_finite) (.of_finite), mul_sub,
    Finset.sum_sub_distrib]
  exact sub_le_sub_right h _

variable [Fintype O]

/-- Against a fixed speaker her Bayesian listener maximizes the free energy. -/
theorem freeEnergy_le_freeEnergy_listener (hα : 0 ≤ α) :
    freeEnergy μ κ C α S L ≤ freeEnergy μ κ C α S (listener μ (S ∘ₖ κ)) :=
  add_le_add_right
    (mul_le_mul_of_nonneg_left (expectedUtility_le_listener μ κ C S L hL) hα) _

end Listener

/-! ### A round of the recursion

The side conditions of the two steps hold of themselves along the recursion: the speaker who
answers a listener uses no utterance whose listener rules out a state she entertains, and the
Bayesian listener of a speaker rules out no state at which she might have said the utterance. -/

section Belief

variable {μ κ} [IsFiniteMeasure μ] [IsFiniteKernel κ] {b : O → Measure W} {o : O} {w : W}
  (hb : ∀ o w, (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o})
include hb

private theorem belief_apply_singleton_ne_zero (hμ : μ {w} ≠ 0) (hκ : κ w {o} ≠ 0) :
    b o {w} ≠ 0 := fun h0 ↦ by
  have h := hb o w
  rw [measureReal_def (b o), h0, ENNReal.toReal_zero, mul_zero, eq_comm, mul_eq_zero,
    measureReal_eq_zero_iff (measure_ne_top _ _),
    measureReal_eq_zero_iff (measure_ne_top _ _)] at h
  exact h.elim hμ hκ

private theorem ne_zero_of_belief_apply_singleton_ne_zero [IsFiniteMeasure (b o)]
    (ho : (κ ∘ₘ μ) {o} ≠ 0) (hbw : b o {w} ≠ 0) : μ {w} ≠ 0 ∧ κ w {o} ≠ 0 := by
  have h : μ.real {w} * (κ w).real {o} ≠ 0 := hb o w ▸ mul_ne_zero
    ((measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 ho)
    ((measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 hbw)
  exact ⟨fun h0 ↦ h (by rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul]),
    fun h0 ↦ h (by rw [measureReal_def (κ w), h0, ENNReal.toReal_zero, mul_zero])⟩

end Belief

section Round

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] {μ κ C α}
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] {b : O → Measure W} [∀ o, IsFiniteMeasure (b o)]
  (hb : ∀ o w, (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o}) (hα : 0 ≤ α)
include hb hα

theorem speaker_listener_apply_singleton_ne_zero {S : Kernel O U} [IsFiniteKernel S]
    {o : O} {u : U} (ho : (κ ∘ₘ μ) {o} ≠ 0) (hS : S o {u} ≠ 0) :
    speaker α C (listener μ (S ∘ₖ κ)) b o {u} ≠ 0 := by
  refine speaker_apply_singleton_ne_zero hα fun w hbw ↦ ?_
  obtain ⟨hμw, hκ⟩ := ne_zero_of_belief_apply_singleton_ne_zero hb ho hbw
  refine listener_apply_singleton_ne_zero hμw ?_
  rw [Kernel.comp_apply_singleton]
  exact fun h ↦ mul_ne_zero hκ hS (Finset.sum_eq_zero_iff.1 h o (Finset.mem_univ o))

theorem isMarkovKernel_speaker_listener (hκ : ∀ o, (κ ∘ₘ μ) {o} ≠ 0) (S : Kernel O U)
    [IsMarkovKernel S] : IsMarkovKernel (speaker α C (listener μ (S ∘ₖ κ)) b) :=
  ⟨fun o ↦ isProbabilityMeasure_speaker_of_absolutelyContinuous hα (q := S o)
    (Measure.absolutelyContinuous_of_forall_singleton fun _ hu ↦ of_not_not fun hS ↦
      speaker_listener_apply_singleton_ne_zero hb hα (hκ o) hS hu)⟩

/-- The speaker's best response to the listener of any speaker raises the free energy. -/
theorem freeEnergy_listener_le_freeEnergy_speaker (S : Kernel O U) [IsMarkovKernel S] :
    freeEnergy μ κ C α S (listener μ (S ∘ₖ κ)) ≤
      freeEnergy μ κ C α (speaker α C (listener μ (S ∘ₖ κ)) b) (listener μ (S ∘ₖ κ)) :=
  freeEnergy_le_freeEnergy_speaker hb hα _ S fun _ ho ↦
    Measure.absolutelyContinuous_of_forall_singleton fun _ hu ↦ of_not_not fun hS ↦
      speaker_listener_apply_singleton_ne_zero hb hα ho hS hu

variable [Nonempty W]

/-- The listener's update to the speaker who answers her raises the free energy. -/
theorem freeEnergy_speaker_le_freeEnergy_listener (L : Kernel U W)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] [IsMarkovKernel (speaker α C L b)] :
    freeEnergy μ κ C α (speaker α C L b) L ≤
      freeEnergy μ κ C α (speaker α C L b) (listener μ (speaker α C L b ∘ₖ κ)) := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp [freeEnergy]
  refine freeEnergy_le_freeEnergy_listener μ κ C α _ L (fun u _ ↦
    Measure.absolutelyContinuous_of_forall_singleton fun w hL ↦ of_not_not fun hlis ↦ ?_) hα
  obtain ⟨hμw, hSw⟩ := ne_zero_of_listener_apply_singleton_ne_zero hlis
  rw [Kernel.comp_apply_singleton] at hSw
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSw
  exact right_ne_zero_of_mul ho ((speaker_apply_singleton_eq_zero_iff hα').2
    ⟨w, belief_apply_singleton_ne_zero hb hμw (left_ne_zero_of_mul ho), hL⟩)

end Round

/-! ### The speaker who knows the state -/

theorem id_comp_real_mul_dirac_real [MeasurableSingletonClass W] (o w : W) :
    ((Kernel.id : Kernel W W) ∘ₘ μ).real {o} * (Measure.dirac o).real {w} =
      μ.real {w} * ((Kernel.id : Kernel W W) w).real {o} := by
  rw [Measure.id_comp, Kernel.id_apply]
  rcases eq_or_ne o w with rfl | h
  · simp
  · simp [measureReal_def, Measure.dirac_apply', h, h.symm]

end RSA
