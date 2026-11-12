module

public import Linglib.Core.InformationTheory.InformationLoss
public import Linglib.Pragmatics.RSA.Recursion

/-!
# The RSA recursion as alternating maximization

A speaker observes the state through a kernel and addresses a listener, who hears her utterance
and infers the state. The expected utility is minus the information the listener loses, the
expected surprisal of the state under her interpretation, and the expected cost of the
utterance, and the free energy of a speaker and a listener is the conditional entropy of the
utterance given the observation plus the rationality times the expected utility. A listener who
rules out a state the speaker's utterance may come from loses infinitely much, and the free energy
is then `⊥`.

The two agents of the Rational Speech Act recursion are the two partial maximizers of the free
energy. The loss of any listener exceeds that of the Bayesian listener, which is the conditional
entropy of the state given the utterance, by [her expected divergence from
it](##InformationTheory.informationLoss_eq_posterior_add). The free energy of any speaker falls
short of that of the speaker of `RSA.speaker` at the Bayesian belief by [her expected divergence
from it](##RSA.freeEnergy_eq_freeEnergy_speaker_sub). Going up a level of the recursion therefore
never lowers the free energy, which [rises](##RSA.monotone_freeEnergy_iterate_recurse) and
[converges](##RSA.exists_tendsto_freeEnergy_iterate_recurse) along it, and since each speaker
update raises it by at least the divergence between the two speakers, successive speakers [grow
alike](##RSA.tendsto_sum_klDiv_speaker_iterate_recurse). The speaker at the Bayesian belief is
the [only maximizer](##RSA.freeEnergy_eq_freeEnergy_speaker_iff) against her listener.

## Implementation notes

* The free energy is the functional the source calls the RSA tradeoff. At each observation it is
  the free energy of the Gibbs variational principle, entropy plus expected log-weight, for the
  weights the speaker normalizes.
* The expected utility depends on the speaker and her observation kernel only through their
  composite, the channel from states to utterances, and is stated for a channel.
* The speaker's belief is any family `b` that agrees with the posterior of the prior given her
  observation at almost every observation, `b =ᵐ[κ ∘ₘ μ] κ†μ`. The listener `listener μ κ` of the
  observation kernel is one, and so is the point mass for a speaker who observes the state itself
  (`RSA.dirac_ae_eq_posterior_id`).
* The source states the two decompositions as maximality claims and proves them, by Lagrange
  multipliers, for a speaker who knows the state. The statements here are for a speaker who
  observes it through a kernel, and they give the size of the gap.

## References

* [zaslavsky-hu-levy-2021]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real Filter Topology
open scoped ENNReal

namespace RSA

/-- Gibbs' variational identity for normalized weights. The divergence from the normalized weights
and the entropy add up to the log of the total weight less the expected log-weight, so normalizing
gives the distribution with the greatest entropy plus expected log-weight. -/
private theorem toReal_klDiv_ofWeights_add_measureEntropy {S ι : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] {μ : Measure S} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [Fintype S] [IsProbabilityMeasure μ] {w : ι → S → ℝ≥0∞} {i : ι}
    (hw : ∀ s, w i s ≠ ∞) (hμ : μ ≪ Kernel.ofWeights w i) :
    (klDiv μ (Kernel.ofWeights w i)).toReal + Hm[μ] =
      log (∑ s, (w i s).toReal) - ∑ s, μ.real {s} * log (w i s).toReal := by
  have := Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous hw hμ
  have hterm (s : S) : μ.real {s} * log ((Kernel.ofWeights w i).real {s}) =
      μ.real {s} * log (w i s).toReal - μ.real {s} * log (∑ s, (w i s).toReal) := by
    rcases eq_or_ne (μ.real {s}) 0 with h | h
    · simp [h]
    · have hp : (Kernel.ofWeights w i).real {s} ≠ 0 := fun h0 ↦
        h ((measureReal_eq_zero_iff (measure_ne_top _ _)).2
          (hμ ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0)))
      rw [Kernel.ofWeights_real_singleton w i hw] at hp ⊢
      rw [log_div (fun h0 ↦ hp (by rw [h0, zero_div])) fun h0 ↦ hp (by rw [h0, div_zero]), mul_sub]
  rw [toReal_klDiv_add_measureEntropy hμ, Finset.sum_congr rfl fun s _ ↦ hterm s,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul, neg_sub]

variable {W O U : Type*} [MeasurableSpace W] [MeasurableSpace O] [MeasurableSpace U]

/-! ### The speaker at one observation -/

section Observation

variable [Fintype W] [Fintype U] [MeasurableSingletonClass U] [Countable O]
  [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} {L : U → Measure W}
  [∀ u, IsFiniteMeasure (L u)] {b : O → Measure W} {o : O} {q : Measure U}
  [IsProbabilityMeasure q]

theorem isProbabilityMeasure_speaker_of_absolutelyContinuous (hα : 0 ≤ α)
    (hq : q ≪ speaker α C L b o) : IsProbabilityMeasure (speaker α C L b o) := by
  rw [speaker_eq_ofWeights] at hq ⊢
  refine Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous (fun _ ↦ ?_) hq
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα
    (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)) ENNReal.ofReal_ne_top

variable [MeasurableSingletonClass W] [IsFiniteMeasure (b o)]

/-- At one observation, the divergence of a distribution over utterances from the speaker's and its
entropy add up to the log of the speaker's normalizer less the rationality times its expected
utility. -/
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
    (fun u ↦ ENNReal.mul_ne_top (hw u) ENNReal.ofReal_ne_top)
    (by rwa [speaker_eq_ofWeights] at hq)
  rw [← speaker_eq_ofWeights] at key
  simp only [hterm, ← Finset.mul_sum] at key
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at key
  rw [integral_fintype .of_finite]
  simp only [smul_eq_mul]
  exact key

end Observation

/-! ### The expected utility

The listener's step. The information a listener loses exceeds the conditional entropy of the state
given the utterance by her expected divergence from the posterior
(`InformationTheory.informationLoss_eq_posterior_add`), and the Bayesian listener is the posterior
at every utterance heard. -/

section ExpectedUtility

variable (μ : Measure W) (η : Kernel W U) (L : Kernel U W)

/-- The expected utility of a channel and a listener is minus the information the listener loses
and the expected cost of the utterance: the expectation, over states and utterances, of the
listener's log-probability of the state less the cost. -/
noncomputable def expectedUtility (C : U → ℝ) : EReal :=
  -(informationLoss μ η L : EReal) - (∫ u, C u ∂(η ∘ₘ μ) : ℝ)

variable [Fintype W] [Fintype U] [MeasurableSingletonClass W] [MeasurableSingletonClass U]
  [IsFiniteMeasure μ] [IsFiniteKernel η]

section

variable {μ η L} (C : U → ℝ)

/-- The expected utility is `⊥` exactly when the listener rules out a state at which an utterance
she may hear is produced. -/
theorem expectedUtility_eq_bot_iff :
    expectedUtility μ η L C = ⊥ ↔ ∃ w u, μ {w} ≠ 0 ∧ η w {u} ≠ 0 ∧ L u {w} = 0 := by
  rw [← informationLoss_eq_top_iff]
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h ↦ ?_⟩
  · rw [expectedUtility, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_neg, ← EReal.coe_sub] at h
    exact EReal.coe_ne_bot _ h
  · rw [expectedUtility, h, EReal.coe_ennreal_top, EReal.neg_top, EReal.bot_sub]

/-- Elsewhere the expected utility is real, the expectation of the listener's log-probability of
the state less the cost of the utterance. -/
theorem expectedUtility_of_forall_ne_zero [∀ u, IsZeroOrProbabilityMeasure (L u)]
    (h : ∀ w u, μ {w} ≠ 0 → η w {u} ≠ 0 → L u {w} ≠ 0) :
    expectedUtility μ η L C =
      (∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂η w : ℝ) := by
  have hC : ∫ u, C u ∂(η ∘ₘ μ) = ∑ w, μ.real {w} * ∫ u, C u ∂η w := by
    simp_rw [integral_fintype (.of_finite), smul_eq_mul, Measure.comp_real_singleton,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun u _ ↦ by ring
  rw [expectedUtility, ← EReal.coe_ennreal_toReal (informationLoss_ne_top_iff.2 h),
    toReal_informationLoss h, ← EReal.coe_neg, ← EReal.coe_sub, neg_neg, hC,
    ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, integral_sub (.of_finite) (.of_finite)]

end

variable [Nonempty W]

/-- The Bayesian listener is the posterior at every utterance heard. -/
theorem listener_ae_eq_posterior : listener μ η =ᵐ[η ∘ₘ μ] η†μ :=
  ae_iff_of_countable.2 fun _ hu ↦ listener_apply_eq_posterior μ η hu

variable [∀ u, IsZeroOrProbabilityMeasure (L u)]

/-- The Bayesian listener loses the least information. -/
theorem informationLoss_listener_le :
    informationLoss μ η (listener μ η) ≤ informationLoss μ η L :=
  informationLoss_congr (listener_ae_eq_posterior μ η) ▸ informationLoss_posterior_le μ η L

/-- The Bayesian listener maximizes the expected utility. -/
theorem expectedUtility_le_listener (C : U → ℝ) :
    expectedUtility μ η L C ≤ expectedUtility μ η (listener μ η) C :=
  EReal.sub_le_sub (EReal.neg_le_neg_iff.2
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 (informationLoss_listener_le μ η L))) le_rfl

end ExpectedUtility

/-! ### The free energy -/

variable (μ : Measure W) (κ : Kernel W O) (C : U → ℝ) (α : ℝ)

section Defs

variable [Fintype O]

/-- The free energy of a speaker and a listener is the conditional entropy of the utterance given
the speaker's observation plus `α` times the expected utility. -/
noncomputable def freeEnergy (S : Kernel O U) (L : Kernel U W) : EReal :=
  (∑ o, (κ ∘ₘ μ).real {o} * Hm[S o] : ℝ) + α * expectedUtility μ (S ∘ₖ κ) L C

theorem freeEnergy_id [Fintype W] (S : Kernel W U) (L : Kernel U W) :
    freeEnergy μ Kernel.id C α S L =
      (∑ w, μ.real {w} * Hm[S w] : ℝ) + α * expectedUtility μ S L C := by
  simp only [freeEnergy, Measure.id_comp, Kernel.comp_id]

/-- Against a fixed speaker her Bayesian listener maximizes the free energy. -/
theorem freeEnergy_le_freeEnergy_listener [Fintype W] [Fintype U] [MeasurableSingletonClass W]
    [MeasurableSingletonClass U] [Nonempty W] [IsFiniteMeasure μ] [IsFiniteKernel κ] {α : ℝ}
    (hα : 0 ≤ α) (S : Kernel O U) [IsFiniteKernel S] (L : Kernel U W)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    freeEnergy μ κ C α S L ≤ freeEnergy μ κ C α S (listener μ (S ∘ₖ κ)) :=
  add_le_add_right (mul_le_mul_of_nonneg_left (expectedUtility_le_listener μ (S ∘ₖ κ) L C)
    (EReal.coe_nonneg.2 hα)) _

end Defs

/-! ### The speaker's step

Where the free energy is not `⊥` it is the real number `realFreeEnergy`, and the identity for the
speaker at one observation, averaged over her observations, gives the gap. -/

section Speaker

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U]

/-- The free energy with the listener's log-probability read as a real number, `0` at a state she
rules out. -/
private noncomputable def realFreeEnergy (S : Kernel O U) (L : Kernel U W) : ℝ :=
  ∑ o, (κ ∘ₘ μ).real {o} * Hm[S o] +
    α * ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)

variable {μ κ C α} [IsFiniteMeasure μ] [IsFiniteKernel κ]

omit [MeasurableSingletonClass O] in
private theorem freeEnergy_eq_coe {S : Kernel O U} [IsFiniteKernel S] {L : Kernel U W}
    [∀ u, IsZeroOrProbabilityMeasure (L u)]
    (h : α = 0 ∨ ∀ w u, μ {w} ≠ 0 → (S ∘ₖ κ) w {u} ≠ 0 → L u {w} ≠ 0) :
    freeEnergy μ κ C α S L = realFreeEnergy μ κ C α S L := by
  rcases h with rfl | h
  · simp [freeEnergy, realFreeEnergy]
  · rw [freeEnergy, expectedUtility_of_forall_ne_zero C h, ← EReal.coe_mul, ← EReal.coe_add]
    rfl

omit [MeasurableSingletonClass O] in
private theorem freeEnergy_eq_bot {S : Kernel O U} [IsFiniteKernel S] {L : Kernel U W}
    (hα : 0 < α) (h : ∃ w u, μ {w} ≠ 0 ∧ (S ∘ₖ κ) w {u} ≠ 0 ∧ L u {w} = 0) :
    freeEnergy μ κ C α S L = ⊥ := by
  rw [freeEnergy, (expectedUtility_eq_bot_iff C).2 h, EReal.coe_mul_bot_of_pos hα, EReal.add_bot]

omit [IsFiniteMeasure μ] in
private theorem realFreeEnergy_le [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hα : 0 ≤ α)
    (S : Kernel O U) [IsMarkovKernel S] (L : Kernel U W)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    realFreeEnergy μ κ C α S L ≤ log (Fintype.card U) + α * ∑ u, |C u| := by
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
  · calc ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)
      _ ≤ ∑ w, μ.real {w} * ∑ u, |C u| := Finset.sum_le_sum fun w _ ↦
          mul_le_mul_of_nonneg_left (hV w) measureReal_nonneg
      _ = ∑ u, |C u| := by rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

/-- The free energy is bounded above. -/
theorem freeEnergy_le [IsProbabilityMeasure μ] [IsMarkovKernel κ] (hα : 0 ≤ α) (S : Kernel O U)
    [IsMarkovKernel S] (L : Kernel U W) [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    freeEnergy μ κ C α S L ≤ (log (Fintype.card U) + α * ∑ u, |C u| : ℝ) := by
  by_cases h : ∀ w u, μ {w} ≠ 0 → (S ∘ₖ κ) w {u} ≠ 0 → L u {w} ≠ 0
  · rw [freeEnergy_eq_coe (.inr h)]
    exact EReal.coe_le_coe_iff.2 (realFreeEnergy_le hα S L)
  · rcases hα.eq_or_lt with rfl | hα'
    · rw [freeEnergy_eq_coe (.inl rfl)]
      exact EReal.coe_le_coe_iff.2 (realFreeEnergy_le le_rfl S L)
    · push Not at h
      rw [freeEnergy_eq_bot hα' h]
      exact bot_le

variable [Nonempty W] {b : O → Measure W} (hb : b =ᵐ[κ ∘ₘ μ] κ†μ)
include hb

variable [∀ o, IsFiniteMeasure (b o)]

omit [∀ o, IsFiniteMeasure (b o)] in
private theorem belief_apply_singleton_ne_zero_iff {o : O} (ho : (κ ∘ₘ μ) {o} ≠ 0) (w : W) :
    b o {w} ≠ 0 ↔ μ {w} ≠ 0 ∧ κ w {o} ≠ 0 := by
  rw [ae_iff_of_countable.1 hb o ho, posterior_apply_singleton_ne_zero_iff κ μ ho]

omit [∀ o, IsFiniteMeasure (b o)] in
private theorem comp_real_mul_belief_real (o : O) (w : W) :
    (κ ∘ₘ μ).real {o} * (b o).real {w} = μ.real {w} * (κ w).real {o} := by
  rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with ho | ho
  · rw [← comp_real_mul_posterior_real κ μ w o, measureReal_def (κ ∘ₘ μ), ho,
      ENNReal.toReal_zero, zero_mul, zero_mul]
  · rw [ae_iff_of_countable.1 hb o ho, comp_real_mul_posterior_real]

private theorem sum_mul_integral_eq_sum_comp (S : Kernel O U) [IsFiniteKernel S]
    (L : Kernel U W) :
    ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w) =
      ∑ o, (κ ∘ₘ μ).real {o} * ∫ u, (∫ w, log ((L u).real {w}) ∂(b o) - C u) ∂(S o) := by
  have hrow (o : O) (u : U) :
      (κ ∘ₘ μ).real {o} * (∑ w, (b o).real {w} * log ((L u).real {w}) - C u) =
        ∑ w, μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u) := by
    have h1 : (κ ∘ₘ μ).real {o} * ∑ w, (b o).real {w} * log ((L u).real {w}) =
        ∑ w, μ.real {w} * (κ w).real {o} * log ((L u).real {w}) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by rw [← mul_assoc, comp_real_mul_belief_real hb]
    rw [mul_sub, h1, Measure.comp_real_singleton, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  calc ∑ w, μ.real {w} * ∫ u, (log ((L u).real {w}) - C u) ∂((S ∘ₖ κ) w)
    _ = ∑ w, ∑ u, ∑ o, (S o).real {u} *
          (μ.real {w} * (κ w).real {o} * (log ((L u).real {w}) - C u)) := by
        simp_rw [integral_fintype (.of_finite), smul_eq_mul,
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

variable (hα : 0 ≤ α) {S : Kernel O U} [IsFiniteKernel S]
  {L : Kernel U W} [∀ u, IsZeroOrProbabilityMeasure (L u)]
include hα

private theorem realFreeEnergy_add_sum_klDiv
    (hSp : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → IsProbabilityMeasure (S o))
    (hS : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o ≪ speaker α C L b o) :
    realFreeEnergy μ κ C α S L +
        ∑ o, (κ ∘ₘ μ).real {o} * (klDiv (S o) (speaker α C L b o)).toReal =
      ∑ o, (κ ∘ₘ μ).real {o} *
        log (∑ u, ((b o).geomMean (fun w ↦ L u {w}) ^ α).toReal * exp (-(α * C u))) := by
  rw [realFreeEnergy, sum_mul_integral_eq_sum_comp hb S L, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with h | h
  · simp [measureReal_def, h]
  · have := hSp o h
    linear_combination
      (κ ∘ₘ μ).real {o} * toReal_klDiv_speaker_add_measureEntropy (C := C) hα (hS o h)

omit [IsFiniteKernel S] in
/-- A speaker whose every utterance leaves her listener some chance at every state it may come
from uses no utterance the RSA speaker never uses. -/
private theorem absolutelyContinuous_speaker
    (h : α = 0 ∨ ∀ w u, μ {w} ≠ 0 → (S ∘ₖ κ) w {u} ≠ 0 → L u {w} ≠ 0) {o : O}
    (ho : (κ ∘ₘ μ) {o} ≠ 0) : S o ≪ speaker α C L b o := by
  refine Measure.absolutelyContinuous_of_forall_singleton fun u hu ↦ by_contra fun hSu ↦ ?_
  rcases hα.eq_or_lt with rfl | hα'
  · simp [speaker_apply_singleton] at hu
  · obtain ⟨w, hbw, hL⟩ := (speaker_apply_singleton_eq_zero_iff hα').1 hu
    obtain ⟨hμ, hκ⟩ := (belief_apply_singleton_ne_zero_iff hb ho w).1 hbw
    exact (h.resolve_left hα'.ne') w u hμ
      ((Kernel.comp_apply_singleton_ne_zero_iff S κ).2 ⟨o, hκ, hSu⟩) hL

omit hα [IsFiniteKernel S] in
private theorem ne_zero_of_absolutelyContinuous_speaker (hα : 0 < α)
    (hS : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o ≪ speaker α C L b o) (w : W) (u : U) (hμ : μ {w} ≠ 0)
    (hη : (S ∘ₖ κ) w {u} ≠ 0) : L u {w} ≠ 0 := fun hL ↦ by
  obtain ⟨o, hκ, hSu⟩ := (Kernel.comp_apply_singleton_ne_zero_iff S κ).1 hη
  have ho := Measure.comp_apply_singleton_ne_zero κ μ hμ hκ
  exact hSu (hS o ho ((speaker_apply_singleton_eq_zero_iff hα).2
    ⟨w, (belief_apply_singleton_ne_zero_iff hb ho w).2 ⟨hμ, hκ⟩, hL⟩))

variable (S) [IsMarkovKernel S] (L)

/-- Against a fixed listener, the free energy of a speaker falls short of that of the speaker at
the Bayesian belief by her expected divergence from it over the observations made. It is `⊥`
exactly when she uses, at such an observation, an utterance that speaker never uses. -/
theorem freeEnergy_eq_freeEnergy_speaker_sub :
    freeEnergy μ κ C α S L = freeEnergy μ κ C α (speaker α C L b) L -
      (∑ o, (κ ∘ₘ μ) {o} * klDiv (S o) (speaker α C L b o) : ℝ≥0∞) := by
  by_cases hS : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o ≪ speaker α C L b o
  · have hsupp {S' : Kernel O U} [IsFiniteKernel S']
        (hS' : ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S' o ≪ speaker α C L b o) :
        α = 0 ∨ ∀ w u, μ {w} ≠ 0 → (S' ∘ₖ κ) w {u} ≠ 0 → L u {w} ≠ 0 :=
      hα.eq_or_lt.imp Eq.symm fun hα' ↦ ne_zero_of_absolutelyContinuous_speaker hb hα' hS'
    have h1 := realFreeEnergy_add_sum_klDiv (C := C) hb hα (fun _ _ ↦ inferInstance) hS
    have h2 := realFreeEnergy_add_sum_klDiv (C := C) (S := speaker α C L b) hb hα
      (fun o ho ↦ isProbabilityMeasure_speaker_of_absolutelyContinuous hα (hS o ho))
      fun _ _ ↦ .rfl
    simp only [klDiv_self, ENNReal.toReal_zero, mul_zero, Finset.sum_const_zero, add_zero] at h2
    have hsum : ∑ o, (κ ∘ₘ μ) {o} * klDiv (S o) (speaker α C L b o) = ENNReal.ofReal
        (∑ o, (κ ∘ₘ μ).real {o} * (klDiv (S o) (speaker α C L b o)).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun o _ ↦ mul_nonneg measureReal_nonneg
        ENNReal.toReal_nonneg]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      rcases eq_or_ne ((κ ∘ₘ μ) {o}) 0 with ho | ho
      · simp [measureReal_def, ho]
      · rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top _ _),
          ENNReal.ofReal_toReal (klDiv_ne_top (hS o ho) .of_finite)]
    rw [freeEnergy_eq_coe (hsupp hS), freeEnergy_eq_coe (hsupp fun _ _ ↦ .rfl), hsum,
      EReal.coe_ennreal_ofReal, max_eq_left (Finset.sum_nonneg fun o _ ↦
        mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg), ← EReal.coe_sub]
    exact congrArg _ (by linarith)
  · have hα' : 0 < α := hα.lt_of_ne fun h0 ↦ hS fun o ho ↦
      absolutelyContinuous_speaker hb hα (.inl h0.symm) ho
    have hsupp : ∃ w u, μ {w} ≠ 0 ∧ (S ∘ₖ κ) w {u} ≠ 0 ∧ L u {w} = 0 := by
      by_contra h
      push Not at h
      exact hS fun o ho ↦ absolutelyContinuous_speaker hb hα (.inr h) ho
    push Not at hS
    obtain ⟨o, ho, hac⟩ := hS
    rw [freeEnergy_eq_bot hα' hsupp, ENNReal.sum_eq_top.2 ⟨o, Finset.mem_univ o, by
      rw [klDiv_of_not_ac hac]; exact ENNReal.mul_top ho⟩, EReal.coe_ennreal_top, EReal.sub_top]

/-- Against a fixed listener the speaker at the Bayesian belief maximizes the free energy. -/
theorem freeEnergy_le_freeEnergy_speaker :
    freeEnergy μ κ C α S L ≤ freeEnergy μ κ C α (speaker α C L b) L := by
  rw [freeEnergy_eq_freeEnergy_speaker_sub hb hα S L]
  exact (EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)).trans_eq (sub_zero _)

omit [IsMarkovKernel S] in
private theorem freeEnergy_speaker_eq_coe :
    freeEnergy μ κ C α (speaker α C L b) L = realFreeEnergy μ κ C α (speaker α C L b) L :=
  freeEnergy_eq_coe (hα.eq_or_lt.imp Eq.symm fun hα' ↦
    ne_zero_of_absolutelyContinuous_speaker hb hα' fun _ _ ↦ .rfl)

/-- Only the speaker at the Bayesian belief maximizes the free energy: a speaker who does as well
is that speaker at every observation made. -/
theorem freeEnergy_eq_freeEnergy_speaker_iff :
    freeEnergy μ κ C α S L = freeEnergy μ κ C α (speaker α C L b) L ↔
      ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o = speaker α C L b o := by
  rw [freeEnergy_eq_freeEnergy_speaker_sub hb hα S L, freeEnergy_speaker_eq_coe hb hα L]
  have hzero : ∑ o, (κ ∘ₘ μ) {o} * klDiv (S o) (speaker α C L b o) = 0 ↔
      ∀ o, (κ ∘ₘ μ) {o} ≠ 0 → S o = speaker α C L b o := by
    rw [Finset.sum_eq_zero_iff]
    exact ⟨fun h o ho ↦ klDiv_eq_zero_iff.1 ((mul_eq_zero.1 (h o (Finset.mem_univ o))).resolve_left
      ho), fun h o _ ↦ mul_eq_zero.2 (or_iff_not_imp_left.2 fun ho ↦ klDiv_eq_zero_iff.2 (h o ho))⟩
  rw [← hzero]
  generalize ∑ o, (κ ∘ₘ μ) {o} * klDiv (S o) (speaker α C L b o) = D
  rcases eq_or_ne D ∞ with rfl | hD
  · simp [EReal.sub_top]
  · rw [← EReal.coe_ennreal_toReal hD, ← EReal.coe_sub, EReal.coe_eq_coe_iff, sub_eq_self,
      ENNReal.toReal_eq_zero_iff, or_iff_left hD]

end Speaker

/-! ### The recursion

The speaker who answers the listener of a speaker is again a probability kernel, so the two steps
alternate along the recursion. -/

section Recursion

variable [Fintype W] [Fintype O] [Fintype U] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass U] {μ κ C α}
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] [Nonempty W] {b : O → Measure W}
  [∀ o, IsFiniteMeasure (b o)] (hb : b =ᵐ[κ ∘ₘ μ] κ†μ) (hα : 0 ≤ α)
include hb hα

omit [∀ o, IsFiniteMeasure (b o)] in
theorem speaker_listener_apply_singleton_ne_zero {S : Kernel O U} [IsFiniteKernel S]
    {o : O} {u : U} (ho : (κ ∘ₘ μ) {o} ≠ 0) (hS : S o {u} ≠ 0) :
    speaker α C (listener μ (S ∘ₖ κ)) b o {u} ≠ 0 := by
  refine speaker_apply_singleton_ne_zero hα fun w hbw ↦ ?_
  obtain ⟨hμ, hκ⟩ := (belief_apply_singleton_ne_zero_iff hb ho w).1 hbw
  exact listener_apply_singleton_ne_zero hμ
    ((Kernel.comp_apply_singleton_ne_zero_iff S κ).2 ⟨o, hκ, hS⟩)

omit [∀ o, IsFiniteMeasure (b o)] in
theorem isMarkovKernel_speaker_listener (hκ : ∀ o, (κ ∘ₘ μ) {o} ≠ 0) (S : Kernel O U)
    [IsMarkovKernel S] : IsMarkovKernel (speaker α C (listener μ (S ∘ₖ κ)) b) :=
  ⟨fun o ↦ isProbabilityMeasure_speaker_of_absolutelyContinuous hα (q := S o)
    (Measure.absolutelyContinuous_of_forall_singleton fun _ hu ↦ of_not_not fun hS ↦
      speaker_listener_apply_singleton_ne_zero hb hα (hκ o) hS hu)⟩

omit [∀ o, IsFiniteMeasure (b o)] in
theorem isMarkovKernel_speaker_iterate_recurse (hκ : ∀ o, (κ ∘ₘ μ) {o} ≠ 0) (L : Kernel U W)
    [IsMarkovKernel (speaker α C L b)] (n : ℕ) :
    IsMarkovKernel (speaker α C ((recurse μ κ b α C)^[n] L) b) := by
  induction n with
  | zero => assumption
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isMarkovKernel_speaker_listener hb hα hκ _

variable (hκ : ∀ o, (κ ∘ₘ μ) {o} ≠ 0) (L : Kernel U W) [∀ u, IsZeroOrProbabilityMeasure (L u)]
  [IsMarkovKernel (speaker α C L b)]
include hκ

/-- The free energy rises along the recursion. -/
theorem monotone_freeEnergy_iterate_recurse : Monotone fun n ↦
    freeEnergy μ κ C α (speaker α C ((recurse μ κ b α C)^[n] L) b) ((recurse μ κ b α C)^[n] L) :=
  monotone_nat_of_le_succ fun n ↦ by
    have := isMarkovKernel_speaker_iterate_recurse (C := C) hb hα hκ L n
    rw [Function.iterate_succ_apply']
    exact (freeEnergy_le_freeEnergy_listener μ κ C hα _ _).trans
      (freeEnergy_le_freeEnergy_speaker hb hα _ _)

omit hκ in
private theorem sum_klDiv_speaker_recurse_le :
    ∑ o, (κ ∘ₘ μ) {o} * klDiv (speaker α C L b o) (speaker α C (recurse μ κ b α C L) b o) ≤
      ENNReal.ofReal (realFreeEnergy μ κ C α (speaker α C (recurse μ κ b α C L) b)
        (recurse μ κ b α C L) - realFreeEnergy μ κ C α (speaker α C L b) L) := by
  have h : freeEnergy μ κ C α (speaker α C L b) L ≤
      freeEnergy μ κ C α (speaker α C L b) (recurse μ κ b α C L) :=
    freeEnergy_le_freeEnergy_listener μ κ C hα _ _
  rw [freeEnergy_speaker_eq_coe hb hα L, freeEnergy_eq_freeEnergy_speaker_sub (C := C) hb hα
    (speaker α C L b) (recurse μ κ b α C L), freeEnergy_speaker_eq_coe hb hα] at h
  generalize ∑ o, (κ ∘ₘ μ) {o} *
    klDiv (speaker α C L b o) (speaker α C (recurse μ κ b α C L) b o) = D at h ⊢
  rcases eq_or_ne D ∞ with rfl | hD
  · rw [EReal.coe_ennreal_top, EReal.sub_top] at h
    exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot _)
  · rw [← EReal.coe_ennreal_toReal hD, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    rw [← ENNReal.ofReal_toReal hD]
    exact ENNReal.ofReal_le_ofReal (by linarith)

private theorem monotone_realFreeEnergy_iterate_recurse : Monotone fun n ↦ realFreeEnergy μ κ C α
    (speaker α C ((recurse μ κ b α C)^[n] L) b) ((recurse μ κ b α C)^[n] L) := fun m n h ↦
  EReal.coe_le_coe_iff.1 <| by
    simpa only [freeEnergy_speaker_eq_coe (C := C) hb hα] using
      monotone_freeEnergy_iterate_recurse (C := C) hb hα hκ L h

omit [∀ o, IsFiniteMeasure (b o)] in
private theorem realFreeEnergy_iterate_recurse_le (n : ℕ) : realFreeEnergy μ κ C α
    (speaker α C ((recurse μ κ b α C)^[n] L) b) ((recurse μ κ b α C)^[n] L) ≤
      log (Fintype.card U) + α * ∑ u, |C u| :=
  have := isMarkovKernel_speaker_iterate_recurse (C := C) hb hα hκ L n
  realFreeEnergy_le hα _ _

/-- The free energy converges along the recursion to a real number, being monotone, bounded above
and nowhere `⊥`. -/
theorem exists_tendsto_freeEnergy_iterate_recurse : ∃ g : ℝ, Tendsto (fun n ↦
    freeEnergy μ κ C α (speaker α C ((recurse μ κ b α C)^[n] L) b) ((recurse μ κ b α C)^[n] L))
      atTop (𝓝 g) := by
  simp_rw [freeEnergy_speaker_eq_coe (C := C) hb hα]
  exact ⟨_, (continuous_coe_real_ereal.tendsto _).comp (tendsto_atTop_ciSup
    (monotone_realFreeEnergy_iterate_recurse hb hα hκ L) ⟨_, Set.forall_mem_range.2
      (realFreeEnergy_iterate_recurse_le (C := C) hb hα hκ L)⟩)⟩

/-- The expected divergences of each speaker of the recursion from the next have a finite sum:
every speaker update raises the free energy by at least that divergence, and the free energy is
bounded. -/
theorem tsum_sum_klDiv_speaker_iterate_recurse_ne_top :
    ∑' n, ∑ o, (κ ∘ₘ μ) {o} * klDiv (speaker α C ((recurse μ κ b α C)^[n] L) b o)
      (speaker α C ((recurse μ κ b α C)^[n + 1] L) b o) ≠ ∞ := by
  set R : ℕ → ℝ := fun n ↦ realFreeEnergy μ κ C α
    (speaker α C ((recurse μ κ b α C)^[n] L) b) ((recurse μ κ b α C)^[n] L) with hR
  have hmono : Monotone R := monotone_realFreeEnergy_iterate_recurse (C := C) hb hα hκ L
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
    (r := log (Fintype.card U) + α * ∑ u, |C u| - R 0))
    (ENNReal.tsum_le_of_sum_range_le fun N ↦ ?_)
  calc ∑ n ∈ Finset.range N, ∑ o, (κ ∘ₘ μ) {o} *
        klDiv (speaker α C ((recurse μ κ b α C)^[n] L) b o)
          (speaker α C ((recurse μ κ b α C)^[n + 1] L) b o)
    _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (R (n + 1) - R n) :=
        Finset.sum_le_sum fun n _ ↦ by
          have := isMarkovKernel_speaker_iterate_recurse (C := C) hb hα hκ L n
          simp only [hR, Function.iterate_succ_apply']
          exact sum_klDiv_speaker_recurse_le hb hα _
    _ = ENNReal.ofReal (R N - R 0) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun n _ ↦ sub_nonneg.2 (hmono (Nat.le_add_right n 1)),
          Finset.sum_range_sub]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (sub_le_sub_right
        (realFreeEnergy_iterate_recurse_le (C := C) hb hα hκ L N) _)

/-- Successive speakers of the recursion grow alike: the expected divergence of each from the next
tends to zero. -/
theorem tendsto_sum_klDiv_speaker_iterate_recurse :
    Tendsto (fun n ↦ ∑ o, (κ ∘ₘ μ) {o} * klDiv (speaker α C ((recurse μ κ b α C)^[n] L) b o)
      (speaker α C ((recurse μ κ b α C)^[n + 1] L) b o)) atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    (tsum_sum_klDiv_speaker_iterate_recurse_ne_top hb hα hκ L)

end Recursion

/-! ### The speaker who knows the state -/

/-- A speaker who observes the state itself believes the point mass at it. -/
theorem dirac_ae_eq_posterior_id [MeasurableSingletonClass W] [StandardBorelSpace W] [Nonempty W]
    [IsFiniteMeasure μ] :
    (Measure.dirac : W → Measure W) =ᵐ[(Kernel.id : Kernel W W) ∘ₘ μ]
      (Kernel.id : Kernel W W)†μ := by
  rw [Measure.id_comp]
  filter_upwards [posterior_id μ] with w hw
  rw [hw, Kernel.id_apply]

end RSA
