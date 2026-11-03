module

public import Linglib.Core.InformationTheory.Entropy.Surprisal
public import Linglib.Pragmatics.RSA.Basic

/-!
# The speaker and the Kullback–Leibler divergence

Goodman and Stuhlmüller's speaker scores an utterance by the expected log-probability its listener
gives the state under her belief. That score and the negative Kullback–Leibler divergence of the
listener from her belief differ by the entropy of the belief, which no utterance changes, so she is
equally [the softmax of the negative divergence](##RSA.speaker_eq_softmax_klDiv), and at no cost
[prefers the utterance whose listener is closer to her
belief](##RSA.speaker_zero_real_singleton_lt_iff_klDiv).

## References

* [goodman-stuhlmuller-2013]
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace RSA

variable {W U O : Type*} [MeasurableSpace W] [Fintype W] [MeasurableSingletonClass W]
  [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U] [MeasurableSpace O] [Countable O]
  [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} {L : U → Measure W} {b : O → Measure W} {o : O}
  {u u' : U}

theorem speaker_eq_softmax_klDiv [∀ o, IsProbabilityMeasure (b o)]
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (hα : 0 ≤ α) :
    speaker α C L b = Kernel.softmax fun o u ↦
      α * -(klDiv (b o) (L u) : EReal) - ((α * C u : ℝ) : EReal) := by
  rw [speaker, Kernel.ofWeights_rpow_mul_eq_softmax]
  refine Kernel.softmax_eq_of_add (k := fun o ↦ α * -Hm[b o]) fun o u ↦ ?_
  rw [geomMean_eq_exp_neg_lintegral_surprisal, EReal.log_exp,
    lintegral_surprisal_eq_ofReal_add_klDiv, EReal.coe_ennreal_add,
    EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _)) (.inr (EReal.coe_ennreal_ne_bot _)),
    EReal.coe_ennreal_ofReal, max_eq_left (measureEntropy_nonneg _), sub_eq_add_neg,
    ← EReal.coe_neg, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hα) (EReal.coe_ne_top α),
    ← EReal.coe_mul, EReal.coe_neg (α * C u), sub_eq_add_neg]
  ac_rfl

theorem speaker_zero_real_singleton_lt_iff_klDiv [IsProbabilityMeasure (b o)]
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (hα : 0 < α) :
    (speaker α 0 L b o).real {u} < (speaker α 0 L b o).real {u'} ↔
      klDiv (b o) (L u') < klDiv (b o) (L u) := by
  by_cases h : ∃ u₀, b o ≪ L u₀
  · obtain ⟨u₀, hu₀⟩ := h
    rw [speaker_real_singleton_lt_iff hα.le ⟨u₀, fun _ hw hL ↦ hw (hu₀ hL)⟩]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one,
      geomMean_eq_exp_neg_lintegral_surprisal, lintegral_surprisal_eq_ofReal_add_klDiv]
    rw [ENNReal.rpow_lt_rpow_iff hα, EReal.exp_lt_exp_iff, EReal.neg_lt_neg_iff,
      EReal.coe_ennreal_lt_coe_ennreal_iff, ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top]
  · push Not at h
    have h0 (v : U) : (speaker α 0 L b o).real {v} = 0 := by
      rw [measureReal_def, (speaker_apply_singleton_eq_zero_iff_not_ac hα).2 (h v),
        ENNReal.toReal_zero]
    rw [h0, h0, klDiv_of_not_ac (h u), klDiv_of_not_ac (h u')]
    exact iff_of_false (lt_irrefl _) (lt_irrefl _)

end RSA
