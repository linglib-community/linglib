module

public import Linglib.Core.MeasureTheory.Function.EssSup
public import Linglib.Pragmatics.Probabilistic.Speaker

/-!
# The MaxiMin speaker

A speaker who weighs an utterance by the least mass its listener gives a state she entertains,
where the speaker of the Rational Speech Act model takes the geometric mean: the
[MaxiMin speaker](##RSA.maximinSpeaker).

## References

* [spector-2025]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

/-! #### The MaxiMin speaker

A speaker who is maximally averse to the risk of being misread values an utterance by its least
utility over the states she entertains, the MaxiMin rule, instead of by its expected utility. Her
weight puts the essential infimum of the listener's mass over her belief where the expected-utility
speaker puts its geometric mean. She produces the utterances that speaker produces, and is that
speaker when her belief is a point mass, but she depends on her belief only through the states
it entertains, not through their probabilities. -/

private theorem essInf_ne_top [Countable W] {β ν : Measure W} [IsFiniteMeasure ν]
    (hβ : ∃ w, β {w} ≠ 0) : essInf (fun w ↦ ν {w}) β ≠ ∞ := by
  obtain ⟨w, hw⟩ := hβ
  rw [essInf_eq_biInf]
  exact ne_top_of_le_ne_top (measure_ne_top ν {w}) (iInf₂_le w hw)

section MaxiMin

variable [Fintype U] [Countable O] [MeasurableSingletonClass O]

/-- The MaxiMin speaker at rationality `α` and cost `C` addresses the listener `L` and at `o`
believes `b o`. Her weight for an utterance is the essential infimum of its listener's mass over
her belief, to the power `α`, times the cost weight. -/
noncomputable def maximinSpeaker (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    Kernel O U :=
  Kernel.ofWeights fun o u ↦
    essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))

instance (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    IsFiniteKernel (maximinSpeaker α C L b) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The MaxiMin speaker who knows the state is the speaker who knows it. -/
theorem maximinSpeaker_dirac [Fintype W] [MeasurableSingletonClass W] (α : ℝ) (C : U → ℝ)
    (L : U → Measure W) : maximinSpeaker α C L Measure.dirac = speaker α C L Measure.dirac := by
  simp only [maximinSpeaker, speaker_eq_ofWeights, essInf_dirac, Measure.geomMean_dirac]

variable [MeasurableSingletonClass U] {α : ℝ} {C : U → ℝ} {L : U → Measure W} {b : O → Measure W}
  {o : O} {u : U}

theorem maximinSpeaker_apply_singleton (u : U) :
    maximinSpeaker α C L b o {u} =
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) /
        ∑ u', essInf (fun w ↦ L u' {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_apply_singleton _ o u

/-- The MaxiMin speaker depends on her belief only through its null sets. -/
theorem maximinSpeaker_congr_belief {b' : O → Measure W} (h : ae (b o) = ae (b' o)) :
    maximinSpeaker α C L b o = maximinSpeaker α C L b' o :=
  Measure.ext_of_singleton fun u ↦ by simp only [maximinSpeaker_apply_singleton, essInf, h]

variable [Fintype W] [∀ u, IsFiniteMeasure (L u)]

/-- The MaxiMin speaker never produces an utterance whose listener rules out a state she
entertains. -/
theorem maximinSpeaker_apply_singleton_eq_zero_iff (hα : 0 < α) (hb : ∃ w, b o {w} ≠ 0) :
    maximinSpeaker α C L b o {u} = 0 ↔ ∃ w, b o {w} ≠ 0 ∧ L u {w} = 0 := by
  rw [maximinSpeaker_apply_singleton, ENNReal.div_eq_zero_iff,
    or_iff_left (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.rpow_mul_ofReal_exp_ne_top hα.le (essInf_ne_top hb) _),
    mul_eq_zero, or_iff_left (ENNReal.ofReal_exp_ne_zero _), ENNReal.rpow_eq_zero_iff_of_pos hα,
    ENNReal.essInf_eq_zero_iff]

/-- The MaxiMin speaker produces exactly the utterances the expected-utility speaker produces. -/
theorem maximinSpeaker_apply_singleton_eq_zero_iff_speaker [IsFiniteMeasure (b o)] (hα : 0 < α)
    (hb : ∃ w, b o {w} ≠ 0) : maximinSpeaker α C L b o {u} = 0 ↔ speaker α C L b o {u} = 0 := by
  rw [maximinSpeaker_apply_singleton_eq_zero_iff hα hb, speaker_apply_singleton_eq_zero_iff hα]

/-- Row preference of the MaxiMin speaker compares the weights; the normalization cancels. -/
theorem maximinSpeaker_real_singleton_lt_iff (hα : 0 ≤ α) (hb : ∃ w, b o {w} ≠ 0)
    (h0 : ∃ u, ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) {u u' : U} :
    (maximinSpeaker α C L b o).real {u} < (maximinSpeaker α C L b o).real {u'} ↔
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) <
        essInf (fun w ↦ L u' {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_real_singleton_lt_iff o
    (fun h ↦ let ⟨u₀, hu₀⟩ := h0
      ENNReal.rpow_mul_ofReal_exp_ne_zero hα (fun h' ↦ (ENNReal.essInf_eq_zero_iff.1 h').elim fun w ⟨hw, hL⟩ ↦
        hu₀ w hw hL) _
        (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.rpow_mul_ofReal_exp_ne_top hα (essInf_ne_top hb) _)

end MaxiMin

end Pipeline

end RSA
