module

public import Linglib.Pragmatics.Probabilistic.Speaker
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# The MaxiMin speaker

The [MaxiMin speaker](##RSA.maximinSpeaker) is the softmax of the
[least utility](##RSA.maximinUtility) of an utterance over the states she entertains, where the
speaker of the Rational Speech Act model takes the expected utility. Written without logarithms,
[her weight for an utterance](##RSA.maximinSpeaker_eq_ofWeights) is the least mass its listener
gives such a state, where that speaker's is the geometric mean.

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
utility over the states she entertains, the MaxiMin rule, instead of by its expected utility: the
essential infimum of the log of the listener's mass under her belief, less the cost. Her weight
puts the essential infimum of the listener's mass where the expected-utility speaker puts its
geometric mean. She produces the utterances that speaker produces, and is that
speaker when her belief is a point mass, but she depends on her belief only through the states
it entertains, not through their probabilities. -/

private theorem essInf_ne_top [Countable W] {β ν : Measure W} [IsFiniteMeasure ν]
    (hβ : ∃ w, β {w} ≠ 0) : essInf (fun w ↦ ν {w}) β ≠ ∞ :=
  let ⟨w, hw⟩ := hβ
  ne_top_of_le_ne_top (measure_ne_top ν {w}) (ae_iff_of_countable.1 ae_essInf_le w hw)

/-- On a finite space the essential infimum is attained at a point of positive mass, so it
vanishes exactly when the function does at such a point. -/
private theorem essInf_eq_zero_iff [Finite W] {β : Measure W} {f : W → ℝ≥0∞} :
    essInf f β = 0 ↔ ∃ w, β {w} ≠ 0 ∧ f w = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨w, hw, h0⟩ ↦
    le_bot_iff.1 <| (ae_iff_of_countable.1 ae_essInf_le w hw).trans_eq h0⟩
  cases isEmpty_or_nonempty {w // β {w} ≠ 0}
  · have : ⊤ ≤ essInf f β := le_essInf_of_ae_le ⊤ <| ae_iff_of_countable.2 fun w hw ↦
      isEmptyElim (⟨w, hw⟩ : {w // β {w} ≠ 0})
    simp [h] at this
  · obtain ⟨⟨w, hw⟩, hmin⟩ := Finite.exists_min fun x : {w // β {w} ≠ 0} ↦ f x
    exact ⟨w, hw, le_bot_iff.1 <|
      (le_essInf_of_ae_le (f w) (ae_iff_of_countable.2 fun v hv ↦ hmin ⟨v, hv⟩)).trans_eq h⟩

section MaxiMin

variable [Fintype U] [Countable O] [MeasurableSingletonClass O]

omit [MeasurableSpace U] [Fintype U] in
/-- The MaxiMin utility of an utterance to a speaker who believes `β` is the least log of its
listener's mass over the states `β` entertains, less its cost: the least value of the utility of
[spector-2025]'s (28) over those states, the cost being the same at each. -/
noncomputable def maximinUtility (C : U → ℝ) (L : U → Measure W) (β : Measure W) (u : U) : EReal :=
  essInf (fun w ↦ ENNReal.log (L u {w})) β - (C u : EReal)

/-- The MaxiMin speaker at rationality `α` soft-maximizes her MaxiMin utility against the
listener `L`, believing `b o` at `o`. -/
noncomputable def maximinSpeaker (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    Kernel O U :=
  Kernel.softmax fun o u ↦ α * maximinUtility C L (b o) u

/-- Her weight for an utterance is the essential infimum of its listener's mass over her belief,
to the power `α`, times the cost weight. -/
theorem maximinSpeaker_eq_ofWeights (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    maximinSpeaker α C L b = Kernel.ofWeights fun o u ↦
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) := by
  have h (o : O) (u : U) : ENNReal.log (essInf (fun w ↦ L u {w}) (b o)) =
      essInf (fun w ↦ ENNReal.log (L u {w})) (b o) := ENNReal.logOrderIso.essInf_apply _ _
  rw [Kernel.ofWeights_rpow_mul_eq_softmax]
  simp_rw [maximinSpeaker, maximinUtility, ← h, EReal.coe_mul_sub_coe, sub_eq_add_neg,
    EReal.coe_neg]

instance (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    IsFiniteKernel (maximinSpeaker α C L b) :=
  inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) (o : O) :
    IsZeroOrProbabilityMeasure (maximinSpeaker α C L b o) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.softmax _ o))

omit [MeasurableSpace U] [Fintype U] in
theorem maximinUtility_dirac [Fintype W] [MeasurableSingletonClass W] (C : U → ℝ)
    (L : U → Measure W) (w : W) (u : U) :
    maximinUtility C L (Measure.dirac w) u = utility C L (Measure.dirac w) u := by
  rw [maximinUtility, essInf_dirac, utility_dirac]

/-- The MaxiMin speaker who knows the state is the speaker who knows it. -/
theorem maximinSpeaker_dirac [Fintype W] [MeasurableSingletonClass W] (α : ℝ) (C : U → ℝ)
    (L : U → Measure W) : maximinSpeaker α C L Measure.dirac = speaker α C L Measure.dirac := by
  simp only [maximinSpeaker, speaker, maximinUtility_dirac]

variable [MeasurableSingletonClass U] {α : ℝ} {C : U → ℝ} {L : U → Measure W} {b : O → Measure W}
  {o : O} {u : U}

theorem maximinSpeaker_apply_singleton (u : U) :
    maximinSpeaker α C L b o {u} =
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) /
        ∑ u', essInf (fun w ↦ L u' {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  rw [maximinSpeaker_eq_ofWeights]
  exact Kernel.ofWeights_apply_singleton _ o u

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
    or_iff_left (ENNReal.sum_ne_top.2 fun _ _ ↦
      ENNReal.rpow_mul_ofReal_exp_ne_top hα.le (essInf_ne_top hb) _),
    mul_eq_zero, or_iff_left (ENNReal.ofReal_exp_ne_zero _), ENNReal.rpow_eq_zero_iff_of_pos hα,
    essInf_eq_zero_iff]

/-- The MaxiMin speaker produces exactly the utterances the expected-utility speaker produces. -/
theorem maximinSpeaker_apply_singleton_eq_zero_iff_speaker [IsFiniteMeasure (b o)] (hα : 0 < α)
    (hb : ∃ w, b o {w} ≠ 0) : maximinSpeaker α C L b o {u} = 0 ↔ speaker α C L b o {u} = 0 := by
  rw [maximinSpeaker_apply_singleton_eq_zero_iff hα hb, speaker_apply_singleton_eq_zero_iff hα]

/-- Of two utterances the MaxiMin speaker prefers the one of greater weight; the normalization
cancels. -/
theorem maximinSpeaker_real_singleton_lt_iff (hα : 0 ≤ α) (hb : ∃ w, b o {w} ≠ 0) {u u' : U} :
    (maximinSpeaker α C L b o).real {u} < (maximinSpeaker α C L b o).real {u'} ↔
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) <
        essInf (fun w ↦ L u' {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  maximinSpeaker_eq_ofWeights α C L b ▸ Kernel.ofWeights_real_singleton_lt_iff o
    fun _ ↦ ENNReal.rpow_mul_ofReal_exp_ne_top hα (essInf_ne_top hb) _

end MaxiMin

end Pipeline

end RSA
