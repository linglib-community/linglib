module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.InformationTheory.KullbackLeibler.Cond
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Pragmatics.RSA.Basic

/-!
# Speakers with beliefs

A speaker who does not know the state believes a measure on states. `RSA.speaker` scores an
utterance by the expected log-probability its listener gives the state under that belief, as
Goodman and Stuhlmüller do. This file relates that score to the Kullback–Leibler divergence of the
listener's posterior from the belief: the two differ by the entropy of the belief, which no
utterance changes, so they define the same speaker. It then treats the speaker whose belief is a
prior conditioned on what she knows.

## Main results

* `RSA.speaker_eq_softmax_sum_log`, `RSA.speaker_eq_softmax_klDiv`: the speaker is
  the softmax of the expected log-probability the listener gives the state under her belief, and
  of the negative divergence of the listener from her belief.
* `RSA.speaker_cond_ofDensity_apply_eq`: a speaker who knows an event on which every graded
  meaning is constant sees the listener only through those constants.
* `RSA.speaker_cond_listener_truthful_apply_eq`,
  `RSA.speaker_zero_cond_listener_truthful_real_singleton_lt_iff`: a speaker whose belief is the
  prior conditioned on what she knows depends on it, against a literal listener, only through
  the utterances it entails, and among those prefers the one of smaller prior mass.

## References

* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace RSA

variable {W U O : Type*} [MeasurableSpace W] [Fintype W] {α : ℝ} {C : U → ℝ}
  {L : U → Measure W} {b : O → Measure W} {o : O} {u u' : U}

private theorem geomMean_eq_ofReal_exp {β ν : Measure W} [IsFiniteMeasure ν] (h : β ≪ ν) :
    β.geomMean (fun w ↦ ν {w}) =
      ENNReal.ofReal (Real.exp (∑ w, β.real {w} * Real.log (ν.real {w}))) :=
  Measure.geomMean_eq_ofReal_exp_sum_log (fun _ hw hν ↦ hw (h hν)) fun _ _ ↦ measure_ne_top _ _

variable [MeasurableSpace U] [Fintype U] [MeasurableSpace O] [Countable O]
  [MeasurableSingletonClass O]

/-- When every listener dominates every belief, the speaker is the softmax of the expected
log-probability the listener gives the state under the belief, less the cost. -/
theorem speaker_eq_softmax_sum_log [∀ u, IsFiniteMeasure (L u)] (h : ∀ o u, b o ≪ L u) :
    speaker α C L b = Kernel.softmax fun o u ↦
      ((α * (∑ w, (b o).real {w} * Real.log ((L u).real {w}) - C u) : ℝ) : EReal) := by
  refine congrArg Kernel.ofWeights (funext fun o ↦ funext fun u ↦ ?_)
  rw [geomMean_eq_ofReal_exp (h o u), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← Real.exp_mul, EReal.exp_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

variable [MeasurableSingletonClass U]

theorem speaker_apply_singleton_eq_zero_iff_not_ac [IsFiniteMeasure (b o)]
    [∀ u, IsFiniteMeasure (L u)] (hα : 0 < α) : speaker α C L b o {u} = 0 ↔ ¬ b o ≪ L u := by
  rw [speaker_apply_singleton_eq_zero_iff hα, Measure.absolutelyContinuous_iff_forall_singleton,
    not_forall]
  exact exists_congr fun w ↦ by rw [Classical.not_imp, and_comm]

variable [MeasurableSingletonClass W]

private theorem geomMean_rpow_eq_exp_klDiv {β ν : Measure W} [IsProbabilityMeasure β]
    [IsZeroOrProbabilityMeasure ν] (hα : 0 < α) :
    β.geomMean (fun w ↦ ν {w}) ^ α =
      EReal.exp (-((ENNReal.ofReal α * klDiv β ν : ℝ≥0∞) : EReal)) *
        ENNReal.ofReal (Real.exp (-(α * Hm[β]))) := by
  by_cases h : β ≪ ν
  · have : IsProbabilityMeasure ν := (eq_zero_or_isProbabilityMeasure ν).resolve_left fun h0 ↦
      NeZero.ne β (Measure.measure_univ_eq_zero.1 (h (by rw [h0]; rfl)))
    rw [geomMean_eq_ofReal_exp h, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← ENNReal.ofReal_toReal (klDiv_ne_top h .of_finite), ← ENNReal.ofReal_mul hα.le,
      EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg hα.le ENNReal.toReal_nonneg),
      ← EReal.coe_neg, EReal.exp_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    linear_combination α * toReal_klDiv_add_measureEntropy h
  · obtain ⟨w, hν, hβ⟩ : ∃ w, ν {w} = 0 ∧ β {w} ≠ 0 := by
      simpa [Measure.absolutelyContinuous_iff_forall_singleton] using h
    rw [klDiv_of_not_ac h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hα).ne', EReal.coe_ennreal_top,
      EReal.neg_top, EReal.exp_bot, zero_mul, Measure.geomMean_eq_zero_iff.2 ⟨w, hβ, hν⟩,
      ENNReal.zero_rpow_of_pos hα]

/-- For probability beliefs the speaker is the softmax of the negative Kullback–Leibler divergence
of the listener from the belief, less the cost, since the divergence and the expected
log-probability differ by the entropy of the belief, which no utterance changes. -/
theorem speaker_eq_softmax_klDiv [∀ o, IsProbabilityMeasure (b o)]
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (hα : 0 < α) :
    speaker α C L b = Kernel.softmax fun o u ↦
      -((ENNReal.ofReal α * klDiv (b o) (L u) : ℝ≥0∞) : EReal) - ((α * C u : ℝ) : EReal) := by
  refine Kernel.ofWeights_eq_of_mul (c := fun o ↦ ENNReal.ofReal (Real.exp (-(α * Hm[b o]))))
    (fun o ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') (fun _ ↦ ENNReal.ofReal_ne_top)
    fun o u ↦ ?_
  beta_reduce
  rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.exp_add, EReal.exp_coe, geomMean_rpow_eq_exp_klDiv hα]
  ring

/-- At no cost the speaker prefers the utterance whose listener is closer to her belief. -/
theorem speaker_zero_real_singleton_lt_iff_klDiv [IsProbabilityMeasure (b o)]
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (hα : 0 < α) (h : ∃ u, klDiv (b o) (L u) ≠ ∞) :
    (speaker α 0 L b o).real {u} < (speaker α 0 L b o).real {u'} ↔
      klDiv (b o) (L u') < klDiv (b o) (L u) := by
  obtain ⟨u₀, hu₀⟩ := h
  have hac : b o ≪ L u₀ := of_not_not fun hn ↦ hu₀ (klDiv_of_not_ac hn)
  rw [speaker_real_singleton_lt_iff hα.le ⟨u₀, fun _ hw hL ↦ hw (hac hL)⟩]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one,
    geomMean_rpow_eq_exp_klDiv hα]
  rw [ENNReal.mul_lt_mul_iff_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top,
    EReal.exp_lt_exp_iff, EReal.neg_lt_neg_iff, EReal.coe_ennreal_lt_coe_ennreal_iff,
    ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hα).ne' ENNReal.ofReal_ne_top]

/-! ### Knowledge against a literal listener

A speaker who knows only that the state lies in an event believes the prior conditioned on it.
Against a literal listener she produces exactly the utterances her knowledge entails, and among
them prefers the one whose extension has the smaller prior mass. -/

section Cond

variable {μ : Measure W} [IsFiniteMeasure μ] {A : O → Set W} {sem : U → Set W}

theorem speaker_cond_listener_truthful_apply_singleton_eq_zero_iff (hα : 0 < α) :
    speaker α C (listener μ (truthful sem)) (fun o ↦ μ[|A o]) o {u} = 0 ↔ ¬ A o ≤ᵐ[μ] sem u := by
  rw [speaker_apply_singleton_eq_zero_iff_not_ac hα, listener_truthful_apply,
    cond_absolutelyContinuous_cond_iff .of_discrete .of_discrete]

/-- Among the utterances her knowledge entails, the speaker prefers the one of smaller prior
mass. -/
theorem speaker_zero_cond_listener_truthful_real_singleton_lt_iff (hα : 0 < α) (hA : μ (A o) ≠ 0)
    (hu : A o ≤ᵐ[μ] sem u) (hu' : A o ≤ᵐ[μ] sem u') :
    (speaker α 0 (listener μ (truthful sem)) (fun o ↦ μ[|A o]) o).real {u} <
        (speaker α 0 (listener μ (truthful sem)) (fun o ↦ μ[|A o]) o).real {u'} ↔
      μ (sem u') < μ (sem u) := by
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o) := cond_isProbabilityMeasure hA
  rw [speaker_zero_real_singleton_lt_iff_klDiv hα ⟨u, by
      rw [listener_truthful_apply]
      exact mt (klDiv_cond_cond_eq_top_iff .of_discrete .of_discrete).1 (not_not.2 hu)⟩,
    listener_truthful_apply, listener_truthful_apply,
    klDiv_cond_cond_lt_iff .of_discrete .of_discrete .of_discrete hA hu' hu]

private theorem cond_apply_singleton_ne_zero_iff {s : Set W} {w : W} :
    μ[|s] {w} ≠ 0 ↔ w ∈ s ∧ μ {w} ≠ 0 := by
  by_cases hw : w ∈ s <;>
    simp [cond_apply (μ := μ) (MeasurableSet.of_discrete (s := s)), hw, measure_ne_top]

/-- A speaker who knows an event on which every graded meaning is constant sees the listener only
through those constants, so two such events with the same constants yield the same speaker. -/
theorem speaker_cond_ofDensity_apply_eq {m : U → W → ℝ≥0∞} (hα : 0 ≤ α) {o₁ o₂ : O}
    (h₁ : μ (A o₁) ≠ 0) (h₂ : μ (A o₂) ≠ 0) {g : U → ℝ≥0∞}
    (hg₁ : ∀ u, ∀ w ∈ A o₁, μ {w} ≠ 0 → m u w = g u)
    (hg₂ : ∀ u, ∀ w ∈ A o₂, μ {w} ≠ 0 → m u w = g u) :
    speaker α C (Kernel.ofDensity μ m) (fun o ↦ μ[|A o]) o₂ =
      speaker α C (Kernel.ofDensity μ m) (fun o ↦ μ[|A o]) o₁ := by
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₁) := cond_isProbabilityMeasure h₁
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₂) := cond_isProbabilityMeasure h₂
  refine speaker_ofDensity_apply_congr hα cond_absolutelyContinuous
    cond_absolutelyContinuous fun u ↦ ?_
  rw [Measure.geomMean_of_forall_eq fun w hw ↦
      hg₂ u w (cond_apply_singleton_ne_zero_iff.1 hw).1 (cond_apply_singleton_ne_zero_iff.1 hw).2,
    Measure.geomMean_of_forall_eq fun w hw ↦
      hg₁ u w (cond_apply_singleton_ne_zero_iff.1 hw).1 (cond_apply_singleton_ne_zero_iff.1 hw).2]

private theorem geomMean_cond_indicator {s t : Set W} (hs : μ s ≠ 0) [Decidable (s ≤ᵐ[μ] t)] :
    μ[|s].geomMean (t.indicator 1) = if s ≤ᵐ[μ] t then 1 else 0 := by
  have := cond_isProbabilityMeasure (μ := μ) hs
  split_ifs with h
  · exact Measure.geomMean_of_forall_eq fun w hw ↦ Set.indicator_of_mem
      (ae_iff_of_countable.1 h w (cond_apply_singleton_ne_zero_iff.1 hw).2
        (cond_apply_singleton_ne_zero_iff.1 hw).1) 1
  · obtain ⟨w, hμ, hws, hwt⟩ : ∃ w, μ {w} ≠ 0 ∧ w ∈ s ∧ w ∉ t := by
      by_contra hne
      exact h (ae_iff_of_countable.2 fun w hμ hws ↦ by_contra fun hwt ↦ hne ⟨w, hμ, hws, hwt⟩)
    exact Measure.geomMean_eq_zero_iff.2
      ⟨w, cond_apply_singleton_ne_zero_iff.2 ⟨hws, hμ⟩, Set.indicator_of_notMem hwt 1⟩

/-- Against a literal listener the speaker depends on what she knows only through the utterances
it entails. -/
theorem speaker_cond_listener_truthful_apply_eq (hα : 0 ≤ α) {o₁ o₂ : O} (h₁ : μ (A o₁) ≠ 0)
    (h₂ : μ (A o₂) ≠ 0) (h : ∀ u, A o₂ ≤ᵐ[μ] sem u ↔ A o₁ ≤ᵐ[μ] sem u) :
    speaker α C (listener μ (truthful sem)) (fun o ↦ μ[|A o]) o₂ =
      speaker α C (listener μ (truthful sem)) (fun o ↦ μ[|A o]) o₁ := by
  classical
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₁) := cond_isProbabilityMeasure h₁
  have : IsProbabilityMeasure ((fun o ↦ μ[|A o]) o₂) := cond_isProbabilityMeasure h₂
  rw [listener_truthful_eq_ofDensity]
  refine speaker_ofDensity_apply_congr hα cond_absolutelyContinuous
    cond_absolutelyContinuous fun u ↦ ?_
  rw [geomMean_cond_indicator h₂, geomMean_cond_indicator h₁]
  exact if_congr (h u) rfl rfl

end Cond

end RSA
