module

public import Linglib.Pragmatics.Agent.FreeEnergy
public import Linglib.Pragmatics.Probabilistic.Decision
public import Linglib.Pragmatics.Probabilistic.Speaker
public import Linglib.Pragmatics.SignalingGame.Defs

/-!
# Rational speech acts in a signaling game

The speaker of the Rational Speech Act model is the policy of an agent: she believes `b`, and an
utterance is worth to her, at a state, the logarithm of its listener's probability of the state
less its cost, which is `⊥` where the listener rules the state out
(`RSA.speaker_eq_policy`). She therefore gives positive probability to exactly the utterances
that are feasible for that agent, and among the distributions over those she alone has the
greatest entropy plus `α` times expected utility
(`RSA.eq_speaker_iff_measureEntropy_add_integral`).

The speakers are also policies of the sender of a signaling game, `SignalingGame.sender`.

The decision-theoretic speaker answers a listener who acts. Where the sender's utility is a reward
for the listener's action less a cost of the signal, `RSA.actionSpeaker` at the scaled cost is the
sender's policy against the listener (`RSA.actionSpeaker_eq_sender_policy`).

The speaker of `RSA.speaker` answers a listener who interprets. In the game `RSA.logScoreGame` the
receiver's action is a belief about the state and the sender's utility is the logarithm of the
probability it gives the state, less a cost. Against a listener who rules out no state, the
speaker who knows the state is the sender's policy (`RSA.speaker_dirac_eq_sender_policy`).

## Implementation notes

The speaker is the policy at each observation where her belief is a probability measure
(`RSA.speaker_apply_eq_policy_apply`). At an observation where it is not, as where it is the
prior conditioned on an event of probability zero, `RSA.speaker` subtracts the cost of an
utterance once and an expected utility weights it by the mass of the belief, so the two differ
when the costs do, and `RSA.speaker` is not defined as the policy.

The utilities of a signaling game are real, so its sender is unconstrained and gives every signal
positive probability. The speaker of `RSA.speaker` gives none to an utterance whose listener rules
out her state, so she is the sender of `RSA.logScoreGame` only against a listener who rules out no
state.

## TODO

* The Bayesian listener as the receiver's best response in `RSA.logScoreGame` among probability
  measures, the logarithmic score being proper.
* A speaker who observes the state through a kernel.

## References

* [frank-goodman-2012]
* [zaslavsky-hu-levy-2021]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section Agent

variable {W O U : Type*} [MeasurableSpace W] [Fintype W] [MeasurableSingletonClass W]
  [MeasurableSpace O] [Countable O] [MeasurableSingletonClass O] [MeasurableSpace U] [Fintype U]

/-- At an observation where her belief is a probability measure, the speaker is the policy of the
agent who believes `b` and to whom an utterance is worth, at a state, the logarithm of its
listener's probability of the state less its cost. -/
theorem speaker_apply_eq_policy_apply (α : ℝ) (C : U → ℝ) (L : U → Measure W)
    [∀ u, IsFiniteMeasure (L u)] (b : O → Measure W) (o : O) [IsProbabilityMeasure (b o)] :
    speaker α C L b o = (Agent.mk (Kernel.ofFunOfCountable b)
      fun w u ↦ ENNReal.log (L u {w}) - (C u : EReal)).policy α o := by
  classical
  have hbot (u : U) (w : W) : ENNReal.log (L u {w}) - (C u : EReal) = ⊥ ↔ L u {w} = 0 := by
    rw [sub_eq_add_neg, EReal.add_eq_bot_iff, ENNReal.log_eq_bot_iff, ← EReal.coe_neg]
    exact or_iff_left (EReal.coe_ne_bot _)
  have key (u : U) : utility C L (b o) u =
      if (Agent.mk (Kernel.ofFunOfCountable b)
        fun w u ↦ ENNReal.log (L u {w}) - (C u : EReal)).Feasible o u then
        ((Agent.mk (Kernel.ofFunOfCountable b)
          fun w u ↦ ENNReal.log (L u {w}) - (C u : EReal)).value o u : EReal) else ⊥ := by
    have hfeas : (Agent.mk (Kernel.ofFunOfCountable b)
        fun w u ↦ ENNReal.log (L u {w}) - (C u : EReal)).Feasible o u ↔
        ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0 := by
      rw [Agent.Feasible, Kernel.ofFunOfCountable_apply,
        measure_null_iff_singleton (Set.to_countable _)]
      exact forall_congr' fun w ↦ by rw [Set.mem_ofPred_eq, hbot, not_imp_not]
    rw [utility, ← Measure.log_geomMean]
    by_cases hf : (Agent.mk (Kernel.ofFunOfCountable b)
        fun w u ↦ ENNReal.log (L u {w}) - (C u : EReal)).Feasible o u
    · have h0 := hfeas.1 hf
      have hpos : 0 < Real.exp (∑ w, (b o).real {w} * Real.log (L u {w}).toReal) := Real.exp_pos _
      simp only [hf, ↓reduceIte]
      rw [Measure.geomMean_eq_ofReal_exp_sum_log h0 fun w _ ↦ measure_ne_top _ _,
        ENNReal.log_pos_real (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hpos.le, Real.log_exp, ← EReal.coe_sub, Agent.value_mk,
        Kernel.ofFunOfCountable_apply, integral_fintype .of_finite]
      congr 1
      have hsum : ∑ w, (b o).real {w} = 1 := by
        rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
      have hterm (w : W) : (b o).real {w} • (ENNReal.log (L u {w}) - (C u : EReal)).toReal =
          (b o).real {w} * Real.log (L u {w}).toReal - (b o).real {w} * C u := by
        rcases eq_or_ne (b o {w}) 0 with hw | hw
        · simp [measureReal_def, hw]
        · rw [ENNReal.log_pos_real (h0 w hw) (measure_ne_top _ _), ← EReal.coe_sub,
            EReal.toReal_coe, smul_eq_mul, mul_sub]
      rw [Finset.sum_congr rfl fun w _ ↦ hterm w, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum,
        one_mul]
    · obtain ⟨w, hb, hL⟩ : ∃ w, b o {w} ≠ 0 ∧ L u {w} = 0 := by
        by_contra h
        exact hf (hfeas.2 fun w hb hL ↦ h ⟨w, hb, hL⟩)
      simp only [hf, ↓reduceIte]
      rw [Measure.geomMean_eq_zero_iff.2 ⟨w, hb, hL⟩, ENNReal.log_zero, EReal.bot_sub]
  unfold speaker Agent.policy Kernel.softmax
  rw [Kernel.ofWeights_apply, Kernel.ofWeights_apply]
  simp only [key]

/-- The speaker whose beliefs are probability measures is the policy of that agent. -/
theorem speaker_eq_policy (α : ℝ) (C : U → ℝ) (L : U → Measure W) [∀ u, IsFiniteMeasure (L u)]
    (b : O → Measure W) [∀ o, IsProbabilityMeasure (b o)] :
    speaker α C L b = (Agent.mk (Kernel.ofFunOfCountable b)
      fun w u ↦ ENNReal.log (L u {w}) - (C u : EReal)).policy α :=
  Kernel.ext fun o ↦ speaker_apply_eq_policy_apply α C L b o

open InformationTheory in
/-- Why the speaker: among the distributions over the utterances she can use, she alone has the
greatest entropy plus `α` times expected utility. -/
theorem eq_speaker_iff_measureEntropy_add_integral {α : ℝ} (hα : 0 < α) (C : U → ℝ)
    (L : U → Measure W) [∀ u, IsFiniteMeasure (L u)] (b : O → Measure W) {o : O}
    [IsProbabilityMeasure (b o)] [MeasurableSingletonClass U] {q : Measure U}
    [IsProbabilityMeasure q] (hq : q ≪ speaker α C L b o) :
    q = speaker α C L b o ↔
      Hm[q] + α * ∫ u, ∫ w, (ENNReal.log (L u {w}) - (C u : EReal)).toReal ∂b o ∂q =
        Hm[speaker α C L b o] +
          α * ∫ u, ∫ w, (ENNReal.log (L u {w}) - (C u : EReal)).toReal ∂b o ∂speaker α C L b o := by
  rw [speaker_apply_eq_policy_apply] at hq ⊢
  exact (Agent.measureEntropy_add_integral_value_eq_iff hα hq).symm

end Agent

section Action

variable {W M A : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
  [MeasurableSpace M] [Fintype M] [MeasurableSpace A]

/-- Where the sender's utility is a reward for the receiver's action less a cost of the signal,
the decision-theoretic speaker at the scaled cost is her policy against the receiver. -/
theorem actionSpeaker_eq_sender_policy (G : SignalingGame W M A) (R : A → W → ℝ) (c : M → ℝ)
    (hG : ∀ w m a, G.senderUtility w m a = R a w - c m) (π : Kernel M A) [IsMarkovKernel π]
    (hR : ∀ w m, Integrable (fun a ↦ R a w) (π m)) (β : ℝ) :
    actionSpeaker β (fun m ↦ β * c m) π R = (G.sender π).policy β := by
  have h (w : W) (m : M) : (G.sender π).value w m = ∫ a, R a w ∂π m - c m := by
    simp only [SignalingGame.sender, Agent.value_coe, Kernel.id_apply, integral_dirac, hG]
    rw [integral_sub (hR w m) (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [Agent.policy_eq_softmax]
  unfold actionSpeaker
  congr 1
  funext w m
  rw [h, mul_sub]

end Action

section LogScore

variable {W U : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
  [MeasurableSpace U] [Fintype U] [DiscreteMeasurableSpace U]

/-- The game in which the receiver's action is a belief about the state, scored by the logarithm
of the probability it gives the state, and the sender pays a cost for her signal. -/
noncomputable def logScoreGame (pr : Measure W) (C : U → ℝ) : SignalingGame W U (Measure W) :=
  ⟨pr, fun w u a ↦ Real.log (a.real {w}) - C u, fun w _ a ↦ Real.log (a.real {w})⟩

-- Against a listener who rules out no state, the speaker who knows the state is the sender's
-- policy in the game of the logarithmic score.
theorem speaker_dirac_eq_sender_policy [Fintype W] (pr : Measure W) (C : U → ℝ)
    (L : U → Measure W) [∀ u, IsFiniteMeasure (L u)] (hL : ∀ u w, L u {w} ≠ 0) (α : ℝ) :
    speaker α C L Measure.dirac =
      ((logScoreGame pr C).sender (Kernel.deterministic L .of_discrete)).policy α := by
  have hm (w : W) (u : U) : StronglyMeasurable fun a : Measure W ↦ Real.log (a.real {w}) - C u :=
    ((Real.measurable_log.comp (Measure.measurable_coe (.singleton w)).ennreal_toReal).sub_const
      _).stronglyMeasurable
  have h (w : W) (u : U) : ((logScoreGame pr C).sender (Kernel.deterministic L .of_discrete)).value
      w u = Real.log ((L u).real {w}) - C u := by
    simp only [SignalingGame.sender, Agent.value_coe, Kernel.id_apply, integral_dirac,
      Kernel.deterministic_apply, logScoreGame]
    rw [integral_dirac' _ _ (hm w u)]
  rw [speaker_dirac_eq_softmax, Agent.policy_eq_softmax]
  congr 1
  funext w u
  rw [h, ENNReal.log_pos_real (hL u w) (measure_ne_top _ _), measureReal_def, EReal.coe_mul,
    EReal.coe_sub]

end LogScore

end RSA
