module

public import Linglib.Pragmatics.Probabilistic.Decision
public import Linglib.Pragmatics.Probabilistic.Speaker
public import Linglib.Pragmatics.SignalingGame.Defs

/-!
# Rational speech acts in a signaling game

The speakers of the Rational Speech Act model are policies of the sender of a signaling game,
`SignalingGame.sender`, at a finite rationality.

The decision-theoretic speaker answers a listener who acts. Where the sender's utility is a reward
for the listener's action less a cost of the signal, `RSA.actionSpeaker` at the scaled cost is the
sender's policy against the listener (`RSA.actionSpeaker_eq_sender_policy`).

The speaker of `RSA.speaker` answers a listener who interprets. In the game `RSA.logScoreGame` the
receiver's action is a belief about the state and the sender's utility is the logarithm of the
probability it gives the state, less a cost. Against a listener who rules out no state, the
speaker who knows the state is the sender's policy (`RSA.speaker_dirac_eq_sender_policy`).

## Implementation notes

An agent's utility is real, and the policy of an agent gives every action positive probability.
The speaker of `RSA.speaker` gives none to an utterance whose listener rules out her state, whose
score is `⊥`, so the two agree only against a listener who rules out no state.

## TODO

* An agent whose utility may be `⊥`, of which `RSA.speaker` is the policy against every listener.
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
    simp only [SignalingGame.sender, Agent.value_mk, Kernel.id_apply, integral_dirac, hG]
    rw [integral_sub (hR w m) (integrable_const _), integral_const, probReal_univ, one_smul]
  unfold actionSpeaker Agent.policy
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

/-- Against a listener who rules out no state, the speaker who knows the state is the sender's
policy in the game of the logarithmic score. -/
theorem speaker_dirac_eq_sender_policy [Fintype W] (pr : Measure W) (C : U → ℝ)
    (L : U → Measure W) [∀ u, IsFiniteMeasure (L u)] (hL : ∀ u w, L u {w} ≠ 0) (α : ℝ) :
    speaker α C L Measure.dirac =
      ((logScoreGame pr C).sender (Kernel.deterministic L .of_discrete)).policy α := by
  have hm (w : W) (u : U) : StronglyMeasurable fun a : Measure W ↦ Real.log (a.real {w}) - C u :=
    ((Real.measurable_log.comp (Measure.measurable_coe (.singleton w)).ennreal_toReal).sub_const
      _).stronglyMeasurable
  have h (w : W) (u : U) : ((logScoreGame pr C).sender (Kernel.deterministic L .of_discrete)).value
      w u = Real.log ((L u).real {w}) - C u := by
    simp only [SignalingGame.sender, Agent.value_mk, Kernel.id_apply, integral_dirac,
      Kernel.deterministic_apply, logScoreGame]
    rw [integral_dirac' _ _ (hm w u)]
  rw [speaker_dirac_eq_softmax]
  unfold Agent.policy
  congr 1
  funext w u
  rw [h, ENNReal.log_pos_real (hL u w) (measure_ne_top _ _), measureReal_def, EReal.coe_mul,
    EReal.coe_sub]

end LogScore

end RSA
