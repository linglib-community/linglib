module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Analysis.SpecialFunctions.Softmax

/-!
# The decision-theoretic listener and speaker

This file defines the listener of Rational Speech Act models who acts. After an utterance the
listener's belief is a kernel from utterances to states, and a decision problem is a reward for
each action at each state. The listener's expected reward of an action is the reward averaged over
the belief, and the listener chooses an action by the softmax of expected reward at a rationality.
The decision-theoretic utility of an utterance for the speaker is the true reward of the action
the listener's policy chooses. In a signaling game an action is a guess of the state, rewarded
when right, so the expected reward of a guess is the belief's mass on it. The decision-theoretic
speaker chooses an utterance by the softmax of its utility less its cost. Her utility is linear in
the listener's choice where that of `RSA.speaker` is the logarithm of the listener's mass, so she
sends every utterance, false ones included, with positive probability.

## Main definitions

* `RSA.expectedReward`: the listener's expected reward of an action after an utterance.
* `RSA.policy`: the listener's policy, the softmax of expected reward at a rationality.
* `RSA.actionUtility`: the expected true reward of the listener's choice, the speaker's
  decision-theoretic utility of an utterance at a state.
* `RSA.actionSpeaker`: the speaker, the softmax of utility less cost at a rationality.

## Main results

* `RSA.policy_real_lt_iff`, `RSA.policy_single_real_lt_iff`: the listener prefers the action with
  the higher expected reward, and in a signaling game the state the belief finds more probable.
* `RSA.policy_real_singleton`: the policy's share of an action is the real softmax.
* `RSA.policy_real_of_pair`, `RSA.actionUtility_of_pair`: with two actions the share is the
  logistic function of the scaled difference in expected reward, and the utility is the rewards
  weighted by the shares.
* `RSA.actionSpeaker_real_lt_iff`, `RSA.actionSpeaker_real_of_pair`,
  `RSA.actionSpeaker_apply_singleton_ne_zero`: the speaker prefers the utterance of higher utility
  less cost, with two utterances her share is logistic, and she sends every utterance.

## References

* [sumers-etal-2024]
* [harding-gerstenberg-icard-2025]
* [brochhagen-franke-van-rooij-2018]
* [van-rooy-2003]
* [qing-franke-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section ActionUtility

variable {W U A : Type*} [MeasurableSpace U] [Fintype A] [MeasurableSpace A]

/-- The decision-theoretic utility of an utterance at a state is the true reward of the action
the listener's policy chooses, in expectation. -/
noncomputable def actionUtility (π : Kernel U A) (R : A → W → ℝ) (u : U) (w : W) : ℝ :=
  ∑ a, (π u).real {a} * R a w

variable [DiscreteMeasurableSpace A] (R : A → W → ℝ) (π : Kernel U A) {u : U} {a a' : A} {w : W}

/-- With two actions, utility is the reward of the first weighted by its share and of the second
by the rest. -/
theorem actionUtility_of_pair [IsMarkovKernel π] (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    actionUtility π R u w = (π u).real {a} * R a w + (1 - (π u).real {a}) * R a' w := by
  rw [actionUtility, Fintype.sum_eq_add a a' haa' (fun c hc ↦ absurd (hall c) (not_or.mpr hc)),
    ← measureReal_singleton_add_singleton_of_pair (π u) haa' (fun c _ ↦ hall c)]
  ring

omit [DiscreteMeasurableSpace A] in
/-- When an action is a guess of the state, rewarded when right, the utility of an utterance at a
state is the listener's chance of guessing that state. -/
theorem actionUtility_single [DecidableEq A] (π : Kernel U A) (u : U) (a : A) :
    actionUtility π (fun a ↦ Pi.single a 1) u a = (π u).real {a} := by
  simp [actionUtility, Pi.single_apply]

end ActionUtility

section Policy

variable {W U A : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSpace U]

/-- The listener's expected reward of an action after an utterance is the reward averaged over
the belief. -/
noncomputable def expectedReward (L : Kernel U W) (R : A → W → ℝ) (u : U) (a : A) : ℝ :=
  ∑ w, (L u).real {w} * R a w

theorem expectedReward_single [DecidableEq W] (L : Kernel U W) (u : U) (w : W) :
    expectedReward L (fun a ↦ Pi.single a 1) u w = (L u).real {w} := by
  simp [expectedReward, Pi.single_apply]

variable [Fintype U] [DiscreteMeasurableSpace U] [Fintype A] [MeasurableSpace A]
  [DiscreteMeasurableSpace A]

/-- The score of an action for the listener is rationality times expected reward. -/
noncomputable def policyScore (β : ℝ) (L : Kernel U W) (R : A → W → ℝ) (u : U) (a : A) :
    EReal :=
  ((β * expectedReward L R u a : ℝ) : EReal)

/-- The listener's policy is the softmax of expected reward at rationality `β`. -/
noncomputable def policy (β : ℝ) (L : Kernel U W) (R : A → W → ℝ) : Kernel U A :=
  Kernel.softmax (policyScore β L R)

variable (β : ℝ) (L : Kernel U W) (R : A → W → ℝ)

instance : IsFiniteKernel (policy β L R) := inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty A] : IsMarkovKernel (policy β L R) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

variable {β} {u : U} {a a' : A} {w : W}

/-- The policy's share of an action is the real softmax of the scaled expected rewards. -/
theorem policy_real_singleton :
    (policy β L R u).real {a} = Real.softmax (fun a ↦ β * expectedReward L R u a) a :=
  Kernel.softmax_coe_real_singleton (fun u a ↦ β * expectedReward L R u a) u a

/-- Row preference of the policy is comparison of expected reward. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (policy β L R u).real {a} < (policy β L R u).real {a'} ↔
      expectedReward L R u a < expectedReward L R u a' :=
  (Kernel.softmax_coe_real_singleton_lt_iff (fun u a ↦ β * expectedReward L R u a) u).trans
    (mul_lt_mul_iff_right₀ hβ)

/-- A listener rewarded for guessing the state prefers the states the belief finds more
probable. -/
theorem policy_single_real_lt_iff [DecidableEq W] [DiscreteMeasurableSpace W] (hβ : 0 < β)
    {w' : W} :
    (policy β L (fun a ↦ Pi.single a 1) u).real {w} <
        (policy β L (fun a ↦ Pi.single a 1) u).real {w'} ↔ (L u).real {w} < (L u).real {w'} := by
  rw [policy_real_lt_iff _ _ hβ, expectedReward_single, expectedReward_single]

/-- With two actions, the policy's share of one is the logistic function of the scaled
difference in expected reward. -/
theorem policy_real_of_pair (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    (policy β L R u).real {a} =
      Real.sigmoid (β * (expectedReward L R u a - expectedReward L R u a')) := by
  rw [policy, Kernel.softmax_real_singleton_of_pair (score := policyScore β L R) (w := u) haa'
    (EReal.coe_ne_bot _) (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c),
    policyScore, policyScore, EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

theorem actionUtility_policy_eq_of_expectedReward_eq_add {L' : Kernel U W} {u' : U} {c : ℝ}
    (h : ∀ a, expectedReward L R u a = expectedReward L' R u' a + c) :
    actionUtility (policy β L R) R u w = actionUtility (policy β L' R) R u' w := by
  simp only [actionUtility, policy_real_singleton, h, mul_add]
  rw [Real.softmax_add_const]

end Policy

/-! ### The decision-theoretic speaker -/

section Speaker

variable {W M A : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
  [MeasurableSpace M] [Fintype M] [Fintype A] [MeasurableSpace A]

/-- The speaker's score of an utterance is rationality times its utility, less its cost. -/
noncomputable def actionSpeakerScore (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ)
    (w : W) (m : M) : EReal :=
  ((β * actionUtility π R m w - cost m : ℝ) : EReal)

/-- The decision-theoretic speaker is the softmax of utility less cost at rationality `β`. The
utility is the true reward of the listener's choice, linear in the listener's probabilities, where
`RSA.speaker` scores an utterance by the logarithm of the listener's mass. -/
noncomputable def actionSpeaker (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ) :
    Kernel W M :=
  Kernel.softmax (actionSpeakerScore β cost π R)

variable (β : ℝ) (R : A → W → ℝ) (cost : M → ℝ) (π : Kernel M A)

instance : IsFiniteKernel (actionSpeaker β cost π R) :=
  inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty M] : IsMarkovKernel (actionSpeaker β cost π R) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary M, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

variable {β} {m m' : M} {w : W} [MeasurableSingletonClass M]

/-- The speaker sends every utterance, false ones included, with positive probability. -/
theorem actionSpeaker_apply_singleton_ne_zero : actionSpeaker β cost π R w {m} ≠ 0 :=
  Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _

/-- The speaker prefers the utterance of higher utility less cost. -/
theorem actionSpeaker_real_lt_iff :
    (actionSpeaker β cost π R w).real {m} < (actionSpeaker β cost π R w).real {m'} ↔
      β * actionUtility π R m w - cost m < β * actionUtility π R m' w - cost m' := by
  rw [actionSpeaker, Kernel.softmax_real_singleton_lt_iff (score := actionSpeakerScore β cost π R)
    (w := w) (fun _ ↦ EReal.coe_ne_top _) ⟨m, EReal.coe_ne_bot _⟩, actionSpeakerScore,
    actionSpeakerScore, EReal.coe_lt_coe_iff]

/-- With two utterances, the speaker's share of one is the logistic function of the scaled
difference in utility less the difference in cost. -/
theorem actionSpeaker_real_of_pair (hmm' : m ≠ m') (hall : ∀ c, c = m ∨ c = m') :
    (actionSpeaker β cost π R w).real {m} =
      Real.sigmoid (β * (actionUtility π R m w - actionUtility π R m' w) - (cost m - cost m')) := by
  rw [actionSpeaker, Kernel.softmax_real_singleton_of_pair (score := actionSpeakerScore β cost π R)
    (w := w) hmm' (EReal.coe_ne_bot _) (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _)
    (fun c _ ↦ hall c), actionSpeakerScore, actionSpeakerScore, EReal.toReal_coe,
    EReal.toReal_coe]
  ring_nf

end Speaker

end RSA
