module

public import Linglib.Pragmatics.Probabilistic.Latent
public import Linglib.Pragmatics.Probabilistic.Literal
public import Linglib.Pragmatics.Probabilistic.Parse
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Pragmatics.Agent.Basic

/-!
# The decision-theoretic listener and speaker

A listener who acts holds a belief after an utterance, and a decision problem gives a reward for
each action at each state. She is the agent with that belief and that reward (`RSA.agent`), and [her
policy](##RSA.policy) is the softmax of an action's expected reward under her belief; [the
decision-theoretic speaker](##RSA.actionSpeaker) the softmax of the true reward of the listener's
choice, in expectation, less a cost. The rule is `Kernel.softmax`, as for `RSA.speaker`, and only
the utility differs: hers is linear in the listener's choice where `RSA.utility` is the logarithm of
the listener's mass, so [she sends every utterance, false ones
included](##RSA.actionSpeaker_apply_singleton_ne_zero).

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

section Policy

variable {W U A : Type*} [MeasurableSpace W] [MeasurableSpace U] [Fintype U]
  [DiscreteMeasurableSpace U] [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]

/-- The listener who acts is the agent that believes her interpretation and is rewarded by `R`. -/
abbrev agent (L : Kernel U W) (R : A → W → ℝ) : Agent U W A := ⟨L, fun w a ↦ R a w⟩

/-- The listener's policy is the softmax at rationality `β` of an action's expected reward under her
belief, the policy of the agent `agent L R`. -/
noncomputable def policy (β : ℝ) (L : Kernel U W) (R : A → W → ℝ) : Kernel U A :=
  (agent L R).policy β

variable (β : ℝ) (L : Kernel U W) (R : A → W → ℝ)

instance : IsFiniteKernel (policy β L R) := inferInstanceAs (IsFiniteKernel (Agent.policy _ _))

instance [Nonempty A] : IsMarkovKernel (policy β L R) :=
  inferInstanceAs (IsMarkovKernel (Agent.policy _ _))

variable {β} {u : U} {a a' : A} {w : W}

/-- The policy's share of an action is the real softmax of the scaled expected rewards. -/
theorem policy_real_singleton :
    (policy β L R u).real {a} = Real.softmax (fun a ↦ β * ∫ w, R a w ∂(L u)) a :=
  Agent.policy_real_singleton (ag := agent L R)

/-- Row preference of the policy is comparison of expected reward. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (policy β L R u).real {a} < (policy β L R u).real {a'} ↔
      ∫ w, R a w ∂(L u) < ∫ w, R a' w ∂(L u) :=
  Agent.policy_real_lt_iff (ag := agent L R) hβ

/-- A listener rewarded for guessing the state prefers the states the belief finds more
probable. -/
theorem policy_single_real_lt_iff [Fintype W] [DecidableEq W] [DiscreteMeasurableSpace W]
    [IsFiniteKernel L] (hβ : 0 < β) {w' : W} :
    (policy β L (fun a ↦ Pi.single a 1) u).real {w} <
        (policy β L (fun a ↦ Pi.single a 1) u).real {w'} ↔ (L u).real {w} < (L u).real {w'} := by
  rw [policy_real_lt_iff _ _ hβ]
  simp [integral_fintype .of_finite, Pi.single_apply]

/-- With two actions, the policy's share of one is the logistic function of the scaled
difference in expected reward. -/
theorem policy_real_of_pair (haa' : a ≠ a') (hall : ∀ c, c = a ∨ c = a') :
    (policy β L R u).real {a} =
      Real.sigmoid (β * (∫ w, R a w ∂(L u) - ∫ w, R a' w ∂(L u))) :=
  Agent.policy_real_of_pair (ag := agent L R) haa' hall

/-- A constant gain in every action's expected reward leaves the policy's own expected reward
unchanged. -/
theorem integral_policy_eq_of_integral_eq_add {L' : Kernel U W} {u' : U} {c : ℝ}
    (h : ∀ a, ∫ w, R a w ∂(L u) = ∫ w, R a w ∂(L' u') + c) :
    ∫ a, R a w ∂(policy β L R u) = ∫ a, R a w ∂(policy β L' R u') := by
  simp only [integral_fintype .of_finite, smul_eq_mul, policy_real_singleton, h,
    mul_add]
  rw [Real.softmax_add_const]

end Policy

/-! ### The decision-theoretic speaker -/

section Speaker

variable {W M A : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
  [MeasurableSpace M] [Fintype M] [MeasurableSpace A]

/-- The decision-theoretic speaker is the softmax at rationality `β` of the true reward of the
listener's choice, in expectation, less the utterance's cost. Her utility is linear in the
listener's probabilities, where `RSA.utility` is the logarithm of the listener's mass. -/
noncomputable def actionSpeaker (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ) :
    Kernel W M :=
  Kernel.softmax fun w m ↦ ((β * ∫ a, R a w ∂(π m) - cost m : ℝ) : EReal)

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
      β * ∫ a, R a w ∂(π m) - cost m < β * ∫ a, R a w ∂(π m') - cost m' := by
  rw [actionSpeaker, Kernel.softmax_coe_real_singleton_lt_iff]

/-- With two utterances, the speaker's share of one is the logistic function of the scaled
difference in utility less the difference in cost. -/
theorem actionSpeaker_real_of_pair (hmm' : m ≠ m') (hall : ∀ c, c = m ∨ c = m') :
    (actionSpeaker β cost π R w).real {m} =
      Real.sigmoid (β * (∫ a, R a w ∂(π m) - ∫ a, R a w ∂(π m')) - (cost m - cost m')) := by
  rw [actionSpeaker, Kernel.softmax_real_singleton_of_pair hmm' (EReal.coe_ne_bot _)
    (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe,
    EReal.toReal_coe]
  ring_nf

end Speaker

end RSA
