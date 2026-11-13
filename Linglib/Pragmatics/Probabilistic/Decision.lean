module

public import Linglib.Pragmatics.Probabilistic.Basic
public import Linglib.Core.Analysis.SpecialFunctions.Softmax

/-!
# The decision-theoretic listener and speaker

A listener who acts holds a belief after an utterance, and a decision problem gives a reward for
each action at each state. [Her policy](##RSA.policy) is the softmax of an action's expected reward
under her belief, and [the decision-theoretic speaker](##RSA.actionSpeaker) the softmax of the true
reward of the listener's choice, in expectation, less a cost. The rule is `Kernel.softmax`, as for
`RSA.speaker`, and only the utility differs: hers is linear in the listener's choice where
`RSA.utility` is the logarithm of the listener's mass, so
[she sends every utterance, false ones included](##RSA.actionSpeaker_apply_singleton_ne_zero).

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

/-- With two actions, the expected reward of a choice weighs the reward of the first by its share
and of the second by the rest. -/
theorem integral_of_pair {A : Type*} [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {ν : Measure A} [IsProbabilityMeasure ν] {f : A → ℝ} {a a' : A} (haa' : a ≠ a')
    (hall : ∀ c, c = a ∨ c = a') :
    ∫ c, f c ∂ν = ν.real {a} * f a + (1 - ν.real {a}) * f a' := by
  rw [integral_fintype .of_finite, Fintype.sum_eq_add a a' haa'
    (fun c hc ↦ absurd (hall c) (not_or.mpr hc)),
    ← measureReal_singleton_add_singleton_of_pair ν haa' (fun c _ ↦ hall c)]
  simp only [smul_eq_mul]
  ring

/-- When an action is a guess of the state, rewarded when right, the expected reward of a guess is
its mass. -/
theorem integral_pi_single {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (x : X) :
    ∫ y, (Pi.single y 1 : X → ℝ) x ∂ν = ν.real {x} := by
  simp [integral_fintype .of_finite, Pi.single_apply]

section Policy

variable {W U A : Type*} [MeasurableSpace W] [MeasurableSpace U] [Fintype U]
  [DiscreteMeasurableSpace U] [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]

/-- The listener's policy is the softmax at rationality `β` of an action's expected reward under her
belief. -/
noncomputable def policy (β : ℝ) (L : Kernel U W) (R : A → W → ℝ) : Kernel U A :=
  Kernel.softmax fun u a ↦ ((β * ∫ w, R a w ∂(L u) : ℝ) : EReal)

variable (β : ℝ) (L : Kernel U W) (R : A → W → ℝ)

instance : IsFiniteKernel (policy β L R) := inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty A] : IsMarkovKernel (policy β L R) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary A, EReal.coe_ne_bot _⟩)
    (fun _ _ ↦ EReal.coe_ne_top _)

variable {β} {u : U} {a a' : A} {w : W}

/-- The policy's share of an action is the real softmax of the scaled expected rewards. -/
theorem policy_real_singleton :
    (policy β L R u).real {a} = Real.softmax (fun a ↦ β * ∫ w, R a w ∂(L u)) a :=
  Kernel.softmax_coe_real_singleton (fun u a ↦ β * ∫ w, R a w ∂(L u)) u a

/-- Row preference of the policy is comparison of expected reward. -/
theorem policy_real_lt_iff (hβ : 0 < β) :
    (policy β L R u).real {a} < (policy β L R u).real {a'} ↔
      ∫ w, R a w ∂(L u) < ∫ w, R a' w ∂(L u) :=
  (Kernel.softmax_coe_real_singleton_lt_iff (fun u a ↦ β * ∫ w, R a w ∂(L u)) u).trans
    (mul_lt_mul_iff_right₀ hβ)

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
      Real.sigmoid (β * (∫ w, R a w ∂(L u) - ∫ w, R a' w ∂(L u))) := by
  rw [policy, Kernel.softmax_real_singleton_of_pair haa' (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)
    (fun _ ↦ EReal.coe_ne_top _) (fun c _ ↦ hall c), EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

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
