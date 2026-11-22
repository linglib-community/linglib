/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Surprisal

/-!
# Generalized surprisal

This file defines the generalized surprisal of [giulianelli-opedal-cotterell-2024]. A
comprehender's language model in a context is a probability measure `μ` on alternative
continuations, and a scoring function `g` scores an alternative against the target. The expected
score of a target `w` is `∫ a, g a w ∂μ`, and a generalized surprisal model is a pair of a warping
function `f : ℝ → ℝ` and a scoring function: the generalized surprisal of the target is the warped
expected score. The score fixes what counts as an accurate prediction, and the warping the
functional relationship between prediction accuracy and the measured cost, the question
[smith-levy-2013] ask of surprisal.

The expected score of the indicator of an event of alternatives, `𝟙[a ∈ S w]`, is the event's
probability. Over strings the event is the set of continuations that begin with the target; over
next units it is the target itself, and then surprisal [levy-2008], through its real part, is
the model with the negative logarithm, and the next-unit probability the model with the identity.
Information value [giulianelli-wallbridge-fernandez-2023], summarised by its mean, is the expected
score of a distance, and the complementary score `1 - g` has expected value one minus that of
`g`. A score is anticipatory when it ignores the target and responsive otherwise, the distinction
[pimentel-etal-2023] draw informally for reading times; an anticipatory score has the same
expected value at every target, and entropy is the expected value of the anticipatory score of
each alternative by its own surprisal.

## Main definitions

* `expectedScore μ g w`: the expected score `∫ a, g a w ∂μ` of the target `w`.
* `genSurprisal μ f g w`: the generalized surprisal `f (expectedScore μ g w)`.
* `IsAnticipatory g`: the score `g` is constant in the target.
* `indicatorScore`: the score that is one when the alternative is the target.

## Main results

* `expectedScore_indicator`: the expected indicator of an event is the event's probability.
* `expectedScore_one_sub`: the complementary score has expected value one minus that of the
  score.
* `genSurprisal_negLog_indicatorScore`: the indicator model with the negative logarithm is the
  target's surprisal.
* `IsAnticipatory.expectedScore_eq`: an anticipatory score does not depend on the target.
* `not_isAnticipatory_indicatorScore`: the indicator score is responsive.
* `expectedScore_surprisal`: entropy is the expected score of an anticipatory model.

## Implementation notes

The source's language model is a family of distributions indexed by the context, and its scoring
function takes the context as a third argument. Every statement here concerns one context, so the
model is a measure and the score a function of the alternative and the target; a context-dependent
model is `expectedScore (L c) (g · · c)`.

## References

* [giulianelli-opedal-cotterell-2024]
* [giulianelli-wallbridge-fernandez-2023]
* [levy-2008]
* [pimentel-etal-2023]
* [smith-levy-2013]
-/

@[expose] public section

namespace SurprisalTheory

open InformationTheory MeasureTheory ProbabilityTheory

variable {A W : Type*} [MeasurableSpace A] {μ : Measure A} {g : A → W → ℝ} {w : W}

/-- The expected score `g a w` of the target `w` against the alternatives `a` that the language
model `μ` samples. -/
noncomputable def expectedScore (μ : Measure A) (g : A → W → ℝ) (w : W) : ℝ :=
  ∫ a, g a w ∂μ

/-- The generalized surprisal of the target `w` under the model `(f, g)`: the warping `f` of the
expected score. -/
noncomputable def genSurprisal (μ : Measure A) (f : ℝ → ℝ) (g : A → W → ℝ) (w : W) : ℝ :=
  f (expectedScore μ g w)

/-- The expected indicator of an event `S w` of alternatives is the event's probability. -/
theorem expectedScore_indicator {S : W → Set A} (hS : MeasurableSet (S w)) :
    expectedScore μ (fun a w ↦ (S w).indicator 1 a) w = μ.real (S w) :=
  integral_indicator_one hS

/-- The complementary score `1 - g` has expected value one minus that of `g`. -/
theorem expectedScore_one_sub [IsProbabilityMeasure μ] (hg : Integrable (fun a ↦ g a w) μ) :
    expectedScore μ (1 - g) w = 1 - expectedScore μ g w := by
  simp only [expectedScore, Pi.sub_apply, Pi.one_apply, integral_sub (integrable_const 1) hg,
    integral_const, probReal_univ, one_smul]

/-! ### Anticipation and responsivity -/

/-- A scoring function is anticipatory when it is constant in the target, so that the model
measures an uncertainty fixed by the context and the language model. A score that is not
anticipatory is responsive. -/
def IsAnticipatory (g : A → W → ℝ) : Prop := ∀ a w w', g a w = g a w'

/-- An anticipatory score has the same expected value at every target. -/
theorem IsAnticipatory.expectedScore_eq (hg : IsAnticipatory g) (μ : Measure A) (w w' : W) :
    expectedScore μ g w = expectedScore μ g w' := by
  simp only [expectedScore, hg _ w w']

/-! ### The indicator score -/

/-- The indicator score: one when the alternative is the target. -/
noncomputable def indicatorScore (a w : W) : ℝ := ({w} : Set W).indicator 1 a

/-- The indicator score is responsive. -/
theorem not_isAnticipatory_indicatorScore [Nontrivial W] :
    ¬ IsAnticipatory (indicatorScore : W → W → ℝ) := fun hg ↦ by
  obtain ⟨w, w', hw⟩ := exists_pair_ne W
  simpa [indicatorScore, hw] using hg w w w'

section indicatorScore

variable [MeasurableSpace W] [MeasurableSingletonClass W] (μ : Measure W) (w : W)

/-- The expected indicator score is the target's probability. -/
theorem expectedScore_indicatorScore : expectedScore μ indicatorScore w = μ.real {w} :=
  expectedScore_indicator (S := fun w ↦ {w}) (measurableSet_singleton w)

/-- Surprisal is the indicator model with the negative logarithm, through its real part: at a
target of probability zero the surprisal is `∞` and both sides are `0`. -/
theorem genSurprisal_negLog_indicatorScore [IsZeroOrProbabilityMeasure μ] :
    genSurprisal μ (fun x ↦ -Real.log x) indicatorScore w = (surprisal μ w).toReal := by
  rw [genSurprisal, expectedScore_indicatorScore, toReal_surprisal prob_le_one]

end indicatorScore

/-! ### Entropy -/

/-- The score of an alternative by the real part of its own surprisal is anticipatory. -/
theorem isAnticipatory_surprisal (μ : Measure A) :
    IsAnticipatory (fun a (_ : W) ↦ (surprisal μ a).toReal) := fun _ _ _ ↦ rfl

/-- Entropy is the expected value of the anticipatory score of each alternative by the real part
of its own surprisal; an alternative of probability zero, whose surprisal is `∞` and its real
part `0`, carries no weight. -/
theorem expectedScore_surprisal [Countable A] [MeasurableSingletonClass A] (μ : Measure A)
    [IsZeroOrProbabilityMeasure μ] (hμ : Integrable (fun a ↦ (surprisal μ a).toReal) μ) (w : W) :
    expectedScore μ (fun a (_ : W) ↦ (surprisal μ a).toReal) w = Hm[μ] :=
  (measureEntropy_eq_integral_surprisal _ hμ).symm

end SurprisalTheory
