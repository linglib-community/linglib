/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Surprisal
public import Mathlib.Probability.Kernel.Defs

/-!
# Generalized surprisal

This file defines the generalized surprisal of [giulianelli-opedal-cotterell-2024]. A
comprehender's language model is a Markov kernel from contexts to alternative continuations, and
a generalized surprisal model is a pair of a warping function `f : ℝ → ℝ` and a scoring function
`g`, which scores an alternative against the target in the context. The generalized surprisal of
the target is the warped expected score. The score fixes what counts as an accurate prediction,
and the warping the functional relationship between prediction accuracy and the measured cost,
the question [smith-levy-2013] ask of surprisal.

A score that is the indicator of an event of alternatives, `𝟙[a ∈ S w c]`, makes every warping
a warping of the event's probability. Over strings the event is the set of continuations that
begin with the target; over next units it is the target itself, and then surprisal [levy-2008],
through its real part, is the model with the negative logarithm, and the next-unit probability
the model with the identity. Information value [giulianelli-wallbridge-fernandez-2023], summarised
by its mean, is the model with the identity and a distance score, and the complementary score
`1 - g` has expected value one minus that of `g`. A model is anticipatory when its score ignores
the target and responsive otherwise, the distinction [pimentel-etal-2023] draw informally for
reading times; an anticipatory model assigns every target the same value, and entropy is the
anticipatory model that scores each alternative by its own surprisal.

## Main definitions

* `genSurprisal L f g c w`: the generalized surprisal of `w` in the context `c`.
* `IsAnticipatory g`: the score `g` is constant in the target.
* `informationValue L d c w`: the expected distance `d` of the alternatives from `w`.
* `indicatorScore`: the score that is one when the alternative is the target.

## Main results

* `genSurprisal_indicator`: a warping of the indicator of an event is that warping of the
  event's probability.
* `genSurprisal_indicatorScore`, `genSurprisal_negLog_indicatorScore`: a warping of the
  indicator model is that warping of the target's probability; with the negative logarithm, the
  target's surprisal.
* `genSurprisal_one_sub`: the complementary score warps one minus the expected score.
* `IsAnticipatory.genSurprisal_eq`: an anticipatory model does not depend on the target.
* `not_isAnticipatory_indicatorScore`: the indicator score is responsive.
* `genSurprisal_id_surprisal`: entropy is an anticipatory generalized surprisal.

## References

* [giulianelli-opedal-cotterell-2024]
* [giulianelli-wallbridge-fernandez-2023]
* [levy-2008]
* [pimentel-etal-2023]
* [smith-levy-2013]
-/

@[expose] public section

namespace Surprisal

open InformationTheory MeasureTheory ProbabilityTheory

variable {C A W : Type*} [MeasurableSpace C] [MeasurableSpace A]

/-- The generalized surprisal of the target `w` in the context `c` under the model `(f, g)`: the
warping `f` of the expected score `g a w c` of the alternatives `a` that the language model `L`
samples in the context. -/
noncomputable def genSurprisal (L : Kernel C A) (f : ℝ → ℝ) (g : A → W → C → ℝ) (c : C)
    (w : W) : ℝ :=
  f (∫ a, g a w c ∂(L c))

/-- Information value with the mean as its summary statistic: the expected distance `d` from the
alternatives to the target, the model with the identity warping and the distance as score. -/
noncomputable def informationValue (L : Kernel C A) (d : A → W → C → ℝ) : C → W → ℝ :=
  genSurprisal L id d

/-- A warping of the model whose score is the indicator of an event `S w c` of alternatives is
that warping of the event's probability. -/
theorem genSurprisal_indicator (L : Kernel C A) (f : ℝ → ℝ) {S : W → C → Set A} {c : C} {w : W}
    (hS : MeasurableSet (S w c)) :
    genSurprisal L f (fun a w c ↦ (S w c).indicator 1 a) c w = f ((L c).real (S w c)) := by
  simp only [genSurprisal, integral_indicator_one hS]

/-- The model with the complementary score `1 - g` warps one minus the expected score. -/
theorem genSurprisal_one_sub (L : Kernel C A) (f : ℝ → ℝ) {g : A → W → C → ℝ} {c : C} {w : W}
    [IsProbabilityMeasure (L c)] (hg : Integrable (fun a ↦ g a w c) (L c)) :
    genSurprisal L f (1 - g) c w = f (1 - informationValue L g c w) := by
  simp only [genSurprisal, informationValue, id, Pi.sub_apply, Pi.one_apply,
    integral_sub (integrable_const 1) hg, integral_const, probReal_univ, one_smul]

/-! ### Anticipation and responsivity -/

/-- A scoring function is anticipatory when it is constant in the target, so that the model
measures an uncertainty fixed by the context and the language model. A model whose score is not
anticipatory is responsive. -/
def IsAnticipatory (g : A → W → C → ℝ) : Prop := ∀ a w w' c, g a w c = g a w' c

/-- An anticipatory model assigns every target the same value. -/
theorem IsAnticipatory.genSurprisal_eq {g : A → W → C → ℝ} (hg : IsAnticipatory g)
    (L : Kernel C A) (f : ℝ → ℝ) (c : C) (w w' : W) :
    genSurprisal L f g c w = genSurprisal L f g c w' := by
  simp only [genSurprisal, hg _ w w']

/-! ### The indicator score -/

/-- The indicator score: one when the alternative is the target. -/
noncomputable def indicatorScore (a w : W) (_ : C) : ℝ := ({w} : Set W).indicator 1 a

omit [MeasurableSpace C] in
/-- The indicator score is responsive. -/
theorem not_isAnticipatory_indicatorScore [Nontrivial W] [Nonempty C] :
    ¬ IsAnticipatory (indicatorScore : W → W → C → ℝ) := fun hg ↦ by
  obtain ⟨w, w', hw⟩ := exists_pair_ne W
  simpa [indicatorScore, hw] using hg w w w' (Classical.arbitrary C)

section indicatorScore

variable [MeasurableSpace W] [MeasurableSingletonClass W] (L : Kernel C W) (c : C) (w : W)

/-- A warping of the indicator model is that warping of the target's probability; with the
identity it is the probability itself. -/
theorem genSurprisal_indicatorScore (f : ℝ → ℝ) :
    genSurprisal L f indicatorScore c w = f ((L c).real {w}) :=
  genSurprisal_indicator L f (S := fun w _ ↦ {w}) (measurableSet_singleton w)

/-- Surprisal is the indicator model with the negative logarithm, through its real part: at a
target of probability zero the surprisal is `∞` and both sides are `0`. -/
theorem genSurprisal_negLog_indicatorScore [IsMarkovKernel L] :
    genSurprisal L (fun x ↦ -Real.log x) indicatorScore c w = (surprisal (L c) w).toReal :=
  (genSurprisal_indicatorScore L c w _).trans (toReal_surprisal prob_le_one).symm

end indicatorScore

/-! ### Entropy -/

/-- The score of an alternative by the real part of its own surprisal is anticipatory. -/
theorem isAnticipatory_surprisal (L : Kernel C A) :
    IsAnticipatory (fun a (_ : W) c ↦ (surprisal (L c) a).toReal) := fun _ _ _ _ ↦ rfl

/-- Entropy is the anticipatory model with the identity warping that scores each alternative by
the real part of its own surprisal; an alternative of probability zero, whose surprisal is `∞`
and its real part `0`, carries no weight. -/
theorem genSurprisal_id_surprisal [Countable A] [MeasurableSingletonClass A] (L : Kernel C A)
    [IsMarkovKernel L] (c : C) (hL : Integrable (fun a ↦ (surprisal (L c) a).toReal) (L c))
    (w : W) : genSurprisal L id (fun a (_ : W) c ↦ (surprisal (L c) a).toReal) c w = Hm[L c] :=
  (measureEntropy_eq_integral_surprisal _ hL).symm

end Surprisal
