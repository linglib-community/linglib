/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy
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

Surprisal [levy-2008] is the model with the negative logarithm and the indicator score, and the
next-unit probability the model with the identity and the indicator: every warping of the
indicator score is a warping of the target's probability. Information value
[giulianelli-wallbridge-fernandez-2023], summarised by its mean, is the model with the identity and
a distance score. A model is anticipatory when its score ignores the target and responsive
otherwise, the distinction [pimentel-etal-2023] draw informally for reading times; an
anticipatory model assigns every target the same value, and entropy is the anticipatory model
that scores each alternative by its own surprisal.

## Main definitions

* `genSurprisal L f g c w`: the generalized surprisal of `w` in the context `c`.
* `IsAnticipatory g`: the score `g` is constant in the target.
* `informationValue`, `indicatorScore`.

## Main results

* `genSurprisal_indicatorScore`, `genSurprisal_negLog_indicatorScore`: a warping of the
  indicator model is that warping of the target's probability; with the negative logarithm, the
  target's surprisal.
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
    genSurprisal L f indicatorScore c w = f ((L c).real {w}) := by
  simp only [genSurprisal, indicatorScore, integral_indicator_one (measurableSet_singleton w)]

/-- Surprisal is the indicator model with the negative logarithm. -/
theorem genSurprisal_negLog_indicatorScore :
    genSurprisal L (fun x ↦ -Real.log x) indicatorScore c w = surprisal (L c) w :=
  genSurprisal_indicatorScore L c w _

end indicatorScore

/-! ### Entropy -/

theorem isAnticipatory_surprisal (L : Kernel C A) :
    IsAnticipatory (fun a (_ : W) c ↦ surprisal (L c) a) := fun _ _ _ _ ↦ rfl

/-- Entropy is the anticipatory model with the identity warping that scores each alternative by
its own surprisal. -/
theorem genSurprisal_id_surprisal [Countable A] [MeasurableSingletonClass A] (L : Kernel C A)
    [IsMarkovKernel L] (c : C) (hL : Integrable (surprisal (L c)) (L c)) (w : W) :
    genSurprisal L id (fun a (_ : W) c ↦ surprisal (L c) a) c w = Hm[L c] :=
  (measureEntropy_eq_integral_surprisal _ hL).symm

end Surprisal
