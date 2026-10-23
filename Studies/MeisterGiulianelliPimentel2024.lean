/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Processing.Surprisal.Generalized

/-!
# Meister, Giulianelli and Pimentel (2024): Towards a Similarity-Adjusted Surprisal Theory

[meister-giulianelli-pimentel-2024] adapt a biodiversity index, which discounts species by their
similarity to one another, into a similarity-adjusted surprisal: the negative logarithm of the
expected similarity of the language model's alternatives to the observed word. It is the
generalized surprisal model of [giulianelli-opedal-cotterell-2024] with the negative logarithm and
a similarity score (`simAdjSurprisal_eq_genSurprisal`). The identity similarity regards different
words as completely distinct, and with it similarity-adjusted surprisal is surprisal
(`simAdjSurprisal_indicatorScore`). The paper's theorem relates it to information value: when the
similarity is one minus a distance, similarity-adjusted surprisal is the negative logarithm of
one minus the information value under that distance (`simAdjSurprisal_one_sub`), so the two
measures stand in a strictly increasing relationship
(`simAdjSurprisal_lt_simAdjSurprisal_iff`).

## Implementation notes

* The paper's similarity and distance take values in the unit interval. The theorems assume only
  that the distance is integrable, and the strict monotonicity that both information values are
  below one: at information value one the paper's similarity-adjusted surprisal is infinite,
  while `Real.log 0 = 0` makes the formal value zero.
* The scoring functions take the alternative first, the target second and the context last, as
  in [giulianelli-opedal-cotterell-2024]; the paper writes the similarity with the target first.
* The similarity-adjusted entropy, the appendix's cost theorem, and the reading-time regressions
  are not formalized.

## References

* [meister-giulianelli-pimentel-2024]
* [giulianelli-opedal-cotterell-2024]
-/

@[expose] public section

namespace MeisterGiulianelliPimentel2024

open InformationTheory MeasureTheory ProbabilityTheory Surprisal Real

variable {C A W : Type*} [MeasurableSpace C] [MeasurableSpace A]

/-- Similarity-adjusted surprisal: the negative logarithm of the expected similarity `z` of the
alternatives to the target. -/
noncomputable def simAdjSurprisal (L : Kernel C A) (z : A → W → C → ℝ) (c : C) (w : W) : ℝ :=
  -log (∫ a, z a w c ∂(L c))

theorem simAdjSurprisal_eq_genSurprisal (L : Kernel C A) (z : A → W → C → ℝ) (c : C) (w : W) :
    simAdjSurprisal L z c w = genSurprisal L (fun x ↦ -log x) z c w := rfl

theorem simAdjSurprisal_indicatorScore [MeasurableSpace W] [MeasurableSingletonClass W]
    (L : Kernel C W) (c : C) (w : W) :
    simAdjSurprisal L indicatorScore c w = surprisal (L c) w :=
  genSurprisal_negLog_indicatorScore L c w

variable (L : Kernel C A) [IsMarkovKernel L] (d : A → W → C → ℝ)

theorem simAdjSurprisal_one_sub {c : C} {w : W} (hd : Integrable (fun a ↦ d a w c) (L c)) :
    simAdjSurprisal L (fun a w c ↦ 1 - d a w c) c w = -log (1 - informationValue L d c w) := by
  simp only [simAdjSurprisal, informationValue, integral_sub (integrable_const 1) hd,
    integral_const, probReal_univ, one_smul]

theorem simAdjSurprisal_lt_simAdjSurprisal_iff {c c' : C} {w w' : W}
    (hd : Integrable (fun a ↦ d a w c) (L c)) (hd' : Integrable (fun a ↦ d a w' c') (L c'))
    (h : informationValue L d c w < 1) (h' : informationValue L d c' w' < 1) :
    simAdjSurprisal L (fun a w c ↦ 1 - d a w c) c w <
        simAdjSurprisal L (fun a w c ↦ 1 - d a w c) c' w' ↔
      informationValue L d c w < informationValue L d c' w' := by
  rw [simAdjSurprisal_one_sub L d hd, simAdjSurprisal_one_sub L d hd', neg_lt_neg_iff,
    log_lt_log_iff (sub_pos.2 h') (sub_pos.2 h), sub_lt_sub_iff_left]

end MeisterGiulianelliPimentel2024
