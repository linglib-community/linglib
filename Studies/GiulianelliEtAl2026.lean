/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.AutoregressiveSequenceModel.Basic
public import Linglib.Processing.Surprisal.Generalized

/-!
# Giulianelli et al. (2026): Incremental Alternative Sampling

[giulianelli-etal-2026] measure a comprehender's predictive uncertainty with alternatives: a
language model, a probability measure on strings, samples continuations of the context, and the
generalised surprisal of a target string scores them against it. Standard surprisal is the member
with the negative logarithm and the prefix indicator, since the continuations beginning with the
target have its conditional prefix probability (`genSurprisal_prefixIndicator`), and by the chain
rule it is the sum of the surprisals of the target's units under the language model's next-unit
laws (`genSurprisal_prefixIndicator_eq_sum`), the paper's treatment of words spanning several
tokens. The indicator evaluates a continuation by its prefix alone: information value with the
complementary distance is the probability of error
(`informationValue_one_sub_prefixIndicator`). Incremental information value (`iiv`) replaces it by
a representational distance between a continuation sampled before the target and the target
followed by a continuation sampled after it, and a distance whose forecast horizon does not reach
past the target reduces it to information value (`iiv_eq_informationValue`).

## Implementation notes

* The paper's `p(· | c)` is `μ.continuation c`, the law of what follows `c` among the strings
  extending it, and its conditional prefix probability `p̄(w | c)` (eq. (1)) is the
  `condPrefixProb` of the autoregressive model of `μ`.
* The forecast horizon enters through the representation function, which averages the encodings
  of the first `min(h, |a|)` units of an alternative (eq. (12)); here it is a distance that reads
  only the first `h` units of each string.
* The alternative-set reformulation with mean, minimum and maximum summary statistics, Monte Carlo
  estimation, and the representation functions, which the paper takes from a Transformer's layers
  and which enter here only through the distance, are not formalized.
* The paper's regression results, which horizon and layer best predict cloze probability, the
  N400 and P600, and eye-tracked and self-paced reading times, are empirical fits and stay in
  prose: explicit predictability peaks at horizon one and lexical representations, the ERP
  components at horizon two, and self-paced reading of multi-sentence stimuli at longer horizons.

## References

* [giulianelli-etal-2026]
* [giulianelli-opedal-cotterell-2024]
* [giulianelli-wallbridge-fernandez-2023]
-/

@[expose] public section

open InformationTheory MeasureTheory ProbabilityTheory Surprisal AutoregressiveSequenceModel

namespace GiulianelliEtAl2026

variable {α : Type*} (μ : Measure (List α))

/-! ### Standard surprisal -/

/-- The prefix indicator (eq. (5)): one when the alternative begins with the target. -/
noncomputable def prefixIndicator (a w _ : List α) : ℝ :=
  ({a' | w <+: a'} : Set (List α)).indicator 1 a

-- (1), (2d)
theorem integral_prefixIndicator (c w : List α) :
    ∫ a, prefixIndicator a w c ∂μ.continuation c =
      (μ[{y | c ++ w <+: y} | {y | c <+: y}]).toReal := by
  simp only [prefixIndicator]
  rw [integral_indicator_one .of_discrete, measureReal_def, Measure.continuation_setOf_prefix]

section LanguageModel

variable [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] {c : List α}

/-- Standard surprisal is generalised surprisal with the negative logarithm and the prefix indicator
(eqs. (2a)–(2d), (4), (5)). -/
theorem genSurprisal_prefixIndicator (hc : μ {y | c <+: y} ≠ 0) (w : List α) :
    genSurprisal μ.continuation (fun r ↦ -Real.log r) prefixIndicator c w =
      -Real.log ((ofMeasure μ).condPrefixProb c w).toReal := by
  rw [genSurprisal, integral_prefixIndicator, condPrefixProb_ofMeasure hc]

theorem genSurprisal_prefixIndicator_eq_sum (hc : μ {y | c <+: y} ≠ 0) {w : List α}
    (hw : μ {y | c ++ w <+: y} ≠ 0) :
    genSurprisal μ.continuation (fun r ↦ -Real.log r) prefixIndicator c w =
      ∑ i : Fin w.length, surprisal ((ofMeasure μ).next (c ++ w.take i)) (some w[i]) := by
  have hsub : {y | c ++ w <+: y} ⊆ {y | c <+: y} := fun _ ↦ (List.prefix_append c w).trans
  rw [genSurprisal_prefixIndicator μ hc, neg_log_condPrefixProb]
  rw [condPrefixProb_ofMeasure hc, cond_apply_of_subset .of_discrete hsub]
  exact ENNReal.div_ne_zero.2 ⟨hw, measure_ne_top _ _⟩

/-! ### What the indicator conflates -/

theorem informationValue_one_sub_prefixIndicator (hc : μ {y | c <+: y} ≠ 0) (w : List α) :
    informationValue μ.continuation (fun a w c ↦ 1 - prefixIndicator a w c) c w =
      1 - ((ofMeasure μ).condPrefixProb c w).toReal := by
  have := μ.isProbabilityMeasure_continuation hc
  have hi : Integrable (fun a ↦ prefixIndicator a w c) (μ.continuation c) :=
    (integrable_const 1).indicator .of_discrete
  rw [informationValue, genSurprisal, id, integral_sub (integrable_const _) hi, integral_const,
    integral_prefixIndicator, condPrefixProb_ofMeasure hc]
  simp

end LanguageModel

/-! ### Incremental information value -/

/-- Incremental information value (eq. (9)): the expected distance between a continuation sampled
before the target and the target followed by a continuation sampled after it. -/
noncomputable def iiv (d : List α → List α → ℝ) (c w : List α) : ℝ :=
  ∫ a, ∫ a', d a (w ++ a') ∂μ.continuation (c ++ w) ∂μ.continuation c

theorem iiv_eq_informationValue [IsFiniteMeasure μ] {d : List α → List α → ℝ} {h : ℕ}
    (hd : ∀ a b, d a b = d (a.take h) (b.take h)) {c w : List α} (hw : h ≤ w.length)
    (hcw : μ {y | c ++ w <+: y} ≠ 0) :
    iiv μ d c w = informationValue μ.continuation (fun a w _ ↦ d a w) c w := by
  have := μ.isProbabilityMeasure_continuation hcw
  have hdw (a a' : List α) : d a (w ++ a') = d a w := by
    rw [hd, List.take_append_of_le_length hw, ← hd]
  simp only [iiv, informationValue, genSurprisal, id, hdw, integral_const, probReal_univ, one_smul]

end GiulianelliEtAl2026
