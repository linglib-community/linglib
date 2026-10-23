/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.UniformOn

/-!
# Trivalent probability

A trivalent proposition is true, false or void at each world, and a bet on it is won, lost or
called off. Its probability is the weight of its truth relative to that of its truth and falsity
together: the conditional probability that it is true given that it is not void, and `1` by
convention when it is void almost surely ([egre-rossi-sprenger-2026a]). On a two-valued
proposition it is the probability that the proposition is true, and on a conditional assertion of
a two-valued consequent it is the conditional probability of the consequent given the condition,
which is Adams's Thesis.

## Main definitions

* `Trivalent.prob`: the probability of a trivalent proposition.

## Main statements

* `Trivalent.prob_eq_div`: the weight of truth over that of truth and falsity.
* `Trivalent.prob_eq_one_iff`, `Trivalent.prob_eq_zero_iff`: probability `1` is almost sure
  non-falsity, and probability `0` is almost sure non-truth where falsity has positive weight.
* `Trivalent.prob_ofProp`, `Trivalent.prob_indicator_ofProp`: ordinary probability on two-valued
  propositions, and Adams's Thesis on conditional assertions.
* `Trivalent.prob_neg`: negation complements the probability unless the proposition is void almost
  surely.
* `Trivalent.prob_joinBelnap`: additivity for disjuncts that are defined together and never true
  together.
* `Trivalent.prob_smul`, `Trivalent.prob_uniformOn_univ`, `Trivalent.prob_count_eq`: only
  relative weights matter, so the uniform credence counts worlds.

## Implementation notes

The credence is any measure on a discrete measurable space, as the finite world spaces of the
literature are, and probabilities are `ℝ≥0∞`-valued.

## References

* [egre-rossi-sprenger-2026a]
-/

@[expose] public section

namespace Trivalent

open MeasureTheory ProbabilityTheory SignType Function
open scoped ENNReal

variable {W : Type*} [MeasurableSpace W]

/-- The probability of a trivalent proposition is the conditional probability that it is true given
that it is not void, and `1` when it is void almost surely. -/
noncomputable def prob (μ : Measure W) (p : W → SignType) : ℝ≥0∞ :=
  if μ (support p) = 0 then 1 else μ[posExt p | support p]

variable {μ : Measure W} {p : W → SignType}

theorem prob_of_measure_support_eq_zero (h : μ (support p) = 0) : prob μ p = 1 :=
  ite_eq_left h

theorem prob_of_measure_support_ne_zero (h : μ (support p) ≠ 0) :
    prob μ p = μ[posExt p | support p] :=
  ite_eq_right h

theorem prob_le_one [IsFiniteMeasure μ] : prob μ p ≤ 1 := by
  unfold prob
  split_ifs with h
  · exact le_rfl
  · have := cond_isProbabilityMeasure (μ := μ) h
    exact MeasureTheory.prob_le_one

/-- Trivalent probability reads only the relative weights, so it is invariant under rescaling the
credence. -/
theorem prob_smul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) : prob (c • μ) p = prob μ p := by
  unfold prob
  rw [cond_smul hc0 hc, Measure.smul_apply, smul_eq_mul]
  simp only [mul_eq_zero, or_iff_right hc0]

/-- Against the uniform credence on a finite world space, trivalent probability counts worlds. -/
theorem prob_uniformOn_univ [Fintype W] [Nonempty W] (p : W → SignType) :
    prob (uniformOn Set.univ) p = prob Measure.count p := by
  rw [show (uniformOn Set.univ : Measure W) = (Fintype.card W : ℝ≥0∞)⁻¹ • Measure.count by
      rw [uniformOn, ProbabilityTheory.cond, Measure.restrict_univ, Measure.count_univ]
      simp [ENat.card_eq_coe_fintype_card],
    prob_smul (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero))]

/-- On a two-valued proposition, trivalent probability is the probability of truth. -/
@[simp] theorem prob_ofProp [IsProbabilityMeasure μ] (A : W → Prop) [DecidablePred A] :
    prob μ (fun w ↦ ofProp (A w)) = μ {w | A w} := by
  rw [prob_of_measure_support_ne_zero (by simp), support_ofProp, cond_univ]
  congr 1
  ext w
  simp

variable [DiscreteMeasurableSpace W]

/-- Where a proposition is not void almost surely, its probability is the weight of its truth over
that of its truth and falsity together. -/
theorem prob_eq_div (h : μ (support p) ≠ 0) :
    prob μ p = μ (posExt p) / (μ (posExt p) + μ (negExt p)) := by
  rw [prob_of_measure_support_ne_zero h,
    cond_apply_of_subset .of_discrete (posExt_subset_support p), ← posExt_union_negExt,
    measure_union (disjoint_posExt_negExt p) .of_discrete]

theorem prob_eq_div_measure_support (h : μ (support p) ≠ 0) :
    prob μ p = μ (posExt p) / μ (support p) := by
  rw [prob_of_measure_support_ne_zero h,
    cond_apply_of_subset .of_discrete (posExt_subset_support p)]

/-- Against the counting credence, trivalent probability is a ratio of world counts. -/
theorem prob_count_eq {P S : Finset W} (hpos : ∀ w, p w = 1 ↔ w ∈ P)
    (hsupp : ∀ w, p w ≠ 0 ↔ w ∈ S) (hS : S.Nonempty) :
    prob Measure.count p = P.card / S.card := by
  have hpos' : posExt p = ↑P := Set.ext fun w ↦ (hpos w).trans Finset.mem_coe.symm
  have hsupp' : support p = ↑S := Set.ext fun w ↦ (hsupp w).trans Finset.mem_coe.symm
  have h : Measure.count (support p) ≠ 0 := by
    rw [hsupp', Measure.count_apply_finset]
    exact_mod_cast Finset.card_ne_zero.2 hS
  rw [prob_eq_div_measure_support h, hpos', hsupp', Measure.count_apply_finset,
    Measure.count_apply_finset]

/-- **Trivalent additivity.** Disjoining propositions that are defined together and never true
together adds their probabilities, the additivity of [egre-rossi-sprenger-2026a]'s trivalent
probability; without the properness hypothesis all three probabilities can be `1` by the all-void
convention. -/
theorem prob_joinBelnap {q : W → SignType} (hsupp : support p = support q)
    (hdisj : Disjoint (posExt p) (posExt q)) (h : μ (support p) ≠ 0) :
    prob μ (fun w ↦ joinBelnap (p w) (q w)) = prob μ p + prob μ q := by
  have hpt : ∀ w, p w = 0 ↔ q w = 0 := fun w ↦
    not_iff_not.1 (iff_of_eq (congrArg (w ∈ ·) hsupp))
  have hsupp' : support (fun w ↦ joinBelnap (p w) (q w)) = support p := by
    ext w
    simp only [mem_support, ne_eq, joinBelnap_eq_zero_iff, hpt w, and_self]
  have hpos : posExt (fun w ↦ joinBelnap (p w) (q w)) = posExt p ∪ posExt q := by
    ext w
    simp [joinBelnap_eq_one_iff]
  rw [prob_eq_div_measure_support (hsupp' ▸ h : μ (support fun w ↦ joinBelnap (p w) (q w)) ≠ 0),
    prob_eq_div_measure_support h, prob_eq_div_measure_support (hsupp ▸ h), hsupp', hpos,
    measure_union hdisj .of_discrete, ← hsupp, ENNReal.div_add_div_same]

/-- Probability `1` is almost sure non-falsity. -/
theorem prob_eq_one_iff [IsFiniteMeasure μ] : prob μ p = 1 ↔ μ (negExt p) = 0 := by
  by_cases h : μ (support p) = 0
  · exact iff_of_true (prob_of_measure_support_eq_zero h)
      (measure_mono_null (negExt_subset_support p) h)
  · have := cond_isProbabilityMeasure (μ := μ) h
    rw [prob_of_measure_support_ne_zero h, ← prob_compl_eq_zero_iff .of_discrete,
      cond_apply .of_discrete, support_inter_compl_posExt, mul_eq_zero,
      or_iff_right (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))]

@[simp] theorem prob_dirac_eq_one_iff {w : W} : prob (Measure.dirac w) p = 1 ↔ 0 ≤ p w := by
  rw [prob_eq_one_iff, Measure.dirac_apply' _ .of_discrete, Set.indicator_apply_eq_zero]
  cases h : p w <;> simp [h]

/-- Probability `0` is almost sure non-truth where falsity has positive weight. -/
theorem prob_eq_zero_iff [IsFiniteMeasure μ] :
    prob μ p = 0 ↔ μ (posExt p) = 0 ∧ μ (negExt p) ≠ 0 := by
  by_cases h : μ (support p) = 0
  · rw [prob_of_measure_support_eq_zero h]
    exact iff_of_false one_ne_zero fun h' ↦ h'.2 (measure_mono_null (negExt_subset_support p) h)
  · rw [prob_of_measure_support_ne_zero h, cond_apply .of_discrete,
      Set.inter_eq_right.2 (posExt_subset_support p), mul_eq_zero,
      or_iff_right (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))]
    refine ⟨fun h0 ↦ ⟨h0, fun h1 ↦ h ?_⟩, And.left⟩
    rw [← posExt_union_negExt]
    exact measure_union_null h0 h1

/-- **Adams's Thesis.** A conditional assertion of a two-valued consequent on the condition `s` has
the conditional probability of the consequent given `s`. -/
theorem prob_indicator_ofProp (s : Set W) (B : W → Prop) [DecidablePred B] (h : μ s ≠ 0) :
    prob μ (s.indicator fun w ↦ ofProp (B w)) = μ[{w | B w} | s] := by
  have hs : support (s.indicator fun w ↦ ofProp (B w)) = s := by simp [Set.support_indicator]
  rw [prob_of_measure_support_ne_zero (by rwa [hs]), hs, ← cond_inter_self .of_discrete {w | B w}]
  congr 1
  ext w
  by_cases hw : w ∈ s <;> simp [hw]

/-- Negation complements the probability, unless the proposition is void almost surely, when both
probabilities are `1`. -/
theorem prob_neg [IsFiniteMeasure μ] (h : μ (support p) ≠ 0) : prob μ (-p) = 1 - prob μ p := by
  have hs : support (-p) = support p := by ext w; simp
  have := cond_isProbabilityMeasure (μ := μ) h
  rw [prob_of_measure_support_ne_zero (hs ▸ h), prob_of_measure_support_ne_zero h, hs,
    ← prob_compl_eq_one_sub .of_discrete, cond_apply .of_discrete, cond_apply .of_discrete,
    support_inter_compl_posExt]
  congr 2
  ext w
  cases h : p w <;> simp [h]

end Trivalent
