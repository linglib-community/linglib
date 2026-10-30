/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Processing.Surprisal.Generalized
public import Mathlib.Probability.StrongLaw

/-!
# Giulianelli, Opedal and Cotterell (2024): Generalized Measures of Anticipation and Responsivity

Giulianelli, Opedal and Cotterell define generalized surprisal as a warping of the expected score
of the continuations a language model samples (`Surprisal.genSurprisal`), and estimate it by
warping the mean score of finitely many sampled continuations (`mcEstimate`). The estimator is
[consistent](##ae_tendsto_mcEstimate) when the warping is continuous: by the strong law of large
numbers the mean score converges almost surely to the expected score. With the identity warping it
is also [unbiased](##integral_mcEstimate_id).

## Implementation notes

* The alternatives are random variables on a probability space, each distributed as the
  language model in the context; the paper draws them by ancestral sampling. Consistency assumes
  them pairwise independent, the hypothesis of mathlib's strong law.
* Consistency needs the warping continuous only at the expected score, where the paper assumes
  it continuous.

## References

* [giulianelli-opedal-cotterell-2024]
-/

@[expose] public section

namespace GiulianelliOpedalCotterell2024

open Surprisal
open MeasureTheory ProbabilityTheory Filter Finset Topology

variable {C A W : Type*} [MeasurableSpace C] [MeasurableSpace A]

/-- Eq. (15): the Monte Carlo estimate of generalized surprisal from the first `N` alternatives
`v`, the warping `f` of their mean score against the target `w` in the context `c`. -/
noncomputable def mcEstimate (f : ℝ → ℝ) (g : A → W → C → ℝ) (c : C) (w : W) (v : ℕ → A)
    (N : ℕ) : ℝ :=
  f ((N : ℝ)⁻¹ * ∑ n ∈ range N, g (v n) w c)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {L : Kernel C A} {g : A → W → C → ℝ}
  {c : C} {w : W} {V : ℕ → Ω → A}

private theorem integral_score_comp {n : ℕ} (hV : Measurable (V n)) (hlaw : P.map (V n) = L c)
    (hint : Integrable (fun a ↦ g a w c) (L c)) :
    ∫ ω, g (V n ω) w c ∂P = ∫ a, g a w c ∂(L c) := by
  rw [← hlaw, integral_map hV.aemeasurable (hlaw ▸ hint).aestronglyMeasurable]

/-- The Monte Carlo estimate is consistent: for pairwise independent alternatives distributed as
the language model and a warping continuous at the expected score, it converges almost surely to
the generalized surprisal. -/
theorem ae_tendsto_mcEstimate {f : ℝ → ℝ} (hV : ∀ n, Measurable (V n))
    (hlaw : ∀ n, P.map (V n) = L c) (hindep : Pairwise fun i j ↦ V i ⟂ᵢ[P] V j)
    (hg : Measurable fun a ↦ g a w c) (hint : Integrable (fun a ↦ g a w c) (L c))
    (hf : ContinuousAt f (∫ a, g a w c ∂(L c))) :
    ∀ᵐ ω ∂P, Tendsto (fun N ↦ mcEstimate f g c w (fun n ↦ V n ω) N) atTop
      (𝓝 (genSurprisal L f g c w)) := by
  have hident (i : ℕ) : IdentDistrib (V i) (V 0) P P :=
    ⟨(hV i).aemeasurable, (hV 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩
  have hint0 : Integrable (fun ω ↦ g (V 0 ω) w c) P :=
    ((hlaw 0).symm ▸ hint).comp_measurable (hV 0)
  filter_upwards [strong_law_ae (fun n ω ↦ g (V n ω) w c) hint0
    (fun i j hij ↦ (hindep hij).comp hg hg) fun i ↦ (hident i).comp hg] with ω hω
  rw [integral_score_comp (hV 0) (hlaw 0) hint] at hω
  exact hf.tendsto.comp (by simpa [smul_eq_mul] using hω)

/-- With the identity warping, the Monte Carlo estimate from `N ≠ 0` alternatives distributed as
the language model is unbiased. -/
theorem integral_mcEstimate_id (hV : ∀ n, Measurable (V n)) (hlaw : ∀ n, P.map (V n) = L c)
    (hint : Integrable (fun a ↦ g a w c) (L c)) {N : ℕ} (hN : N ≠ 0) :
    ∫ ω, mcEstimate id g c w (fun n ↦ V n ω) N ∂P = genSurprisal L id g c w := by
  simp only [mcEstimate, genSurprisal, id]
  rw [integral_const_mul, integral_finsetSum _ fun n _ ↦
      ((hlaw n).symm ▸ hint).comp_measurable (hV n)]
  simp_rw [integral_score_comp (hV _) (hlaw _) hint]
  rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN),
    one_mul]

end GiulianelliOpedalCotterell2024
