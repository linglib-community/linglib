/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.MeasureTheory.Measure.Tilted
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Probability.Kernel.Softmax
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# MaxEnt grammars

A MaxEnt grammar gives each candidate `c` a probability [proportional
to](##HarmonicGrammar.maxEnt_real_singleton) the exponential of its harmony `-(w ⬝ᵥ T c)`:
`HarmonicGrammar.maxEnt T w` is the counting measure tilted by the harmony. So the
[log-odds](##HarmonicGrammar.log_maxEnt_real_singleton_div) of two candidates are the difference
of their harmonies. Scaling the weights up
[concentrates](##HarmonicGrammar.tendsto_maxEnt_smul_atTop) the distribution on the candidate of
greatest harmony, and when the violations of a tuple of outputs add up, the outputs [are
independent](##HarmonicGrammar.maxEnt_sum). The conditional grammar
`HarmonicGrammar.condMaxEnt T w` is the softmax kernel of the harmony, taking each input to the
MaxEnt distribution of its candidates.

## Implementation notes

* The candidates of one input form a finite type. A conditional grammar takes, at an input `i`,
  the violations `(con.comap (i, ·)).violations` of the candidates paired with `i`, and
  `condMaxEnt` assembles these into a kernel over finitely many inputs.
* Goldwater and Johnson write the exponent as `∑ i, wᵢ fᵢ` without a sign; harmony negates the
  weighted violations here, as in Hayes and Wilson, so that positive weights penalize.
* The log-likelihood takes the empirical distribution of a sample; the log-probability of `n`
  draws is `n` times it.

## References

* [goldwater-johnson-2003]
* [hayes-wilson-2008]
* [berger-della-pietra-della-pietra-1996]
* [della-pietra-della-pietra-lafferty-1997]
* [smolensky-legendre-2006]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal

namespace HarmonicGrammar

variable {C ι : Type*} [Fintype ι]

section LogPartition

variable [Fintype C] (T : C → ι → ℝ) (w : ι → ℝ)

/-- The log-partition function, the log of the normalizing constant of the MaxEnt
distribution. -/
noncomputable def logPartition : ℝ :=
  log (∑ c, exp (harmony T w c))

end LogPartition

variable [MeasurableSpace C]

/-- The MaxEnt distribution of candidates with violation vectors `T` under weights `w` weighs each
candidate by the exponential of its harmony. -/
noncomputable def maxEnt (T : C → ι → ℝ) (w : ι → ℝ) : Measure C :=
  Measure.count.tilted (harmony T w)

theorem maxEnt_congr {ι' : Type*} [Fintype ι'] {T : C → ι → ℝ} {w : ι → ℝ} {T' : C → ι' → ℝ}
    {w' : ι' → ℝ} (h : harmony T w = harmony T' w') : maxEnt T w = maxEnt T' w' := by
  simp only [maxEnt, h]

variable [Fintype C] [MeasurableSingletonClass C] (T : C → ι → ℝ) (w : ι → ℝ)

instance : IsZeroOrProbabilityMeasure (maxEnt T w) := by
  unfold maxEnt; infer_instance

instance [Nonempty C] : IsProbabilityMeasure (maxEnt T w) :=
  isProbabilityMeasure_tilted .of_finite

theorem integral_eq_sum (q : Measure C) [IsFiniteMeasure q] :
    ∫ c, T c ∂q = ∑ c, q.real {c} • T c :=
  integral_fintype .of_finite

/-! ### Probabilities -/

theorem maxEnt_real_singleton (c : C) : (maxEnt T w).real {c} = softmax (harmony T w) c :=
  count_tilted_real_singleton _ c

theorem maxEnt_singleton (c : C) :
    maxEnt T w {c} = ENNReal.ofReal (softmax (harmony T w) c) := by
  rw [← maxEnt_real_singleton, ofReal_measureReal]

theorem maxEnt_real_singleton_pos (c : C) : 0 < (maxEnt T w).real {c} := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton]
  exact softmax_pos _ c

theorem absolutelyContinuous_maxEnt (q : Measure C) : q ≪ maxEnt T w :=
  absolutelyContinuous_count_tilted q _

theorem log_maxEnt_real_singleton (c : C) :
    log ((maxEnt T w).real {c}) = harmony T w c - logPartition T w := by
  have : Nonempty C := ⟨c⟩
  rw [maxEnt_real_singleton, log_softmax, logPartition]

/-- The log-odds of two candidates are their harmony difference, `-(w ⬝ᵥ (T a - T b))`, linear
in the weights. -/
theorem log_maxEnt_real_singleton_div (a b : C) :
    log ((maxEnt T w).real {a} / (maxEnt T w).real {b}) = harmony T w a - harmony T w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, log_softmax_div_softmax]

theorem maxEnt_real_singleton_lt_iff {a b : C} :
    (maxEnt T w).real {a} < (maxEnt T w).real {b} ↔ harmony T w a < harmony T w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, softmax_lt_softmax_iff]

theorem maxEnt_real_singleton_le_iff {a b : C} :
    (maxEnt T w).real {a} ≤ (maxEnt T w).real {b} ↔ harmony T w a ≤ harmony T w b := by
  have : Nonempty C := ⟨a⟩
  rw [maxEnt_real_singleton, maxEnt_real_singleton, softmax_le_softmax_iff]

/-- Of exactly two candidates, one has the sigmoid of its harmony advantage over the other. -/
theorem maxEnt_real_singleton_of_pair [DecidableEq C] {a b : C} (hab : a ≠ b)
    (h : (univ : Finset C) = {a, b}) :
    (maxEnt T w).real {a} = sigmoid (harmony T w a - harmony T w b) := by
  rw [maxEnt_real_singleton, softmax_eq_sigmoid_of_univ_eq_pair hab h]

/-- Scaling the weights scales the harmonies, so the MaxEnt distribution concentrates on the sole
candidate of greatest harmony. -/
theorem tendsto_maxEnt_smul_atTop {c : C} (h : univ.argmax (harmony T w) = {c}) :
    Tendsto (fun α : ℝ ↦ (maxEnt T (α • w)).real {c}) atTop (𝓝 1) := by
  simpa [maxEnt_real_singleton, harmony_smul] using tendsto_softmax_atTop fun c' hc' ↦
    (Finset.argmax_eq_singleton_iff.1 h).2 c' (mem_univ c') hc'

/-! ### Joint evaluation -/

section Joint

variable {κ O : Type*} [Fintype κ] [DecidableEq κ] [Fintype O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [Nonempty O] (T : κ → O → ι → ℝ)

/-- When the violations of an output tuple add up its coordinates' violations, the MaxEnt
distribution of the tuples is the product of the coordinates' MaxEnt distributions, so the
coordinates are independent. -/
theorem maxEnt_sum :
    maxEnt (fun f : κ → O ↦ ∑ k, T k (f k)) w = Measure.pi fun k ↦ maxEnt (T k) w := by
  refine Measure.ext_iff_singleton.2 fun f ↦ ?_
  simp_rw [Measure.pi_singleton, maxEnt_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ ↦ softmax_nonneg _ _, funext (harmony_sum T w),
    softmax_sum_apply (fun k ↦ harmony (T k) w) f]

theorem map_eval_maxEnt_sum (k : κ) :
    (maxEnt (fun f : κ → O ↦ ∑ k, T k (f k)) w).map (Function.eval k) = maxEnt (T k) w := by
  simp [maxEnt_sum, Measure.pi_map_eval]

end Joint

/-! ### Conditional MaxEnt -/

section Conditional

variable {X Y : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y] (T : X × Y → ι → ℝ) (w : ι → ℝ)

/-- The conditional MaxEnt grammar takes each input to the MaxEnt distribution of its candidates,
whose violation vectors are `T (x, ·)`. It is the softmax kernel of the harmony. -/
noncomputable def condMaxEnt : Kernel X Y :=
  Kernel.softmax fun x y ↦ ((harmony T w (x, y) : ℝ) : EReal)

@[simp] theorem condMaxEnt_apply (x : X) : condMaxEnt T w x = maxEnt (fun y ↦ T (x, y)) w := by
  rcases isEmpty_or_nonempty Y with h | h
  · rw [Measure.eq_zero_of_isEmpty (condMaxEnt T w x), Measure.eq_zero_of_isEmpty (maxEnt _ w)]
  · exact Kernel.softmax_coe_eq_count_tilted _ x

variable [Nonempty Y]

instance : IsMarkovKernel (condMaxEnt T w) :=
  ⟨fun x ↦ by rw [condMaxEnt_apply]; infer_instance⟩

end Conditional

end HarmonicGrammar
