/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.BranchingProcess.GaltonWatson
public import Linglib.Core.Probability.SequenceModel.Tight

/-!
# An autoregressive sequence model as a branching process

A model is a Galton–Watson process whose types are the prefixes: a prefix has no offspring when
the string ends after it, and otherwise one, the prefix extended by the next symbol
(`galtonWatson`). Its family tree is a path, finite exactly when the string ends, so the model is
tight exactly when the process dies out (`isTight_iff_extinctionProb`), which is how a
probabilistic context-free grammar is tight.

## References

* [du-etal-2023]
* [neveu-1986]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace AutoregressiveSequenceModel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  (M : AutoregressiveSequenceModel α)

/-- The model as a Galton–Watson process on prefixes: a prefix has no offspring with the
probability of ending after it, and the prefix extended by `a` with the probability of `a`. -/
noncomputable def galtonWatson : Kernel (List α) (List (List α)) :=
  ⟨fun c ↦ (M.next c).map fun o ↦ o.toList.map (c ++ [·]), .of_discrete⟩

theorem lintegral_galtonWatson (c : List α) (F : List (List α) → ℝ≥0∞) :
    ∫⁻ js, F js ∂M.galtonWatson c =
      M.next c {none} * F [] + ∑' a, M.next c {some a} * F [c ++ [a]] := by
  change ∫⁻ js, F js ∂(M.next c).map _ = _
  rw [lintegral_map .of_discrete (measurable_of_countable _), lintegral_option]
  simp [mul_comm]

instance : IsMarkovKernel M.galtonWatson :=
  ⟨fun c ↦ by change IsProbabilityMeasure ((M.next c).map _); infer_instance⟩

/-- The probability that the family tree is complete within `n` generations is the probability
of a string shorter than `n`. -/
theorem extinctWithin_galtonWatson (n : ℕ) (c : List α) :
    GaltonWatson.extinctWithin M.galtonWatson n c = ∑ k ∈ range n, (M.after c).stopProb k := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [GaltonWatson.extinctWithin_succ _ fun _ ↦ prob_le_one, lintegral_galtonWatson]
    simp only [List.map_nil, List.prod_nil, List.map_cons, List.prod_cons, mul_one, ih]
    rw [sum_range_succ', stopProb_zero, next_after, List.append_nil, add_comm]
    congr 1
    simp_rw [stopProb_succ, next_after, List.append_nil, after_after, mul_sum]
    exact Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable

/-- The extinction probability of the process at a prefix is the total probability of the strings
of the model after it. -/
theorem extinctionProb_galtonWatson (c : List α) :
    GaltonWatson.extinctionProb M.galtonWatson c = ∑' z, (M.after c).stringProb z := by
  rw [GaltonWatson.extinctionProb_eq_iSup, tsum_stringProb, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n ↦ M.extinctWithin_galtonWatson n c

/-- A model is tight exactly when its branching process dies out almost surely. -/
theorem isTight_iff_extinctionProb :
    M.IsTight ↔ GaltonWatson.extinctionProb M.galtonWatson [] = 1 := by
  rw [extinctionProb_galtonWatson, after_nil, IsTight]

end AutoregressiveSequenceModel
