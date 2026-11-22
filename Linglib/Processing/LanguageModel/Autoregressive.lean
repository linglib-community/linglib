/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.Probability.Kernel.Continuation
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Autoregressive sequence models

An autoregressive sequence model over an alphabet `α` gives, after every prefix, a distribution
over the next symbol or the end of the string, `none` [du-etal-2023]. The probability that a
string begins with a prefix is the product of the conditional probabilities along it
(`condPrefixProb_eq_prod`), the probability of the string itself multiplies in the probability of
ending after it, and the model is tight when the string probabilities sum to one. Prefixes act on
a model by starting it after the prefix (`after_after`).

## Main definitions

* `AutoregressiveSequenceModel α`: a Markov kernel from prefixes to the next symbol or the end.
* `condPrefixProb`, `prefixProb`, `stringProb`: the probability that the continuation of a context
  begins with a string, that a string begins with a prefix, and of a string itself.
* `stringMeasure`: the law of the generated string.
* `IsTight`: the string probabilities sum to one.
* `after`: the model after a context.

## Implementation notes

The alphabet need only carry a measurable space; [du-etal-2023] take it finite. The surprisal of a
string counts the end of the string, so that it is the negative logarithm of the probability of
the string (`surprisal_stringMeasure`) rather than of its prefix probability.

## References

* [du-etal-2023]
-/

@[expose] public section

open InformationTheory MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- An autoregressive sequence model over the alphabet `α`: after each prefix, a distribution over
the next symbol, or the end of the string, `none`. -/
@[ext]
structure AutoregressiveSequenceModel (α : Type*) [MeasurableSpace α] where
  /-- The distribution of what follows a prefix. -/
  next : Kernel (List α) (Option α)
  [isMarkovKernel_next : IsMarkovKernel next]

namespace AutoregressiveSequenceModel

attribute [instance] isMarkovKernel_next

variable {α : Type*} [MeasurableSpace α] (M : AutoregressiveSequenceModel α)

/-! ### Prefix and string probabilities -/

/-- The probability that the continuation of the context `c` begins with `x`: the product of the
conditional probabilities along `x`. -/
noncomputable def condPrefixProb : List α → List α → ℝ≥0∞
  | _, [] => 1
  | c, a :: x => M.next c {some a} * condPrefixProb (c ++ [a]) x

@[simp] theorem condPrefixProb_nil (c : List α) : M.condPrefixProb c [] = 1 := rfl

@[simp] theorem condPrefixProb_cons (c : List α) (a : α) (x : List α) :
    M.condPrefixProb c (a :: x) = M.next c {some a} * M.condPrefixProb (c ++ [a]) x := rfl

theorem toReal_condPrefixProb_cons (c : List α) (a : α) (x : List α) :
    (M.condPrefixProb c (a :: x)).toReal =
      (M.next c).real {some a} * (M.condPrefixProb (c ++ [a]) x).toReal := by
  rw [condPrefixProb_cons, ENNReal.toReal_mul, measureReal_def]

/-- A property of contexts that each symbol of positive conditional probability preserves holds
after every continuation of positive conditional probability. -/
theorem induction_of_condPrefixProb_ne_zero {P : List α → Prop}
    (step : ∀ c a, P c → M.next c {some a} ≠ 0 → P (c ++ [a])) {c x : List α} (hc : P c)
    (h : M.condPrefixProb c x ≠ 0) : P (c ++ x) := by
  induction x generalizing c with
  | nil => simpa using hc
  | cons a x ih =>
    rw [condPrefixProb_cons] at h
    simpa using ih (step c a hc (left_ne_zero_of_mul h)) (right_ne_zero_of_mul h)

/-- The chain rule: a continuation begins with `x ++ y` when it begins with `x` and the
continuation of `c ++ x` begins with `y`. -/
theorem condPrefixProb_append (c x y : List α) :
    M.condPrefixProb c (x ++ y) = M.condPrefixProb c x * M.condPrefixProb (c ++ x) y := by
  induction x generalizing c with
  | nil => simp
  | cons a x ih => simp [ih, mul_assoc]

/-- The conditional prefix probability is the product of the conditional probabilities of the
symbols along the continuation. -/
theorem condPrefixProb_eq_prod (c x : List α) :
    M.condPrefixProb c x = ∏ i : Fin x.length, M.next (c ++ x.take i) {some x[i]} := by
  induction x generalizing c with
  | nil => simp
  | cons a x ih => simp [ih, Fin.prod_univ_succ]

/-- The surprisal of a continuation of positive probability, the negative log of its conditional
prefix probability, is the sum of the surprisals of its symbols. -/
theorem neg_log_condPrefixProb {c x : List α} (h : M.condPrefixProb c x ≠ 0) :
    -Real.log (M.condPrefixProb c x).toReal =
      ∑ i : Fin x.length, (surprisal (M.next (c ++ x.take i)) (some x[i])).toReal := by
  rw [condPrefixProb_eq_prod] at h ⊢
  rw [ENNReal.toReal_prod, Real.log_prod fun i _ ↦ ENNReal.toReal_ne_zero.2
    ⟨Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i), measure_ne_top _ _⟩,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ (toReal_surprisal prob_le_one).symm

/-- The prefix probability of `x`: the probability that a generated string begins with `x`. -/
noncomputable def prefixProb (x : List α) : ℝ≥0∞ := M.condPrefixProb [] x

@[simp] theorem prefixProb_nil : M.prefixProb [] = 1 := rfl

theorem prefixProb_concat (x : List α) (a : α) :
    M.prefixProb (x ++ [a]) = M.prefixProb x * M.next x {some a} := by
  simp [prefixProb, condPrefixProb_append]

/-- The probability of generating exactly `x`: its prefix probability times the probability of
ending after it. -/
noncomputable def stringProb (x : List α) : ℝ≥0∞ := M.prefixProb x * M.next x {none}

/-- The law of the generated string, carried by the finite strings. -/
noncomputable def stringMeasure : Measure (List α) :=
  Measure.sum fun x ↦ M.stringProb x • Measure.dirac x

@[simp] theorem stringMeasure_singleton (x : List α) : M.stringMeasure {x} = M.stringProb x :=
  Measure.sum_smul_dirac_singleton

theorem stringMeasure_real_singleton (x : List α) :
    M.stringMeasure.real {x} = (M.prefixProb x).toReal * (M.next x).real {none} := by
  rw [measureReal_def, stringMeasure_singleton, stringProb, ENNReal.toReal_mul, measureReal_def]

theorem stringMeasure_univ : M.stringMeasure Set.univ = ∑' x, M.stringProb x := by
  simp [stringMeasure, Measure.sum_apply _ MeasurableSet.univ]

/-- An integral against the law of the string is a sum weighted by the string probabilities. -/
theorem lintegral_stringMeasure (f : List α → ℝ≥0∞) :
    ∫⁻ x, f x ∂M.stringMeasure = ∑' x, M.stringProb x * f x := by
  simp [stringMeasure, lintegral_sum_measure, lintegral_smul_measure]

/-- A model is tight when its string probabilities sum to one: no mass leaks to sequences that
never end. -/
def IsTight : Prop := ∑' x, M.stringProb x = 1

theorem isTight_iff_isProbabilityMeasure : M.IsTight ↔ IsProbabilityMeasure M.stringMeasure :=
  ⟨fun h ↦ ⟨by rw [stringMeasure_univ, h]⟩, fun h ↦ by
    rw [IsTight, ← stringMeasure_univ, measure_univ]⟩

/-! ### Continuations -/

/-- The model after the context `c`: after each prefix `u` it continues as the model does after
`c ++ u`. -/
noncomputable def after (c : List α) : AutoregressiveSequenceModel α where
  next := M.next.comap (c ++ ·) .of_discrete

@[simp] theorem next_after (c u : List α) : (M.after c).next u = M.next (c ++ u) := rfl

@[simp] theorem after_nil : M.after [] = M :=
  AutoregressiveSequenceModel.ext (Kernel.ext fun u ↦ by simp)

/-- The model after `c` and then after `c'` is the model after `c ++ c'`. -/
@[simp] theorem after_after (c c' : List α) : (M.after c).after c' = M.after (c ++ c') :=
  AutoregressiveSequenceModel.ext (Kernel.ext fun u ↦ by simp [List.append_assoc])

@[simp] theorem condPrefixProb_after (c c' z : List α) :
    (M.after c).condPrefixProb c' z = M.condPrefixProb (c ++ c') z := by
  induction z generalizing c' with
  | nil => simp
  | cons a z ih => simp [ih, List.append_assoc]

theorem prefixProb_after (c z : List α) : (M.after c).prefixProb z = M.condPrefixProb c z := by
  rw [prefixProb, condPrefixProb_after, List.append_nil]

theorem prefixProb_append (x z : List α) :
    M.prefixProb (x ++ z) = M.prefixProb x * (M.after x).prefixProb z := by
  rw [prefixProb, condPrefixProb_append, prefixProb_after, List.nil_append]
  rfl

theorem stringProb_append (x z : List α) :
    M.stringProb (x ++ z) = M.prefixProb x * (M.after x).stringProb z := by
  rw [stringProb, stringProb, prefixProb_append, next_after, mul_assoc]

theorem stringProb_cons (a : α) (x : List α) :
    M.stringProb (a :: x) = M.next [] {some a} * (M.after [a]).stringProb x := by
  simpa [prefixProb] using M.stringProb_append [a] x

theorem condPrefixProb_le_one (c x : List α) : M.condPrefixProb c x ≤ 1 := by
  induction x generalizing c with
  | nil => simp
  | cons a x ih => exact mul_le_one' prob_le_one (ih _)

theorem prefixProb_ne_top (x : List α) : M.prefixProb x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (M.condPrefixProb_le_one [] x)

/-- The surprisal of a continuation, the negative log of its conditional prefix probability, is
the sum of the surprisals of its symbols. -/
theorem toENNReal_neg_log_condPrefixProb (c x : List α) :
    (-ENNReal.log (M.condPrefixProb c x)).toENNReal =
      ∑ i : Fin x.length, surprisal (M.next (c ++ x.take i)) (some x[i]) := by
  induction x generalizing c with
  | nil => simp
  | cons a x ih =>
    rw [condPrefixProb_cons, ENNReal.toENNReal_neg_log_mul (prob_le_one (μ := M.next c))
      (condPrefixProb_le_one _ _ _), ih]
    simp [Fin.sum_univ_succ, surprisal, List.append_assoc]

/-- The surprisal of a string under the string law is the sum of the surprisals of its symbols and
of the end of the string after it. -/
theorem surprisal_stringMeasure (x : List α) :
    surprisal M.stringMeasure x =
      ∑ i : Fin x.length, surprisal (M.next (x.take i)) (some x[i]) +
        surprisal (M.next x) none := by
  rw [surprisal, stringMeasure_singleton, stringProb, prefixProb,
    ENNReal.toENNReal_neg_log_mul (condPrefixProb_le_one _ _ _) (prob_le_one (μ := M.next x)),
    toENNReal_neg_log_condPrefixProb]
  simp only [List.nil_append]
  rfl

/-- A model whose every continuation has positive probability gives every prefix positive
probability. -/
theorem condPrefixProb_ne_zero (h : ∀ c a, M.next c {some a} ≠ 0) (c x : List α) :
    M.condPrefixProb c x ≠ 0 := by
  induction x generalizing c with
  | nil => simp
  | cons a x ih => exact mul_ne_zero (h c a) (ih _)

/-- The strings extending `x` have total probability the prefix probability of `x` times the
total probability of the model after `x`. -/
theorem stringMeasure_cylinder (x : List α) :
    M.stringMeasure x.cylinder = M.prefixProb x * ∑' z, (M.after x).stringProb z := by
  classical
  have hind (y : List α) : (M.stringProb y • Measure.dirac y) x.cylinder =
      x.cylinder.indicator M.stringProb y := by
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_apply]
  rw [stringMeasure, Measure.sum_apply _ .of_discrete, tsum_congr hind, ← ENNReal.tsum_mul_left,
    ← (List.append_right_injective x).tsum_eq (f := x.cylinder.indicator M.stringProb)
      fun y hy ↦ Set.mem_of_indicator_ne_zero hy]
  exact tsum_congr fun z ↦ (Set.indicator_of_mem (s := x.cylinder) (x.append_mem_cylinder z)
    _).trans (M.stringProb_append x z)

end AutoregressiveSequenceModel
