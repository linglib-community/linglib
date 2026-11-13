/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Autoregressive sequence models

An autoregressive sequence model over an alphabet `α` gives, after every prefix, a distribution
over the next symbol or the end of the string, `none` [du-etal-2023]. The probability that a
string begins with a prefix is [the product](##condPrefixProb_eq_prod) of the conditional
probabilities along it, the probability of the string itself multiplies in the probability of
ending after it, and the model is tight when the string probabilities sum to one. Conversely a
language model, a probability measure on strings, has after each prefix the law of its
continuation, and it is [the string law](##stringMeasure_ofMeasure) of the model whose
conditionals are the laws of the first symbol of the continuation. Prefixes act on both sides, on
a measure by [taking continuations](##MeasureTheory.Measure.continuation_continuation) and on a
model by [starting it after the prefix](##after_after), and the passage from measures to models
[carries one action to the other](##ofMeasure_continuation).

## Implementation notes

The alphabet need only carry a measurable space, and the results about string laws a countable one
with measurable singletons; [du-etal-2023] take it finite. The surprisal of a string counts the end
of the string, so that it is the negative logarithm of the probability of the string
(`surprisal_stringMeasure`) rather than of its prefix probability.

## References

* [du-etal-2023]
-/

@[expose] public section

open InformationTheory MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Continuations -/

namespace MeasureTheory.Measure

variable {α : Type*} (μ : Measure (List α))

/-- The continuation law of a measure on strings: after the prefix `c`, the law of what follows
`c` among the strings extending it. -/
noncomputable def continuation : Kernel (List α) (List α) :=
  ⟨fun c ↦ (μ[|{y | c <+: y}]).map (List.drop c.length), .of_discrete⟩

theorem continuation_apply (c : List α) :
    μ.continuation c = (μ[|{y | c <+: y}]).map (List.drop c.length) :=
  rfl

instance (c : List α) : IsZeroOrProbabilityMeasure (μ.continuation c) := by
  rw [continuation_apply]
  infer_instance

theorem isProbabilityMeasure_continuation [IsFiniteMeasure μ] {c : List α}
    (hc : μ {y | c <+: y} ≠ 0) : IsProbabilityMeasure (μ.continuation c) := by
  have := cond_isProbabilityMeasure (s := {y | c <+: y}) hc
  rw [continuation_apply]
  infer_instance

/-- The continuations of `c` beginning with `w` have the conditional probability of the strings
extending `c ++ w` among those extending `c`. -/
theorem continuation_setOf_prefix (c w : List α) :
    μ.continuation c {a | w <+: a} = μ[{y | c ++ w <+: y} | {y | c <+: y}] := by
  rw [continuation_apply, map_apply .of_discrete .of_discrete, cond_apply .of_discrete,
    cond_apply .of_discrete]
  congr 2
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  refine and_congr_right fun ⟨r, hr⟩ ↦ ?_
  subst hr
  simp

/-- The continuation of `c` is empty with the conditional probability of `c` itself. -/
theorem continuation_singleton_nil (c : List α) :
    μ.continuation c {[]} = μ[{c} | {y | c <+: y}] := by
  rw [continuation_apply, map_apply .of_discrete .of_discrete, cond_apply .of_discrete,
    cond_apply .of_discrete]
  congr 2
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    List.drop_eq_nil_iff]
  exact ⟨fun ⟨h, hl⟩ ↦ ⟨h, (h.eq_of_length_le hl).symm⟩, fun ⟨h, hy⟩ ↦ ⟨h, hy ▸ le_rfl⟩⟩

/-- The continuation after `c` and then after `u` is the continuation after `c ++ u`. -/
theorem continuation_continuation [IsFiniteMeasure μ] (c u : List α) :
    (μ.continuation c).continuation u = μ.continuation (c ++ u) := by
  have h : {y | c <+: y} ∩ List.drop c.length ⁻¹' {y | u <+: y} = {y | c ++ u <+: y} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun ⟨⟨r, hr⟩, hu⟩ ↦ ?_, fun ⟨r, hr⟩ ↦ ?_⟩ <;> subst hr
    · simpa using hu
    · simp [List.append_assoc]
  rw [continuation_apply, continuation_apply,
    cond_map (Measurable.of_discrete.aemeasurable) .of_discrete,
    cond_cond_eq_cond_inter .of_discrete .of_discrete, h, map_map .of_discrete .of_discrete,
    continuation_apply, List.length_append]
  congr 1
  ext y : 1
  simp [List.drop_drop]

end MeasureTheory.Measure

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
theorem stringMeasure_setOf_prefix (x : List α) :
    M.stringMeasure {y | x <+: y} = M.prefixProb x * ∑' z, (M.after x).stringProb z := by
  classical
  have hind (y : List α) : (M.stringProb y • Measure.dirac y) {y | x <+: y} =
      {y | x <+: y}.indicator M.stringProb y := by
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_apply]
  rw [stringMeasure, Measure.sum_apply _ .of_discrete, tsum_congr hind, ← ENNReal.tsum_mul_left,
    ← (List.append_right_injective x).tsum_eq (f := {y | x <+: y}.indicator M.stringProb)
      fun y hy ↦ Set.mem_of_indicator_ne_zero hy]
  exact tsum_congr fun z ↦ (Set.indicator_of_mem (s := {y | x <+: y}) (List.prefix_append x z)
    _).trans (M.stringProb_append x z)

/-! ### The model of a language model

After each prefix of positive probability, the first symbol of the continuation of a measure on
strings, `none` where the continuation is empty, has a law, and these laws form a model. When the
measure is a probability measure, every model that agrees with them after each prefix of positive
probability has the measure as its string law. -/

section ofMeasure

variable (μ : Measure (List α))

open Classical in
/-- The model of a measure on strings: after a prefix of positive finite measure, the law of the
first symbol of its continuation, and the end of the string after any other prefix. -/
noncomputable def ofMeasure : AutoregressiveSequenceModel α where
  next := ⟨fun x ↦ if μ.continuation x = 0 then .dirac none
    else (μ.continuation x).map List.head?, .of_discrete⟩
  isMarkovKernel_next := ⟨fun x ↦ by
    change IsProbabilityMeasure (if _ then _ else _)
    split_ifs with h
    · infer_instance
    · have := (eq_zero_or_isProbabilityMeasure (μ.continuation x)).resolve_left h
      infer_instance⟩

open Classical in
private theorem next_ofMeasure (x : List α) :
    (ofMeasure μ).next x = if μ.continuation x = 0 then .dirac none
      else (μ.continuation x).map List.head? :=
  rfl

theorem next_ofMeasure_of_ne_zero {x : List α} (hx : μ.continuation x ≠ 0) :
    (ofMeasure μ).next x = (μ.continuation x).map List.head? := by
  rw [next_ofMeasure, ite_eq_right hx]

theorem next_ofMeasure_of_eq_zero {x : List α} (hx : μ.continuation x = 0) :
    (ofMeasure μ).next x = .dirac none := by
  rw [next_ofMeasure, ite_eq_left hx]

/-- The model of the continuation of a measure after `c` is the model of the measure after `c`. -/
theorem ofMeasure_continuation [IsFiniteMeasure μ] (c : List α) :
    ofMeasure (μ.continuation c) = (ofMeasure μ).after c :=
  AutoregressiveSequenceModel.ext <| Kernel.ext fun u ↦ by
    rw [next_after, next_ofMeasure, next_ofMeasure, Measure.continuation_continuation]

variable [MeasurableSingletonClass α]

theorem next_ofMeasure_apply_some (x : List α) (a : α) :
    (ofMeasure μ).next x {some a} = μ[{y | x ++ [a] <+: y} | {y | x <+: y}] := by
  rw [← Measure.continuation_setOf_prefix]
  by_cases h : μ.continuation x = 0
  · simp [next_ofMeasure_of_eq_zero μ h, h]
  rw [next_ofMeasure_of_ne_zero μ h, Measure.map_apply .of_discrete (measurableSet_singleton _)]
  congr 1
  ext l
  cases l <;> simp [eq_comm]

theorem next_ofMeasure_apply_none [IsFiniteMeasure μ] {x : List α} (hx : μ {y | x <+: y} ≠ 0) :
    (ofMeasure μ).next x {none} = μ[{x} | {y | x <+: y}] := by
  have := μ.isProbabilityMeasure_continuation hx
  rw [next_ofMeasure_of_ne_zero μ (IsProbabilityMeasure.ne_zero _),
    Measure.map_apply .of_discrete (measurableSet_singleton _),
    ← Measure.continuation_singleton_nil]
  congr 1
  ext l
  cases l <;> simp

variable [IsProbabilityMeasure μ] {μ}

/-- A model whose conditionals are the next-symbol laws of a probability measure on strings after
every prefix of positive probability gives each prefix the measure of the strings extending it. -/
theorem prefixProb_eq_of_next_eq {M : AutoregressiveSequenceModel α}
    (h : ∀ x, μ {y | x <+: y} ≠ 0 → M.next x = (ofMeasure μ).next x) (x : List α) :
    M.prefixProb x = μ {y | x <+: y} := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
    have hsub : {y | x ++ [a] <+: y} ⊆ {y | x <+: y} := fun y ↦ (List.prefix_append x [a]).trans
    rw [prefixProb_concat, ih]
    rcases eq_or_ne (μ {y | x <+: y}) 0 with h0 | h0
    · rw [h0, zero_mul, measure_mono_null hsub h0]
    rw [h x h0, next_ofMeasure_apply_some, mul_comm, cond_mul_eq_inter .of_discrete,
      Set.inter_eq_right.2 hsub]

variable (μ) in
theorem prefixProb_ofMeasure (x : List α) : (ofMeasure μ).prefixProb x = μ {y | x <+: y} :=
  prefixProb_eq_of_next_eq (fun _ _ ↦ rfl) x

/-- After a prefix of positive probability, the model of a probability measure on strings
continues with `x` with the conditional probability of the strings extending the prefix by
`x`. -/
theorem condPrefixProb_ofMeasure {c : List α} (hc : μ {y | c <+: y} ≠ 0) (x : List α) :
    (ofMeasure μ).condPrefixProb c x = μ[{y | c ++ x <+: y} | {y | c <+: y}] := by
  have := μ.isProbabilityMeasure_continuation hc
  rw [← prefixProb_after, ← ofMeasure_continuation, prefixProb_ofMeasure,
    Measure.continuation_setOf_prefix]

variable [Countable α]

/-- A model whose conditionals are the next-symbol laws of a string measure at every
positive-probability prefix has that measure as its string law ([du-etal-2023], footnote 4). -/
theorem stringMeasure_eq_of_next_eq {M : AutoregressiveSequenceModel α}
    (h : ∀ x, μ {y | x <+: y} ≠ 0 → M.next x = (ofMeasure μ).next x) : M.stringMeasure = μ := by
  refine Measure.ext_of_singleton fun x ↦ ?_
  have hsub : {x} ⊆ {y | x <+: y} := Set.singleton_subset_iff.2 (List.prefix_refl x)
  rw [stringMeasure_singleton, stringProb, prefixProb_eq_of_next_eq h]
  rcases eq_or_ne (μ {y | x <+: y}) 0 with h0 | h0
  · rw [h0, zero_mul, measure_mono_null hsub h0]
  rw [h x h0, next_ofMeasure_apply_none μ h0, mul_comm, cond_mul_eq_inter .of_discrete,
    Set.inter_eq_right.2 hsub]

variable (μ) in
theorem stringMeasure_ofMeasure : (ofMeasure μ).stringMeasure = μ :=
  stringMeasure_eq_of_next_eq fun _ _ ↦ rfl

/-- After a prefix of positive probability, the model of a language model generates the
continuation of the prefix. -/
theorem stringMeasure_after_ofMeasure {c : List α} (hc : μ {y | c <+: y} ≠ 0) :
    ((ofMeasure μ).after c).stringMeasure = μ.continuation c := by
  have := μ.isProbabilityMeasure_continuation hc
  rw [← ofMeasure_continuation, stringMeasure_ofMeasure]

variable (μ) in
theorem isTight_ofMeasure : (ofMeasure μ).IsTight := by
  rw [isTight_iff_isProbabilityMeasure, stringMeasure_ofMeasure]
  infer_instance

variable (μ) in
theorem stringProb_ofMeasure (x : List α) : (ofMeasure μ).stringProb x = μ {x} := by
  rw [← stringMeasure_singleton, stringMeasure_ofMeasure]

variable (μ) in
/-- The surprisal of a string under a language is the sum of the surprisals of its symbols and of
the end of the string under the model of the language. -/
theorem surprisal_eq_sum_surprisal_next (x : List α) :
    surprisal μ x = ∑ i : Fin x.length, surprisal ((ofMeasure μ).next (x.take i)) (some x[i]) +
      surprisal ((ofMeasure μ).next x) none := by
  rw [← surprisal_stringMeasure, stringMeasure_ofMeasure]

end ofMeasure

end AutoregressiveSequenceModel
