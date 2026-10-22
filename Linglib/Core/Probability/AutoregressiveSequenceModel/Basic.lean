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
over the next symbol or the end of the string, `none` [du-etal-2023]. The prefix probability of a
string is the product of the conditional probabilities along it, the probability of the string
itself multiplies in the probability of ending after it, and the model is tight when the string
probabilities sum to one. Conversely, a language model, a probability measure on strings, gives
after each prefix the law of its continuation, and it is the string law of the model whose
conditionals are the laws of the first symbol of the continuation.

## Main definitions

* `MeasureTheory.Measure.continuation`: the law of what follows a prefix under a measure on
  strings.
* `AutoregressiveSequenceModel α`: a Markov kernel from prefixes to `Option α`.
* `condPrefixProb`, `prefixProb`, `stringProb`, `stringMeasure`, `IsTight`.
* `after`: the model after a context.
* `ofMeasure`: the model whose conditionals are the first symbols of the continuations of a
  measure on strings.

## Main results

* `MeasureTheory.Measure.continuation_setOf_prefix`: the continuations beginning with `w` have
  the conditional probability of the strings extending the prefix by `w`.
* `condPrefixProb_append`, `condPrefixProb_eq_prod`: the chain rule.
* `neg_log_condPrefixProb`: the surprisal of a continuation is the sum of the surprisals of its
  symbols.
* `stringMeasure_eq_of_next_eq`, `stringMeasure_ofMeasure`: a model whose conditionals are the
  next-symbol laws of a language model after every prefix of positive probability has it as its
  string law ([du-etal-2023]).
* `condPrefixProb_ofMeasure`: the conditional prefix probabilities of the model of a language model
  are its conditional probabilities of prefix sets.

## Implementation notes

The alphabet need only carry a measurable space, and the results about string laws a countable one
with measurable singletons; [du-etal-2023] take it finite.

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

end MeasureTheory.Measure

/-- An autoregressive sequence model over the alphabet `α`: after each prefix, a distribution over
the next symbol, or the end of the string, `none`. -/
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

/-- The surprisal of a continuation, the negative log of its conditional prefix probability, is
the sum of the surprisals of its symbols. -/
theorem neg_log_condPrefixProb {c x : List α} (h : M.condPrefixProb c x ≠ 0) :
    -Real.log (M.condPrefixProb c x).toReal =
      ∑ i : Fin x.length, surprisal (M.next (c ++ x.take i)) (some x[i]) := by
  rw [condPrefixProb_eq_prod] at h ⊢
  rw [ENNReal.toReal_prod, Real.log_prod fun i _ ↦ ENNReal.toReal_ne_zero.2
    ⟨Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i), measure_ne_top _ _⟩,
    ← Finset.sum_neg_distrib]
  rfl

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

theorem condPrefixProb_append_left (c c' z : List α) :
    M.condPrefixProb (c ++ c') z = (M.after c).condPrefixProb c' z := by
  induction z generalizing c' with
  | nil => simp
  | cons a z ih => simp [← ih, List.append_assoc]

theorem prefixProb_after (c z : List α) : (M.after c).prefixProb z = M.condPrefixProb c z := by
  rw [prefixProb, ← condPrefixProb_append_left, List.append_nil]

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
  let e : List α ≃ ({y | x <+: y} : Set (List α)) :=
    { toFun z := ⟨x ++ z, List.prefix_append x z⟩
      invFun y := y.1.drop x.length
      left_inv z := by simp
      right_inv y := Subtype.ext (List.prefix_iff_eq_append.1 y.2) }
  rw [stringMeasure, Measure.sum_apply _ .of_discrete, ← ENNReal.tsum_mul_left]
  have hind (y : List α) : (M.stringProb y • Measure.dirac y) {y | x <+: y} =
      {y | x <+: y}.indicator M.stringProb y := by
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_apply]
  rw [tsum_congr hind, ← _root_.tsum_subtype, ← e.tsum_eq]
  exact tsum_congr fun z ↦ M.stringProb_append x z

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
    rw [h x h0, next_ofMeasure_apply_some, cond_apply_of_subset .of_discrete hsub,
      ENNReal.mul_div_cancel h0 (measure_ne_top _ _)]

variable (μ) in
theorem prefixProb_ofMeasure (x : List α) : (ofMeasure μ).prefixProb x = μ {y | x <+: y} :=
  prefixProb_eq_of_next_eq (fun _ _ ↦ rfl) x

/-- After a prefix of positive probability, the model of a probability measure on strings
continues with `x` with the conditional probability of the strings extending the prefix by
`x`. -/
theorem condPrefixProb_ofMeasure {c : List α} (hc : μ {y | c <+: y} ≠ 0) (x : List α) :
    (ofMeasure μ).condPrefixProb c x = μ[{y | c ++ x <+: y} | {y | c <+: y}] := by
  have h := (ofMeasure μ).prefixProb_append c x
  rw [prefixProb_after, prefixProb_ofMeasure, prefixProb_ofMeasure] at h
  have hsub : {y | c ++ x <+: y} ⊆ {y | c <+: y} := fun y ↦ (List.prefix_append c x).trans
  rw [cond_apply_of_subset .of_discrete hsub]
  exact (ENNReal.eq_div_iff hc (measure_ne_top _ _)).2 h.symm

variable [Countable α]

/-- A model whose conditionals are the next-symbol laws of a probability measure on strings after
every prefix of positive probability has the measure as its string law ([du-etal-2023],
footnote 4). -/
theorem stringMeasure_eq_of_next_eq {M : AutoregressiveSequenceModel α}
    (h : ∀ x, μ {y | x <+: y} ≠ 0 → M.next x = (ofMeasure μ).next x) : M.stringMeasure = μ := by
  refine Measure.ext_of_singleton fun x ↦ ?_
  have hsub : {x} ⊆ {y | x <+: y} := Set.singleton_subset_iff.2 (List.prefix_refl x)
  rw [stringMeasure_singleton, stringProb, prefixProb_eq_of_next_eq h]
  rcases eq_or_ne (μ {y | x <+: y}) 0 with h0 | h0
  · rw [h0, zero_mul, measure_mono_null hsub h0]
  rw [h x h0, next_ofMeasure_apply_none μ h0, cond_apply_of_subset .of_discrete hsub,
    ENNReal.mul_div_cancel h0 (measure_ne_top _ _)]

variable (μ) in
theorem stringMeasure_ofMeasure : (ofMeasure μ).stringMeasure = μ :=
  stringMeasure_eq_of_next_eq fun _ _ ↦ rfl

variable (μ) in
theorem isTight_ofMeasure : (ofMeasure μ).IsTight := by
  rw [isTight_iff_isProbabilityMeasure, stringMeasure_ofMeasure]
  infer_instance

end ofMeasure

end AutoregressiveSequenceModel
