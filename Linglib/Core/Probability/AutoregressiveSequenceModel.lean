/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecificLimits.ProdOneSub
public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.MeasureTheory.Constructions.Option
public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Mathlib.Data.List.ReduceOption
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Autoregressive sequence models

An autoregressive sequence model over an alphabet `α` gives, after every prefix, a distribution
over the next symbol or the end of the string, `none` [du-etal-2023]. The prefix probability of a
string is the product of the conditional probabilities along it, and the probability of the
string itself multiplies in the probability of ending after it. The string probabilities need not
sum to one: the remaining mass leaks to sequences that never end. A model is tight when they do.
Conversely, a language model, a probability measure on strings, is the string law of the model
whose conditionals are its next-symbol laws, and a tight model's conditionals are the next-symbol
laws of its own string law.

Tightness is a statement about survival, the probability that no end symbol appears in the first
`n` steps. The probabilities of the strings shorter than `n` and the survival at `n` sum to one,
so a model is tight exactly when survival tends to zero. Survival is the product of one minus the
end probability at each step given survival to it, so a model is tight exactly when that
conditional end probability reaches one or has a divergent sum; an end probability bounded below
by a divergent series suffices.

The model is a prediction rule on the extended alphabet, the end of the string absorbing, and
the Ionescu–Tulcea theorem gives the law of its whole trajectory, a probability measure on
infinite sequences of units or ends. Survival is the probability that none of the first `n`
units is the end, a string's probability is that of the trajectories that spell it and then end,
and the model is tight exactly when the trajectory ends almost surely, which is how
[du-etal-2023] define tightness.

## Main definitions

* `AutoregressiveSequenceModel α`: a Markov kernel from prefixes to `Option α`.
* `condPrefixProb`, `prefixProb`, `stringProb`, `stringMeasure`.
* `IsTight`: the string probabilities sum to one.
* `survival`, `stopProb`, `eosHazard`.
* `after`: the model after a context.
* `ofMeasure`: the model of the next-symbol laws of a measure on strings.
* `rule`, `trajectory`: the model as a prediction rule on the extended alphabet, and the law of
  its whole trajectory.

## Main results

* `condPrefixProb_append`: the chain rule for prefix probabilities.
* `sum_range_stopProb_add_survival`, `isTight_iff_tendsto_survival`.
* `survival_eq_prod`: survival is a product over the conditional end probabilities.
* `isTight_iff`: tight exactly when the conditional end probability reaches one or has a
  divergent sum ([du-etal-2023], Theorem 4.7).
* `isTight_of_le_next_none`: a divergent lower bound on the end probability gives tightness
  ([du-etal-2023], Proposition 4.3).
* `survival_le_pow`: a constant lower bound makes survival decay geometrically.
* `isTight_iff_of_next_none_eq`: the criterion when the end probability depends only on length.
* `stringMeasure_setOf_length_le`, `IsTight.stringMeasure_setOf_length_le`: survival is at
  least, and in a tight model exactly, the probability of a string of at least that length.
* `lintegral_length_le`, `IsTight.lintegral_length`, `lintegral_length_le_div`: the expected
  length is at most, and in a tight model exactly, the total survival after the first step, and
  at most `(1 - c) / c` under an end probability of at least `c`.
* `IsTight.tsum_prefixProb`: in a tight model the prefix probabilities sum to the expected
  length plus one ([opedal-chodroff-cotterell-wilcox-2024]).
* `stringMeasure_eq_of_next_eq`, `stringMeasure_ofMeasure`: a model whose conditionals are the
  next-symbol laws of a language model after every prefix of positive probability has that
  language model as its string law ([du-etal-2023]).
* `IsTight.next_ofMeasure_stringMeasure`: a tight model's conditionals are the next-symbol laws of
  its string law.
* `trajectory_setOf_forall_lt_ne_none`, `trajectory_cylinder`: survival and string probabilities
  as probabilities of the trajectory.
* `isTight_iff_trajectory_setOf_forall_ne_none`: tight exactly when the trajectory ends almost
  surely ([du-etal-2023]'s definition).
* `stringProb_append`, `IsTight.after`, `IsTight.stringMeasure_setOf_prefix`: a string's
  probability factors through the model after its prefix, which inherits tightness, so in a tight
  model the strings extending a prefix have total probability its prefix probability.

## Implementation notes

* The alphabet need only be countable with measurable singletons; [du-etal-2023] take it finite.
* The product criterion behind `isTight_iff` is `ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff`,
  [du-etal-2023]'s Corollary 4.6 extended to factors that may vanish.
* [du-etal-2023] count steps from one, so their conditional end probability at step `t` is
  `eosHazard (t - 1)`. Where survival is zero the ratio is `0` by the convention of `ℝ≥0∞`
  division; the characterization is unaffected, since survival first reaching zero forces a
  conditional end probability of one.
* [du-etal-2023] define tightness as zero mass on the infinite sequences under the trajectory
  measure; `IsTight` is the equivalent condition that the string probabilities sum to one, and
  `isTight_iff_trajectory_setOf_forall_ne_none` is the equivalence.

## References

* [du-etal-2023]
* [opedal-chodroff-cotterell-wilcox-2024]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Preorder Topology
open scoped ENNReal

/-- An autoregressive sequence model over the alphabet `α`: after each prefix, a distribution over
the next symbol, or the end of the string, `none`. -/
structure AutoregressiveSequenceModel (α : Type*) [MeasurableSpace α] where
  /-- The distribution of what follows a prefix. -/
  next : Kernel (List α) (Option α)
  [isMarkovKernel_next : IsMarkovKernel next]

namespace AutoregressiveSequenceModel

private theorem reduceOption_map_some {α : Type*} (l : List α) :
    (l.map some).reduceOption = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

/-- A list extends `x ++ [a]` exactly when it extends `x` and has `a` right after it. -/
private theorem append_singleton_prefix_iff {α : Type*} {x y : List α} {a : α} :
    x ++ [a] <+: y ↔ x <+: y ∧ y[x.length]? = some a := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(List.prefix_append x [a]).trans (List.prefix_append _ r), by simp⟩
  · rintro ⟨⟨r, rfl⟩, h⟩
    cases r with
    | nil => simp at h
    | cons b r => simp at h; subst h; exact ⟨r, by simp⟩

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

A measure on strings gives, after each prefix of positive probability, the law of the next symbol
among the strings extending the prefix, with `none` where the prefix ends them. These laws form a
model. When the measure is a probability measure, every model that agrees with them after each
prefix of positive probability has the measure as its string law. -/

section ofMeasure

variable (μ : Measure (List α))

open Classical in
/-- The model of a measure on strings: after a prefix of positive finite measure, the law of the
symbol after it among the strings extending it, and the end of the string after any other
prefix. -/
noncomputable def ofMeasure : AutoregressiveSequenceModel α where
  next := ⟨fun x ↦ if μ[|{y | x <+: y}] = 0 then .dirac none
    else (μ[|{y | x <+: y}]).map (·[x.length]?), .of_discrete⟩
  isMarkovKernel_next := ⟨fun x ↦ by
    change IsProbabilityMeasure (if _ then _ else _)
    split_ifs with h
    · infer_instance
    · have := (eq_zero_or_isProbabilityMeasure (μ[|{y | x <+: y}])).resolve_left h
      infer_instance⟩

open Classical in
private theorem next_ofMeasure (x : List α) :
    (ofMeasure μ).next x = if μ[|{y | x <+: y}] = 0 then .dirac none
      else (μ[|{y | x <+: y}]).map (·[x.length]?) :=
  rfl

theorem next_ofMeasure_of_ne_zero {x : List α} (hx : μ[|{y | x <+: y}] ≠ 0) :
    (ofMeasure μ).next x = (μ[|{y | x <+: y}]).map (·[x.length]?) := by
  rw [next_ofMeasure, ite_eq_right hx]

theorem next_ofMeasure_of_eq_zero {x : List α} (hx : μ[|{y | x <+: y}] = 0) :
    (ofMeasure μ).next x = .dirac none := by
  rw [next_ofMeasure, ite_eq_left hx]

variable [MeasurableSingletonClass α]

theorem next_ofMeasure_apply_some (x : List α) (a : α) :
    (ofMeasure μ).next x {some a} = μ[{y | x ++ [a] <+: y} | {y | x <+: y}] := by
  by_cases h : μ[|{y | x <+: y}] = 0
  · simp [next_ofMeasure_of_eq_zero μ h, h]
  rw [next_ofMeasure_of_ne_zero μ h, Measure.map_apply .of_discrete (measurableSet_singleton _),
    cond_apply .of_discrete, cond_apply .of_discrete]
  congr 2
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    append_singleton_prefix_iff]
  exact ⟨fun h ↦ ⟨h.1, h⟩, fun h ↦ h.2⟩

theorem next_ofMeasure_apply_none [IsFiniteMeasure μ] {x : List α} (hx : μ {y | x <+: y} ≠ 0) :
    (ofMeasure μ).next x {none} = μ[{x} | {y | x <+: y}] := by
  rw [next_ofMeasure_of_ne_zero μ (by simp [hx, measure_ne_top]),
    Measure.map_apply .of_discrete (measurableSet_singleton _), cond_apply .of_discrete,
    cond_apply .of_discrete]
  congr 2
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    List.getElem?_eq_none_iff]
  exact ⟨fun ⟨h, hl⟩ ↦ ⟨h, (h.eq_of_length_le hl).symm⟩, fun ⟨h, hy⟩ ↦ ⟨h, hy ▸ le_rfl⟩⟩

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

/-! ### Survival -/

/-- The probability that no end symbol appears in the first `n` steps: the total prefix
probability of the strings of length `n`. -/
noncomputable def survival (n : ℕ) : ℝ≥0∞ := ∑' x : {x : List α // x.length = n}, M.prefixProb x

/-- The probability of generating a string of length `n`. -/
noncomputable def stopProb (n : ℕ) : ℝ≥0∞ := ∑' x : {x : List α // x.length = n}, M.stringProb x

/-- The probability of ending after `n` symbols given survival to that point, the end
probability at step `n + 1` of [du-etal-2023]. -/
noncomputable def eosHazard (n : ℕ) : ℝ≥0∞ := M.stopProb n / M.survival n

@[simp] theorem survival_zero : M.survival 0 = 1 := by
  rw [survival, tsum_eq_single (⟨[], rfl⟩ : {x : List α // x.length = 0}) fun x hx ↦
    absurd (Subtype.ext (List.eq_nil_of_length_eq_zero x.2)) hx]
  rfl

theorem tsum_stringProb : ∑' x, M.stringProb x = ∑' n, M.stopProb n := by
  rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma']
  rfl

/-- Strings of length `n + 1` are the strings of length `n` followed by a symbol. -/
private def concatEquiv (n : ℕ) :
    {x : List α // x.length = n} × α ≃ {y : List α // y.length = n + 1} where
  toFun p := ⟨p.1.1 ++ [p.2], by simp [p.1.2]⟩
  invFun y := (⟨y.1.dropLast, by simp [y.2]⟩, y.1.getLast (List.ne_nil_of_length_eq_add_one y.2))
  left_inv p := by ext <;> simp
  right_inv y := Subtype.ext (List.dropLast_append_getLast _)

/-- The strings of length `n` end with probability at least `c` times survival to `n` when every
prefix of length `n` ends with probability at least `c`. -/
theorem mul_survival_le_stopProb {n : ℕ} {c : ℝ≥0∞}
    (hc : ∀ x : List α, x.length = n → c ≤ M.next x {none}) :
    c * M.survival n ≤ M.stopProb n := by
  rw [survival, ← ENNReal.tsum_mul_left, stopProb]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [stringProb, mul_comm c]
  gcongr
  exact hc x x.2

/-- Surviving `n` steps after `x` is surviving `n + |x|` steps through `x`. -/
theorem prefixProb_mul_survival_after_le (x : List α) (n : ℕ) :
    M.prefixProb x * (M.after x).survival n ≤ M.survival (n + x.length) := by
  calc M.prefixProb x * (M.after x).survival n
      = ∑' z : {z : List α // z.length = n}, M.prefixProb (x ++ z.1) := by
        rw [survival, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun z ↦ (M.prefixProb_append x z).symm
    _ ≤ M.survival (n + x.length) :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun z ↦
          (⟨x ++ z.1, by simp [z.2, add_comm]⟩ : {y : List α // y.length = n + x.length}))
        (fun z z' h ↦ Subtype.ext (List.append_cancel_left (congrArg Subtype.val h)))
        fun y ↦ M.prefixProb y.1

variable [MeasurableSingletonClass α]

theorem measurableSet_setOf_forall_lt_ne_none (n : ℕ) :
    MeasurableSet {ω : ℕ → Option α | ∀ i < n, ω i ≠ none} := by
  have hi (i : ℕ) : MeasurableSet {ω : ℕ → Option α | ω i ≠ none} :=
    (measurableSet_singleton (none : Option α)).compl.preimage (measurable_pi_apply i)
  simp_rw [Set.ofPred_forall]
  exact .iInter fun i ↦ .iInter fun _ ↦ hi i

variable [Countable α]

/-- After any prefix the model either ends or continues with some symbol. -/
theorem next_none_add_tsum_next_some (x : List α) :
    M.next x {none} + ∑' a, M.next x {some a} = 1 := by
  have hU : ({none} : Set (Option α))ᶜ = ⋃ a, {some a} := by ext o; cases o <;> simp
  rw [← measure_iUnion (fun a b hab ↦ Set.disjoint_singleton.2 ((Option.some_injective α).ne hab))
    fun a ↦ measurableSet_singleton _, ← hU, measure_add_measure_compl (measurableSet_singleton _),
    measure_univ]

theorem survival_succ_add_stopProb (n : ℕ) : M.survival (n + 1) + M.stopProb n = M.survival n := by
  rw [survival, ← (concatEquiv n).tsum_eq, ENNReal.tsum_prod', stopProb, survival,
    ← ENNReal.tsum_add]
  refine tsum_congr fun x ↦ ?_
  simp only [concatEquiv, Equiv.coe_fn_mk, prefixProb_concat, ENNReal.tsum_mul_left, stringProb,
    ← mul_add, add_comm (∑' a, _), next_none_add_tsum_next_some, mul_one]

theorem sum_range_stopProb_add_survival (n : ℕ) :
    ∑ k ∈ range n, M.stopProb k + M.survival n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_assoc, add_comm (M.stopProb n),
      survival_succ_add_stopProb, ih]

theorem survival_le_one (n : ℕ) : M.survival n ≤ 1 :=
  (M.sum_range_stopProb_add_survival n).le.trans' le_add_self

theorem survival_ne_top (n : ℕ) : M.survival n ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (M.survival_le_one n)

theorem stopProb_le_survival (n : ℕ) : M.stopProb n ≤ M.survival n :=
  (M.survival_succ_add_stopProb n).le.trans' le_add_self

theorem survival_antitone : Antitone M.survival :=
  antitone_nat_of_succ_le fun n ↦ (M.survival_succ_add_stopProb n).le.trans' le_self_add

theorem isTight_iff_tendsto_survival : M.IsTight ↔ Tendsto M.survival atTop (𝓝 0) := by
  have hsum (n : ℕ) : ∑ k ∈ range n, M.stopProb k = 1 - M.survival n :=
    ENNReal.eq_sub_of_add_eq (M.survival_ne_top n) (M.sum_range_stopProb_add_survival n)
  have hinf : ⨅ n, M.survival n ≤ 1 := (iInf_le _ 0).trans (M.survival_le_one 0)
  rw [IsTight, tsum_stringProb, ENNReal.tsum_eq_iSup_nat, iSup_congr hsum, ← ENNReal.sub_iInf]
  constructor
  · intro h
    have h0 : ⨅ n, M.survival n = 0 := by
      rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top hinf, h, tsub_self]
    exact h0 ▸ tendsto_atTop_iInf M.survival_antitone
  · intro h
    rw [tendsto_nhds_unique (tendsto_atTop_iInf M.survival_antitone) h, tsub_zero]

/-! ### The conditional end probability -/

theorem eosHazard_le_one (n : ℕ) : M.eosHazard n ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact M.stopProb_le_survival n)

theorem survival_succ (n : ℕ) : M.survival (n + 1) = M.survival n * (1 - M.eosHazard n) := by
  by_cases h : M.survival n = 0
  · rw [h, zero_mul]
    exact nonpos_iff_eq_zero.1 ((M.survival_antitone n.le_succ).trans h.le)
  · rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, eosHazard,
      ENNReal.mul_div_cancel h (M.survival_ne_top n)]
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n)

theorem survival_eq_prod (n : ℕ) : M.survival n = ∏ k ∈ range n, (1 - M.eosHazard k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [survival_succ, ih, prod_range_succ]

/-- A model is tight exactly when the conditional end probability reaches one or has a divergent
sum ([du-etal-2023], Theorem 4.7). -/
theorem isTight_iff : M.IsTight ↔ (∃ n, M.eosHazard n = 1) ∨ ∑' n, M.eosHazard n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext M.survival_eq_prod]
  exact ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff M.eosHazard_le_one

/-- A model whose end probability after every prefix of length `t - 1` is at least `f t`, for a
divergent series of bounds, is tight ([du-etal-2023], Proposition 4.3). -/
theorem isTight_of_le_next_none {f : ℕ → ℝ≥0∞}
    (hf : ∀ x : List α, f (x.length + 1) ≤ M.next x {none}) (h : ∑' t, f (t + 1) = ∞) :
    M.IsTight := by
  by_cases hs : ∃ n, M.survival n = 0
  · obtain ⟨n, hn⟩ := hs
    rw [isTight_iff_tendsto_survival]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun m hm ↦ ?_⟩)
    exact (nonpos_iff_eq_zero.1 ((M.survival_antitone hm).trans hn.le)).symm
  · simp only [not_exists] at hs
    refine M.isTight_iff.2 (.inr (eq_top_mono (ENNReal.tsum_le_tsum fun n ↦ ?_) h))
    rw [eosHazard, ENNReal.le_div_iff_mul_le (.inl (hs n)) (.inl (M.survival_ne_top n))]
    exact M.mul_survival_le_stopProb fun x hx ↦ hx ▸ hf x

/-- When the end probability after a prefix depends only on its length, survival is the product
of one minus it. -/
theorem survival_eq_prod_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (n : ℕ) :
    M.survival n = ∏ k ∈ range n, (1 - e k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop : M.stopProb n = e n * M.survival n := by
      rw [stopProb, survival, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun x ↦ by rw [stringProb, he, x.2, mul_comm]
    rw [prod_range_succ, ← ih, ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n), hstop,
      ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]

/-- When the end probability after a prefix depends only on its length, the model is tight exactly
when that probability reaches one or has a divergent sum. -/
theorem isTight_iff_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (he1 : ∀ n, e n ≤ 1) :
    M.IsTight ↔ (∃ n, e n = 1) ∨ ∑' n, e n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext (M.survival_eq_prod_of_next_none_eq he)]
  exact ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff he1

/-- An end probability of at least `c` after every prefix makes survival decay geometrically. -/
theorem survival_le_pow {c : ℝ≥0∞} (hc : ∀ x : List α, c ≤ M.next x {none}) (n : ℕ) :
    M.survival n ≤ (1 - c) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop := M.mul_survival_le_stopProb (n := n) fun x _ ↦ hc x
    rw [pow_succ, ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n)]
    calc M.survival n - M.stopProb n ≤ M.survival n - c * M.survival n := tsub_le_tsub_left hstop _
      _ = M.survival n * (1 - c) := by
        rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]
      _ ≤ (1 - c) ^ n * (1 - c) := by gcongr

/-- The string probabilities of any model sum to at most one. -/
theorem tsum_stringProb_le_one : ∑' x, M.stringProb x ≤ 1 := by
  rw [tsum_stringProb, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n ↦ le_self_add.trans (M.sum_range_stopProb_add_survival n).le

/-- The model after a prefix of positive probability inherits tightness. -/
theorem IsTight.after {M : AutoregressiveSequenceModel α} (hM : M.IsTight) {x : List α}
    (hx : M.prefixProb x ≠ 0) : (M.after x).IsTight := by
  rw [isTight_iff_tendsto_survival] at hM ⊢
  have hlim : Tendsto (fun n ↦ M.survival (n + x.length) / M.prefixProb x) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const ((tendsto_add_atTop_iff_nat x.length).2 hM) (.inr hx)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
    fun n ↦ ?_
  rw [ENNReal.le_div_iff_mul_le (.inl hx) (.inl (M.prefixProb_ne_top x)), mul_comm]
  exact M.prefixProb_mul_survival_after_le x n

/-- In a tight model the strings extending `x` have total probability its prefix probability. -/
theorem IsTight.stringMeasure_setOf_prefix {M : AutoregressiveSequenceModel α} (hM : M.IsTight)
    (x : List α) : M.stringMeasure {y | x <+: y} = M.prefixProb x := by
  rw [M.stringMeasure_setOf_prefix]
  by_cases hx : M.prefixProb x = 0
  · rw [hx, zero_mul]
  · rw [hM.after hx, mul_one]

/-- A tight model's conditional after a prefix of positive probability is the next-symbol law of
its string law. -/
theorem IsTight.next_ofMeasure_stringMeasure {M : AutoregressiveSequenceModel α} (hM : M.IsTight)
    {x : List α} (hx : M.prefixProb x ≠ 0) : (ofMeasure M.stringMeasure).next x = M.next x := by
  have := M.isTight_iff_isProbabilityMeasure.1 hM
  refine Measure.ext_of_singleton fun o ↦ ?_
  cases o with
  | some a =>
    have hsub : {y | x ++ [a] <+: y} ⊆ {y | x <+: y} := fun y ↦ (List.prefix_append x [a]).trans
    rw [next_ofMeasure_apply_some, cond_apply_of_subset .of_discrete hsub,
      hM.stringMeasure_setOf_prefix, hM.stringMeasure_setOf_prefix, prefixProb_concat,
      mul_comm (M.prefixProb x), ENNReal.mul_div_cancel_right hx (M.prefixProb_ne_top x)]
  | none =>
    have hsub : {x} ⊆ {y | x <+: y} := Set.singleton_subset_iff.2 (List.prefix_refl x)
    rw [next_ofMeasure_apply_none _ (by rwa [hM.stringMeasure_setOf_prefix]),
      cond_apply_of_subset .of_discrete hsub, stringMeasure_singleton,
      hM.stringMeasure_setOf_prefix, stringProb, mul_comm (M.prefixProb x),
      ENNReal.mul_div_cancel_right hx (M.prefixProb_ne_top x)]

/-! ### Expected length

The law of the generated string is a sum of point masses, so an integral against it is a sum
weighted by the string probabilities. Survival to `n` is at least the probability of a string of
length at least `n`, with equality in a tight model, so the tail-sum formula bounds the expected
length by the total survival after the first step. -/

/-- Survival to `n` is at least the probability of a string of length at least `n`. -/
theorem stringMeasure_setOf_length_le (n : ℕ) :
    M.stringMeasure {y | n ≤ y.length} ≤ M.survival n := by
  rw [← Measure.tsum_measure_setOf_prefix_length, survival]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [M.stringMeasure_setOf_prefix]
  exact mul_le_of_le_one_right' (M.after x.1).tsum_stringProb_le_one

/-- In a tight model survival to `n` is the probability of a string of length at least `n`. -/
theorem IsTight.stringMeasure_setOf_length_le {M : AutoregressiveSequenceModel α}
    (hM : M.IsTight) (n : ℕ) : M.stringMeasure {y | n ≤ y.length} = M.survival n := by
  rw [← Measure.tsum_measure_setOf_prefix_length, survival]
  exact tsum_congr fun x ↦ hM.stringMeasure_setOf_prefix x.1

/-- The expected length of the generated string is at most the total survival after the first
step. -/
theorem lintegral_length_le :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure ≤ ∑' n, M.survival (n + 1) := by
  rw [lintegral_natCast_eq_tsum_measure_lt .of_discrete]
  exact ENNReal.tsum_le_tsum fun n ↦ M.stringMeasure_setOf_length_le (n + 1)

/-- In a tight model the expected length is the total survival after the first step. -/
theorem IsTight.lintegral_length {M : AutoregressiveSequenceModel α} (hM : M.IsTight) :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure = ∑' n, M.survival (n + 1) := by
  rw [lintegral_natCast_eq_tsum_measure_lt .of_discrete]
  exact tsum_congr fun n ↦ hM.stringMeasure_setOf_length_le (n + 1)

/-- In a tight model the prefix probabilities sum to the expected length plus one, the
normalizing constant of the prefix distribution ([opedal-chodroff-cotterell-wilcox-2024],
Proposition 1). -/
theorem IsTight.tsum_prefixProb {M : AutoregressiveSequenceModel α} (hM : M.IsTight) :
    ∑' x, M.prefixProb x = ∫⁻ x, (x.length : ℝ≥0∞) + 1 ∂M.stringMeasure := by
  rw [← Measure.tsum_measure_setOf_prefix]
  exact tsum_congr fun x ↦ (hM.stringMeasure_setOf_prefix x).symm

/-- An end probability of at least `c` after every prefix bounds the expected length by
`(1 - c) / c`. -/
theorem lintegral_length_le_div {c : ℝ≥0∞} (hc : ∀ x : List α, c ≤ M.next x {none}) :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure ≤ (1 - c) / c := by
  have hc1 : c ≤ 1 := (hc []).trans prob_le_one
  calc ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure
      ≤ ∑' n, M.survival (n + 1) := M.lintegral_length_le
    _ ≤ ∑' n, (1 - c) ^ (n + 1) := ENNReal.tsum_le_tsum fun n ↦ M.survival_le_pow hc (n + 1)
    _ = (1 - c) / c := by
        simp_rw [pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1, div_eq_mul_inv]

/-! ### The trajectory

The model is a prediction rule on the extended alphabet, with the end absorbing, and the law of
its whole trajectory is the Ionescu–Tulcea trajectory measure of that rule. -/

open Classical in
/-- The model as a prediction rule on the extended alphabet: after a history of units it draws
the next unit, and after the end of the string it stays at the end. -/
noncomputable def rule (n : ℕ) : Kernel (Fin n → Option α) (Option α) :=
  Kernel.ofFunOfCountable fun h ↦
    if ∀ i, h i ≠ none then M.next (List.ofFn h).reduceOption else Measure.dirac none

instance (n : ℕ) : IsMarkovKernel (M.rule n) :=
  ⟨fun h ↦ by
    change IsProbabilityMeasure (if ∀ i, h i ≠ none then _ else _)
    split_ifs <;> infer_instance⟩

/-- After a history of units the rule is the model's next-unit distribution. -/
theorem rule_apply_some {n : ℕ} (f : Fin n → α) :
    M.rule n (some ∘ f) = M.next (List.ofFn f) := by
  change (if ∀ i, (some ∘ f) i ≠ none then _ else _) = _
  simp only [Function.comp_apply, ne_eq, Option.some_ne_none, not_false_eq_true, implies_true,
    ite_true, ← List.map_ofFn, reduceOption_map_some]

/-- The mass of a history of units is its prefix probability. -/
theorem seqLaw_rule_singleton_some : ∀ {n : ℕ} (f : Fin n → α),
    seqLaw M.rule n {some ∘ f} = M.prefixProb (List.ofFn f)
  | 0, f => by
    rw [seqLaw_zero, Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 (Subsingleton.elim _ _)),
      List.ofFn_zero, prefixProb_nil]
  | n + 1, f => by
    conv_lhs => rw [← Fin.snoc_init_self (some ∘ f)]
    rw [seqLaw_succ_singleton_snoc, show Fin.init (some ∘ f) = some ∘ Fin.init f from rfl,
      seqLaw_rule_singleton_some, rule_apply_some, List.ofFn_succ', List.concat_eq_append,
      prefixProb_concat]
    rfl

/-- Survival to `n` is the law of the first `n` draws on the histories of units. -/
theorem survival_eq_seqLaw (n : ℕ) :
    M.survival n = seqLaw M.rule n {h | ∀ i, h i ≠ none} := by
  have hU : {h : Fin n → Option α | ∀ i, h i ≠ none} = ⋃ f : Fin n → α, {some ∘ f} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hh
      exact ⟨fun i ↦ (h i).get (Option.ne_none_iff_isSome.1 (hh i)), funext fun i ↦ by simp⟩
    · rintro ⟨f, rfl⟩ i
      exact Option.some_ne_none _
  have hinj : Function.Injective fun f : Fin n → α ↦ some ∘ f := (Option.some_injective α).comp_left
  rw [hU, measure_iUnion (fun f g hfg ↦ Set.disjoint_singleton.2 (hinj.ne hfg))
    fun _ ↦ measurableSet_singleton _, survival]
  show ∑' x : List.Vector α n, M.prefixProb x.1 = _
  rw [← (Equiv.vectorEquivFin α n).symm.tsum_eq]
  exact tsum_congr fun f ↦ by
    rw [seqLaw_rule_singleton_some]
    exact congrArg M.prefixProb (List.Vector.toList_ofFn f)

/-- The law of the whole trajectory of the model: the units it generates one after another,
with the end of the string absorbing. -/
noncomputable def trajectory : Measure (ℕ → Option α) := seqTrajectory M.rule

instance : IsProbabilityMeasure M.trajectory := by
  unfold trajectory; infer_instance

/-- Survival to `n` is the probability that none of the first `n` units is the end. -/
theorem trajectory_setOf_forall_lt_ne_none (n : ℕ) :
    M.trajectory {ω | ∀ i < n, ω i ≠ none} = M.survival n := by
  cases n with
  | zero => simp
  | succ n =>
    have hpre : (trajEquivFin n ∘ frestrictLe (π := fun _ : ℕ ↦ Option α) n) ⁻¹'
        {h : Fin (n + 1) → Option α | ∀ i, h i ≠ none} =
          {ω : ℕ → Option α | ∀ i < n + 1, ω i ≠ none} := by
      ext ω
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_ofPred_eq, trajEquivFin_apply,
        frestrictLe_apply, Fin.forall_iff]
    rw [survival_eq_seqLaw, trajectory, ← seqTrajectory_map_frestrictLe,
      Measure.map_apply ((trajEquivFin n).measurable.comp (measurable_frestrictLe n))
        (Set.to_countable _).measurableSet, hpre]

/-- The probability that the string never ends is the infimum of survival. -/
theorem trajectory_setOf_forall_ne_none :
    M.trajectory {ω | ∀ i, ω i ≠ none} = ⨅ n, M.survival n := by
  have h : {ω : ℕ → Option α | ∀ i, ω i ≠ none} = ⋂ n, {ω | ∀ i < n, ω i ≠ none} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h n i _ ↦ h i, fun h i ↦ h (i + 1) i i.lt_succ_self⟩
  rw [h, Antitone.measure_iInter (s := fun n ↦ {ω : ℕ → Option α | ∀ i < n, ω i ≠ none})
    (fun m n hmn ω hω i hi ↦ hω i (hi.trans_le hmn))
    (fun n ↦ (measurableSet_setOf_forall_lt_ne_none n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact iInf_congr M.trajectory_setOf_forall_lt_ne_none

/-- A model is tight exactly when its trajectory ends almost surely, [du-etal-2023]'s definition
of tightness. -/
theorem isTight_iff_trajectory_setOf_forall_ne_none :
    M.IsTight ↔ M.trajectory {ω | ∀ i, ω i ≠ none} = 0 := by
  rw [trajectory_setOf_forall_ne_none, isTight_iff_tendsto_survival]
  have hinf := tendsto_atTop_iInf M.survival_antitone
  exact ⟨fun h ↦ tendsto_nhds_unique hinf h, fun h ↦ h ▸ hinf⟩

/-- The probability of generating exactly the string `List.ofFn f` is the probability that the
trajectory begins with its units and then ends. -/
theorem trajectory_cylinder {n : ℕ} (f : Fin n → α) :
    M.trajectory {ω | (∀ i : Fin n, ω i = some (f i)) ∧ ω n = none} =
      M.stringProb (List.ofFn f) := by
  have hpre : (trajEquivFin n ∘ frestrictLe (π := fun _ : ℕ ↦ Option α) n) ⁻¹'
      {Fin.snoc (some ∘ f) none} =
        {ω : ℕ → Option α | (∀ i : Fin n, ω i = some (f i)) ∧ ω n = none} := by
    ext ω
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, funext_iff,
      trajEquivFin_apply, frestrictLe_apply, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨fun i ↦ by simpa using h i.castSucc, by simpa using h (Fin.last n)⟩
    · rintro ⟨h₁, h₂⟩ j
      induction j using Fin.lastCases with
      | last => simpa using h₂
      | cast i => simpa using h₁ i
  rw [trajectory, ← hpre, ← Measure.map_apply ((trajEquivFin n).measurable.comp
    (measurable_frestrictLe n)) (measurableSet_singleton _), seqTrajectory_map_frestrictLe,
    seqLaw_succ_singleton_snoc, seqLaw_rule_singleton_some, rule_apply_some, stringProb]

end AutoregressiveSequenceModel
