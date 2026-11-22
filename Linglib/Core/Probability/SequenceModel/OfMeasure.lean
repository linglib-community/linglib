/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.SequenceModel.Basic

/-!
# The autoregressive model of a measure on strings

After each prefix of positive probability, the first symbol of the continuation of a measure on
strings, `none` where the continuation is empty, has a law, and these laws form a model,
`ofMeasure`. A probability measure on strings is the string law of its model
(`stringMeasure_ofMeasure`), and of every model that agrees with it after each prefix of positive
probability (`stringMeasure_eq_of_next_eq`). Prefixes act on a measure by taking continuations and
on a model by starting it after the prefix, and the passage from measures to models carries one
action to the other (`ofMeasure_continuation`).

A random string `str : T → List W` on a probability space has a law, and the model of that law
continues a prefix with the conditional probability of the event that the string begins with the
extended prefix (`condPrefixProb_ofMeasure_map`), the prefix probability of [stolcke-1995].

## Main definitions

* `ofMeasure μ`: the model of a measure on strings.
* `consistent str ws`: the event that the random string `str` begins with `ws`.

## Implementation notes

The results about string laws take a countable alphabet with measurable singletons.

## References

* [du-etal-2023]
* [stolcke-1995]
-/

@[expose] public section

open InformationTheory MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AutoregressiveSequenceModel

section ofMeasure

variable {α : Type*} [MeasurableSpace α] (μ : Measure (List α))

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
    (ofMeasure μ).next x {some a} = μ[(x ++ [a]).cylinder | x.cylinder] := by
  rw [← Measure.continuation_cylinder]
  by_cases h : μ.continuation x = 0
  · simp [next_ofMeasure_of_eq_zero μ h, h]
  rw [next_ofMeasure_of_ne_zero μ h, Measure.map_apply .of_discrete (measurableSet_singleton _)]
  congr 1
  ext l
  cases l <;> simp [eq_comm]

theorem next_ofMeasure_apply_none [IsFiniteMeasure μ] {x : List α} (hx : μ x.cylinder ≠ 0) :
    (ofMeasure μ).next x {none} = μ[{x} | x.cylinder] := by
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
    (h : ∀ x, μ x.cylinder ≠ 0 → M.next x = (ofMeasure μ).next x) (x : List α) :
    M.prefixProb x = μ x.cylinder := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
    have hsub := List.cylinder_append_subset x [a]
    rw [prefixProb_concat, ih]
    rcases eq_or_ne (μ x.cylinder) 0 with h0 | h0
    · rw [h0, zero_mul, measure_mono_null hsub h0]
    rw [h x h0, next_ofMeasure_apply_some, mul_comm, cond_mul_eq_inter .of_discrete,
      Set.inter_eq_right.2 hsub]

variable (μ) in
theorem prefixProb_ofMeasure (x : List α) : (ofMeasure μ).prefixProb x = μ x.cylinder :=
  prefixProb_eq_of_next_eq (fun _ _ ↦ rfl) x

/-- After a prefix of positive probability, the model of a probability measure on strings
continues with `x` with the conditional probability of the strings extending the prefix by
`x`. -/
theorem condPrefixProb_ofMeasure {c : List α} (hc : μ c.cylinder ≠ 0) (x : List α) :
    (ofMeasure μ).condPrefixProb c x = μ[(c ++ x).cylinder | c.cylinder] := by
  have := μ.isProbabilityMeasure_continuation hc
  rw [← prefixProb_after, ← ofMeasure_continuation, prefixProb_ofMeasure,
    Measure.continuation_cylinder]

variable [Countable α]

/-- A model whose conditionals are the next-symbol laws of a string measure at every
positive-probability prefix has that measure as its string law ([du-etal-2023], footnote 4). -/
theorem stringMeasure_eq_of_next_eq {M : AutoregressiveSequenceModel α}
    (h : ∀ x, μ x.cylinder ≠ 0 → M.next x = (ofMeasure μ).next x) : M.stringMeasure = μ := by
  refine Measure.ext_of_singleton fun x ↦ ?_
  have hsub := List.singleton_subset_cylinder x
  rw [stringMeasure_singleton, stringProb, prefixProb_eq_of_next_eq h]
  rcases eq_or_ne (μ x.cylinder) 0 with h0 | h0
  · rw [h0, zero_mul, measure_mono_null hsub h0]
  rw [h x h0, next_ofMeasure_apply_none μ h0, mul_comm, cond_mul_eq_inter .of_discrete,
    Set.inter_eq_right.2 hsub]

variable (μ) in
theorem stringMeasure_ofMeasure : (ofMeasure μ).stringMeasure = μ :=
  stringMeasure_eq_of_next_eq fun _ _ ↦ rfl

/-- After a prefix of positive probability, the model of a language model generates the
continuation of the prefix. -/
theorem stringMeasure_after_ofMeasure {c : List α} (hc : μ c.cylinder ≠ 0) :
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


/-! ### The law of a random string -/

section map

variable {T W : Type*} (str : T → List W)

/-- The sample points whose string extends the prefix `ws`: the event that the random string `str`
begins with `ws`. -/
def consistent (ws : List W) : Set T := str ⁻¹' ws.cylinder

@[simp] theorem consistent_nil : consistent str ([] : List W) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ List.nil_prefix

theorem consistent_anti {ws ws' : List W} (h : ws <+: ws') :
    consistent str ws' ⊆ consistent str ws :=
  fun _ ht ↦ h.trans ht

variable [MeasurableSpace T] [DiscreteMeasurableSpace T] (P : Measure T)

theorem map_apply_cylinder (ws : List W) :
    P.map str ws.cylinder = P (consistent str ws) :=
  Measure.map_apply .of_discrete .of_discrete

variable [MeasurableSpace W] [MeasurableSingletonClass W]

/-- After a prefix of positive probability, the model of the law of a random string continues with
`xs` with the ratio of the probabilities that the string begins with the extended prefix and with
the prefix. -/
theorem condPrefixProb_ofMeasure_map [IsProbabilityMeasure P] {ws : List W}
    (hws : P (consistent str ws) ≠ 0) (xs : List W) :
    (ofMeasure (P.map str)).condPrefixProb ws xs =
      P (consistent str (ws ++ xs)) / P (consistent str ws) := by
  rw [condPrefixProb_ofMeasure (by rwa [map_apply_cylinder]),
    cond_apply_of_subset .of_discrete (ws.cylinder_append_subset xs), map_apply_cylinder,
    map_apply_cylinder]

/-- The probability of the next symbol `w` after the prefix `ws` is the conditional probability,
given that the random string begins with `ws`, that it begins with `ws ++ [w]`. -/
theorem next_ofMeasure_map_apply_some (ws : List W) (w : W) :
    (ofMeasure (P.map str)).next ws {some w} =
      P[consistent str (ws ++ [w]) | consistent str ws] := by
  rw [next_ofMeasure_apply_some, cond_map .of_discrete .of_discrete,
    Measure.map_apply .of_discrete .of_discrete]
  rfl

end map

end AutoregressiveSequenceModel
