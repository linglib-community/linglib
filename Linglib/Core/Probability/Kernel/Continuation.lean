/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Basic

/-!
# Continuations of a measure on lists

After a prefix `c`, a measure on lists has the law of what follows `c` among the lists beginning
with it: the measure conditioned on the cylinder of `c`, with `c` dropped. The continuations
beginning with `w` have [the conditional probability](##MeasureTheory.Measure.continuation_cylinder)
of the cylinder of `c ++ w`, and taking continuations is an action of prefixes: the continuation
after `c` and then after `u` is
[the continuation after `c ++ u`](##MeasureTheory.Measure.continuation_continuation).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} (μ : Measure (List α))

/-- The continuation law of a measure on strings: after the prefix `c`, the law of what follows
`c` among the strings extending it. -/
noncomputable def continuation : Kernel (List α) (List α) :=
  ⟨fun c ↦ (μ[|c.cylinder]).map (List.drop c.length), .of_discrete⟩

theorem continuation_apply (c : List α) :
    μ.continuation c = (μ[|c.cylinder]).map (List.drop c.length) :=
  rfl

instance (c : List α) : IsZeroOrProbabilityMeasure (μ.continuation c) := by
  rw [continuation_apply]
  infer_instance

theorem isProbabilityMeasure_continuation [IsFiniteMeasure μ] {c : List α}
    (hc : μ c.cylinder ≠ 0) : IsProbabilityMeasure (μ.continuation c) := by
  have := cond_isProbabilityMeasure (s := c.cylinder) hc
  rw [continuation_apply]
  infer_instance

/-- The continuations of `c` beginning with `w` have the conditional probability of the strings
extending `c ++ w` among those extending `c`. -/
theorem continuation_cylinder (c w : List α) :
    μ.continuation c w.cylinder = μ[(c ++ w).cylinder | c.cylinder] := by
  rw [continuation_apply, map_apply .of_discrete .of_discrete, cond_apply .of_discrete,
    cond_apply .of_discrete, List.cylinder_inter_drop,
    Set.inter_eq_right.2 (List.cylinder_append_subset c w)]

/-- The continuation of `c` is empty with the conditional probability of `c` itself. -/
theorem continuation_singleton_nil (c : List α) :
    μ.continuation c {[]} = μ[{c} | c.cylinder] := by
  rw [continuation_apply, map_apply .of_discrete .of_discrete, cond_apply .of_discrete,
    cond_apply .of_discrete]
  congr 2
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, List.mem_cylinder,
    List.drop_eq_nil_iff]
  exact ⟨fun ⟨h, hl⟩ ↦ ⟨h, (h.eq_of_length_le hl).symm⟩, fun ⟨h, hy⟩ ↦ ⟨h, hy ▸ le_rfl⟩⟩

/-- The continuation after `c` and then after `u` is the continuation after `c ++ u`. -/
theorem continuation_continuation [IsFiniteMeasure μ] (c u : List α) :
    (μ.continuation c).continuation u = μ.continuation (c ++ u) := by
  rw [continuation_apply, continuation_apply,
    cond_map (Measurable.of_discrete.aemeasurable) .of_discrete,
    cond_cond_eq_cond_inter .of_discrete .of_discrete, List.cylinder_inter_drop,
    map_map .of_discrete .of_discrete, continuation_apply, List.length_append]
  congr 1
  ext y : 1
  simp [List.drop_drop]

end MeasureTheory.Measure
