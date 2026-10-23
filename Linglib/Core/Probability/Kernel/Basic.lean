/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Kernels between countable spaces

The kernel `ofFunOfCountable f` that a function out of a countable type defines has row `f a`
at `a`. Every measure on a countable type is s-finite, and every kernel out of a countable type
with measurable singletons is a countable sum of the kernels concentrated at one point, so every
kernel between two countable types is s-finite. The pushforward of a kernel into a countable type
gives a point the mass of the fibre over it. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/Basic.lean`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem ofFunOfCountable_apply [Countable α] [MeasurableSingletonClass α] (f : α → Measure β)
    (a : α) : ofFunOfCountable f a = f a := rfl

open scoped Classical in
theorem sum_piecewise_singleton_const [Countable α] [MeasurableSingletonClass α]
    (κ : Kernel α β) :
    (Kernel.sum fun a ↦ piecewise (measurableSet_singleton a) (const α (κ a)) 0) = κ := by
  ext a s hs
  rw [sum_apply' _ _ hs, tsum_eq_single a fun n hn ↦ by simp [piecewise_apply, Ne.symm hn]]
  simp [piecewise_apply]

instance [Countable α] [MeasurableSingletonClass α] [Countable β] (κ : Kernel α β) :
    IsSFiniteKernel κ := by
  rw [← sum_piecewise_singleton_const κ]
  infer_instance

section Map

variable {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ] [Countable β]
  [MeasurableSingletonClass β] (κ : Kernel α β) (f : β → γ) (a : α) (c : γ)

theorem map_apply_singleton : κ.map f a {c} = κ a (f ⁻¹' {c}) :=
  map_apply' κ (measurable_of_countable f) a (measurableSet_singleton c)

theorem map_apply_singleton_ne_zero_iff : κ.map f a {c} ≠ 0 ↔ ∃ b, f b = c ∧ κ a {b} ≠ 0 := by
  rw [map_apply_singleton, ← Set.biUnion_of_singleton (f ⁻¹' {c}), ne_eq,
    measure_biUnion_null_iff (Set.to_countable _)]
  simp

end Map

end ProbabilityTheory.Kernel
