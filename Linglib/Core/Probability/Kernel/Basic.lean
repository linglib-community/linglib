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
# Kernels out of countable spaces

Out of a countable space with measurable singletons every family of measures is measurable, so a
kernel is its family of rows: `ofFunOfCountable f` has row `f a` at `a`, and its classes are read
off the rows. It is Markov when every row is a probability measure, and a kernel out of such a
space is [s-finite exactly when every row is](##isSFiniteKernel_iff_of_countable), being
[the sum of its rows](##sum_piecewise_singleton_const), each placed at its point. Every kernel
between countable types is therefore s-finite. Pushed forward along a map out of a discrete
space, a kernel gives a point the mass of its fibre. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/Basic.lean`, and for the pushforward `Composition/MapComap.lean`.

## Implementation notes

The criterion `isSFiniteKernel_iff_of_countable` is a theorem rather than an instance: read from
right to left it would let instance search loop through `IsSFiniteKernel.sfinite`, which reads it
from left to right. The instances are the ones for `ofFunOfCountable` with s-finite rows and for a
countable target, where every row is s-finite outright.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

section Countable

variable [Countable α] [MeasurableSingletonClass α]

@[simp, norm_cast]
lemma coe_ofFunOfCountable (f : α → Measure β) : ⇑(ofFunOfCountable f) = f := rfl

lemma ofFunOfCountable_apply (f : α → Measure β) (a : α) : ofFunOfCountable f a = f a := rfl

instance ofFunOfCountable.instIsMarkovKernel {f : α → Measure β}
    [∀ a, IsProbabilityMeasure (f a)] : IsMarkovKernel (ofFunOfCountable f) :=
  ⟨fun a ↦ inferInstanceAs (IsProbabilityMeasure (f a))⟩

/-- A kernel out of a countable space is the sum over the points `a` of the kernel equal to its
row at `a` on `{a}` and to zero elsewhere. -/
theorem sum_piecewise_singleton_const [DecidableEq α] (κ : Kernel α β) :
    (Kernel.sum fun a ↦ piecewise (measurableSet_singleton a) (const α (κ a)) 0) = κ := by
  ext a s hs
  rw [sum_apply' _ _ hs, tsum_eq_single a fun n hn ↦ by simp [piecewise_apply, Ne.symm hn]]
  simp [piecewise_apply]

theorem isSFiniteKernel_iff_of_countable {κ : Kernel α β} :
    IsSFiniteKernel κ ↔ ∀ a, SFinite (κ a) := by
  classical
  refine ⟨fun _ _ ↦ inferInstance, fun _ ↦ ?_⟩
  rw [← sum_piecewise_singleton_const κ]
  infer_instance

instance ofFunOfCountable.instIsSFiniteKernel {f : α → Measure β} [∀ a, SFinite (f a)] :
    IsSFiniteKernel (ofFunOfCountable f) :=
  isSFiniteKernel_iff_of_countable.2 ‹_›

instance [Countable β] (κ : Kernel α β) : IsSFiniteKernel κ :=
  isSFiniteKernel_iff_of_countable.2 fun _ ↦ inferInstance

end Countable

section Map

variable [MeasurableSingletonClass γ] (κ : Kernel α β) (f : β → γ) (a : α) (c : γ)

theorem map_apply_singleton [DiscreteMeasurableSpace β] : κ.map f a {c} = κ a (f ⁻¹' {c}) :=
  map_apply' κ .of_discrete a (.singleton c)

theorem map_apply_singleton_ne_zero_iff [Countable β] [MeasurableSingletonClass β] :
    κ.map f a {c} ≠ 0 ↔ ∃ b, f b = c ∧ κ a {b} ≠ 0 := by
  rw [map_apply_singleton, ← Set.biUnion_of_singleton (f ⁻¹' {c}), ne_eq,
    measure_biUnion_null_iff (Set.to_countable _)]
  simp

end Map

end ProbabilityTheory.Kernel
