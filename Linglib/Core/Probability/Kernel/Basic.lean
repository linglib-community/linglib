/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Kernels out of countable spaces

Out of a countable space with measurable singletons every family of measures is measurable, so
every family `f` is the rows of a kernel, `ofFunOfCountable f`, whose classes are read off the
rows. It is Markov when every row is a probability measure, and a kernel out of such a space is
[s-finite exactly when every row is](##isSFiniteKernel_iff_of_countable), being
[the sum of its rows](##sum_piecewise_singleton_const), each placed at its point. Every kernel
between countable types is therefore s-finite. `[UPSTREAM]` candidate for
`Mathlib/Probability/Kernel/Basic.lean`.

## Implementation notes

The criterion `isSFiniteKernel_iff_of_countable` is a theorem rather than an instance: read from
right to left it would let instance search loop through `IsSFiniteKernel.sfinite`, which reads it
from left to right. The instances are the ones for `ofFunOfCountable` with s-finite rows and for a
countable target, where every row is s-finite outright.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [Countable α]
  [MeasurableSingletonClass α]

@[simp, norm_cast]
lemma coe_ofFunOfCountable (f : α → Measure β) : ⇑(ofFunOfCountable f) = f := rfl

lemma ofFunOfCountable_apply (f : α → Measure β) (a : α) : ofFunOfCountable f a = f a := rfl

instance ofFunOfCountable.instIsMarkovKernel {f : α → Measure β}
    [∀ a, IsProbabilityMeasure (f a)] : IsMarkovKernel (ofFunOfCountable f) :=
  ⟨fun a ↦ inferInstanceAs (IsProbabilityMeasure (f a))⟩

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

end ProbabilityTheory.Kernel
