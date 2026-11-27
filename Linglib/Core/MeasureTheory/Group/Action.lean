/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measures invariant under group actions: countable spaces and mixtures

On a countable space with measurable singletons, invariance of a measure under a group action
can be checked on points. A mixture of measures invariant under an action is invariant.

## Main results

* `MeasureTheory.smulInvariantMeasure_of_measure_singleton`: the criterion on points.
* `MeasureTheory.smulInvariantMeasure_bind`: a mixture of invariant measures is invariant.

`[UPSTREAM]` candidates for `Mathlib/MeasureTheory/Group/Action.lean`.
-/

public section

namespace MeasureTheory

/-- On a countable space with measurable singletons, a measure is invariant under a group action
as soon as moving a point never changes its mass. -/
@[to_additive /-- On a countable space with measurable singletons, a measure is invariant under
an additive group action as soon as moving a point never changes its mass. -/]
theorem smulInvariantMeasure_of_measure_singleton {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {μ : Measure X}
    (h : ∀ (g : G) (x : X), μ {g • x} = μ {x}) : SMulInvariantMeasure G X μ := by
  refine ⟨fun g s hs ↦ ?_⟩
  rw [← Measure.map_apply (measurable_of_countable _) hs]
  congr 1
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x),
    Set.preimage_smul, Set.smul_set_singleton, h]

/-- A mixture of measures invariant under an action is invariant. -/
@[to_additive /-- A mixture of measures invariant under an additive action is invariant. -/]
theorem smulInvariantMeasure_bind {M α β : Type*} [SMul M α] [MeasurableSpace α]
    [MeasurableConstSMul M α] [MeasurableSpace β] {m : Measure β} {κ : β → Measure α}
    (hκ : AEMeasurable κ m) (h : ∀ᵐ b ∂m, SMulInvariantMeasure M α (κ b)) :
    SMulInvariantMeasure M α (m.bind κ) := by
  refine ⟨fun c s hs ↦ ?_⟩
  rw [Measure.bind_apply (hs.preimage (measurable_const_smul c)) hκ, Measure.bind_apply hs hκ]
  exact lintegral_congr_ae (h.mono fun b hb ↦ hb.measure_preimage_smul c hs)

end MeasureTheory
