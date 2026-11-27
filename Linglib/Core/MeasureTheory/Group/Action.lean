/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measures invariant under group actions: countable spaces, mixtures and products

This file supplements mathlib's theory of measures invariant under a group action with three
facts. On a countable space, invariance can be checked on points. A mixture of invariant measures
is invariant. A monoid `M` acting on `ι` acts on the functions `ι → α` by precomposition, as the
domain action `Mᵈᵐᵃ` with `(DomMulAct.mk c • x) i = x (c • i)`; this action is measurable for the
product σ-algebra, and a finite product of copies of one measure is invariant under it when `M`
is a group.

## Main results

* `MeasureTheory.smulInvariantMeasure_of_measure_singleton`: on a countable space with measurable
  singletons, a measure is invariant under a group action when moving a point never changes its
  mass.
* `MeasureTheory.smulInvariantMeasure_bind`: a mixture of invariant measures is invariant.
* `MeasureTheory.Measure.pi.smulInvariantMeasure_domMulAct`: a finite product of copies of one
  measure is invariant under a group acting on the indices, so under permuting the coordinates.

## Implementation notes

`[UPSTREAM]` candidates for `Mathlib/MeasureTheory/Group/Action.lean` and
`Mathlib/MeasureTheory/Constructions/Pi.lean`.
-/

public section

open MeasureTheory

@[to_additive]
instance {M ι α : Type*} [SMul M ι] [MeasurableSpace α] : MeasurableConstSMul Mᵈᵐᵃ (ι → α) :=
  ⟨fun _ ↦ Measurable.of_eval fun _ ↦ measurable_pi_apply _⟩

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

/-- Independent and identically distributed values are exchangeable: a finite product of copies
of one measure is invariant under a group acting on the indices. -/
@[to_additive /-- A finite product of copies of one measure is invariant under an additive group
acting on the indices. -/]
instance Measure.pi.smulInvariantMeasure_domMulAct {G ι α : Type*} [Group G] [MulAction G ι]
    [Fintype ι] [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν] :
    SMulInvariantMeasure Gᵈᵐᵃ (ι → α) (Measure.pi fun _ : ι ↦ ν) := by
  refine ⟨fun c s _ ↦ ?_⟩
  have hc : (fun x : ι → α ↦ c • x) =
      MeasurableEquiv.piCongrLeft (fun _ ↦ α) (MulAction.toPerm (DomMulAct.mk.symm c)).symm := by
    ext x i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', DomMulAct.smul_apply]
  rw [hc]
  exact (measurePreserving_piCongrLeft (fun _ : ι ↦ ν) _).measure_preimage_equiv s

end MeasureTheory
