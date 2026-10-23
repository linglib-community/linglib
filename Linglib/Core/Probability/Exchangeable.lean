/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Group.Action

/-!
# Exchangeable laws

A family of random variables indexed by `ι` with values in `α` is *exchangeable* when its law, a
measure on `ι → α`, is unchanged by permuting the indices. The permutations act on `ι → α` by
precomposition, as the domain action `(Equiv.Perm ι)ᵈᵐᵃ` (`(DomMulAct.mk σ • x) i = x (σ i)`),
and `Exchangeable μ` is invariance under that action, `SMulInvariantMeasure`. Random partitions
are exchangeable in the same sense, for the action of the permutations on partitions. On a
countable space with measurable singletons, invariance is invariance of the point masses.

## Main definitions

* `ProbabilityTheory.Exchangeable μ`: every permutation of the indices leaves `μ` unchanged.

## Main results

* `ProbabilityTheory.smulInvariantMeasure_of_measure_singleton`: on a countable space with
  measurable singletons, a measure is invariant under a group action when moving a point never
  changes its mass.
* `ProbabilityTheory.exchangeable_of_measure_singleton`: the same for exchangeability.

## Implementation notes

For infinite `ι` the usual definition asks for invariance only under the permutations that move
finitely many indices; `Exchangeable` asks for all of them, which de Finetti's theorem shows
equivalent on standard Borel spaces but which is not proved here. `[UPSTREAM]` candidate:
mathlib has no notion of exchangeability.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- On a countable space with measurable singletons, a measure is invariant under a group action
as soon as moving a point never changes its mass. -/
theorem smulInvariantMeasure_of_measure_singleton {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {ν : Measure X}
    (h : ∀ (g : G) (x : X), ν {g • x} = ν {x}) : SMulInvariantMeasure G X ν := by
  refine ⟨fun g S hS ↦ ?_⟩
  have hmap : ν.map (g • ·) = ν := Measure.ext_of_singleton fun x ↦ by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x),
      show (g • ·) ⁻¹' {x} = {g⁻¹ • x} from Set.ext fun y ↦ by
        simp [eq_inv_smul_iff], h]
  rw [← Measure.map_apply (measurable_of_countable _) hS, hmap]

variable {ι α : Type*} [MeasurableSpace α] {μ : Measure (ι → α)}

/-- The law `μ` of an `ι`-indexed family is *exchangeable* when every permutation of the indices,
acting by precomposition, leaves it unchanged. -/
abbrev Exchangeable (μ : Measure (ι → α)) : Prop :=
  SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → α) μ

/-- On a countable space with measurable singletons, a law is exchangeable as soon as permuting a
point never changes its mass. -/
theorem exchangeable_of_measure_singleton [Countable (ι → α)] [MeasurableSingletonClass (ι → α)]
    (h : ∀ (x : ι → α) (σ : Equiv.Perm ι), μ {x ∘ σ} = μ {x}) : Exchangeable μ :=
  smulInvariantMeasure_of_measure_singleton fun c x ↦ h x (DomMulAct.mk.symm c)

end ProbabilityTheory
