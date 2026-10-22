/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Partial trajectories at the next time

The one-step trajectory from `x` is the step kernel at `x` pushed forward by appending its value
to `x`. In discrete state spaces this gives the chain rule
`partialTraj_succ_apply_singleton`: the mass of a trajectory up to time `b + 1` is the mass of its
restriction to time `b` times the probability of its last step. `[UPSTREAM]` candidates for
`Mathlib/Probability/Kernel/IonescuTulcea/PartialTraj.lean`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Preorder

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} {mX : ∀ n, MeasurableSpace (X n)}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]

/-- The one-step trajectory from `x` is `κ a x` pushed forward by appending its value to `x`. -/
theorem partialTraj_succ_self_apply (a : ℕ) (x : Π i : Iic a, X i) :
    partialTraj κ a (a + 1) x
      = (κ a x).map fun y ↦ IicProdIoc a (a + 1) (x, MeasurableEquiv.piSingleton a y) := by
  rw [partialTraj_succ_self, map_apply _ (by fun_prop), prod_apply, id_apply,
    map_apply _ (by fun_prop), Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A trajectory up to time `b + 1` is obtained by appending exactly one point to exactly one
trajectory up to time `b`. -/
theorem IicProdIoc_piSingleton_eq_iff {b : ℕ} {z : Π i : Iic b, X i} {w : X (b + 1)}
    {y : Π i : Iic (b + 1), X i} :
    IicProdIoc b (b + 1) (z, MeasurableEquiv.piSingleton b w) = y ↔
      z = frestrictLe₂ b.le_succ y ∧ w = y ⟨b + 1, mem_Iic.2 le_rfl⟩ := by
  rw [← MeasurableEquiv.coe_IicProdIoc b.le_succ, ← MeasurableEquiv.eq_symm_apply,
    MeasurableEquiv.coe_IicProdIoc_symm, Prod.mk.injEq]
  exact and_congr_right' (MeasurableEquiv.piSingleton b).eq_symm_apply.symm

/-- In discrete state spaces, the mass of a trajectory up to time `b + 1` is the mass of its
restriction to time `b` times the probability of its last step. -/
theorem partialTraj_succ_apply_singleton [∀ n, Countable (X n)]
    [∀ n, MeasurableSingletonClass (X n)] {a b : ℕ} (hab : a ≤ b) (x : Π i : Iic a, X i)
    (y : Π i : Iic (b + 1), X i) :
    partialTraj κ a (b + 1) x {y} = partialTraj κ a b x {frestrictLe₂ b.le_succ y} *
      κ b (frestrictLe₂ b.le_succ y) {y ⟨b + 1, mem_Iic.2 le_rfl⟩} := by
  rw [partialTraj_succ_eq_comp hab, comp_apply, Measure.bind_apply (measurableSet_singleton _)
    (Kernel.aemeasurable _), lintegral_countable', tsum_eq_single (frestrictLe₂ b.le_succ y)]
  · rw [partialTraj_succ_self_apply, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      show (fun w ↦ IicProdIoc b (b + 1) (frestrictLe₂ b.le_succ y,
          MeasurableEquiv.piSingleton b w)) ⁻¹' {y} = {y ⟨b + 1, mem_Iic.2 le_rfl⟩} from
        Set.ext fun w ↦ by simp [IicProdIoc_piSingleton_eq_iff], mul_comm]
  · intro z hz
    rw [partialTraj_succ_self_apply, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      show (fun w ↦ IicProdIoc b (b + 1) (z, MeasurableEquiv.piSingleton b w)) ⁻¹' {y} = ∅ from
        Set.eq_empty_of_forall_notMem fun w hw ↦ hz (IicProdIoc_piSingleton_eq_iff.1 hw).1,
      measure_empty, zero_mul]

end ProbabilityTheory.Kernel
