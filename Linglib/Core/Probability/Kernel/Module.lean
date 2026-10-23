module

public import Mathlib.Algebra.Module.FunLike
public import Mathlib.Probability.Kernel.Defs

/-!
# Kernels as a module

Mathlib makes `Kernel α β` an additive monoid, adding rows pointwise. This file adds the scalar
action, row by row, of any `R` acting on `ℝ≥0∞` through a scalar tower, as mathlib does for
`Measure β`, so that `Kernel α β` is a module over `ℝ≥0∞`. A finite family of kernels averaged
over a latent index by weights `c` is then the sum `∑ i, c i • κ i`, whose row at `a` is
`∑ i, c i • κ i a` by `sum_apply` and `smul_apply`. Finite kernels are closed under finite sums
and finite multiples. `[UPSTREAM]` candidate for `Mathlib/Probability/Kernel/Defs.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Kernel

section SMul

variable {R R' : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [SMul R' ℝ≥0∞]
  [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

noncomputable instance instSMul : SMul R (Kernel α β) where
  smul c κ := ⟨c • ⇑κ, Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simpa only [Pi.smul_apply, Measure.smul_apply, smul_one_mul] using
      (κ.measurable_coe hs).const_mul (c • 1 : ℝ≥0∞)⟩

instance : IsSMulApply R (Kernel α β) α (Measure β) where
  smul_apply _ _ _ := rfl

instance [SMulCommClass R R' ℝ≥0∞] : SMulCommClass R R' (Kernel α β) := FunLike.smulCommClass

instance [SMul R R'] [IsScalarTower R R' ℝ≥0∞] : IsScalarTower R R' (Kernel α β) :=
  FunLike.isScalarTower

end SMul

/-- The `ℕ`-action agrees with mathlib's `nsmul` on kernels. -/
example : (instSMulNat : SMul ℕ (Kernel α β)) = instSMul := by with_reducible_and_instances rfl

noncomputable instance instModule {R : Type*} [Semiring R] [Module R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] : Module R (Kernel α β) :=
  fast_instance% FunLike.module

end Kernel

theorem IsFiniteKernel.smul_of_ne_top (κ : Kernel α β) [IsFiniteKernel κ] {c : ℝ≥0∞}
    (hc : c ≠ ∞) : IsFiniteKernel (c • κ) :=
  ⟨⟨c * κ.bound, ENNReal.mul_lt_top hc.lt_top κ.bound_lt_top, fun a ↦
    mul_le_mul_right (κ.measure_le_bound a _) c⟩⟩

theorem IsFiniteKernel.finsetSum {κs : ι → Kernel α β} (I : Finset ι)
    (h : ∀ i ∈ I, IsFiniteKernel (κs i)) : IsFiniteKernel (∑ i ∈ I, κs i) := by
  classical
  induction I using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i I hi h_ind =>
    rw [Finset.sum_insert hi]
    have := h i (Finset.mem_insert_self _ _)
    have := h_ind fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    infer_instance

end ProbabilityTheory
