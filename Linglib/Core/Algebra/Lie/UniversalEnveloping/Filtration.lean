/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.Algebra.Operations
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The filtration of the universal enveloping algebra

The universal enveloping algebra `U(L)` of a Lie algebra is filtered by the submodules
`UniversalEnvelopingAlgebra.filtration R L n` spanned by the products of at most `n` elements of
`L`, the powers of `1 ⊔ M` for `M` the range of `UniversalEnvelopingAlgebra.ι`. The filtration is
increasing, multiplicative and exhaustive, and its `n + 1`-st step is the `n`-th together with the
image of the homogeneous tensors of degree `n + 1`
(`UniversalEnvelopingAlgebra.filtration_succ`, `UniversalEnvelopingAlgebra.map_mkAlgHom_pow`).

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The sums of products of at most `n` elements of `L` in the enveloping algebra. -/
def filtration (n : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  (1 ⊔ LinearMap.range ((ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L) : L →ₗ[R] _)) ^ n

theorem filtration_zero : filtration R L 0 = 1 := pow_zero _

theorem filtration_mono : Monotone (filtration R L) :=
  fun _ _ h ↦ Submodule.one_sup_pow_mono _ h

theorem filtration_add (m n : ℕ) :
    filtration R L (m + n) = filtration R L m * filtration R L n := pow_add _ _ _

/-- The products of at most `n + 1` elements of `L` are those of at most `n` together with those
of exactly `n + 1`. -/
theorem filtration_succ (n : ℕ) :
    filtration R L (n + 1) = filtration R L n ⊔
      LinearMap.range ((ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L) : L →ₗ[R] _) ^ (n + 1) :=
  Submodule.one_sup_pow_succ _ n

theorem pow_range_ι_le_filtration (n : ℕ) :
    LinearMap.range ((ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L) : L →ₗ[R] _) ^ n ≤
      filtration R L n :=
  Submodule.pow_le_one_sup_pow _ n

theorem algebraMap_mem_filtration (r : R) (n : ℕ) :
    algebraMap R (UniversalEnvelopingAlgebra R L) r ∈ filtration R L n :=
  filtration_mono R L n.zero_le (by rw [filtration_zero]; exact Submodule.mem_one.mpr ⟨r, rfl⟩)

theorem ι_mem_filtration (x : L) : ι R x ∈ filtration R L 1 := by
  rw [filtration, pow_one]
  exact Submodule.mem_sup_right ⟨x, rfl⟩

/-- The products of `n` elements of `L` are the images of the homogeneous tensors of degree
`n`. -/
theorem map_mkAlgHom_pow (n : ℕ) :
    (LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ n).map
        (mkAlgHom R L).toLinearMap =
      LinearMap.range ((ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L) : L →ₗ[R] _) ^ n := by
  rw [Submodule.map_pow, ← LinearMap.range_comp]
  rfl

theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom R L) := Quotient.mk_surjective

/-- The filtration is exhaustive. -/
theorem exists_mem_filtration (u : UniversalEnvelopingAlgebra R L) : ∃ n, u ∈ filtration R L n := by
  obtain ⟨a, rfl⟩ := mkAlgHom_surjective R L u
  induction a using TensorAlgebra.induction with
  | algebraMap r => exact ⟨0, by rw [AlgHom.commutes]; exact algebraMap_mem_filtration R L r 0⟩
  | ι x => exact ⟨1, ι_mem_filtration R L x⟩
  | mul a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [map_mul, filtration_add]; exact Submodule.mul_mem_mul hm hn⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨max m n, by
      rw [map_add]
      exact add_mem (filtration_mono R L (le_max_left m n) hm)
        (filtration_mono R L (le_max_right m n) hn)⟩

end UniversalEnvelopingAlgebra
