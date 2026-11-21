/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading of the symmetric algebra

The symmetric algebra of a module `M` is graded by the natural numbers: its part of degree `n` is
the `n`-th power of the range of `SymmetricAlgebra.ι`, the span of the products of `n` elements of
`M`. The construction is that of `TensorAlgebra.gradedAlgebra` and
`ExteriorAlgebra.gradedAlgebra`: the map of `M` into the degree-one summand of the direct sum of
the parts lifts to an algebra homomorphism, which is the decomposition.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace SymmetricAlgebra

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

open scoped DirectSum

/-- A version of `SymmetricAlgebra.ι` that maps into the direct sum of the homogeneous parts,
used to construct `SymmetricAlgebra.gradedAlgebra`. -/
protected def GradedAlgebra.ι : M →ₗ[R] ⨁ n : ℕ, ↥(LinearMap.range (ι R M) ^ n) :=
  DirectSum.lof R ℕ (fun n ↦ ↥(LinearMap.range (ι R M) ^ n)) 1 ∘ₗ
    (ι R M).codRestrict _ fun m ↦ by simpa only [pow_one] using LinearMap.mem_range_self _ m

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun n : ℕ ↦ ↥(LinearMap.range (ι R M) ^ n)) 1
        ⟨ι R M m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

/-- `SymmetricAlgebra.GradedAlgebra.ι` lifted to the symmetric algebra, used to construct
`SymmetricAlgebra.gradedAlgebra`. -/
def GradedAlgebra.liftι : SymmetricAlgebra R M →ₐ[R] ⨁ n : ℕ, ↥(LinearMap.range (ι R M) ^ n) :=
  lift (GradedAlgebra.ι R M)

theorem GradedAlgebra.liftι_eq (n : ℕ) (x : ↥(LinearMap.range (ι R M) ^ n)) :
    GradedAlgebra.liftι R M x =
      DirectSum.of (fun n : ℕ ↦ ↥(LinearMap.range (ι R M) ^ n)) n x := by
  obtain ⟨x, hx⟩ := x
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
    obtain ⟨_, rfl⟩ := hm
    simp_rw [map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
      DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/-- The symmetric algebra is graded by the powers of the range of `SymmetricAlgebra.ι`. -/
instance gradedAlgebra : GradedAlgebra fun n : ℕ ↦ LinearMap.range (ι R M) ^ n :=
  GradedAlgebra.ofAlgHom _ (GradedAlgebra.liftι R M)
    (by
      ext m
      change DirectSum.coeAlgHom _ (lift (GradedAlgebra.ι R M) (ι R M m)) = ι R M m
      rw [lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of])
    (GradedAlgebra.liftι_eq R M)

end SymmetricAlgebra
