/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# The Rees algebra of the filtration by products of elements of a submodule

For a submodule `M` of an algebra `A`, `Submodule.rees M` is the subalgebra of `A[X]` of the
polynomials whose coefficient of `X ^ k` is a sum of products of at most `k` elements of `M`. It
is the Rees algebra of the filtration of `A` by the powers of `1 ⊔ M`; its quotient by `X` is the
associated graded algebra. `reesAlgebra` is the analogous object for the powers of an ideal of a
commutative ring.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace Submodule

open Polynomial

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (M : Submodule R A)

/-- The Rees algebra of the filtration by the powers of `1 ⊔ M`: the polynomials whose
coefficient of `X ^ k` is a sum of products of at most `k` elements of `M`. -/
def rees : Subalgebra R A[X] where
  carrier := {p | ∀ k, p.coeff k ∈ (1 ⊔ M) ^ k}
  mul_mem' := fun {p q} hp hq k ↦ by
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun x hx ↦ ?_
    rw [← Finset.mem_antidiagonal.mp hx, pow_add]
    exact Submodule.mul_mem_mul (hp _) (hq _)
  add_mem' := fun {p q} hp hq k ↦ by rw [coeff_add]; exact add_mem (hp k) (hq k)
  algebraMap_mem' := fun r k ↦ by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      rw [pow_zero]
      exact Submodule.mem_one.mpr ⟨r, rfl⟩
    · exact zero_mem _

variable {M}

theorem mem_rees {p : A[X]} : p ∈ M.rees ↔ ∀ k, p.coeff k ∈ (1 ⊔ M) ^ k := Iff.rfl

theorem C_mul_X_mem_rees {x : A} (hx : x ∈ M) : C x * X ∈ M.rees :=
  mem_rees.2 fun k ↦ by
    rw [coeff_C_mul_X]
    split_ifs with h
    · subst h
      rw [pow_one]
      exact Submodule.mem_sup_right hx
    · exact zero_mem _

end Submodule
