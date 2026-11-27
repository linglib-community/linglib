/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations and powers of a submodule

A derivation of a commutative algebra that preserves a submodule preserves its powers, by the
Leibniz rule.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem mem_pow_of_forall_mem (D : Derivation R A A) {N : Submodule R A}
    (hN : ∀ a ∈ N, D a ∈ N) {n : ℕ} {a : A} (ha : a ∈ N ^ n) : D a ∈ N ^ n := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [Derivation.map_algebraMap]; exact zero_mem _
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem ((pow_succ' N i).symm ▸ Submodule.mul_mem_mul hm ih)
      ((pow_succ N i).symm ▸ Submodule.mul_mem_mul hx (hN m hm))

end Derivation
