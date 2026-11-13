/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Tensors of multiset sums

A pure tensor with a multiset sum in one slot is the multiset sum of the pure tensors, the
`Multiset` counterparts of `TensorProduct.sum_tmul` and `TensorProduct.tmul_sum`; with a sum in
each slot it is the sum over the product of the two multisets. `[UPSTREAM]`
candidates; eventual mathlib home `Mathlib.LinearAlgebra.TensorProduct.Defs`.
-/

public section

namespace TensorProduct

open scoped TensorProduct

variable {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N]

/-- A multiset sum in the left slot of a pure tensor comes out (`TensorProduct.sum_tmul` for
multisets). -/
theorem sum_map_tmul (s : Multiset ι) (f : ι → M) (n : N) :
    (s.map f).sum ⊗ₜ[R] n = (s.map fun i ↦ f i ⊗ₜ[R] n).sum :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by simp [add_tmul, ih]

/-- A multiset sum in the right slot of a pure tensor comes out (`TensorProduct.tmul_sum` for
multisets). -/
theorem tmul_sum_map (m : M) (s : Multiset ι) (g : ι → N) :
    m ⊗ₜ[R] (s.map g).sum = (s.map fun i ↦ m ⊗ₜ[R] g i).sum :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by simp [tmul_add, ih]

/-- Multiset sums in both slots of a pure tensor come out as one sum over the product. -/
theorem sum_map_tmul_sum_map (s : Multiset ι) (t : Multiset κ) (f : ι → M) (g : κ → N) :
    (s.map f).sum ⊗ₜ[R] (t.map g).sum = ((s ×ˢ t).map fun p ↦ f p.1 ⊗ₜ[R] g p.2).sum :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by
    rw [Multiset.map_cons, Multiset.sum_cons, add_tmul, ih, tmul_sum_map]
    simp

end TensorProduct
