/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Multiset.Convolution
public import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# Products of sums over multisets

The product of two multiset sums is the sum of the pairwise products over the cartesian product,
the `Multiset` counterpart of `Finset.sum_mul_sum` followed by `Finset.sum_product'`. A map that
takes sums to products therefore takes the sum over a convolution `Multiset.conv` to the product
of the two sums. The first is an `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Algebra.BigOperators.Ring.Multiset`, beside `Multiset.sum_map_mul_left`.
-/

public section

namespace Multiset

variable {ι κ M R : Type*} [NonUnitalNonAssocSemiring R]

theorem sum_map_mul_sum_map (s : Multiset ι) (t : Multiset κ) (f : ι → R) (g : κ → R) :
    (s.map f).sum * (t.map g).sum = ((s ×ˢ t).map fun p ↦ f p.1 * g p.2).sum :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by simp [add_mul, ih, sum_map_mul_left]

/-- A map taking sums to products takes the sum over a convolution to the product of the sums. -/
theorem sum_map_conv [Add M] (s t : Multiset M) {f : M → R} (hf : ∀ x y, f (x + y) = f x * f y) :
    ((s.conv t).map f).sum = (s.map f).sum * (t.map f).sum := by
  rw [sum_map_mul_sum_map, conv, map_map]
  exact congrArg sum (map_congr rfl fun x _ ↦ hf x.1 x.2)

end Multiset
