/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# Products of sums over multisets

The product of two multiset sums is the sum of the pairwise products over the cartesian product,
the `Multiset` counterpart of `Finset.sum_mul_sum` followed by `Finset.sum_product'`. An
`[UPSTREAM]` candidate; eventual mathlib home `Mathlib.Algebra.BigOperators.Ring.Multiset`, beside
`Multiset.sum_map_mul_left`.
-/

public section

namespace Multiset

variable {ι κ R : Type*} [NonUnitalNonAssocSemiring R]

/-- The product of two multiset sums is the sum of the pairwise products over the cartesian
product (`Finset.sum_mul_sum` for multisets). -/
theorem sum_map_mul_sum_map (s : Multiset ι) (t : Multiset κ) (f : ι → R) (g : κ → R) :
    (s.map f).sum * (t.map g).sum = ((s ×ˢ t).map fun p ↦ f p.1 * g p.2).sum :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by simp [add_mul, ih, sum_map_mul_left]

end Multiset
