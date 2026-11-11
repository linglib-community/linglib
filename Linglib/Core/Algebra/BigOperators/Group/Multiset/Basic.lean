/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Products over a filtered multiset

The product of `f` over `s.filter p` is the product over `s` of the function that is `f` where
`p` holds and `1` elsewhere, the `Multiset` counterpart of `Finset.prod_filter`. `[UPSTREAM]`
candidate; eventual mathlib home `Mathlib.Algebra.BigOperators.Group.Multiset.Basic`, beside
`Multiset.prod_filter_mul_prod_filter_not`.
-/

public section

namespace Multiset

variable {ι M : Type*} [CommMonoid M] {s : Multiset ι}

@[to_additive]
theorem prod_map_filter (p : ι → Prop) [DecidablePred p] (f : ι → M) :
    ((s.filter p).map f).prod = (s.map fun a ↦ if p a then f a else 1).prod :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by by_cases h : p a <;> simp [h, ih]

end Multiset
