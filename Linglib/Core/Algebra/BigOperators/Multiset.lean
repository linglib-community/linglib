/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Multiset.Bind

/-!
# Products over filters and cartesian products of multisets

`[UPSTREAM]` candidates, absent from mathlib: the `Multiset` analogues of `Finset.prod_filter`
and `Finset.sum_mul_sum`.
-/

@[expose] public section

namespace Multiset

@[to_additive /-- The sum over a filter is the sum of the indicator (`Finset.sum_filter`
analogue). -/]
theorem prod_map_filter {ι M : Type*} [CommMonoid M] (p : ι → Prop) [DecidablePred p]
    (f : ι → M) (s : Multiset ι) :
    ((s.filter p).map f).prod = (s.map fun a ↦ if p a then f a else 1).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => by_cases h : p a <;> simp [h, ih]

theorem sum_map_product_mul {α β M : Type*} [NonUnitalNonAssocSemiring M]
    (s : Multiset α) (t : Multiset β) (f : α → M) (g : β → M) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum = (s.map f).sum * (t.map g).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [Multiset.map_map,
        show (fun p => f p.1 * g p.2) ∘ (Prod.mk a) = (fun b => f a * g b) from rfl,
        ← Multiset.sum_map_mul_left]

end Multiset
