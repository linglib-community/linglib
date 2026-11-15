/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Sections

/-!
# Multisets in the monoid semiring

A multiset over an additive monoid `M` is an element of the monoid semiring `ℕ[M]`, each element
counted with its multiplicity. The map is additive and
[injective](##AddMonoidAlgebra.ofMultiset_injective), and it takes the multiset of sums `x + y`
of an element of each of two multisets to
[the product](##AddMonoidAlgebra.ofMultiset_map_add_product), and the sums over the sections of
a family to [the product of the family](##AddMonoidAlgebra.ofMultiset_map_sum_sections). An
enumeration built by combining choices can therefore stay a multiset, to be mapped, filtered and
counted, while the laws of the combination and the homomorphisms out of it are those of `ℕ[M]`.
-/

@[expose] public section

noncomputable section

namespace AddMonoidAlgebra

variable {M A ι : Type*}

/-- A multiset over `M` as an element of `ℕ[M]`: the sum of its elements. -/
def ofMultiset : Multiset M →+ ℕ[M] where
  toFun s := (s.map (single · 1)).sum
  map_zero' := by simp
  map_add' s t := by simp

theorem ofMultiset_apply (s : Multiset M) : ofMultiset s = (s.map (single · 1)).sum := rfl

@[simp] theorem ofMultiset_singleton (x : M) : ofMultiset {x} = single x 1 := by
  simp [ofMultiset_apply]

theorem ofMultiset_bind (S : Multiset ι) (h : ι → Multiset M) :
    ofMultiset (S.bind h) = (S.map fun a ↦ ofMultiset (h a)).sum := by
  rw [Multiset.bind, Multiset.join, map_multiset_sum, Multiset.map_map]; rfl

theorem coeff_ofMultiset [DecidableEq M] (s : Multiset M) :
    (ofMultiset s).coeff = Multiset.toFinsupp s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add, map_add, coeff_add, ih, ofMultiset_singleton,
      coeff_single, Multiset.toFinsupp_singleton]

theorem ofMultiset_injective : Function.Injective (ofMultiset (M := M)) := fun s t h ↦ by
  classical
  exact Multiset.toFinsupp.injective (by rw [← coeff_ofMultiset, ← coeff_ofMultiset, h])

/-- The sums of an element of each of two multisets are their product in `ℕ[M]`. -/
theorem ofMultiset_map_add_product [Add M] (s t : Multiset M) :
    ofMultiset ((s ×ˢ t).map fun x ↦ x.1 + x.2) = ofMultiset s * ofMultiset t := by
  rw [ofMultiset_apply, ofMultiset_apply, ofMultiset_apply, Multiset.sum_map_mul_sum_map,
    Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun x _ ↦ by simp [single_mul_single])

/-- Choosing an element of each multiset of a family and adding the choices up gives the product
of the family in `ℕ[M]`. -/
theorem ofMultiset_map_sum_sections [AddCommMonoid M] (s : Multiset (Multiset M)) :
    ofMultiset (s.Sections.map Multiset.sum) = (s.map ofMultiset).prod := by
  induction s using Multiset.induction with
  | empty => simp [one_def]
  | cons m s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← ih, ← ofMultiset_map_add_product]
    simp only [Multiset.sections_cons, Multiset.map_bind, Multiset.map_map, SProd.sprod,
      Multiset.product, Function.comp_def, Multiset.sum_cons]

/-- The lift of a multiplicative map adds up its values over a multiset. -/
theorem lift_ofMultiset [AddMonoid M] [Semiring A] (F : Multiplicative M →* A) (s : Multiset M) :
    lift ℕ A M F (ofMultiset s) = (s.map fun x ↦ F (.ofAdd x)).sum := by
  rw [ofMultiset_apply, map_multiset_sum, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun x _ ↦ by simp)

end AddMonoidAlgebra
