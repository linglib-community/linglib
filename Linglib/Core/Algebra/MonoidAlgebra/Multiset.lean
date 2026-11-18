/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Multiset.Sections

/-!
# Multisets in a monoid semiring

A multiset over an additive monoid `M` is an element of the monoid semiring `R[M]`, each element
counted with its multiplicity. The map is additive, and
[injective](##AddMonoidAlgebra.ofMultiset_injective) in characteristic zero. It takes the sums
`x + y` of an element of each of two multisets to
[the product](##AddMonoidAlgebra.ofMultiset_map_add_product), and the sums over the sections of a
family to [the product of the family](##AddMonoidAlgebra.ofMultiset_map_sum_sections). An
enumeration built by combining choices can therefore stay a multiset, to be mapped, filtered and
counted, while the laws of the combination and the homomorphisms out of it are those of `R[M]`.
-/

@[expose] public section

noncomputable section

namespace AddMonoidAlgebra

variable (R : Type*) {M A ι : Type*} [Semiring R]

/-- A multiset over `M` as an element of `R[M]`: the sum of its elements. -/
def ofMultiset : Multiset M →+ R[M] where
  toFun s := (s.map (single · 1)).sum
  map_zero' := by simp
  map_add' s t := by simp

variable {R}

theorem ofMultiset_apply (s : Multiset M) : ofMultiset R s = (s.map (single · 1)).sum := rfl

@[simp] theorem ofMultiset_singleton (x : M) : ofMultiset R {x} = single x 1 := by
  simp [ofMultiset_apply]

theorem ofMultiset_bind (S : Multiset ι) (h : ι → Multiset M) :
    ofMultiset R (S.bind h) = (S.map fun a ↦ ofMultiset R (h a)).sum := by
  rw [Multiset.bind, Multiset.join, map_multiset_sum, Multiset.map_map]; rfl

/-- The coefficient of an element is its multiplicity. -/
theorem coeff_ofMultiset [DecidableEq M] (s : Multiset M) (m : M) :
    (ofMultiset R s).coeff m = s.count m := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add, coeff_add, Finsupp.add_apply, ih, ofMultiset_singleton,
      coeff_single, Finsupp.single_apply, Multiset.singleton_add, Multiset.count_cons]
    rw [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_comm]
    simp only [eq_comm (a := a)]

variable (R) in
theorem ofMultiset_injective [CharZero R] : Function.Injective (ofMultiset R (M := M)) :=
  fun s t h ↦ by
    classical
    exact Multiset.ext.mpr fun m ↦ Nat.cast_injective (R := R) <| by
      rw [← coeff_ofMultiset, ← coeff_ofMultiset, h]

/-- The sums of an element of each of two multisets are their product in `R[M]`. -/
theorem ofMultiset_map_add_product [Add M] (s t : Multiset M) :
    ofMultiset R ((s ×ˢ t).map fun x ↦ x.1 + x.2) = ofMultiset R s * ofMultiset R t := by
  rw [ofMultiset_apply, ofMultiset_apply, ofMultiset_apply, Multiset.sum_map_mul_sum_map,
    Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun x _ ↦ by simp [single_mul_single])

/-- Choosing an element of each multiset of a family and adding the choices up gives the product
of the family in `ℕ[M]`. -/
theorem ofMultiset_map_sum_sections {R : Type*} [CommSemiring R] [AddCommMonoid M]
    (s : Multiset (Multiset M)) :
    ofMultiset R (s.Sections.map Multiset.sum) = (s.map (ofMultiset R)).prod := by
  induction s using Multiset.induction with
  | empty => simp [one_def]
  | cons m s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← ih, ← ofMultiset_map_add_product]
    simp only [Multiset.sections_cons, Multiset.map_bind, Multiset.map_map, SProd.sprod,
      Multiset.product, Function.comp_def, Multiset.sum_cons]

/-- The lift of a multiplicative map adds up its values over a multiset. -/
theorem lift_ofMultiset {R : Type*} [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A]
    (F : Multiplicative M →* A) (s : Multiset M) :
    lift R A M F (ofMultiset R s) = (s.map fun x ↦ F (.ofAdd x)).sum := by
  rw [ofMultiset_apply, map_multiset_sum, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun x _ ↦ by simp)

end AddMonoidAlgebra
