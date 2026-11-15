/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Multiset.Bind
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.WithConv

/-!
# The convolution semiring of multisets

The convolution of two multisets over an additive structure `M` collects the sums `x + y` of an
element of each, with multiplicity. With the sum of multisets as addition it makes the multisets
over an additive monoid a semiring, commutative when `M` is, with unit `{0}`. A convolution over
a family is then a `Multiset.prod` or a `List.prod`, and an additive map of the monoids
[induces a ring homomorphism](##Multiset.convMap).

## Implementation notes

`Multiset M` already carries the sum of multisets, and a pointwise product on it would become a
second addition under `to_additive`, so the product lives on mathlib's synonym
`WithConv (Multiset M)`. The semiring is the monoid semiring `ℕ[M]` through
`Multiset.toFinsupp`; it is kept on multisets so that its elements can be mapped, filtered and
bound without decidable equality on `M`.
-/

@[expose] public section

namespace Multiset

open WithConv

variable {M N : Type*}

section Add

variable [Add M]

/-- The convolution of two multisets: the sums of an element of each, with multiplicity. -/
instance convMul : Mul (WithConv (Multiset M)) where
  mul s t := toConv ((s.ofConv ×ˢ t.ofConv).map fun x ↦ x.1 + x.2)

theorem convMul_def (s t : WithConv (Multiset M)) :
    s * t = toConv ((s.ofConv ×ˢ t.ofConv).map fun x ↦ x.1 + x.2) := rfl

theorem ofConv_mul_eq_bind (s t : WithConv (Multiset M)) :
    (s * t).ofConv = s.ofConv.bind fun x ↦ t.ofConv.map (x + ·) := by
  change ((s.ofConv.bind fun x ↦ t.ofConv.map (Prod.mk x)).map fun x ↦ x.1 + x.2) = _
  rw [map_bind]
  exact bind_congr fun _ _ ↦ by rw [map_map]; rfl

instance convNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (WithConv (Multiset M)) where
  left_distrib s t u := by ext1; simp [convMul_def, product_add]
  right_distrib s t u := by ext1; simp [ofConv_mul_eq_bind]
  zero_mul s := by ext1; simp [convMul_def]
  mul_zero s := by ext1; simp [convMul_def]

@[simp] theorem toConv_singleton_mul (x : M) (s : WithConv (Multiset M)) :
    toConv {x} * s = toConv (s.ofConv.map (x + ·)) := by
  ext1; simp [ofConv_mul_eq_bind]

@[simp] theorem mul_toConv_singleton (s : WithConv (Multiset M)) (x : M) :
    s * toConv {x} = toConv (s.ofConv.map (· + x)) := by
  ext1; simp [ofConv_mul_eq_bind, bind_singleton]

end Add

/-- The multisets `h a` over a multiset of indices add up to the bind. -/
theorem toConv_bind {A : Type*} (S : Multiset A) (h : A → Multiset M) :
    toConv (S.bind h) = (S.map fun a ↦ toConv (h a)).sum := by
  rw [bind, join, toConv_multisetSum, map_map]; rfl

instance convNonUnitalSemiring [AddSemigroup M] : NonUnitalSemiring (WithConv (Multiset M)) where
  mul_assoc s t u := by
    ext1
    rw [ofConv_mul_eq_bind, ofConv_mul_eq_bind, bind_assoc, ofConv_mul_eq_bind]
    refine bind_congr fun x _ ↦ ?_
    rw [bind_map, ofConv_mul_eq_bind, map_bind]
    exact bind_congr fun y _ ↦ by rw [map_map]; exact map_congr rfl fun z _ ↦ add_assoc ..

instance convOne [Zero M] : One (WithConv (Multiset M)) where one := toConv {0}

theorem convOne_def [Zero M] : (1 : WithConv (Multiset M)) = toConv {0} := rfl

instance convSemiring [AddMonoid M] : Semiring (WithConv (Multiset M)) where
  one_mul s := by simp [convOne_def]
  mul_one s := by simp [convOne_def]

instance convCommSemiring [AddCommMonoid M] : CommSemiring (WithConv (Multiset M)) where
  mul_comm s t := by
    ext1
    rw [ofConv_mul_eq_bind, ofConv_mul_eq_bind, bind_map_comm]
    exact bind_congr fun _ _ ↦ map_congr rfl fun _ _ ↦ add_comm _ _

/-- The ring homomorphism of convolution semirings induced by an additive map. -/
def convMap [AddMonoid M] [AddMonoid N] (f : M →+ N) :
    WithConv (Multiset M) →+* WithConv (Multiset N) where
  toFun s := toConv (s.ofConv.map f)
  map_zero' := rfl
  map_one' := by simp [convOne_def]
  map_add' s t := by ext1; simp
  map_mul' s t := by
    ext1
    exact map_map_product_distrib (f' := fun x ↦ x.1 + x.2) (fun a b ↦ _root_.map_add f a b) _ _

@[simp] theorem ofConv_convMap [AddMonoid M] [AddMonoid N] (f : M →+ N)
    (s : WithConv (Multiset M)) : (convMap f s).ofConv = s.ofConv.map f := rfl

end Multiset
