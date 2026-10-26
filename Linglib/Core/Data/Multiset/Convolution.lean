/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Multiset.Bind
public import Mathlib.Algebra.Group.Defs

/-!
# Convolution of multisets

The convolution of two multisets in an additive structure collects the sums `x + y` of an element
of each, with multiplicity, as `MeasureTheory.Measure.conv` does for measures. It distributes over
`+`, and in a commutative monoid it is commutative and associative with unit `{0}`, so it folds
over a multiset of multisets.

## Main definitions

* `Multiset.conv`: the convolution of two multisets.

## Main results

* `Multiset.conv_comm`, `Multiset.conv_assoc`, `Multiset.singleton_zero_conv`: the commutative
  monoid laws.
* `Multiset.map_conv`: a map taking sums to sums of images takes convolutions to convolutions.
* `Multiset.bind_map_product`, `Multiset.bind_conv`: so does a bind taking each combination to a
  convolution.
-/

@[expose] public section

namespace Multiset

variable {M N : Type*}

/-- The convolution of two multisets: the sums of an element of each, with multiplicity. -/
def conv [Add M] (s t : Multiset M) : Multiset M := (s ×ˢ t).map fun x ↦ x.1 + x.2

section Add

variable [Add M] (s t u : Multiset M)

theorem conv_eq_bind : s.conv t = s.bind fun x ↦ t.map (x + ·) := by
  change ((s.bind fun x ↦ t.map (Prod.mk x)).map fun x ↦ x.1 + x.2) = _
  rw [Multiset.map_bind]
  exact bind_congr fun _ _ ↦ by rw [Multiset.map_map]; rfl

@[simp] theorem zero_conv : (0 : Multiset M).conv t = 0 := by simp [conv]

@[simp] theorem conv_zero : s.conv 0 = 0 := by simp [conv]

theorem add_conv : (s + t).conv u = s.conv u + t.conv u := by
  simp [conv_eq_bind]

theorem conv_add : s.conv (t + u) = s.conv t + s.conv u := by
  simp [conv, Multiset.product_add]

@[simp] theorem singleton_conv (x : M) : ({x} : Multiset M).conv t = t.map (x + ·) := by
  simp [conv_eq_bind]

/-- A map taking each sum to a sum of images takes convolutions to convolutions. -/
theorem map_conv [Add N] {f f' g : M → N} (h : ∀ x y, g (x + y) = f x + f' y) :
    (s.conv t).map g = (s.map f).conv (t.map f') := by
  rw [conv, conv, Multiset.map_map, ← Multiset.prodMap_map_product, Multiset.map_map]
  exact map_congr rfl fun x _ ↦ h x.1 x.2

/-- Convolving two binds convolves their values pairwise. -/
theorem bind_conv_bind {A B : Type*} (f : A → Multiset M) (g : B → Multiset M) (S : Multiset A)
    (T : Multiset B) :
    (S.bind f).conv (T.bind g) = S.bind fun a ↦ T.bind fun b ↦ (f a).conv (g b) := by
  rw [conv_eq_bind, bind_assoc]
  refine bind_congr fun a _ ↦ ?_
  simp_rw [map_bind]
  rw [bind_bind]
  exact bind_congr fun b _ ↦ (conv_eq_bind _ _).symm

/-- A bind taking each combination `c x y` to the convolution of the values at `x` and `y` takes
    the combinations of two multisets to the convolution of their binds. -/
theorem bind_map_product {A : Type*} {c : A → A → A} {h : A → Multiset M}
    (hh : ∀ x y, h (c x y) = (h x).conv (h y)) (S T : Multiset A) :
    ((S ×ˢ T).map fun x ↦ c x.1 x.2).bind h = (S.bind h).conv (T.bind h) := by
  rw [bind_conv_bind, bind_map]
  change ((S.bind fun a ↦ T.map (Prod.mk a)).bind _) = _
  rw [bind_assoc]
  exact bind_congr fun a _ ↦ by rw [bind_map]; exact bind_congr fun b _ ↦ hh a b

/-- A bind taking each sum to a convolution takes convolutions to convolutions. -/
theorem bind_conv {A : Type*} [Add A] {h : A → Multiset M}
    (hh : ∀ x y, h (x + y) = (h x).conv (h y)) (S T : Multiset A) :
    (S.conv T).bind h = (S.bind h).conv (T.bind h) :=
  bind_map_product hh S T

end Add

theorem singleton_zero_conv [AddZeroClass M] (s : Multiset M) : ({0} : Multiset M).conv s = s := by
  simp

theorem conv_comm [AddCommMagma M] (s t : Multiset M) : s.conv t = t.conv s := by
  rw [conv_eq_bind, conv_eq_bind, bind_map_comm]
  exact bind_congr fun _ _ ↦ map_congr rfl fun _ _ ↦ add_comm _ _

theorem conv_singleton_zero [AddZeroClass M] (s : Multiset M) :
    s.conv ({0} : Multiset M) = s := by
  simpa [conv_eq_bind] using Multiset.bind_singleton (s := s) id

theorem conv_assoc [AddSemigroup M] (s t u : Multiset M) :
    (s.conv t).conv u = s.conv (t.conv u) := by
  rw [conv_eq_bind, conv_eq_bind, bind_assoc, conv_eq_bind]
  refine bind_congr fun x _ ↦ ?_
  rw [bind_map, conv_eq_bind, map_bind]
  exact bind_congr fun y _ ↦ by rw [Multiset.map_map]; exact map_congr rfl fun z _ ↦ add_assoc ..

theorem conv_left_comm [AddCommSemigroup M] (s t u : Multiset M) :
    s.conv (t.conv u) = t.conv (s.conv u) := by
  rw [← conv_assoc, ← conv_assoc, conv_comm s t]

instance [AddCommSemigroup M] : LeftCommutative (conv (M := M)) := ⟨conv_left_comm⟩

end Multiset
