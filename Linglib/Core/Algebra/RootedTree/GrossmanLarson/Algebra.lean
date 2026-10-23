/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.PruningDuality
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The Grossman–Larson algebra

This file proves that the Grossman–Larson product is associative, makes `GrossmanLarson R α` an
`R`-algebra, and maps the pre-Lie algebra of trees into it as a Lie algebra.

## Main results

* `UnorderedTree.productMultiset_assoc`: the product is associative on basis forests.
* `GrossmanLarson.product_assoc`: `(x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)`.
* `GrossmanLarson.instSemiring`, `GrossmanLarson.instAlgebra`, `GrossmanLarson.instRing`.
* `GrossmanLarson.ιLie`: the one-tree forests as a map of Lie algebras from the commutator of the
  grafting product to the commutator of the Grossman–Larson product. It extends to the map
  `UniversalEnvelopingAlgebra.lift R ιLie` from the enveloping algebra.

## Implementation notes

Associativity is proved over `ℤ` by duality: the product is the transpose of the pruning
coproduct under the symmetry-weighted pairing (`Coproduct/PruningDuality.lean`), which is
coassociative, and over `ℤ` the pairing separates points. The structure constants are natural
numbers, so the `ℤ` case is an identity of multisets of forests, which gives associativity over
every commutative semiring.

## TODO

* `UniversalEnvelopingAlgebra.lift R ιLie` is an isomorphism: Oudom and Guin's identification of
  their product with the enveloping algebra. Injectivity needs the Poincaré–Birkhoff–Witt theorem.

## References

* [grossman-larson-1989]
* [oudom-guin-2008]
* [foissy-2021]
-/

@[expose] public section

open UnorderedTree

namespace GrossmanLarson

open ConnesKreimer

variable {α : Type*}

private theorem product_assoc_int [DecidableEq α] (x y z : ConnesKreimer ℤ (UnorderedTree α)) :
    product (product x y) z = product x (product y z) :=
  ext_pairing_right fun w ↦ congr($(pairing_product_assoc x y z) w)

variable {R : Type*} [CommSemiring R]

private theorem product_product_of' (F G H : Forest (UnorderedTree α)) :
    product (product (of' F) (of' G)) (of' (R := R) H) =
      (((productMultiset F G).bind (productMultiset · H)).map of').sum := by
  change product.flip (of' H) (product (of' F) (of' G)) = _
  rw [product_of'_of', map_multiset_sum, Multiset.map_map, Multiset.map_bind, Multiset.sum_bind]
  simp

private theorem product_of'_product (F G H : Forest (UnorderedTree α)) :
    product (of' F) (product (of' G) (of' (R := R) H)) =
      (((productMultiset G H).bind (productMultiset F ·)).map of').sum := by
  rw [product_of'_of' G, map_multiset_sum, Multiset.map_map, Multiset.map_bind, Multiset.sum_bind]
  simp

end GrossmanLarson

namespace UnorderedTree

variable {α : Type*}

/-- The Grossman–Larson product is associative on basis forests, multiplicities included. -/
theorem productMultiset_assoc (F G H : Multiset (UnorderedTree α)) :
    (productMultiset F G).bind (productMultiset · H) =
      (productMultiset G H).bind (productMultiset F ·) := by
  classical
  refine ConnesKreimer.sum_map_of'_injective (R := ℤ) ?_
  simp only
  rw [← GrossmanLarson.product_product_of', ← GrossmanLarson.product_of'_product,
    GrossmanLarson.product_assoc_int]

end UnorderedTree

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- The Grossman–Larson product is associative. -/
theorem product_assoc (x y z : ConnesKreimer R (UnorderedTree α)) :
    product (product x y) z = product x (product y z) := by
  have h₁ (F G : Forest (UnorderedTree α)) :
      product (product (of' (R := R) F) (of' G)) = (product (of' F)).comp (product (of' G)) :=
    lhom_ext' fun H ↦ by
      rw [LinearMap.comp_apply, product_product_of', product_of'_product, productMultiset_assoc]
  have h₂ (F : Forest (UnorderedTree α)) (w : ConnesKreimer R (UnorderedTree α)) :
      (product.flip w).comp (product (of' F)) = (product (of' F)).comp (product.flip w) :=
    lhom_ext' fun G ↦ LinearMap.congr_fun (h₁ F G) w
  have h₃ (w y : ConnesKreimer R (UnorderedTree α)) :
      (product.flip w).comp (product.flip y) = product.flip (product y w) :=
    lhom_ext' fun F ↦ LinearMap.congr_fun (h₂ F w) y
  exact LinearMap.congr_fun (h₃ z y) x

noncomputable instance instSemiring : Semiring (GrossmanLarson R α) where
  mul_assoc x y z := ext (product_assoc x.toConnesKreimer y.toConnesKreimer z.toConnesKreimer)

noncomputable instance instAlgebra : Algebra R (GrossmanLarson R α) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

section Ring

variable {R : Type*} [CommRing R]

noncomputable instance instNeg : Neg (GrossmanLarson R α) := ⟨fun x ↦ ⟨-x.toConnesKreimer⟩⟩

noncomputable instance instSub : Sub (GrossmanLarson R α) :=
  ⟨fun x y ↦ ⟨x.toConnesKreimer - y.toConnesKreimer⟩⟩

@[simp] theorem toConnesKreimer_neg (x : GrossmanLarson R α) :
    (-x).toConnesKreimer = -x.toConnesKreimer := rfl

@[simp] theorem toConnesKreimer_sub (x y : GrossmanLarson R α) :
    (x - y).toConnesKreimer = x.toConnesKreimer - y.toConnesKreimer := rfl

noncomputable instance instAddCommGroup : AddCommGroup (GrossmanLarson R α) :=
  fast_instance% toConnesKreimer_injective.addCommGroup _ rfl toConnesKreimer_add
    toConnesKreimer_neg toConnesKreimer_sub (fun _ _ ↦ rfl) fun _ _ ↦ rfl

noncomputable instance instRing : Ring (GrossmanLarson R α) where

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The one-tree forests as a map of Lie algebras: the commutator of two trees in the
Grossman–Larson algebra is the commutator of their grafting products. -/
noncomputable def ιLie : ChapotonLivernet R α →ₗ⁅R⁆ GrossmanLarson R α :=
  { ι with
    map_lie' := fun {x y} ↦ ext <| by
      change (ι (x * y - y * x)).toConnesKreimer = (ι x * ι y - ι y * ι x).toConnesKreimer
      rw [map_sub, toConnesKreimer_sub, toConnesKreimer_sub, toConnesKreimer_ι_mul,
        toConnesKreimer_ι_mul, toConnesKreimer_ι_mul_ι, toConnesKreimer_ι_mul_ι,
        mul_comm (ι y).toConnesKreimer]
      abel }

@[simp] theorem ιLie_apply (x : ChapotonLivernet R α) : ιLie x = ι x := rfl

end Ring

end GrossmanLarson
