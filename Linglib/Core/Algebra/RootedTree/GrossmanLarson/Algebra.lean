/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.OudomGuin
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The Grossman–Larson algebra

The Grossman–Larson product is [associative](##GrossmanLarson.product_assoc), which makes
`GrossmanLarson R α` an `R`-algebra, and the one-tree forests are
[a map of Lie algebras](##GrossmanLarson.ιLie) from the commutator of the grafting product to the
commutator of the Grossman–Larson product; it extends to the map
`UniversalEnvelopingAlgebra.lift R ιLie` from the enveloping algebra. The product is
[the product of Oudom and Guin](##GrossmanLarson.product_eq_oudomGuin) on the symmetric algebra
of the pre-Lie algebra of trees.

## Implementation notes

Associativity is that of the product of Oudom and Guin, which holds in the symmetric algebra of
every pre-Lie algebra. The two products agree over a commutative ring because both satisfy the
recursion `(x ⋆ E) ⋆ X = x ⋆ (E X) + x ⋆ (E ∘ X)` in the last tree of the right factor. The
structure constants are natural numbers, so associativity over `ℤ` is an identity of multisets of
forests, `UnorderedTree.productMultiset_assoc`, which gives it over every commutative semiring.

## TODO

* `UniversalEnvelopingAlgebra.lift R ιLie` is an isomorphism: Oudom and Guin's identification of
  their product with the enveloping algebra. The product has the commutative product as its
  leading term, so surjectivity is by induction on the number of trees; injectivity needs the
  ordered monomials in the trees to span the enveloping algebra, and not their independence.

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

section Ring

variable {R : Type*} [CommRing R]

/-! ### The Grossman–Larson product as the product of Oudom and Guin -/

/-- Grafting one tree onto a forest is the derivation of the forests that grafts it onto one
tree. -/
theorem insertion_ofTree (y : ConnesKreimer R (UnorderedTree α)) (X : UnorderedTree α) :
    insertion y (ofTree X) =
      OudomGuin.derivation (ChapotonLivernet.basis R α) (.of X) y := by
  refine LinearMap.congr_fun (lhom_ext' (f := insertion.flip (ofTree X))
    (g := (OudomGuin.derivation (ChapotonLivernet.basis R α) (.of X) :
      ConnesKreimer R (UnorderedTree α) →ₗ[R] _)) fun F ↦ ?_) y
  rw [LinearMap.flip_apply, Derivation.coeFn_coe, ← of'_singleton, insertion_of'_of']
  induction F using Multiset.induction_on with
  | empty =>
    rw [insertionMultiset_zero_left_of_ne_zero _ (Multiset.singleton_ne_zero X), of'_zero,
      Derivation.map_one_eq_zero]
    rfl
  | cons T F ih =>
    rw [insertionMultiset_cons_singleton, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map, of'_cons, Derivation.leibniz, ← ih, OudomGuin.derivation_ofTree,
      ChapotonLivernet.basis_apply, ChapotonLivernet.of_mul_of, map_multiset_sum,
      Multiset.map_map, smul_eq_mul, smul_eq_mul, ← Multiset.sum_map_mul_left,
      ← Multiset.sum_map_mul_left, add_comm]
    refine congrArg₂ _ (congrArg _ (Multiset.map_congr rfl fun G _ ↦ ?_))
      (congrArg _ (Multiset.map_congr rfl fun T' _ ↦ ?_))
    · rw [Function.comp_apply, of'_cons]
    · rw [Function.comp_apply, Function.comp_apply, ← ChapotonLivernet.basis_apply,
        OudomGuin.incl_basis, of'_cons, mul_comm]

/-- The Grossman–Larson product is the product of Oudom and Guin on the symmetric algebra of the
pre-Lie algebra of rooted trees. -/
theorem product_eq_oudomGuin :
    (product : LinearMap.BilinMap R (ConnesKreimer R (UnorderedTree α)) _) =
      OudomGuin.product (ChapotonLivernet.basis R α) := by
  refine LinearMap.ext fun x ↦ ?_
  have hstep (w : ConnesKreimer R (UnorderedTree α)) (X : UnorderedTree α) :
      product w (ofTree X) = OudomGuin.product (ChapotonLivernet.basis R α) w (ofTree X) := by
    rw [OudomGuin.product_ofTree, ChapotonLivernet.basis_apply, ← insertion_ofTree,
      product_apply, comulPrim_ofTree]
    simp [mul_comm, add_comm]
  suffices h : ∀ n (E : Forest (UnorderedTree α)), Multiset.card E = n →
      product x (of' E) = OudomGuin.product (ChapotonLivernet.basis R α) x (of' E) from
    lhom_ext' fun E ↦ h _ E rfl
  intro n
  induction n with
  | zero =>
    intro E hE
    obtain rfl := Multiset.card_eq_zero.mp hE
    simp [product_one_right]
  | succ n ih =>
    intro E hE
    obtain ⟨X, hX⟩ := (Multiset.card_pos_iff_exists_mem (s := E)).mp (by omega)
    obtain ⟨E, rfl⟩ := Multiset.exists_cons_of_mem hX
    have hE' : Multiset.card E = n := by simpa using hE
    have hD := OudomGuin.eqOn_derivation_of' (ChapotonLivernet.basis R α) ih (.of X) E hE'
    have hGL : product x (of' E * ofTree X) =
        product (product x (of' E)) (ofTree X) -
          product x (OudomGuin.derivation (ChapotonLivernet.basis R α) (.of X) (of' E)) := by
      rw [product_product_ofTree, insertion_ofTree, of'_cons, mul_comm, add_sub_cancel_right]
    rw [of'_cons, mul_comm, hGL, OudomGuin.product_mul_ofTree, ChapotonLivernet.basis_apply,
      ih E hE', hD, hstep]

end Ring

end GrossmanLarson

namespace UnorderedTree

variable {α : Type*}

/-- The Grossman–Larson product is associative on basis forests, multiplicities included. -/
theorem productMultiset_assoc (F G H : Multiset (UnorderedTree α)) :
    (productMultiset F G).bind (productMultiset · H) =
      (productMultiset G H).bind (productMultiset F ·) := by
  refine ConnesKreimer.sum_map_of'_injective (R := ℤ) ?_
  simp only
  rw [← GrossmanLarson.product_product_of', ← GrossmanLarson.product_of'_product,
    GrossmanLarson.product_eq_oudomGuin, OudomGuin.product_assoc]

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

/-- The one-tree forests are the pre-Lie algebra of trees in its symmetric algebra. -/
theorem toConnesKreimer_ι (x : ChapotonLivernet R α) :
    (ι x).toConnesKreimer = OudomGuin.incl (ChapotonLivernet.basis R α) x := by
  have h : linearEquiv.toLinearMap ∘ₗ ι = OudomGuin.incl (ChapotonLivernet.basis R α) :=
    (ChapotonLivernet.basis R α).ext fun T ↦ by
      rw [OudomGuin.incl_basis, LinearMap.comp_apply, ChapotonLivernet.basis_apply, ι_of]
      rfl
  exact LinearMap.congr_fun h x

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The one-tree forests as a map of Lie algebras: the commutator of two trees in the
Grossman–Larson algebra is the commutator of their grafting products. -/
noncomputable def ιLie : ChapotonLivernet R α →ₗ⁅R⁆ GrossmanLarson R α :=
  { ι with
    map_lie' := fun {x y} ↦ ext <| by
      change (ι (x * y - y * x)).toConnesKreimer = (ι x * ι y - ι y * ι x).toConnesKreimer
      rw [toConnesKreimer_sub, toConnesKreimer_mul, toConnesKreimer_mul, toConnesKreimer_ι,
        toConnesKreimer_ι, toConnesKreimer_ι, product_eq_oudomGuin,
        OudomGuin.product_incl_incl_sub] }

@[simp] theorem ιLie_apply (x : ChapotonLivernet R α) : ιLie x = ι x := rfl

end Ring

end GrossmanLarson
