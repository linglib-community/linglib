/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Multiset
public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Algebra.RootedTree.PreLie.ChapotonLivernet
public import Linglib.Core.Algebra.RootedTree.PreLie.InsertionUnordered
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The Grossman–Larson product

This file defines the Grossman–Larson product on the free module of forests of nonplanar rooted
trees. The product `F ⋆ G` sums, over the splits `G = G₁ + G₂`, the forests obtained by grafting
the trees of `G₂` onto vertices of `F` in all ways, with the trees of `G₁` placed alongside.
Grossman and Larson introduce the product; the closed form used here is Foissy's Theorem 5.1,
through the Guin–Oudom extension of the grafting product.

The module of forests is `ConnesKreimer R (UnorderedTree α)`, which Oudom and Guin read as the
symmetric algebra on the trees: its own product is the disjoint union of forests. The insertion
`x ∘ y` and the product `x ⋆ y` are bilinear maps on it, and the algebra `GrossmanLarson R α` is
that module with `⋆` as its multiplication.

## Main definitions

* `UnorderedTree.productMultiset F G`: the forests in the product `F ⋆ G`, with multiplicity.
* `GrossmanLarson.insertion`: the Guin–Oudom extension `x ∘ y` of the grafting product, grafting
  every tree of `y` onto a vertex of `x`.
* `GrossmanLarson.product`: the Grossman–Larson product `x ⋆ y`.
* `GrossmanLarson R α`: the forests with the product `⋆`.
* `GrossmanLarson.ι`: the pre-Lie algebra of trees as the one-tree forests.

## Main results

* `GrossmanLarson.insertion_one_left`, `GrossmanLarson.insertion_of'_add`,
  `GrossmanLarson.counit_insertion`: Oudom and Guin's rules `1 ∘ x = ε(x)`,
  `AB ∘ C = Σ (A ∘ C₍₁₎)(B ∘ C₍₂₎)` and `ε(x ∘ y) = ε(x) ε(y)`, on basis forests for the second.
* `GrossmanLarson.product_of'`: `x ⋆ G = Σ_{G = G₁ + G₂} (x ∘ G₂) G₁`.
* `GrossmanLarson.counit_product`: the counit is multiplicative for `⋆`.
* `GrossmanLarson.instNonAssocSemiring`: the empty forest is a two-sided unit; associativity and
  the `Semiring` and `Algebra` instances are in `GrossmanLarson/Algebra.lean`.
* `GrossmanLarson.toConnesKreimer_ι_mul`, `GrossmanLarson.toConnesKreimer_ι_mul_ι`: on one-tree
  forests, `∘` is the grafting product and `x ⋆ y = x y + x ∘ y`.

## Implementation notes

`GrossmanLarson R α` is a one-field structure over the Connes–Kreimer module, as `WithConv` is
over a module of linear maps: the forests already carry the disjoint-union product, and the
structure keeps the two multiplications on different types. `insertion` and `product` are stated
on the underlying module, where the disjoint-union product is available to state their rules.

The insertion `x ∘ y` grafts every tree of `y` onto the original `x`. It is not iterated one-tree
insertion, which would also graft later trees onto earlier ones.

## References

* [grossman-larson-1989]
* [oudom-guin-2008]
* [foissy-2021]
-/

@[expose] public section

open UnorderedTree

/-! ### Insertion and the product on the module of forests -/

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- The Guin–Oudom extension `x ∘ y` of the grafting product sums, on basis forests, the
graftings of every tree of `G` onto a vertex of `F`. -/
noncomputable def insertion :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  linearLift fun F ↦ linearLift fun G ↦ ((insertionMultiset F G).map of').sum

@[simp] theorem insertion_of'_of' (F G : Forest (UnorderedTree α)) :
    insertion (of' F) (of' G) = ((insertionMultiset F G).map (of' (R := R))).sum := by
  simp [insertion]

@[simp] theorem insertion_one_right (x : ConnesKreimer R (UnorderedTree α)) :
    insertion x 1 = x := by
  refine LinearMap.congr_fun (lhom_ext' (f := insertion.flip 1) (g := .id) fun F ↦ ?_) x
  simp [← of'_zero, insertionMultiset_zero_right]

theorem insertion_one_left (x : ConnesKreimer R (UnorderedTree α)) :
    insertion 1 x = counit x • 1 := by
  refine LinearMap.congr_fun (lhom_ext' (f := insertion 1) (g := counit.toLinearMap.smulRight 1)
    fun G ↦ ?_) x
  rcases eq_or_ne G 0 with rfl | hG
  · simp [← of'_zero, insertionMultiset_zero_right]
  · simp [← of'_zero, insertionMultiset_zero_left_of_ne_zero G hG, counit_of', hG]

@[simp] theorem insertion_ofTree_ofTree (T S : UnorderedTree α) :
    insertion (ofTree (R := R) T) (ofTree S) = ((T ◁ S).map ofTree).sum := by
  rw [← of'_singleton, ← of'_singleton, insertion_of'_of', insertionMultiset_singleton_singleton,
    Multiset.map_map]
  rfl

theorem insertion_of'_add (A B C : Forest (UnorderedTree α)) :
    insertion (of' (A + B)) (of' C) =
      (C.antidiagonal.map fun p ↦
        insertion (of' (R := R) A) (of' p.1) * insertion (of' B) (of' p.2)).sum := by
  rw [insertion_of'_of', insertionMultiset_add_host, Multiset.map_bind, Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  rw [insertion_of'_of', insertion_of'_of', Multiset.map_map,
    ← Multiset.sum_map_product_mul _ _ (of' (R := R)) (of' (R := R))]
  simp [of'_add]

private theorem counit_insertion_of'_of' (F G : Forest (UnorderedTree α)) :
    counit (insertion (of' F) (of' G)) = counit (of' (R := R) F) * counit (of' (R := R) G) := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp [insertion_one_left]
  · rw [insertion_of'_of', map_multiset_sum, Multiset.map_map]
    simp only [Function.comp_def, counit_of', Multiset.card_eq_zero, hF, ↓reduceIte, zero_mul]
    refine Multiset.sum_eq_zero fun r hr ↦ ?_
    obtain ⟨X, hX, rfl⟩ := Multiset.mem_map.mp hr
    simp [insertionMultiset_card_eq F G hX, hF]

theorem counit_insertion (x y : ConnesKreimer R (UnorderedTree α)) :
    counit (insertion x y) = counit x * counit y := by
  have h : (insertion (R := R) (α := α)).compr₂ counit.toLinearMap =
      (LinearMap.mul R R).compl₁₂ counit.toLinearMap counit.toLinearMap :=
    lhom_ext' fun F ↦ lhom_ext' fun G ↦ counit_insertion_of'_of' F G
  exact LinearMap.congr_fun₂ h x y

/-- The Grossman–Larson product `x ⋆ y`, on basis forests the sum over `productMultiset`. -/
noncomputable def product :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  linearLift fun F ↦ linearLift fun G ↦ ((productMultiset F G).map of').sum

@[simp] theorem product_of'_of' (F G : Forest (UnorderedTree α)) :
    product (of' F) (of' G) = ((productMultiset F G).map (of' (R := R))).sum := by
  simp [product]

theorem product_of' (x : ConnesKreimer R (UnorderedTree α)) (G : Forest (UnorderedTree α)) :
    product x (of' G) = (G.antidiagonal.map fun p ↦ insertion x (of' p.2) * of' p.1).sum := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul, Multiset.sum_map_add]
  | single F r =>
    rw [← smul_of', map_smul, LinearMap.smul_apply]
    change r • product (of' (R := R) F) (of' G) =
      (G.antidiagonal.map fun p ↦ insertion (r • of' (R := R) F) (of' p.2) * of' p.1).sum
    rw [product_of'_of', productMultiset,
      Multiset.map_bind, Multiset.sum_bind, Multiset.smul_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
    simp [← Multiset.sum_map_mul_right, Multiset.smul_sum, Multiset.map_map]

theorem product_one_right (x : ConnesKreimer R (UnorderedTree α)) : product x 1 = x := by
  refine LinearMap.congr_fun (lhom_ext' (f := product.flip 1) (g := .id) fun F ↦ ?_) x
  simp [← of'_zero]

theorem product_one_left (x : ConnesKreimer R (UnorderedTree α)) : product 1 x = x := by
  refine LinearMap.congr_fun (lhom_ext' (f := product 1) (g := .id) fun G ↦ ?_) x
  simp [← of'_zero]

private theorem counit_product_of'_of' (F G : Forest (UnorderedTree α)) :
    counit (product (of' F) (of' G)) = counit (of' (R := R) F) * counit (of' (R := R) G) := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp [product_one_left]
  · rw [product_of'_of', map_multiset_sum, Multiset.map_map]
    simp only [Function.comp_def, counit_of', Multiset.card_eq_zero, hF, ↓reduceIte, zero_mul]
    refine Multiset.sum_eq_zero fun r hr ↦ ?_
    obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.mp hr
    have := card_le_of_mem_productMultiset hW
    have := Multiset.card_pos.mpr hF
    simp only [ite_eq_right_iff]
    omega

theorem counit_product (x y : ConnesKreimer R (UnorderedTree α)) :
    counit (product x y) = counit x * counit y := by
  have h : (product (R := R) (α := α)).compr₂ counit.toLinearMap =
      (LinearMap.mul R R).compl₁₂ counit.toLinearMap counit.toLinearMap :=
    lhom_ext' fun F ↦ lhom_ext' fun G ↦ counit_product_of'_of' F G
  exact LinearMap.congr_fun₂ h x y

theorem product_ofTree_ofTree (T S : UnorderedTree α) :
    product (ofTree (R := R) T) (ofTree S) =
      ofTree T * ofTree S + insertion (ofTree T) (ofTree S) := by
  rw [← of'_singleton, ← of'_singleton, product_of'_of', productMultiset_singleton_singleton,
    insertion_of'_of', insertionMultiset_singleton_singleton, ← of'_add]
  simp [Multiset.map_map, Multiset.singleton_add, Multiset.insert_eq_cons]

end GrossmanLarson

/-! ### The Grossman–Larson algebra -/

/-- The forests of nonplanar rooted trees labelled by `α`, with the Grossman–Larson product. -/
structure GrossmanLarson (R : Type*) [CommSemiring R] (α : Type*) where
  /-- The element of the Grossman–Larson algebra with the given underlying forests. -/
  ofConnesKreimer ::
  /-- The underlying element of the module of forests. -/
  toConnesKreimer : ConnesKreimer R (UnorderedTree α)

namespace GrossmanLarson

open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

theorem toConnesKreimer_injective :
    Function.Injective
      (toConnesKreimer : GrossmanLarson R α → ConnesKreimer R (UnorderedTree α)) :=
  fun ⟨_⟩ ⟨_⟩ h ↦ congrArg ofConnesKreimer h

@[ext] theorem ext {x y : GrossmanLarson R α} (h : x.toConnesKreimer = y.toConnesKreimer) :
    x = y :=
  toConnesKreimer_injective h

noncomputable instance instZero : Zero (GrossmanLarson R α) := ⟨⟨0⟩⟩

noncomputable instance instAdd : Add (GrossmanLarson R α) :=
  ⟨fun x y ↦ ⟨x.toConnesKreimer + y.toConnesKreimer⟩⟩

instance instSMul {S : Type*} [SMul S (ConnesKreimer R (UnorderedTree α))] :
    SMul S (GrossmanLarson R α) :=
  ⟨fun s x ↦ ⟨s • x.toConnesKreimer⟩⟩

@[simp] theorem toConnesKreimer_zero : (0 : GrossmanLarson R α).toConnesKreimer = 0 := rfl

@[simp] theorem toConnesKreimer_add (x y : GrossmanLarson R α) :
    (x + y).toConnesKreimer = x.toConnesKreimer + y.toConnesKreimer := rfl

@[simp] theorem toConnesKreimer_smul {S : Type*} [SMul S (ConnesKreimer R (UnorderedTree α))]
    (s : S) (x : GrossmanLarson R α) : (s • x).toConnesKreimer = s • x.toConnesKreimer := rfl

noncomputable instance instAddCommMonoid : AddCommMonoid (GrossmanLarson R α) :=
  fast_instance% toConnesKreimer_injective.addCommMonoid _ rfl toConnesKreimer_add
    fun _ _ ↦ rfl

/-- `toConnesKreimer` as an additive equivalence. -/
noncomputable def addEquiv : GrossmanLarson R α ≃+ ConnesKreimer R (UnorderedTree α) where
  toFun := toConnesKreimer
  invFun := ofConnesKreimer
  map_add' _ _ := rfl

noncomputable instance instModule : Module R (GrossmanLarson R α) :=
  fast_instance% toConnesKreimer_injective.module R addEquiv.toAddMonoidHom fun _ _ ↦ rfl

/-- `toConnesKreimer` as a linear equivalence. -/
noncomputable def linearEquiv : GrossmanLarson R α ≃ₗ[R] ConnesKreimer R (UnorderedTree α) where
  __ := addEquiv
  map_smul' _ _ := rfl

@[simp] theorem linearEquiv_apply (x : GrossmanLarson R α) : linearEquiv x = x.toConnesKreimer :=
  rfl

@[simp] theorem linearEquiv_symm_apply (x : ConnesKreimer R (UnorderedTree α)) :
    linearEquiv.symm x = ofConnesKreimer (R := R) x :=
  rfl

@[simp] theorem toConnesKreimer_multisetSum (s : Multiset (GrossmanLarson R α)) :
    s.sum.toConnesKreimer = (s.map toConnesKreimer).sum :=
  map_multiset_sum linearEquiv s

noncomputable instance instOne : One (GrossmanLarson R α) := ⟨⟨1⟩⟩

@[simp] theorem toConnesKreimer_one : (1 : GrossmanLarson R α).toConnesKreimer = 1 := rfl

noncomputable instance instMul : Mul (GrossmanLarson R α) :=
  ⟨fun x y ↦ ⟨product x.toConnesKreimer y.toConnesKreimer⟩⟩

@[simp] theorem toConnesKreimer_mul (x y : GrossmanLarson R α) :
    (x * y).toConnesKreimer = product x.toConnesKreimer y.toConnesKreimer := rfl

noncomputable instance instNonAssocSemiring : NonAssocSemiring (GrossmanLarson R α) where
  left_distrib _ _ _ := by ext; simp
  right_distrib _ _ _ := by ext; simp
  zero_mul _ := by ext; simp
  mul_zero _ := by ext; simp
  one_mul _ := by ext; simp [product_one_left]
  mul_one _ := by ext; simp [product_one_right]

instance instIsScalarTower : IsScalarTower R (GrossmanLarson R α) (GrossmanLarson R α) where
  smul_assoc _ _ _ := by ext; simp

instance instSMulCommClass : SMulCommClass R (GrossmanLarson R α) (GrossmanLarson R α) where
  smul_comm _ _ _ := by ext; simp

/-! ### The basis -/

/-- `of F` is the basis vector of the forest `F`. -/
noncomputable def of (F : Forest (UnorderedTree α)) : GrossmanLarson R α := ⟨of' F⟩

@[simp] theorem toConnesKreimer_of (F : Forest (UnorderedTree α)) :
    (of (R := R) F).toConnesKreimer = of' F := rfl

@[simp] theorem of_zero : (of 0 : GrossmanLarson R α) = 1 := by ext; simp

theorem of_mul_of (F G : Forest (UnorderedTree α)) :
    (of F : GrossmanLarson R α) * of G = ((productMultiset F G).map of).sum := by
  ext; simp [Multiset.map_map]

theorem lhom_ext {M : Type*} [AddCommMonoid M] [Module R M] {f g : GrossmanLarson R α →ₗ[R] M}
    (h : ∀ F, f (of F) = g (of F)) : f = g :=
  LinearMap.ext fun x ↦ LinearMap.congr_fun (lhom_ext' (f := f ∘ₗ linearEquiv.symm.toLinearMap)
    (g := g ∘ₗ linearEquiv.symm.toLinearMap) h) x.toConnesKreimer

/-! ### Trees as one-tree forests -/

/-- `ι` sends each tree to its one-tree forest. -/
noncomputable def ι : ChapotonLivernet R α →ₗ[R] GrossmanLarson R α :=
  linearEquiv.symm.toLinearMap ∘ₗ (Finsupp.linearCombination R ofTree) ∘ₗ
    ChapotonLivernet.coeffLinearEquiv.toLinearMap

@[simp] theorem ι_of (T : UnorderedTree α) :
    ι (ChapotonLivernet.of T : ChapotonLivernet R α) = of {T} := by
  ext; simp [ι, ChapotonLivernet.coeffLinearEquiv, ChapotonLivernet.coeffAddEquiv,
    ChapotonLivernet.coeffEquiv]

theorem ι_injective : Function.Injective (ι : ChapotonLivernet R α → GrossmanLarson R α) := by
  have h : LinearIndependent R (ofTree : UnorderedTree α → ConnesKreimer R (UnorderedTree α)) :=
    (basisSingleOne (R := R)).linearIndependent.comp _ fun _ _ ↦ Multiset.singleton_inj.1
  exact fun x y hxy ↦
    ChapotonLivernet.coeffLinearEquiv.injective (h (linearEquiv.symm.injective hxy))

theorem toConnesKreimer_ι_mul (x y : ChapotonLivernet R α) :
    (ι (x * y)).toConnesKreimer = insertion (ι x).toConnesKreimer (ι y).toConnesKreimer := by
  induction x using ChapotonLivernet.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single T a =>
    induction y using ChapotonLivernet.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single S b =>
      rw [ChapotonLivernet.single_eq_smul_of T, ChapotonLivernet.single_eq_smul_of S]
      simp [smul_mul_smul_comm, ChapotonLivernet.of_mul_of, ChapotonLivernet.graft,
        map_multiset_sum, Multiset.map_map, smul_smul, mul_comm a b]

theorem toConnesKreimer_ι_mul_ι (x y : ChapotonLivernet R α) :
    (ι x * ι y).toConnesKreimer = (ι x).toConnesKreimer * (ι y).toConnesKreimer +
      insertion (ι x).toConnesKreimer (ι y).toConnesKreimer := by
  induction x using ChapotonLivernet.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]; abel
  | single T a =>
    induction y using ChapotonLivernet.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]; abel
    | single S b =>
      rw [ChapotonLivernet.single_eq_smul_of T, ChapotonLivernet.single_eq_smul_of S]
      simp [smul_mul_smul_comm, product_ofTree_ofTree, smul_add, smul_smul, mul_comm a b]

end GrossmanLarson
