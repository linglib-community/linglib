/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.OudomGuin
public import Linglib.Core.Algebra.RootedTree.Coproduct.AdmissibleCutDuality
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Pairing
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The Grossman–Larson algebra

The Grossman–Larson product is [associative](##GrossmanLarson.product_assoc), which makes
`GrossmanLarson R α` an `R`-algebra, and the one-tree forests are
[a map of Lie algebras](##GrossmanLarson.ιLie) from the commutator of the grafting product to the
commutator of the Grossman–Larson product; it extends to the map
`UniversalEnvelopingAlgebra.lift R ιLie` from the enveloping algebra. Associativity gives the rule
for [grafting onto a grafting](##UnorderedTree.insertionMultiset_bind_insertionMultiset_singleton),
by which the braces of the pre-Lie algebra of trees are
[the graftings of several trees at once](##ChapotonLivernet.brace_of).
The product is [the product of Oudom and Guin](##GrossmanLarson.product_eq_oudomGuin) on the
symmetric algebra of the pre-Lie algebra of trees.

## Implementation notes

Associativity is proved over `ℕ` by duality: the product is the transpose of the Connes–Kreimer
coproduct under the symmetry-weighted pairing (`Coproduct/AdmissibleCutDuality.lean`), which is
coassociative, and over `ℕ` an element is determined by its pairings. The structure constants are
natural numbers, so the `ℕ` case is an identity of multisets of forests, which gives associativity
over every commutative semiring.

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

private theorem product_assoc_nat [DecidableEq α] (x y z : ConnesKreimer ℕ (UnorderedTree α)) :
    product (product x y) z = product x (product y z) :=
  pairing_injective (pairing_product_assoc x y z)

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
  refine ConnesKreimer.sum_map_of'_injective (R := ℕ) ?_
  simp only
  rw [← GrossmanLarson.product_product_of', ← GrossmanLarson.product_of'_product,
    GrossmanLarson.product_assoc_nat]

theorem productMultiset_singleton (W : Multiset (UnorderedTree α)) (X : UnorderedTree α) :
    productMultiset W {X} = (X ::ₘ W) ::ₘ insertionMultiset W {X} := by
  rw [productMultiset, ← Multiset.cons_zero, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp only [insertionMultiset_zero_right, Multiset.map_singleton, Prod.map_apply, id,
    Multiset.cons_bind, Multiset.singleton_bind, Multiset.cons_zero, Multiset.singleton_add,
    add_zero, Multiset.map_id']
  rw [add_comm, Multiset.singleton_add, add_comm W, Multiset.singleton_add]

/-- The forests of `F ⋆ G` with as many trees as `F` are the graftings of all of `G` onto `F`. -/
theorem filter_card_productMultiset (F G : Multiset (UnorderedTree α)) :
    (productMultiset F G).filter (fun W ↦ Multiset.card W = Multiset.card F) =
      insertionMultiset F G := by
  classical
  have h0 : ∀ p ∈ G.antidiagonal.filter fun p ↦ ¬Multiset.card p.1 = 0,
      ((insertionMultiset F p.2).map (· + p.1)).filter
        (fun W ↦ Multiset.card W = Multiset.card F) = 0 := fun p hp ↦ by
    refine Multiset.filter_eq_nil.mpr fun W hW ↦ ?_
    obtain ⟨Y, hY, rfl⟩ := Multiset.mem_map.mp hW
    have := (Multiset.mem_filter.mp hp).2
    rw [Multiset.card_add, insertionMultiset_card_eq F p.2 hY]
    omega
  rw [productMultiset, Multiset.filter_bind,
    ← Multiset.filter_add_not (fun p ↦ Multiset.card p.1 = 0) G.antidiagonal, Multiset.add_bind,
    Multiset.bind_congr h0, Multiset.bind_zero, add_zero,
    Multiset.filter_card_fst_eq_antidiagonal, Multiset.powersetCard_zero_left,
    Multiset.map_singleton, Multiset.singleton_bind]
  simp only [tsub_zero, add_zero, Multiset.map_id']
  exact Multiset.filter_eq_self.mpr fun W hW ↦ insertionMultiset_card_eq F G hW

/-- Grafting `G` onto `F` and then `X` onto the result grafts `X` onto a vertex of `F` or onto
a vertex of a tree of `G`: the rule `(A ∘ B) ∘ X = A ∘ (B X) + A ∘ (B ∘ X)` of Oudom and Guin. -/
theorem insertionMultiset_bind_insertionMultiset_singleton (F G : Multiset (UnorderedTree α))
    (X : UnorderedTree α) :
    (insertionMultiset F G).bind (insertionMultiset · {X}) =
      insertionMultiset F (X ::ₘ G) + (insertionMultiset G {X}).bind (insertionMultiset F ·) := by
  have h := congrArg (Multiset.filter fun W ↦ Multiset.card W = Multiset.card F)
    (productMultiset_assoc F G {X})
  have h1 : ∀ W ∈ (productMultiset F G).filter fun W ↦ Multiset.card W = Multiset.card F,
      (productMultiset W {X}).filter (fun V ↦ Multiset.card V = Multiset.card F) =
        insertionMultiset W {X} := fun W hW ↦ by
    have hc := (Multiset.mem_filter.mp hW).2
    rw [productMultiset_singleton, Multiset.filter_cons_of_neg _ (by simp [hc])]
    exact Multiset.filter_eq_self.mpr fun V hV ↦ (insertionMultiset_card_eq W {X} hV).trans hc
  have h2 : ∀ W ∈ (productMultiset F G).filter fun W ↦ ¬Multiset.card W = Multiset.card F,
      (productMultiset W {X}).filter (fun V ↦ Multiset.card V = Multiset.card F) = 0 :=
    fun W hW ↦ by
      have hc := (Multiset.mem_filter.mp hW).2
      have hle := card_le_of_mem_productMultiset (Multiset.mem_filter.mp hW).1
      refine Multiset.filter_eq_nil.mpr fun V hV ↦ ?_
      rw [productMultiset_singleton, Multiset.mem_cons] at hV
      obtain rfl | hV := hV
      · rw [Multiset.card_cons]; omega
      · rw [insertionMultiset_card_eq W {X} hV]; exact hc
  rw [Multiset.filter_bind,
    ← Multiset.filter_add_not (fun W ↦ Multiset.card W = Multiset.card F) (productMultiset F G),
    Multiset.add_bind, Multiset.bind_congr h1, Multiset.bind_congr h2, Multiset.bind_zero,
    add_zero, filter_card_productMultiset, Multiset.filter_bind, productMultiset_singleton,
    Multiset.cons_bind] at h
  simpa only [filter_card_productMultiset] using h

/-- Grafting `G` onto `T` and then `X` onto the result grafts `X` onto a vertex of `T` or onto
a vertex of a tree of `G`. -/
theorem insertion_bind_insertSum (T : UnorderedTree α) (G : Multiset (UnorderedTree α))
    (X : UnorderedTree α) :
    (insertion T G).bind (· ◁ X) =
      insertion T (X ::ₘ G) + (insertionMultiset G {X}).bind (insertion T ·) := by
  refine Multiset.map_injective (fun _ _ ↦ Multiset.singleton_inj.1) ?_
  have h := insertionMultiset_bind_insertionMultiset_singleton {T} G X
  simp only [insertionMultiset_singleton, Multiset.bind_map] at h
  rw [Multiset.map_bind, Multiset.map_add, Multiset.map_bind]
  exact h

end UnorderedTree

namespace ChapotonLivernet

variable {R : Type*} [CommRing R] {α : Type*}

/-- In the pre-Lie algebra of rooted trees the brace of a tree and a multiset of trees sums the
graftings of the trees of the multiset onto vertices of the tree. -/
theorem brace_of (T : UnorderedTree α) (M : Multiset (UnorderedTree α)) :
    RightPreLieRing.brace (of T : ChapotonLivernet R α) (M.map of) =
      ((insertion T M).map of).sum := by
  induction hn : Multiset.card M using Nat.strong_induction_on generalizing M with | _ n ih =>
  obtain rfl | ⟨X, hX⟩ := M.empty_or_exists_mem
  · simp [insertion_zero]
  obtain ⟨B, rfl⟩ := Multiset.exists_cons_of_mem hX
  subst hn
  have hB : ((insertionMultiset B {X}).map fun B' ↦
        RightPreLieRing.brace (of T : ChapotonLivernet R α) (B'.map of)) =
      (insertionMultiset B {X}).map fun B' ↦ ((insertion T B').map of).sum :=
    Multiset.map_congr rfl fun B' hB' ↦
      ih _ (by rw [insertionMultiset_card_eq B {X} hB', Multiset.card_cons]; omega) B' rfl
  rw [Multiset.map_cons, RightPreLieRing.brace_cons, ih _ (by simp) B rfl,
    ← sum_map_insertionMultiset_singleton (RightPreLieRing.brace_sum_cons _) B X
      fun T' _ ↦ (of_mul_of T' X).symm,
    hB, ← Multiset.sum_map_mul_right, sub_eq_iff_eq_add]
  simp only [of_mul_of]
  rw [← Multiset.sum_bind, ← Multiset.sum_bind, ← Multiset.map_bind, ← Multiset.map_bind,
    ← Multiset.sum_add, ← Multiset.map_add, insertion_bind_insertSum]

end ChapotonLivernet

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
      rw [product_assoc, eq_sub_iff_add_eq, ← map_add, ← insertion_ofTree, product_apply (of' E),
        comulPrim_ofTree]
      simp [mul_comm, add_comm]
    rw [of'_cons, mul_comm, hGL, OudomGuin.product_mul_ofTree, ChapotonLivernet.basis_apply,
      ih E hE', hD, hstep]

end Ring

end GrossmanLarson
