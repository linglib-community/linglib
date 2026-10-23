/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Tactic.Ring

/-!
# The pre-Lie algebra of rooted trees

This file defines `ChapotonLivernet R α`, the free `R`-module on nonplanar rooted trees labelled
by `α`, with the grafting product: `of T * of S` sums the trees obtained by grafting `S` onto one
vertex of `T`. Chapoton and Livernet show that this is the free pre-Lie algebra on `α`. This file
proves that it is a right pre-Lie algebra, from the symmetry of the associator
`UnorderedTree.insertSum_assoc_symm`; freeness is not proved.

## Main definitions

* `ChapotonLivernet R α`: the free module on the trees, a structure over its coefficients
  `coeff : UnorderedTree α →₀ R`, as for `MonoidAlgebra`.
* `ChapotonLivernet.of`: the basis vector of a tree.
* `ChapotonLivernet.graft`: the product of two basis vectors.

## Main results

* `ChapotonLivernet.instRightPreLieRing`, `ChapotonLivernet.instRightPreLieAlgebra`: the grafting
  product is right pre-Lie, and so its commutator is a Lie bracket.
* `ChapotonLivernet.of_mul_of`: `of T * of S = graft T S`.

## Implementation notes

The host comes first, as in Chapoton and Livernet and in Foissy: `of T * of S` grafts `S` onto
`T`, and the associator is symmetric in its last two arguments. The convention that grafts the
first factor onto the second gives a left pre-Lie algebra, `(ChapotonLivernet R α)ᵐᵒᵖ`.

## References

* [chapoton-livernet-2001]
* [foissy-2021]
-/

@[expose] public section

/-- The free module on the nonplanar rooted trees labelled by `α`, which the grafting product
makes a pre-Lie algebra. -/
structure ChapotonLivernet (R : Type*) [Semiring R] (α : Type*) where
  /-- The element with the given coefficients. -/
  ofCoeff ::
  /-- The coefficient of each tree. -/
  coeff : UnorderedTree α →₀ R

namespace ChapotonLivernet

open UnorderedTree

variable {R α : Type*}

section Semiring

variable [Semiring R]

/-- `coeff` as an equivalence with the finitely supported functions on trees. -/
def coeffEquiv : ChapotonLivernet R α ≃ (UnorderedTree α →₀ R) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

@[ext] theorem ext {x y : ChapotonLivernet R α} (h : x.coeff = y.coeff) : x = y := by
  cases x; cases y; cases h; rfl

noncomputable instance instAddCommMonoid : AddCommMonoid (ChapotonLivernet R α) :=
  fast_instance% coeffEquiv.addCommMonoid

/-- `coeff` as an additive equivalence. -/
noncomputable def coeffAddEquiv : ChapotonLivernet R α ≃+ (UnorderedTree α →₀ R) :=
  coeffEquiv.addEquiv

noncomputable instance instModule : Module R (ChapotonLivernet R α) :=
  fast_instance% coeffAddEquiv.module R

@[simp] theorem coeff_zero : (0 : ChapotonLivernet R α).coeff = 0 := rfl

@[simp] theorem coeff_add (x y : ChapotonLivernet R α) : (x + y).coeff = x.coeff + y.coeff := rfl

@[simp] theorem coeff_smul (r : R) (x : ChapotonLivernet R α) : (r • x).coeff = r • x.coeff := rfl

/-- `coeff` as a linear equivalence. -/
noncomputable def coeffLinearEquiv : ChapotonLivernet R α ≃ₗ[R] (UnorderedTree α →₀ R) where
  __ := coeffAddEquiv
  map_smul' _ _ := rfl

/-- `single T r` is `r` times the tree `T`. -/
noncomputable def single (T : UnorderedTree α) (r : R) : ChapotonLivernet R α :=
  ofCoeff (Finsupp.single T r)

@[simp] theorem coeff_single (T : UnorderedTree α) (r : R) :
    (single T r).coeff = Finsupp.single T r := rfl

/-- `of T` is the basis vector of the tree `T`. -/
noncomputable abbrev of (T : UnorderedTree α) : ChapotonLivernet R α := single T 1

/-- `graft T S` sums the basis vectors of the trees in `T ◁ S`. -/
noncomputable def graft (T S : UnorderedTree α) : ChapotonLivernet R α := ((T ◁ S).map of).sum

/-- The grafting product extends `graft` bilinearly. -/
noncomputable instance instMul : Mul (ChapotonLivernet R α) where
  mul x y := x.coeff.sum fun T a => y.coeff.sum fun S b => (a * b) • graft T S

theorem mul_def (x y : ChapotonLivernet R α) :
    x * y = x.coeff.sum fun T a => y.coeff.sum fun S b => (a * b) • graft T S := rfl

noncomputable instance instNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (ChapotonLivernet R α) where
  zero_mul := by simp [mul_def]
  mul_zero := by simp [mul_def]
  left_distrib := by
    classical simp [mul_def, mul_add, add_smul, Finsupp.sum_add, Finsupp.sum_add_index]
  right_distrib := by
    classical simp [mul_def, add_mul, add_smul, Finsupp.sum_add, Finsupp.sum_add_index]

theorem single_mul_single (T S : UnorderedTree α) (a b : R) :
    single T a * single S b = (a * b) • graft T S := by
  simp [mul_def, single]

@[elab_as_elim]
theorem induction_linear {motive : ChapotonLivernet R α → Prop} (x : ChapotonLivernet R α)
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (single : ∀ T r, motive (single T r)) : motive x :=
  Finsupp.induction_linear (motive := fun f => motive (ofCoeff f)) x.coeff zero
    (fun _ _ => add _ _) single

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem single_eq_smul_of (T : UnorderedTree α) (r : R) :
    (single T r : ChapotonLivernet R α) = r • of T := by
  ext; simp [single]

instance instIsScalarTower : IsScalarTower R (ChapotonLivernet R α) (ChapotonLivernet R α) where
  smul_assoc r x y := by
    classical simp [mul_def, Finsupp.sum_smul_index, Finsupp.smul_sum, mul_smul]

instance instSMulCommClass : SMulCommClass R (ChapotonLivernet R α) (ChapotonLivernet R α) where
  smul_comm r x y := by
    classical
    simp [mul_def, Finsupp.sum_smul_index, Finsupp.smul_sum, mul_smul]
    exact Finsupp.sum_congr fun _ _ => Finsupp.sum_congr fun _ _ => smul_comm _ _ _

theorem of_mul_of (T S : UnorderedTree α) : (of T : ChapotonLivernet R α) * of S = graft T S := by
  rw [single_mul_single, mul_one, one_smul]

theorem graft_mul_of (T S U : UnorderedTree α) :
    graft T S * (of U : ChapotonLivernet R α) = (((T ◁ S).bind (· ◁ U)).map of).sum := by
  rw [graft, ← Multiset.sum_map_mul_right, Multiset.map_bind, Multiset.sum_bind]
  simp only [of_mul_of, graft]

theorem of_mul_graft (T S U : UnorderedTree α) :
    (of T : ChapotonLivernet R α) * graft S U = (((S ◁ U).bind (T ◁ ·)).map of).sum := by
  rw [graft, ← Multiset.sum_map_mul_left, Multiset.map_bind, Multiset.sum_bind]
  simp only [of_mul_of, graft]

theorem of_leaf_mul_of_leaf (a b : α) :
    (of (leaf a) : ChapotonLivernet R α) * of (leaf b) = of (mk (.node a [.leaf b])) := by
  rw [of_mul_of, graft, leaf, mk_insertSum, RoseTree.insertSum_leaf, Multiset.map_singleton,
    Multiset.map_singleton, Multiset.sum_singleton]

end CommSemiring

section CommRing

variable [CommRing R]

noncomputable instance instAddCommGroup : AddCommGroup (ChapotonLivernet R α) :=
  fast_instance% coeffEquiv.addCommGroup

noncomputable instance instNonUnitalNonAssocRing :
    NonUnitalNonAssocRing (ChapotonLivernet R α) where

private theorem associator_of_symm (T S U : UnorderedTree α) :
    associator (of T : ChapotonLivernet R α) (of S) (of U) = associator (of T) (of U) (of S) := by
  rw [associator_apply, associator_apply, sub_eq_sub_iff_add_eq_add, of_mul_of, of_mul_of,
    of_mul_of, of_mul_of, graft_mul_of, graft_mul_of, of_mul_graft, of_mul_graft,
    ← Multiset.sum_add, ← Multiset.sum_add, ← Multiset.map_add, ← Multiset.map_add,
    insertSum_assoc_symm]

private theorem associator_single (T S U : UnorderedTree α) (a b c : R) :
    associator (single T a : ChapotonLivernet R α) (single S b) (single U c) =
      (a * b * c) • associator (of T : ChapotonLivernet R α) (of S) (of U) := by
  rw [single_eq_smul_of T, single_eq_smul_of S, single_eq_smul_of U]
  simp only [associator_apply, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  ring_nf

noncomputable instance instRightPreLieRing : RightPreLieRing (ChapotonLivernet R α) where
  assoc_symm' x y z := by
    simp only [← AddMonoidHom.associator_apply]
    induction x using induction_linear with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add x₁ x₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
    | single T a =>
      induction y using induction_linear with
      | zero => simp only [map_zero, AddMonoidHom.zero_apply]
      | add y₁ y₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
      | single S b =>
        induction z using induction_linear with
        | zero => simp only [map_zero, AddMonoidHom.zero_apply]
        | add z₁ z₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
        | single U c =>
          simp only [AddMonoidHom.associator_apply]
          rw [associator_single T S U, associator_single T U S, associator_of_symm,
            mul_right_comm]

noncomputable instance instRightPreLieAlgebra : RightPreLieAlgebra R (ChapotonLivernet R α) where

/-- The commutator of the grafting product is a Lie bracket. -/
noncomputable example : LieAlgebra R (ChapotonLivernet R α) := inferInstance

example (x y : ChapotonLivernet R α) : ⁅x, y⁆ = x * y - y * x := rfl

end CommRing

/-- On three leaves the associator is the single tree whose root carries the second and third
leaves as children. -/
example : associator (of (leaf 0) : ChapotonLivernet ℤ ℕ) (of (leaf 1)) (of (leaf 2)) =
    of (mk (.node 0 [.leaf 2, .leaf 1])) := by
  rw [associator_apply, of_leaf_mul_of_leaf, of_leaf_mul_of_leaf, of_mul_of, of_mul_of, graft,
    graft, mk_insertSum, mk_insertSum, RoseTree.insertSum_leaf,
    show RoseTree.insertSum (.node 0 [.leaf 1]) (.leaf 2) =
      {.node 0 [.leaf 2, .leaf 1], .node 0 [.node 1 [.leaf 2]]} from by decide]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    Multiset.insert_eq_cons]
  exact add_sub_cancel_right _ _

/-- The grafting product is not associative. -/
example : (of (leaf 0) : ChapotonLivernet ℤ ℕ) * of (leaf 1) * of (leaf 2) ≠
    of (leaf 0) * (of (leaf 1) * of (leaf 2)) := by
  rw [of_leaf_mul_of_leaf, of_leaf_mul_of_leaf, of_mul_of, of_mul_of, graft, graft, mk_insertSum,
    mk_insertSum, RoseTree.insertSum_leaf,
    show RoseTree.insertSum (.node 0 [.leaf 1]) (.leaf 2) =
      {.node 0 [.leaf 2, .leaf 1], .node 0 [.node 1 [.leaf 2]]} from by decide]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    Multiset.insert_eq_cons]
  intro h
  have h := congrArg coeff (add_eq_right.mp h)
  rw [coeff_single, coeff_zero] at h
  exact one_ne_zero (Finsupp.single_eq_zero.mp h)

end ChapotonLivernet
