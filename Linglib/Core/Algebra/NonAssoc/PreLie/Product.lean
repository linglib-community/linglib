/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.Enveloping

/-!
# The product of Oudom and Guin

For a right pre-Lie algebra `L` over a commutative ring `R`, the product of the enveloping
algebra of its commutator Lie algebra, carried to the symmetric algebra `S(L)` along
`RightPreLieAlgebra.equivSymmetricAlgebra`, is the product of [oudom-guin-2008],
`RightPreLieAlgebra.product`. It is associative with unit `1`, and multiplying on the right by an
element of `L` is the action: `a ⋆ X = a * ι X + D_X a` (`RightPreLieAlgebra.product_ι`). On a
monomial it is the symmetric brace of the action, `a ⋆ (X₁ ⋯ Xₙ) = a{X₁, …, Xₙ}`
(`RightPreLieAlgebra.product_prod_ι`).

## References

* [oudom-guin-2008]
-/

@[expose] public section

noncomputable section

namespace RightPreLieAlgebra

open SymmetricAlgebra RightPreLieRing

variable (R : Type*) {L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]

/-! ### The product of Oudom and Guin -/

/-- The product of Oudom and Guin on the symmetric algebra: the product of the enveloping
algebra, carried along `equivSymmetricAlgebra`. -/
def product : SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L :=
  ((LinearMap.mul R (UniversalEnvelopingAlgebra R L)).compl₁₂
    (equivSymmetricAlgebra R).symm.toLinearMap (equivSymmetricAlgebra R).symm.toLinearMap).compr₂
    (equivSymmetricAlgebra R).toLinearMap

theorem product_apply (a b : SymmetricAlgebra R L) :
    product R a b = equivSymmetricAlgebra R
      ((equivSymmetricAlgebra R).symm a * (equivSymmetricAlgebra R).symm b) := rfl

/-- The equivalence carries the product of the enveloping algebra to `product`. -/
theorem equivSymmetricAlgebra_mul (u v : UniversalEnvelopingAlgebra R L) :
    equivSymmetricAlgebra R (u * v) =
      product R (equivSymmetricAlgebra R u) (equivSymmetricAlgebra R v) := by
  rw [product_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem equivSymmetricAlgebra_symm_one :
    (equivSymmetricAlgebra R).symm (1 : SymmetricAlgebra R L) = 1 :=
  (LinearEquiv.symm_apply_eq _).mpr (toSymmetricAlgebra_one R).symm

theorem equivSymmetricAlgebra_symm_ι (X : L) :
    (equivSymmetricAlgebra R).symm (ι R L X) = UniversalEnvelopingAlgebra.ι R X :=
  (LinearEquiv.symm_apply_eq _).mpr (toSymmetricAlgebra_ι R X).symm

/-- The product of Oudom and Guin is associative. -/
theorem product_assoc (a b c : SymmetricAlgebra R L) :
    product R (product R a b) c = product R a (product R b c) := by
  simp only [product_apply, LinearEquiv.symm_apply_apply, mul_assoc]

@[simp] theorem product_one_left (a : SymmetricAlgebra R L) : product R 1 a = a := by
  rw [product_apply, equivSymmetricAlgebra_symm_one, one_mul, LinearEquiv.apply_symm_apply]

@[simp] theorem product_one_right (a : SymmetricAlgebra R L) : product R a 1 = a := by
  rw [product_apply, equivSymmetricAlgebra_symm_one, mul_one, LinearEquiv.apply_symm_apply]

/-- The product with an element of `L` is its action: `a ⋆ X = a X + D_X a`. -/
theorem product_ι (a : SymmetricAlgebra R L) (X : L) :
    product R a (ι R L X) = a * ι R L X + derivation R X a := by
  rw [product_apply, equivSymmetricAlgebra_symm_ι, equivSymmetricAlgebra_apply,
    toSymmetricAlgebra_mul_ι, ← equivSymmetricAlgebra_apply, LinearEquiv.apply_symm_apply,
    act_apply]

/-- The recursion of the product in its second argument: `a ⋆ (b X) = (a ⋆ b) ⋆ X - a ⋆ D_X b`. -/
theorem product_mul_ι (a b : SymmetricAlgebra R L) (X : L) :
    product R a (b * ι R L X) =
      product R (product R a b) (ι R L X) - product R a (derivation R X b) := by
  rw [product_assoc, product_ι R b, map_add, add_sub_cancel_right]

/-- On `L` the product is the commutative product plus the pre-Lie product. -/
theorem product_ι_ι (X Y : L) :
    product R (ι R L X) (ι R L Y) = ι R L X * ι R L Y + ι R L (X * Y) := by
  rw [product_ι, derivation_ι]

/-- The commutator of the product on `L` is the commutator of the pre-Lie product. -/
theorem product_ι_ι_sub (X Y : L) :
    product R (ι R L X) (ι R L Y) - product R (ι R L Y) (ι R L X) = ι R L (X * Y - Y * X) := by
  rw [product_ι_ι, product_ι_ι, mul_comm (ι R L Y), map_sub]
  abel

/-! ### The brace formula -/

/-- The action as a biadditive map, the form in which `RightPreLieRing.braceWith` takes it. -/
def actAddHom : L →+ SymmetricAlgebra R L →+ SymmetricAlgebra R L :=
  AddMonoidHom.mk' (fun X ↦ (act R X).toAddMonoidHom) fun X Y ↦ by rw [map_add]; rfl

theorem actAddHom_apply (X : L) (a : SymmetricAlgebra R L) :
    actAddHom R X a = a * ι R L X + derivation R X a := rfl

theorem isRightLieAction_actAddHom : IsRightLieAction (actAddHom R (L := L)) :=
  fun a Y Z ↦ act_act R a Y Z

/-- The derivation of `X` on a monomial multiplies each of its factors in turn by `X`. -/
theorem derivation_prod_ι (X : L) (M : Multiset L) :
    derivation R X (M.map (ι R L)).prod =
      ((M.mulOnce X).map fun D ↦ (D.map (ι R L)).prod).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, ih, derivation_ι,
      Multiset.mulOnce_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
    simp only [smul_eq_mul, Function.comp_def, Multiset.map_cons, Multiset.prod_cons,
      Multiset.sum_map_mul_left]
    ring

/-- The product with a monomial is the symmetric brace of the action:
`a ⋆ (X₁ ⋯ Xₙ) = a{X₁, …, Xₙ}`. -/
theorem product_prod_ι (a : SymmetricAlgebra R L) (M : Multiset L) :
    product R a (M.map (ι R L)).prod = braceWith (actAddHom R) a M := by
  induction hc : Multiset.card M using Nat.strong_induction_on generalizing M with | _ k ih =>
  rcases Multiset.empty_or_exists_mem M with rfl | ⟨y, hy⟩
  · rw [Multiset.map_zero, Multiset.prod_zero, product_one_right, braceWith_zero]
  · obtain ⟨M, rfl⟩ := Multiset.exists_cons_of_mem hy
    have hM : Multiset.card M < k := by rw [← hc, Multiset.card_cons]; exact Nat.lt_succ_self _
    rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, product_mul_ι,
      braceWith_cons (isRightLieAction_actAddHom R), derivation_prod_ι, map_multiset_sum,
      Multiset.map_map, ih _ hM M rfl, product_ι, actAddHom_apply]
    refine congrArg _ (congrArg _ (Multiset.map_congr rfl fun D hD ↦ ?_))
    exact ih _ (by rwa [Multiset.card_of_mem_mulOnce hD]) D rfl

end RightPreLieAlgebra
