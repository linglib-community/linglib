/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Bialgebra
public import Linglib.Core.RingTheory.Bialgebra.Primitive

/-!
# Dual-primitive functionals on the Connes–Kreimer bialgebra

A linear functional on the Connes–Kreimer bialgebra is a dual primitive exactly when it vanishes
on every forest that is not a single tree. The delta functionals `δ_T = lcoeff R {T}` of the trees
are dual primitives, and the commutator of two of them counts single cuts. The symmetry-weighted
pairing sends the primitive elements of the Grossman–Larson bialgebra to dual primitives, and it
maps the pre-Lie algebra of rooted trees to the Lie algebra of dual primitives. Chapoton and
Livernet observe this identification with the Lie algebra that Connes and Kreimer find dual to
their Hopf algebra.

## Main definitions

* `GrossmanLarson.pairingLie`: the pairing as a map of Lie algebras from the pre-Lie algebra of
  rooted trees to `Bialgebra.dualPrimitives`.

## Main results

* `ConnesKreimer.isDualPrimitive_iff`: the dual primitives are the functionals supported on
  single trees.
* `ConnesKreimer.lie_lcoeff_singleton_apply_ofTree`,
  `ConnesKreimer.lie_lcoeff_singleton_apply_of'`: the commutator `⁅δ_{T₁}, δ_{T₂}⁆` takes a tree
  `T` to the number of single cuts of `T` with crown `T₁` and trunk `T₂` minus the number with
  crown `T₂` and trunk `T₁`, and vanishes on every other forest.
* `ConnesKreimer.autCard_mul_autCard_mul_countSingleCutsRho`: Hoffman's relation between the
  single cuts of `T` with crown `T₁` and trunk `T₂` and the graftings of `T₁` onto `T₂` that give
  `T`, each weighted by numbers of symmetries.
* `GrossmanLarson.isDualPrimitive_pairing`, `GrossmanLarson.pairingLie_injective`: pairing with a
  primitive element is a dual primitive, and in characteristic zero the pre-Lie algebra of trees
  embeds in the dual primitives.

## Implementation notes

The product `δ_{T₁} ⋆ δ_{T₂}` is not a combination of the `δ_T`: on the forest `{T₁, T₂}` it takes
the value `1`, or `2` when the trees are equal (`ConnesKreimer.convMul_lcoeff_singleton_apply_mul`).
Only the commutator is a dual primitive.

The grafting product puts the host first and the pruning coproduct puts the crown first, so the
pairing reverses products. `GrossmanLarson.pairingLie` is therefore defined on the opposite
pre-Lie algebra `(ChapotonLivernet R α)ᵐᵒᵖ`, whose product grafts the first factor onto the
second, as Connes and Kreimer's does.

## References

* [connes-kreimer-1998]
* [chapoton-livernet-2001]
* [hoffman-2003]
-/

@[expose] public section

open UnorderedTree

namespace ConnesKreimer

open Bialgebra WithConv

variable {R α : Type*}

section CommSemiring

variable [CommSemiring R] {f : ConnesKreimer R (UnorderedTree α) →ₗ[R] R}
  {F : Forest (UnorderedTree α)}

theorem isDualPrimitive_iff :
    IsDualPrimitive R f ↔ ∀ F : Forest (UnorderedTree α), F.card ≠ 1 → f (of' F) = 0 := by
  refine ⟨fun hf F hF ↦ ?_, fun h ↦ ?_⟩
  · induction F using Multiset.induction with
    | empty => simpa using hf.map_one_eq_zero
    | cons T F _ =>
      rw [of'_cons]
      exact hf.map_mul_eq_zero (counit_ofTree T)
        (by simp [coalgebra_counit_apply, show F ≠ 0 by simpa using hF])
  · have h₁ : f 1 = 0 := by simpa using h 0
    have key : (LinearMap.mul R _).compr₂ f =
        f.smulRight (Coalgebra.counit (R := R)) + (Coalgebra.counit (R := R)).smulRight f := by
      refine lhom_ext' fun F ↦ lhom_ext' fun G ↦ ?_
      obtain rfl | hF := eq_or_ne F 0
      · simp [h₁]
      obtain rfl | hG := eq_or_ne G 0
      · simp [coalgebra_counit_apply, hF]
      have hFG : (F + G).card ≠ 1 := by
        have := Multiset.card_pos.2 hF
        have := Multiset.card_pos.2 hG
        rw [Multiset.card_add]
        omega
      simp [coalgebra_counit_apply, ← of'_add, hF, hG, h _ hFG]
    exact ⟨h₁, fun a b ↦ by simpa using congr($key a b)⟩

theorem isDualPrimitive_lcoeff_singleton (T : UnorderedTree α) :
    IsDualPrimitive R (lcoeff R ({T} : Forest (UnorderedTree α))) := by
  classical
  refine isDualPrimitive_iff.2 fun F hF ↦ ?_
  rw [lcoeff_apply, coeff_of', ite_eq_right]
  rintro rfl
  simp at hF

theorem isDualPrimitive_lcoeff_iff [Nontrivial R] :
    IsDualPrimitive R (lcoeff R F) ↔ F.card = 1 := by
  refine ⟨fun h ↦ by_contra fun hF ↦ one_ne_zero (α := R) ?_, fun hF ↦ ?_⟩
  · simpa [of'] using isDualPrimitive_iff.1 h F hF
  · obtain ⟨T, rfl⟩ := Multiset.card_eq_one.1 hF
    exact isDualPrimitive_lcoeff_singleton T

variable [DecidableEq α] (T T₁ T₂ : UnorderedTree α)

theorem convMul_lcoeff_singleton_apply_ofTree :
    (toConv (lcoeff R {T₁}) * toConv (lcoeff R ({T₂} : Forest (UnorderedTree α)))) (ofTree T) =
      countSingleCutsRho T T₁ T₂ := by
  rw [LinearMap.convMul_apply, coalgebra_comul_apply, comulAlgHomN_apply_ofTree, comulTreeN,
    comulTreeNG]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply, ofTree, lcoeff_apply, ← of'_zero,
    coeff_of', Multiset.singleton_inj, ite_zero_mul_ite_zero, one_mul,
    Multiset.zero_ne_singleton, ite_false, mul_zero, zero_add]
  rw [countSingleCutsRho, Multiset.countP_eq_card_filter, ← Multiset.sum_map_filter,
    Multiset.map_const', Multiset.sum_replicate, nsmul_one]

theorem convMul_lcoeff_singleton_apply_mul :
    (toConv (lcoeff R {T₁}) * toConv (lcoeff R ({T₂} : Forest (UnorderedTree α))))
        (ofTree T₁ * ofTree T₂) = if T₁ = T₂ then 2 else 1 := by
  rw [(isDualPrimitive_lcoeff_singleton T₁).convMul_apply_mul
    (isDualPrimitive_lcoeff_singleton T₂)]
  simp only [coalgebra_counit_apply, lcoeff_apply, ← of'_singleton, coeff_of',
    Multiset.singleton_inj]
  obtain rfl | h := eq_or_ne T₁ T₂
  · simp [one_add_one_eq_two]
  · simp [h, h.symm]

end CommSemiring

section CommRing

variable [CommRing R] (T T₁ T₂ : UnorderedTree α)

theorem lie_lcoeff_singleton_apply_of' {F : Forest (UnorderedTree α)} (hF : F.card ≠ 1) :
    ⁅toConv (lcoeff R {T₁}), toConv (lcoeff R ({T₂} : Forest (UnorderedTree α)))⁆ (of' F) = 0 :=
  isDualPrimitive_iff.1
    ((isDualPrimitive_lcoeff_singleton T₁).lie (isDualPrimitive_lcoeff_singleton T₂)) F hF

theorem lie_lcoeff_singleton_apply_ofTree [DecidableEq α] :
    ⁅toConv (lcoeff R {T₁}), toConv (lcoeff R ({T₂} : Forest (UnorderedTree α)))⁆ (ofTree T) =
      (countSingleCutsRho T T₁ T₂ : R) - countSingleCutsRho T T₂ T₁ := by
  simp only [Ring.lie_def, ofConv_sub, LinearMap.sub_apply,
    convMul_lcoeff_singleton_apply_ofTree]

end CommRing

end ConnesKreimer

/-! ### The pairing with the pre-Lie algebra of trees -/

namespace GrossmanLarson

open ConnesKreimer Bialgebra WithConv MulOpposite

variable {R α : Type*} [DecidableEq α]

section CommSemiring

variable [CommSemiring R]

theorem isDualPrimitive_pairing {x : GrossmanLarson R α} (hx : IsPrimitiveElem R x) :
    IsDualPrimitive R (pairing (R := R) x.toConnesKreimer) := by
  have h (z : ConnesKreimer R (UnorderedTree α)) :
      (pairing (R := R) ∘ₗ linearEquiv.toLinearMap).flip z = pairing z ∘ₗ linearEquiv.toLinearMap :=
    LinearMap.ext fun _ ↦ pairing_symm _ _
  exact hx.isDualPrimitive (p := pairing ∘ₗ linearEquiv.toLinearMap)
    (fun a ↦ (pairing_symm 1 a).trans (pairing_one_right a)) (fun _ ↦ pairing_one_right _)
    fun z w ↦ by simp only [h, toConv_pairing_mul]

theorem isPrimitiveElem_of_iff [CharZero R] {F : Forest (UnorderedTree α)} :
    IsPrimitiveElem R (of F : GrossmanLarson R α) ↔ F.card = 1 := by
  refine ⟨fun h ↦ by_contra fun hF ↦ (forestAutCard_pos F).ne' ?_, fun hF ↦ ?_⟩
  · simpa using isDualPrimitive_iff.1 (isDualPrimitive_pairing h) F hF
  · obtain ⟨T, rfl⟩ := Multiset.card_eq_one.1 hF
    exact isPrimitiveElem_of_singleton T

end CommSemiring

theorem _root_.ConnesKreimer.autCard_mul_autCard_mul_countSingleCutsRho
    (T T₁ T₂ : UnorderedTree α) :
    autCard T₁ * autCard T₂ * countSingleCutsRho T T₁ T₂ = (T₂ ◁ T₁).count T * autCard T := by
  have hL : pairing (R := ℕ) (product (ofTree T₂) (ofTree T₁)) (ofTree T) =
      (T₂ ◁ T₁).count T * autCard T := by
    have h : ({T₂} + {T₁} : Forest (UnorderedTree α)) ≠ {T} := fun h ↦ by
      simpa using congrArg Multiset.card h
    rw [product_ofTree_ofTree, insertion_ofTree_ofTree, map_add, LinearMap.add_apply,
      ← of'_singleton T, ← of'_singleton T₂, ← of'_singleton T₁, ← of'_add, pairing_of'_of',
      ite_eq_right h, zero_add, pairing_apply_of', forestAutCard_singleton]
    congr 1
    rw [← Multiset.count_map_eq_count' _ _ fun _ _ ↦ Multiset.singleton_inj.1,
      ← Nat.cast_id (Multiset.count _ _), ← coeff_sum_map_of', Multiset.map_map]
    rfl
  have hR : (toConv (pairing (ofTree T₁)) * toConv (pairing (ofTree T₂)) :
      WithConv (ConnesKreimer ℕ (UnorderedTree α) →ₗ[ℕ] ℕ)) (ofTree T) =
      autCard T₁ * autCard T₂ * countSingleCutsRho T T₁ T₂ := by
    rw [← of'_singleton T₁, ← of'_singleton T₂, pairing_of', pairing_of', toConv_smul,
      toConv_smul, smul_mul_smul_comm, ofConv_smul, LinearMap.smul_apply,
      convMul_lcoeff_singleton_apply_ofTree, forestAutCard_singleton, forestAutCard_singleton]
    simp
  rw [← hR, ← toConv_pairing_product]
  exact hL

section CommRing

variable [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The pairing as a map of Lie algebras from the left pre-Lie algebra of rooted trees, in which
the first factor is grafted onto the second, to the dual primitives of the Connes–Kreimer
bialgebra. It sends a tree `T` to `|Aut T| • δ_T`. -/
noncomputable def pairingLie :
    (ChapotonLivernet R α)ᵐᵒᵖ →ₗ⁅R⁆ dualPrimitives R (ConnesKreimer R (UnorderedTree α)) where
  toFun x := ⟨toConv (pairing (R := R) (ι x.unop).toConnesKreimer),
    isDualPrimitive_pairing (isPrimitiveElem_ι _)⟩
  map_add' x y := Subtype.ext <| by simp
  map_smul' r x := Subtype.ext <| by simp
  map_lie' {x y} := Subtype.ext <| by
    change toConv (pairing (R := R) (ι ⁅y.unop, x.unop⁆).toConnesKreimer) =
      ⁅toConv (pairing (ι x.unop).toConnesKreimer), toConv (pairing (ι y.unop).toConnesKreimer)⁆
    rw [← ιLie_apply ⁅y.unop, x.unop⁆, LieHom.map_lie, Ring.lie_def, Ring.lie_def]
    simp [← toConv_pairing_product]

@[simp] theorem coe_pairingLie (x : (ChapotonLivernet R α)ᵐᵒᵖ) :
    (pairingLie x : WithConv (ConnesKreimer R (UnorderedTree α) →ₗ[R] R)) =
      toConv (pairing (ι x.unop).toConnesKreimer) := rfl

theorem coe_pairingLie_op_of (T : UnorderedTree α) :
    (pairingLie (R := R) (op (.of T)) : WithConv (ConnesKreimer R (UnorderedTree α) →ₗ[R] R)) =
      (autCard T : R) • toConv (lcoeff R {T}) := by
  rw [coe_pairingLie, unop_op, ι_of, toConnesKreimer_of, pairing_of', forestAutCard_singleton,
    toConv_smul]

theorem pairingLie_injective [CharZero R] [NoZeroDivisors R] :
    Function.Injective (pairingLie (R := R) (α := α)) := fun _ _ h ↦
  unop_injective <| ι_injective <| GrossmanLarson.ext <|
    ext_pairing_right fun z ↦ congr($(congrArg Subtype.val h) z)

end CommRing

end GrossmanLarson
