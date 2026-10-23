/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Algebra
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# The Grossman–Larson bialgebra

The Grossman–Larson algebra is a cocommutative bialgebra. Its comultiplication splits a forest
into two subforests in all ways, as in the symmetric algebra on the trees, and its counit takes
the coefficient of the empty forest. The one-tree forests are primitive, and the symmetry-weighted
pairing transposes the product of the Connes–Kreimer algebra to this comultiplication.

## Main definitions

* `GrossmanLarson.instBialgebra`: the bialgebra structure.

## Main results

* `GrossmanLarson.comul_of`: `Δ(F) = ∑_{A + B = F} A ⊗ B`.
* `GrossmanLarson.isPrimitiveElem_ι`: the pre-Lie algebra of trees lies in the primitive elements.
* `GrossmanLarson.toConv_pairing_mul`: `⟨z w, ·⟩ = ⟨z, ·⟩ * ⟨w, ·⟩` in the convolution algebra of
  linear functionals on the Grossman–Larson bialgebra.

## Implementation notes

The coalgebra is the primitive coproduct of `Coproduct/Primitive.lean`, moved along the linear
identification with the Connes–Kreimer module. Its compatibility with the product is Oudom and
Guin's Lemma 3.11, here read off `UnorderedTree.productMultiset_bind_antidiagonal`.

## TODO

The Grossman–Larson bialgebra is graded and connected, so it has an antipode.

## References

* [grossman-larson-1989]
* [oudom-guin-2008]
* [hoffman-2003]
-/

@[expose] public section

open UnorderedTree

namespace GrossmanLarson

open ConnesKreimer Coalgebra WithConv
open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### The coalgebra -/

noncomputable instance instCoalgebra : Coalgebra R (GrossmanLarson R α) :=
  letI : Coalgebra R (ConnesKreimer R (UnorderedTree α)) :=
    { comul := comulPrim.toLinearMap
      counit := ConnesKreimer.counit.toLinearMap
      coassoc := congr(($comulPrim_coassoc).toLinearMap)
      rTensor_counit_comp_comul := congr(($rTensor_counit_comp_comulPrim).toLinearMap)
      lTensor_counit_comp_comul := congr(($lTensor_counit_comp_comulPrim).toLinearMap) }
  linearEquiv.coalgebra R

theorem comul_apply (x : GrossmanLarson R α) :
    comul (R := R) x = TensorProduct.map linearEquiv.symm.toLinearMap linearEquiv.symm.toLinearMap
      (comulPrim x.toConnesKreimer) := rfl

@[simp] theorem counit_apply (x : GrossmanLarson R α) :
    counit (R := R) x = ConnesKreimer.counit x.toConnesKreimer := rfl

theorem comul_of (F : Forest (UnorderedTree α)) :
    comul (R := R) (of F) =
      (F.antidiagonal.map fun p ↦ (of p.1 : GrossmanLarson R α) ⊗ₜ[R] (of p.2 : _)).sum := by
  rw [comul_apply, toConnesKreimer_of, comulPrim_of', map_multiset_sum, Multiset.map_map]
  rfl

instance instIsCocomm : IsCocomm R (GrossmanLarson R α) where
  comm_comp_comul := lhom_ext fun F ↦ by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, comul_of, map_multiset_sum, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_swap_antidiagonal, Multiset.map_map]
    rfl

/-! ### The bialgebra -/

private theorem tmul_sum_map_of (s t : Multiset (Forest (UnorderedTree α))) :
    ((s.map of).sum : GrossmanLarson R α) ⊗ₜ[R] ((t.map of).sum : GrossmanLarson R α) =
      ((s ×ˢ t).map fun q ↦ (of q.1 : GrossmanLarson R α) ⊗ₜ[R] (of q.2 : _)).sum := by
  have h (a b : GrossmanLarson R α) :
      a ⊗ₜ[R] b = (a ⊗ₜ[R] 1) * ((1 : GrossmanLarson R α) ⊗ₜ[R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, ← Algebra.TensorProduct.includeLeft_apply (S := R),
    ← Algebra.TensorProduct.includeRight_apply, map_multiset_sum, map_multiset_sum,
    Multiset.map_map, Multiset.map_map, ← Multiset.sum_map_product_mul]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun q _ ↦ (h _ _).symm)

protected theorem comul_mul (x y : GrossmanLarson R α) :
    comul (R := R) (x * y) = comul x * comul y := by
  have h : (LinearMap.mul R (GrossmanLarson R α)).compr₂ (comul (R := R)) =
      (LinearMap.mul R (GrossmanLarson R α ⊗[R] GrossmanLarson R α)).compl₁₂ comul comul := by
    refine lhom_ext fun F ↦ lhom_ext fun G ↦ ?_
    change comul (R := R) ((of F : GrossmanLarson R α) * of G) = comul (of F) * comul (of G)
    rw [of_mul_of, map_multiset_sum, Multiset.map_map, comul_of, comul_of,
      ← Multiset.sum_map_product_mul]
    simp only [Function.comp_def, comul_of]
    rw [← Multiset.sum_bind, ← Multiset.map_bind, productMultiset_bind_antidiagonal,
      Multiset.map_bind, Multiset.sum_bind]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ ↦ ?_)
    rw [Algebra.TensorProduct.tmul_mul_tmul, of_mul_of, of_mul_of, tmul_sum_map_of]
  exact congr($h x y)

noncomputable instance instBialgebra : Bialgebra R (GrossmanLarson R α) :=
  .mk' R _ (by simp) (counit_product _ _)
    (by rw [← of_zero, comul_of]; simp [Algebra.TensorProduct.one_def])
    (GrossmanLarson.comul_mul _ _)

/-! ### Primitive elements -/

theorem isPrimitiveElem_of_singleton (T : UnorderedTree α) :
    Bialgebra.IsPrimitiveElem R (of {T} : GrossmanLarson R α) where
  counit_eq_zero := by simp
  comul_eq_tmul_add_tmul := by
    rw [comul_apply, toConnesKreimer_of, of'_singleton, comulPrim_ofTree, add_comm]
    rfl

theorem isPrimitiveElem_ι (x : ChapotonLivernet R α) : Bialgebra.IsPrimitiveElem R (ι x) := by
  induction x using ChapotonLivernet.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using hx.add hy
  | single T a =>
    rw [ChapotonLivernet.single_eq_smul_of]
    simpa using (isPrimitiveElem_of_singleton (R := R) T).smul a

/-! ### The pairing -/

theorem toConv_pairing_mul [DecidableEq α] (z w : ConnesKreimer R (UnorderedTree α)) :
    toConv (pairing (R := R) (z * w) ∘ₗ linearEquiv.toLinearMap) =
      toConv (pairing z ∘ₗ linearEquiv.toLinearMap) *
        toConv (pairing w ∘ₗ linearEquiv.toLinearMap) := by
  refine WithConv.ext (lhom_ext fun F ↦ ?_)
  simp only [LinearMap.convMul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply,
    toConnesKreimer_of, comul_of, map_multiset_sum, Multiset.map_map, Function.comp_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply]
  rw [pairing_symm, pairing_of'_mul]
  exact congrArg _ (Multiset.map_congr rfl fun p _ ↦ by rw [pairing_symm z, pairing_symm w])

end GrossmanLarson
