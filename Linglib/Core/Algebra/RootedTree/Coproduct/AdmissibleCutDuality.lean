/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.BigOperators.Ring.Multiset
public import Linglib.Core.Algebra.RootedTree.BMinus
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Linglib.Core.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Duality of the Grossman–Larson product and the Connes–Kreimer coproduct

Under the symmetry-weighted pairing, the Grossman–Larson product is the transpose of the
Connes–Kreimer coproduct `Δ^ρ`: `⟨x ⋆ y, z⟩ = ⟨y ⊗ x, Δ^ρ z⟩`. So the pairing turns the
Grossman–Larson product into the convolution product of linear functionals on the Connes–Kreimer
bialgebra, in the opposite order. Hoffman states the duality in this form, as a map of the
Grossman–Larson algebra to the graded dual.

## Main results

* `ConnesKreimer.pairing_gl_eq_pairing_coproduct`: the duality
  `⟨x ⋆ y, z⟩ = ⟨y ⊗ x, Δ^ρ z⟩`.
* `ConnesKreimer.isAdjointPair_product_comulAlgHom`: the same as a `LinearMap.IsAdjointPair`.
* `ConnesKreimer.toConv_pairing_product`: `⟨x ⋆ y, ·⟩ = ⟨y, ·⟩ * ⟨x, ·⟩` in the convolution
  algebra of linear functionals.
* `ConnesKreimer.pairing_product_assoc`: the two triple products pair equally against everything,
  since the convolution product is associative.

## Implementation notes

The tensor slots of the duality are crossed. The product `x ⋆ y` grafts the trees of `y` onto the
host `x`, while `Δ^ρ` puts the pruned crown in the first tensor slot and the trunk in the second,
so `y` pairs against crowns and `x` against trunks. The uncrossed statement is false: for the
one-vertex trees `x = •_p` and `y = •_q` and the chain `z` with root `p` and leaf `q`, the left
side is `1` and `⟨x ⊗ y, Δ^ρ z⟩` is `0`.

The duality is proved on basis forests `z = of' C` by recursion on the number of vertices. The
one-tree step uses the adjunction of `B⁺` and `B⁻` (`BMinus.lean`) and the Hochschild cocycle
property; the step for several trees uses the product rule of the pairing.

## References

* [foissy-2002]
* [oudom-guin-2008]
* [hoffman-2003]
-/

public section

open RoseTree UnorderedTree WithConv

namespace ConnesKreimer

open scoped TensorProduct
open GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Adjoint through the second tensor slot -/

private lemma pairing_tmul_lTensor_bPlus (a : α) (u v : ConnesKreimer R (UnorderedTree α))
    (V : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    pairing.tmul pairing (u ⊗ₜ[R] v) (LinearMap.lTensor _ (bPlus (R := R) a) V) =
      pairing.tmul pairing (u ⊗ₜ[R] bMinus (R := R) a v) V :=
  (LinearMap.IsAdjointPair.tmul (f₁ := .id) (g₁ := .id) (fun _ _ ↦ rfl)
    (isAdjointPair_bMinus_bPlus a) (u ⊗ₜ[R] v) V).symm

/-! ### Tensor-square of the pairing product rule -/

private lemma pairing_tmul_of'_of'_mul (A B : Forest (UnorderedTree α))
    (U V : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    pairing.tmul pairing (of' B ⊗ₜ[R] of' A) (U * V) =
      ((A.antidiagonal ×ˢ B.antidiagonal).map fun pq ↦
        pairing.tmul pairing (of' pq.2.1 ⊗ₜ[R] of' pq.1.1) U *
          pairing.tmul pairing (of' pq.2.2 ⊗ₜ[R] of' pq.1.2) V).sum := by
  induction U using TensorProduct.inductionOn with
  | add U₁ U₂ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂, Multiset.sum_map_add]
  | tmul u₁ u₂ =>
    induction V using TensorProduct.inductionOn with
    | add V₁ V₂ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂, Multiset.sum_map_add]
    | tmul v₁ v₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        pairing_of'_mul B u₁ v₁, pairing_of'_mul A u₂ v₂, smul_eq_mul,
        Multiset.sum_map_mul_sum_map]
      exact congrArg Multiset.sum <| Multiset.map_congr rfl fun _ _ ↦ by
        simp only [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]; ring

/-! ### The duality theorem -/

/-- The duality on a basis forest, by recursion on its number of vertices. -/
private theorem pairing_gl_of' (C : Forest (UnorderedTree α))
    (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (product x y) (of' C) = pairing.tmul pairing (y ⊗ₜ[R] x) (comulAlgHom (of' C)) := by
  rcases Multiset.empty_or_exists_mem C with rfl | ⟨T, hT⟩
  · -- No trees: both sides are counits.
    simp [Algebra.TensorProduct.one_def, counit_product]
  obtain ⟨C', rfl⟩ := Multiset.exists_cons_of_mem hT
  rcases Multiset.empty_or_exists_mem C' with rfl | ⟨T₂, hT₂⟩
  · -- One tree `B⁺_a W`: the `B⁻` recurrence on the left, the cocycle on the right.
    obtain ⟨a, W, rfl⟩ : ∃ a W, T = UnorderedTree.node a W := ⟨_, _, (node_eta T).symm⟩
    rw [Multiset.cons_zero, of'_singleton, ← bPlus_of', pairing_product_bPlus,
      comulAlgHom_bPlus_cocycle, map_add, LinearMap.BilinForm.tensorDistrib_tmul,
      pairing_tmul_lTensor_bPlus, ← pairing_gl_of' W, ← pairing_bMinus, pairing_one_right]
    ring
  · -- Several trees `T ::ₘ C'`: both sides are bilinear in `(x, y)`, so split off `T` on basis
    -- forests.
    have h : (product (R := R)).compr₂ (pairing.flip (of' (T ::ₘ C'))) =
        (TensorProduct.mk R _ _).flip.compr₂
          ((pairing.tmul pairing).flip (comulAlgHom (R := R) (of' (T ::ₘ C')))) :=
      lhom_ext' fun A ↦ lhom_ext' fun B ↦ by
        simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
          TensorProduct.mk_apply]
        rw [← Multiset.singleton_add, of'_add, pairing_product_of'_mul_of', map_mul,
          pairing_tmul_of'_of'_mul]
        exact congrArg Multiset.sum <| Multiset.map_congr rfl fun pq _ ↦ by
          rw [pairing_gl_of' {T}, pairing_gl_of' C']
    exact LinearMap.congr_fun₂ h x y
termination_by (C.map UnorderedTree.numNodes).sum
decreasing_by
  all_goals subst_vars; simp only [Multiset.map_cons, Multiset.sum_cons]
  · simp
  · have := (UnorderedTree.numNodes_pos T₂).trans_le
      (Multiset.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (Multiset.mem_map_of_mem _ hT₂))
    simp only [Multiset.map_singleton, Multiset.sum_singleton]; omega
  · have := UnorderedTree.numNodes_pos T
    omega

/-- The Grossman–Larson product is the transpose of the Connes–Kreimer coproduct under the
symmetry-weighted pairing, `⟨x ⋆ y, z⟩ = ⟨y ⊗ x, Δ^ρ z⟩`. The tensor slots are crossed:
the grafted factor `y` pairs against the pruned crowns and the host `x` against the trunks. -/
theorem pairing_gl_eq_pairing_coproduct (x y z : ConnesKreimer R (UnorderedTree α)) :
    pairing (product x y) z = pairing.tmul pairing (y ⊗ₜ[R] x) (comulAlgHom (R := R) z) :=
  LinearMap.congr_fun (lhom_ext' (f := pairing (product x y))
    (g := (pairing.tmul pairing (y ⊗ₜ[R] x)).comp (comulAlgHom (R := R)).toLinearMap)
    fun C ↦ pairing_gl_of' C x y) z

/-- The duality as an adjoint pair: the Grossman–Larson product with its factors swapped, as a map
out of the tensor square, is adjoint to the Connes–Kreimer coproduct. -/
theorem isAdjointPair_product_comulAlgHom :
    LinearMap.IsAdjointPair (pairing.tmul pairing) (pairing (R := R))
      (TensorProduct.lift (product (α := α)).flip) comulAlgHom := fun t z ↦ by
  induction t using TensorProduct.inductionOn with
  | tmul y x => exact pairing_gl_eq_pairing_coproduct x y z
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

/-! ### The pairing as a map to the convolution algebra -/

/-- The pairing turns the Grossman–Larson product into the convolution product of linear
functionals, in the opposite order. -/
theorem toConv_pairing_product (x y : ConnesKreimer R (UnorderedTree α)) :
    toConv (pairing (R := R) (product x y)) = toConv (pairing y) * toConv (pairing x) := by
  ext z
  have h : LinearMap.mul' R R ∘ₗ TensorProduct.map (pairing (R := R) y) (pairing x) =
      pairing.tmul pairing (y ⊗ₜ[R] x) := TensorProduct.ext' fun _ _ ↦ mul_comm _ _
  exact (pairing_gl_eq_pairing_coproduct x y (ConnesKreimer.of' z)).trans
    (LinearMap.congr_fun h _).symm

/-- The two triple Grossman–Larson products pair equally against everything, since the
convolution product is associative. -/
theorem pairing_product_assoc (x y z : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (product (product x y) z) = pairing (product x (product y z)) :=
  toConv_injective <| by simp only [toConv_pairing_product, mul_assoc]

end ConnesKreimer

