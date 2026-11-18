/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Linglib.Core.Combinatorics.RootedTree.Aut
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# The symmetry-weighted pairing on forests

This file defines the bilinear form on the module of forests `ConnesKreimer R (UnorderedTree α)`
for which the forests are an [orthogonal family](##GrossmanLarson.isOrthoᵢ_pairing), each paired
with itself to its number of symmetries, $\langle F, G\rangle = \delta_{F,G}\,|\mathrm{Aut}\,F|$.
The form is [symmetric](##GrossmanLarson.pairing_isSymm), and
[nondegenerate](##GrossmanLarson.pairing_nondegenerate) over a semiring of characteristic zero
without zero divisors. Foissy uses it to obtain the Connes–Kreimer coproduct as the transpose of
the Grossman–Larson product. It also [transposes](##GrossmanLarson.pairing_mul) the disjoint-union
product to the coproduct in which every tree is primitive,
$\langle x, yz\rangle = \langle\Delta(x), y \otimes z\rangle$.

## Implementation notes

The pairing is a form on one module, not a map between the Grossman–Larson algebra and the
Connes–Kreimer algebra, although each of its transposition laws relates a structure of the one to a
structure of the other. On one module it is a `LinearMap.BilinForm`, so that symmetry is
`LinearMap.IsSymm`, the form on the tensor square is `LinearMap.BilinForm.tmul`, and a
transposition is a `LinearMap.IsAdjointPair`.

## References

* [foissy-2021]
* [grossman-larson-1989]
* [oudom-guin-2008]
-/

@[expose] public section

open UnorderedTree ConnesKreimer
open scoped TensorProduct

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### The bilinear form -/

/-- The symmetry-weighted pairing: pairing with a forest `F` takes the coefficient of `F`, times
the number of symmetries of `F`. -/
noncomputable def pairing : LinearMap.BilinForm R (ConnesKreimer R (UnorderedTree α)) :=
  linearLift fun F ↦ (forestAutCard F : R) • lcoeff R F

theorem pairing_of' (F : Forest (UnorderedTree α)) :
    pairing (of' F) = (forestAutCard F : R) • lcoeff R F :=
  linearLift_of' _ F

@[simp] theorem pairing_of'_of' (F G : Forest (UnorderedTree α)) :
    pairing (of' F) (of' G) = if F = G then (forestAutCard F : R) else 0 := by
  rw [pairing_of', LinearMap.smul_apply, lcoeff_apply, coeff_of', smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  exact if_congr eq_comm rfl rfl

/-- The forests are pairwise orthogonal. -/
theorem isOrthoᵢ_pairing :
    (pairing (R := R)).IsOrthoᵢ (of' : Forest (UnorderedTree α) → _) :=
  fun F G h ↦ (pairing_of'_of' F G).trans (ite_eq_right h)

/-- The pairing is symmetric. -/
theorem pairing_isSymm : (pairing (R := R) (α := α)).IsSymm :=
  LinearMap.isSymm_iff_eq_flip.2 <| lhom_ext' fun F ↦ lhom_ext' fun G ↦ by
    rcases eq_or_ne F G with rfl | h
    · simp
    · simp [h, h.symm]

theorem pairing_comm (x y : ConnesKreimer R (UnorderedTree α)) : pairing x y = pairing y x :=
  pairing_isSymm.eq x y

theorem pairing_apply_of' (x : ConnesKreimer R (UnorderedTree α))
    (G : Forest (UnorderedTree α)) : pairing x (of' G) = x.coeff G * (forestAutCard G : R) := by
  rw [pairing_comm, pairing_of', LinearMap.smul_apply, lcoeff_apply, smul_eq_mul, mul_comm]

/-- Pairing with the empty forest is the counit. -/
theorem pairing_one :
    pairing (1 : ConnesKreimer R (UnorderedTree α)) = (counit (R := R)).toLinearMap :=
  lhom_ext' fun F ↦ by rcases eq_or_ne F 0 with rfl | h <;> simp [← of'_zero, *, eq_comm]

@[simp] theorem pairing_one_left (x : ConnesKreimer R (UnorderedTree α)) :
    pairing 1 x = counit x :=
  congr($pairing_one x)

@[simp] theorem pairing_one_right (x : ConnesKreimer R (UnorderedTree α)) :
    pairing x 1 = counit x :=
  (pairing_comm x 1).trans (pairing_one_left x)

/-! ### Nondegeneracy -/

section NoZeroDivisors

variable [CharZero R] [NoZeroDivisors R]

theorem pairing_separatingLeft : (pairing (R := R) (α := α)).SeparatingLeft := fun x h ↦
  ext_coeff fun G ↦ (mul_eq_zero.1 ((pairing_apply_of' x G).symm.trans (h _))).resolve_right
    (Nat.cast_ne_zero.2 (forestAutCard_pos G).ne')

/-- Over a semiring of characteristic zero without zero divisors, the pairing is nondegenerate. -/
theorem pairing_nondegenerate : (pairing (R := R) (α := α)).Nondegenerate :=
  ⟨pairing_separatingLeft, fun y h ↦
    pairing_separatingLeft y fun x ↦ (pairing_comm y x).trans (h x)⟩

end NoZeroDivisors

/-- Over a cancellative semiring of characteristic zero, an element is determined by its
pairings. -/
theorem pairing_injective [CharZero R] [IsCancelMulZero R] :
    Function.Injective (pairing (R := R) (α := α)) := fun x y h ↦
  ext_coeff fun G ↦ mul_right_cancel₀ (Nat.cast_ne_zero.2 (forestAutCard_pos G).ne') <| by
    simpa only [pairing_apply_of'] using congr($h (of' G))

/-! ### Multiplication is adjoint to the coproduct of the symmetric algebra

Pairing against a disjoint union splits the other argument over its antidiagonal; the weights
recombine by `UnorderedTree.forestAutCard_add`. -/

theorem pairing_of'_mul_of' (W C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (of' W) (of' C₁ * of' C₂) =
      (W.antidiagonal.map fun p ↦
        pairing (R := R) (of' p.1) (of' C₁) * pairing (of' p.2) (of' C₂)).sum := by
  rw [Multiset.sum_map_eq_nsmul_single (C₁, C₂) fun p hp _ ↦ ?_, ← of'_add]
  · simp only [pairing_of'_of', ite_true, nsmul_eq_mul]
    split_ifs with hW
    · rw [hW, ← Nat.cast_mul, ← Nat.cast_mul, forestAutCard_add]
    · rw [Multiset.count_eq_zero.mpr (mt (Multiset.mem_antidiagonal (x := (C₁, C₂))).mp
        (Ne.symm hW)), Nat.cast_zero, zero_mul]
  · rw [pairing_of'_of', pairing_of'_of']
    split_ifs with h₁ h₂ <;> simp_all [Prod.ext_iff]

/-- Pairing a basis forest against a product splits the forest over its antidiagonal. -/
theorem pairing_of'_mul (W : Forest (UnorderedTree α))
    (z₁ z₂ : ConnesKreimer R (UnorderedTree α)) :
    pairing (of' W) (z₁ * z₂) =
      (W.antidiagonal.map fun p ↦ pairing (of' p.1) z₁ * pairing (of' p.2) z₂).sum := by
  induction z₁ using induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb, Multiset.sum_map_add]
  | single F r =>
    induction z₂ using induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mul_add, map_add, ha, hb, Multiset.sum_map_add]
    | single G s =>
      simp only [← smul_of', smul_mul_smul_comm, map_smul, smul_eq_mul,
        pairing_of'_mul_of', mul_mul_mul_comm r, Multiset.sum_map_mul_left]

/-- The pairing transposes the disjoint-union product to the coproduct in which every tree is
primitive: `⟨x, y z⟩ = ⟨Δ(x), y ⊗ z⟩`. -/
theorem pairing_mul (x z₁ z₂ : ConnesKreimer R (UnorderedTree α)) :
    pairing x (z₁ * z₂) = pairing.tmul pairing (comulPrim x) (z₁ ⊗ₜ z₂) := by
  induction x using induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single W r =>
    rw [← smul_of', map_smul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      pairing_of'_mul, comulPrim_of']
    have h := map_multiset_sum ((pairing.tmul pairing).flip (z₁ ⊗ₜ z₂))
      (W.antidiagonal.map fun p ↦ (of' p.1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] of' p.2)
    rw [LinearMap.flip_apply, Multiset.map_map] at h
    rw [h]
    exact congrArg _ (congrArg _ (Multiset.map_congr rfl fun p _ ↦ mul_comm _ _))

/-- Multiplication and the coproduct of the symmetric algebra are an adjoint pair. -/
theorem isAdjointPair_comulPrim_mul' :
    LinearMap.IsAdjointPair (pairing (R := R)) (pairing.tmul pairing)
      (comulPrim (T := UnorderedTree α)) (LinearMap.mul' R _) := fun x z ↦ by
  induction z using TensorProduct.inductionOn with
  | tmul z₁ z₂ => exact (pairing_mul x z₁ z₂).symm
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Pairing a Grossman–Larson product against a Connes–Kreimer product splits both of its
factors, `⟨A ⋆ B, C₁ · C₂⟩ = Σ_{A = A₁ + A₂} Σ_{B = B₁ + B₂} ⟨A₁ ⋆ B₁, C₁⟩ ⟨A₂ ⋆ B₂, C₂⟩`. -/
theorem pairing_product_of'_mul_of' (A B C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (product (of' A) (of' B)) (of' C₁ * of' C₂) =
      ((A.antidiagonal ×ˢ B.antidiagonal).map fun pq ↦
        pairing (R := R) (product (of' pq.1.1) (of' pq.2.1)) (of' C₁) *
          pairing (product (of' pq.1.2) (of' pq.2.2)) (of' C₂)).sum := by
  have h := map_multiset_sum ((pairing.tmul pairing).flip (of' (R := R) C₁ ⊗ₜ of' C₂))
    ((A.antidiagonal ×ˢ B.antidiagonal).map fun pq ↦
      product (of' (R := R) pq.1.1) (of' pq.2.1) ⊗ₜ[R] product (of' pq.1.2) (of' pq.2.2))
  rw [LinearMap.flip_apply, Multiset.map_map] at h
  rw [pairing_mul, comulPrim_product_of'_of', h]
  exact congrArg _ (Multiset.map_congr rfl fun pq _ ↦ mul_comm _ _)

end GrossmanLarson
